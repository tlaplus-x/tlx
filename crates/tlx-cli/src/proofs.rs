//! Persist the mandatory Lean output before an optimized search starts.
//! This module never invokes Lean or another verification process.

use std::fs::OpenOptions;
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

use tlx_eval::model::InterpModel;

use crate::out::{self, code};

pub(crate) fn emit(model: &InterpModel, proofdir: Option<&Path>, applied: Option<(&str, &[String])>) -> Result<(), std::process::ExitCode> {
    let (rule, fields) = applied.map_or((None, &[][..]), |(rule, fields)| (Some(rule), fields));
    let contents = tlx_sema::optimize::projection_lean(
        &model.ip.prog,
        &model.ip.cfg,
        rule,
        fields,
        model.view_expr(),
        model.projection_certificate(),
        model.ordered_projection(),
    );
    let path = write(proofdir, &contents).map_err(|e| {
        out::error(code::GENERAL, &format!("Cannot write mandatory optimization Lean output: {e}"));
        std::process::ExitCode::from(2)
    })?;
    let coverage = if model.has_projected_symmetry() && model.projection_certificate().is_some() {
        if model.projection_certificate().is_some_and(|c| c.contains("namespace TlxOptimization.GeneratedErasedEquivSymmetry")) {
            "parametric erasure/equivariant-symmetry composition certificate; lowering, totality, group closure and runtime remain trusted"
        } else {
            "parametric erasure/keyed-symmetry composition certificate; lowering, totality, group closure and runtime remain trusted"
        }
    } else if model.projection_certificate().is_some() && model.ordered_projection().is_some() {
        "parametric ordered-allocation rule-IR certificate; lowering and runtime remain trusted"
    } else if rule == Some("unobserved-state-projection") && model.projection_certificate().is_some() {
        "parametric unobserved-state rule-IR certificate; lowering and runtime remain trusted"
    } else if rule == Some("relative-age-projection") && model.projection_certificate().is_some() {
        "parametric relative-age rule-IR certificate; lowering and runtime remain trusted"
    } else if rule == Some("phase-field-projection") && model.projection_certificate().is_some() {
        "parametric phase-field rule-IR certificate; lowering and runtime remain trusted"
    } else if rule == Some("sequence-length-projection") && model.projection_certificate().is_some() {
        "parametric sequence-length rule-IR certificate; lowering and runtime remain trusted"
    } else if rule == Some("keyed-symmetry") && model.projection_certificate().is_some_and(|c| c.contains("GeneratedChooseSymmetry")) {
        "parametric choice-symmetry rule-IR certificate; lowering, totality, group closure and runtime remain trusted"
    } else if rule == Some("keyed-symmetry") && model.projection_certificate().is_some() {
        if model.projection_certificate().is_some_and(|c| c.contains("namespace TlxOptimization.GeneratedEquivSymmetry")) {
            "parametric equivariant-symmetry rule-IR certificate; lowering, totality, group closure and runtime remain trusted"
        } else {
            "parametric keyed-symmetry rule-IR certificate; lowering, totality, group closure and runtime remain trusted"
        }
    } else if model.projection_certificate().is_some() {
        "parametric history rule-IR certificate; lowering and runtime remain trusted"
    } else {
        "no reduction applied; rule algebra only"
    };
    out::info(code::GENERAL, &format!("Lean output: {} (not verified; {coverage}).", path.display()));
    Ok(())
}

/// Persist `contents` under `proofdir` (when explicitly given) or under the
/// default content-addressed cache (`$TLX_CACHE/proofs`, else
/// `~/.cache/tlx/proofs`, falling back to a private per-user directory
/// `$TMPDIR/tlx-proofs-<uid>` with mode `0700` on Unix, or `$TMPDIR/tlx-proofs`
/// elsewhere, if the default cache location is unwritable).
fn write(proofdir: Option<&Path>, contents: &str) -> io::Result<PathBuf> {
    if let Some(dir) = proofdir {
        return write_in(dir, contents);
    }
    let env = tlx_base::knobs::Env::process();
    if let Some(cache) = env.path("TLX_CACHE") {
        return write_in(&cache.join("proofs"), contents);
    }
    let primary =
        std::env::var_os("HOME").filter(|h| !h.is_empty()).map(PathBuf::from).map(|home| home.join(".cache").join("tlx").join("proofs"));
    if let Some(dir) = primary {
        match write_in(&dir, contents) {
            Ok(path) => return Ok(path),
            Err(first) => {
                if let Ok(fallback) = private_fallback_dir() {
                    if let Ok(path) = write_in(&fallback, contents) {
                        return Ok(path);
                    }
                }
                return Err(first);
            }
        }
    }
    let fallback = private_fallback_dir()?;
    write_in(&fallback, contents)
}

fn private_fallback_dir() -> io::Result<PathBuf> {
    private_fallback_dir_in(&std::env::temp_dir())
}

#[cfg(unix)]
fn private_fallback_dir_in(tmp_root: &Path) -> io::Result<PathBuf> {
    use std::fs::DirBuilder;
    use std::os::unix::fs::{DirBuilderExt, MetadataExt, PermissionsExt};

    let uid = current_uid_in(tmp_root)?;
    let dir = tmp_root.join(format!("tlx-proofs-{uid}"));
    match DirBuilder::new().mode(0o700).create(&dir) {
        Ok(()) => {}
        Err(err) if err.kind() == io::ErrorKind::AlreadyExists => {}
        Err(err) => return Err(err),
    }
    // Use lstat (`symlink_metadata`) so symlinks are rejected rather than followed.
    let meta = std::fs::symlink_metadata(&dir)?;
    if !meta.file_type().is_dir() {
        return Err(io::Error::new(io::ErrorKind::PermissionDenied, format!("fallback proof path is not a directory: {}", dir.display())));
    }
    if meta.uid() != uid {
        return Err(io::Error::new(
            io::ErrorKind::PermissionDenied,
            format!("fallback proof directory is not owned by current user: {}", dir.display()),
        ));
    }
    let mode = meta.permissions().mode();
    if (mode & 0o077) != 0 || (mode & 0o700) != 0o700 {
        return Err(io::Error::new(
            io::ErrorKind::PermissionDenied,
            format!("fallback proof directory must have private 0700 permissions: {}", dir.display()),
        ));
    }
    Ok(dir)
}

/// Determine the current effective UID in `tmp_root` without `unsafe` FFI by
/// creating an exclusive `0600` probe file and inspecting its inode via `fstat`.
#[cfg(unix)]
fn current_uid_in(tmp_root: &Path) -> io::Result<u32> {
    use std::os::unix::fs::{MetadataExt, OpenOptionsExt};

    static PROBE: AtomicU64 = AtomicU64::new(0);
    let pid = std::process::id();
    for _ in 0..1_000 {
        let n = PROBE.fetch_add(1, Ordering::Relaxed);
        let probe = tmp_root.join(format!(".tlx-proofs-uid.{pid}.{n}"));
        match OpenOptions::new().write(true).create_new(true).mode(0o600).open(&probe) {
            Ok(file) => {
                let res = file.metadata().map(|m| m.uid());
                drop(file);
                let _ = std::fs::remove_file(&probe);
                return res;
            }
            Err(err) if err.kind() == io::ErrorKind::AlreadyExists => continue,
            Err(err) => return Err(err),
        }
    }
    Err(io::Error::new(io::ErrorKind::AlreadyExists, "cannot reserve a temporary uid probe file"))
}

#[cfg(not(unix))]
fn private_fallback_dir_in(tmp_root: &Path) -> io::Result<PathBuf> {
    Ok(tmp_root.join("tlx-proofs"))
}

/// Content-addressed write under `base/<key>/Optimization.lean`.
/// Identical certificates reuse the existing slot; distinct certificates never
/// overwrite an existing file (even on hash collision or concurrent runs).
fn write_in(base: &Path, contents: &str) -> io::Result<PathBuf> {
    std::fs::create_dir_all(base)?;
    let key = content_key(contents.as_bytes());
    for suffix in 0u32..10_000 {
        let slot = if suffix == 0 { base.join(&key) } else { base.join(format!("{key}-{suffix}")) };
        std::fs::create_dir_all(&slot)?;
        let path = slot.join("Optimization.lean");
        if let Ok(existing) = std::fs::read(&path) {
            if existing == contents.as_bytes() {
                return Ok(path);
            }
            continue;
        }
        let tmp = write_exclusive_tmp(&slot, contents.as_bytes())?;
        if link_or_create_new(&tmp, &path, contents.as_bytes(), |src, dst| std::fs::hard_link(src, dst))? {
            return Ok(path);
        }
    }
    Err(io::Error::new(io::ErrorKind::AlreadyExists, "cannot reserve a fresh Lean output directory"))
}

fn acquire_slot_lock(path: &Path) -> io::Result<std::fs::File> {
    let lock_path = path.with_extension("lean.lock");
    let mut opts = OpenOptions::new();
    opts.create(true).write(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        opts.mode(0o600);
    }
    let file = opts.open(&lock_path)?;
    // OS-managed advisory lock: automatically released by the kernel on drop or crash,
    // so an interrupted writer can never leave a permanently wedged slot.
    file.lock()?;
    Ok(file)
}

/// Publish `tmp` to `path` without overwriting any existing file.
/// Returns `Ok(true)` if `path` now holds `contents` (newly published or
/// deduplicated against identical bytes), `Ok(false)` if another writer owns
/// `path` with distinct bytes (caller should advance to the next slot), or
/// `Err(e)` on I/O failure. Always removes `tmp`.
fn link_or_create_new(
    tmp: &Path,
    path: &Path,
    contents: &[u8],
    hard_link: impl FnOnce(&Path, &Path) -> io::Result<()>,
) -> io::Result<bool> {
    match hard_link(tmp, path) {
        Ok(()) => {
            let _ = std::fs::remove_file(tmp);
            Ok(true)
        }
        Err(e) if e.kind() == io::ErrorKind::AlreadyExists => {
            let _ = std::fs::remove_file(tmp);
            Ok(std::fs::read(path).is_ok_and(|existing| existing == contents))
        }
        Err(e) if matches!(e.kind(), io::ErrorKind::Unsupported | io::ErrorKind::PermissionDenied) => {
            // Filesystems without hard links report Unsupported or EPERM (PermissionDenied on
            // Linux FAT/vfat/etc.). Serialize per-slot publication with an exclusive lock file
            // and atomically rename the already-complete `tmp` file so readers never observe
            // partial/truncated contents and concurrent identical runs deduplicate cleanly.
            let _lock = match acquire_slot_lock(path) {
                Ok(guard) => guard,
                Err(err) => {
                    let _ = std::fs::remove_file(tmp);
                    return Err(err);
                }
            };
            match std::fs::read(path) {
                Ok(existing) => {
                    let _ = std::fs::remove_file(tmp);
                    Ok(existing == contents)
                }
                Err(err) if err.kind() == io::ErrorKind::NotFound => {
                    if let Err(ren_err) = std::fs::rename(tmp, path) {
                        let _ = std::fs::remove_file(tmp);
                        return Err(ren_err);
                    }
                    Ok(true)
                }
                Err(err) => {
                    let _ = std::fs::remove_file(tmp);
                    Err(err)
                }
            }
        }
        Err(e) => {
            let _ = std::fs::remove_file(tmp);
            Err(e)
        }
    }
}

fn write_exclusive_tmp(slot: &Path, contents: &[u8]) -> io::Result<PathBuf> {
    for _ in 0..1_000 {
        let tmp = unique_tmp(slot);
        let mut opts = OpenOptions::new();
        opts.write(true).create_new(true);
        #[cfg(unix)]
        {
            use std::os::unix::fs::OpenOptionsExt;
            opts.mode(0o600);
        }
        match opts.open(&tmp) {
            Ok(mut file) => {
                if let Err(err) = file.write_all(contents) {
                    let _ = std::fs::remove_file(&tmp);
                    return Err(err);
                }
                return Ok(tmp);
            }
            Err(err) if err.kind() == io::ErrorKind::AlreadyExists => continue,
            Err(err) => return Err(err),
        }
    }
    Err(io::Error::new(io::ErrorKind::AlreadyExists, "cannot reserve a fresh temporary Lean output file"))
}

fn unique_tmp(slot: &Path) -> PathBuf {
    static NEXT: AtomicU64 = AtomicU64::new(0);
    let n = NEXT.fetch_add(1, Ordering::Relaxed);
    slot.join(format!("Optimization.lean.tmp.{}.{n}", std::process::id()))
}

/// 128-bit content hash (32 lowercase hex chars) from two independent 64-bit
/// hashes plus length, avoiding any external crypto dependency.
fn content_key(bytes: &[u8]) -> String {
    let h1 = tlx_base::hash::hash_bytes(bytes);
    let mut h2: u64 = 0xcbf2_9ce4_8422_2325 ^ (bytes.len() as u64);
    for &b in bytes.iter().rev() {
        h2 ^= u64::from(b);
        h2 = h2.wrapping_mul(0x0100_0000_01b3);
    }
    format!("{h1:016x}{h2:016x}")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(unix)]
    #[test]
    fn private_fallback_dir_enforces_owner_only_0700_and_rejects_symlinks() {
        use std::os::unix::fs::{symlink, MetadataExt, PermissionsExt};

        let root = tlx_testkit::TempDir::new("proofs-fallback");
        let dir = private_fallback_dir_in(root.path()).expect("create private fallback dir");
        let name = dir.file_name().unwrap().to_str().unwrap();
        assert!(name.starts_with("tlx-proofs-"), "expected per-user dir name, got {name}");
        let meta = std::fs::symlink_metadata(&dir).unwrap();
        assert!(meta.file_type().is_dir());
        assert_eq!(meta.permissions().mode() & 0o777, 0o700);
        assert_eq!(name, format!("tlx-proofs-{}", meta.uid()));

        // Reusing an existing valid 0700 owner directory succeeds.
        assert_eq!(private_fallback_dir_in(root.path()).unwrap(), dir);

        // Loose group/other permissions must be refused.
        std::fs::set_permissions(&dir, std::fs::Permissions::from_mode(0o755)).unwrap();
        let err = private_fallback_dir_in(root.path()).unwrap_err();
        assert_eq!(err.kind(), io::ErrorKind::PermissionDenied);

        // A symlink at the fallback path must be refused.
        std::fs::remove_dir(&dir).unwrap();
        let target = root.join("target");
        std::fs::create_dir(&target).unwrap();
        std::fs::set_permissions(&target, std::fs::Permissions::from_mode(0o700)).unwrap();
        symlink(&target, &dir).unwrap();
        let err = private_fallback_dir_in(root.path()).unwrap_err();
        assert_eq!(err.kind(), io::ErrorKind::PermissionDenied);
    }

    #[test]
    fn exclusive_tmp_retries_without_truncating_preexisting_file() {
        let root = tlx_testkit::TempDir::new("proofs-exclusive-tmp");
        let contents = "-- lean proof payload\n";
        let key = content_key(contents.as_bytes());
        let slot = root.join(&key);
        std::fs::create_dir_all(&slot).unwrap();

        // Pre-create a block of candidate temp filenames so the first create_new
        // attempt(s) collide regardless of other tests sharing NEXT in this process.
        let pid = std::process::id();
        let mut decoys = Vec::new();
        for n in 0u64..16 {
            let decoy = slot.join(format!("Optimization.lean.tmp.{pid}.{n}"));
            std::fs::write(&decoy, "do-not-truncate").unwrap();
            decoys.push(decoy);
        }

        let path = write_in(root.path(), contents).expect("write_in retries past existing tmp");
        assert_eq!(std::fs::read_to_string(&path).unwrap(), contents);
        for decoy in decoys {
            assert_eq!(std::fs::read_to_string(&decoy).unwrap(), "do-not-truncate", "pre-existing temp file must not be truncated");
        }
    }

    #[test]
    fn link_or_create_new_falls_back_on_permission_denied_and_unsupported() {
        for kind in [io::ErrorKind::PermissionDenied, io::ErrorKind::Unsupported] {
            let root = tlx_testkit::TempDir::new("proofs-link-fallback");
            let contents = b"-- lean certificate payload\n";

            // 1. Fresh destination succeeds via create_new fallback and removes tmp.
            let tmp = write_exclusive_tmp(root.path(), contents).unwrap();
            let dst = root.join("Optimization.lean");
            let published = link_or_create_new(&tmp, &dst, contents, |_, _| Err(io::Error::new(kind, "no hard links")))
                .expect("fallback create_new should succeed");
            assert!(published, "expected Ok(true) for fresh publish ({kind:?})");
            assert!(!tmp.exists(), "tmp file must be removed after fallback ({kind:?})");
            assert_eq!(std::fs::read(&dst).unwrap(), contents);
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                assert_eq!(std::fs::symlink_metadata(&dst).unwrap().permissions().mode() & 0o777, 0o600);
            }

            // 2. Identical existing destination deduplicates without error and removes tmp.
            let tmp2 = write_exclusive_tmp(root.path(), contents).unwrap();
            let deduped = link_or_create_new(&tmp2, &dst, contents, |_, _| Err(io::Error::new(kind, "no hard links")))
                .expect("matching-bytes dedup should succeed");
            assert!(deduped, "expected Ok(true) for matching-bytes dedup ({kind:?})");
            assert!(!tmp2.exists(), "tmp file must be removed after dedup ({kind:?})");
            assert_eq!(std::fs::read(&dst).unwrap(), contents);

            // 3. Distinct existing destination is never overwritten; returns Ok(false).
            let other = b"-- distinct certificate payload\n";
            let tmp3 = write_exclusive_tmp(root.path(), other).unwrap();
            let collided = link_or_create_new(&tmp3, &dst, other, |_, _| Err(io::Error::new(kind, "no hard links")))
                .expect("distinct-bytes collision should return Ok(false)");
            assert!(!collided, "expected Ok(false) on distinct existing bytes ({kind:?})");
            assert!(!tmp3.exists(), "tmp file must be removed after collision ({kind:?})");
            assert_eq!(std::fs::read(&dst).unwrap(), contents, "existing distinct file must never be overwritten ({kind:?})");

            // 4. Error from fallback create_new is propagated cleanly (missing parent -> NotFound).
            let tmp4 = write_exclusive_tmp(root.path(), contents).unwrap();
            let missing_dst = root.join("missing-dir").join("Optimization.lean");
            let err = link_or_create_new(&tmp4, &missing_dst, contents, |_, _| Err(io::Error::new(kind, "no hard links")))
                .expect_err("create_new failure must propagate");
            assert_eq!(err.kind(), io::ErrorKind::NotFound);
            assert!(!tmp4.exists(), "tmp file must be removed on fallback error ({kind:?})");
        }

        // 5. When create_new itself fails with PermissionDenied, propagate PermissionDenied cleanly.
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            let root = tlx_testkit::TempDir::new("proofs-link-fallback-ro");
            if current_uid_in(root.path()).ok() != Some(0) {
                let ro_dir = root.join("readonly");
                std::fs::create_dir(&ro_dir).unwrap();
                std::fs::set_permissions(&ro_dir, std::fs::Permissions::from_mode(0o500)).unwrap();
                let contents = b"-- lean certificate payload\n";
                let tmp = write_exclusive_tmp(root.path(), contents).unwrap();
                let dst = ro_dir.join("Optimization.lean");
                let err = link_or_create_new(&tmp, &dst, contents, |_, _| {
                    Err(io::Error::new(io::ErrorKind::PermissionDenied, "EPERM from link(2)"))
                })
                .expect_err("unwritable destination must propagate PermissionDenied");
                assert_eq!(err.kind(), io::ErrorKind::PermissionDenied);
                assert!(!tmp.exists(), "tmp file must be removed on PermissionDenied fallback failure");
                // Restore write bit so TempDir cleanup succeeds.
                std::fs::set_permissions(&ro_dir, std::fs::Permissions::from_mode(0o700)).unwrap();
            }
        }
    }
}
