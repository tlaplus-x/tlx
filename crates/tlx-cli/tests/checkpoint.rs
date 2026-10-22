//! `-checkpoint` and `-recover` (docs/scale.md §9.2): a run killed
//! after a checkpoint (aborted by `TLX_CHECKPOINT_ABORT`, or SIGKILLed)
//! and recovered gives the results of an uninterrupted run: the same
//! verdict, counts, depth and trace length (one worker: the same trace),
//! with the interpreter and `-compile`, other numbers of workers, VIEW
//! (representatives in BFS order), liveness, the disk tier, a layout miss
//! after the recovery and TLCSet registers. SIGINT keeps a committed
//! checkpoint; a checkpoint of another run, or a damaged one, is refused.

#![cfg(unix)]

use std::os::unix::process::CommandExt;
use std::path::Path;
use std::process::Stdio;
use std::time::{Duration, Instant};

/// Strings built at run time (the intern order is restored), a liveness
/// property TLC finds violated, about 1,700 states over 80 levels.
const LIVE: &str = r#"---- MODULE CkLive ----
EXTENDS Naturals, Sequences, TLC
VARIABLES x, y, s
Init == x = 0 /\ y = 0 /\ s = "n0"
Next == \/ x < 40 /\ x' = x + 1 /\ y' = y /\ s' = "n" \o ToString(x' * 1000 + y')
        \/ y < 40 /\ y' = y + 1 /\ x' = x /\ s' = "n" \o ToString(x' * 1000 + y')
        \/ x = 40 /\ y = 40 /\ x' = 0 /\ y' = 0 /\ s' = "n0"
Spec == Init /\ [][Next]_<<x, y, s>> /\ WF_<<x, y, s>>(Next)
Live == []<>(x = 0)
Bad == <>[](x > 0)
====
"#;
const LIVE_CFG: &str = "SPECIFICATION Spec\nPROPERTY Live Bad\nCHECK_DEADLOCK FALSE\n";

const CHAIN: &str = r#"---- MODULE CkChain ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x < 100 /\ x' = x + 1
Live == <>(x = 101)
====
"#;

/// Initial nodes and every historical edge survive repeated recovery,
/// including checkpoints taken by a recovered run.
#[test]
fn repeated_recovery_preserves_liveness() {
    let dir = tlx_testkit::TempDir::with_spec("chain", CHAIN, "INIT Init\nNEXT Next\nPROPERTY Live\nCHECK_DEADLOCK FALSE\n");
    for tier in [&[][..], &["-compile"]] {
        let env = [("TLX_PARANOID", "1"), ("TLX_NATIVE_SYNC", "1")];
        let args = [tier, &["-workers", "1", "-stats"]].concat();
        let (code, want) = run(&dir, "CkChain", &args, &env);
        assert_eq!(code, 13, "{want}");
        for recoveries in [1, 2, 3] {
            let md = dir.child_path("md");
            let mut checkpoint_env = env.to_vec();
            checkpoint_env.extend([("TLX_CHECKPOINT_STATES", "20"), ("TLX_CHECKPOINT_ABORT", "1")]);
            for generation in 0..recoveries {
                let flag = if generation == 0 { "-metadir" } else { "-recover" };
                let a = [&args[..], &[flag, md.to_str().unwrap()]].concat();
                let (code, out) = run(&dir, "CkChain", &a, &checkpoint_env);
                assert_eq!(code, 134, "{out}");
                assert!(md.join("checkpoint/MANIFEST").is_file(), "{out}");
            }
            let a = [&args[..], &["-recover", md.to_str().unwrap()]].concat();
            let (code, out) = run(&dir, "CkChain", &a, &env);
            assert_eq!(code, 13, "{tier:?}, {recoveries} recoveries:\n{out}");
            assert_eq!(results(&out, true, true), results(&want, true, true), "{out}");
            assert!(out.contains("liveness: edge graph (CSR)"), "{out}");
            assert!(!out.contains("liveness: behavior graph (search again)"), "{out}");
            assert!(!md.exists());
        }
    }
}

/// VIEW hides h, which the guards read: which state of a class is found
/// first (in BFS order) decides what is reachable (tests/specs/VR1).
const VIEW: &str = r#"---- MODULE CkView ----
EXTENDS Naturals
VARIABLES a, b, c, h
Init == a = 0 /\ b = 0 /\ c = 0 /\ h = 0
Next == \/ a < 12 /\ h # 4 /\ a' = a + 1 /\ h' = (h * 3 + b + 1) % 7 /\ UNCHANGED <<b, c>>
        \/ b < 12 /\ h # 5 /\ b' = b + 1 /\ h' = (h + a + c) % 7 /\ UNCHANGED <<a, c>>
        \/ c < 12 /\ h < 5 /\ c' = c + 1 /\ h' = (h * 2 + a) % 7 /\ UNCHANGED <<a, b>>
        \/ h = 6 /\ a' = (a + b) % 13 /\ h' = 0 /\ UNCHANGED <<b, c>>
View == <<a, b, c>>
Inv == ~(a = 11 /\ b = 12 /\ c = 12)
====
"#;
const VIEW_CFG: &str = "INIT Init\nNEXT Next\nVIEW View\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n";

/// The TLCSet register 1 counts the states worker 0 expands (all of them
/// with one worker: restored from the checkpoint); y changes shape late
/// (a layout miss of `-compile` after the checkpoints).
const REG: &str = r#"---- MODULE CkReg ----
EXTENDS Naturals, TLC
VARIABLES x, y, z
Init == x = 0 /\ y = 0 /\ z = 0 /\ TLCSet(1, 0)
Next == /\ TLCSet(1, TLCGet(1) + 1)
        /\ \/ x < 60 /\ x' = x + 1 /\ z' = z /\ y' = IF x' > 45 THEN <<"late", x'>> ELSE y
           \/ z < 30 /\ z' = z + 1 /\ x' = x /\ y' = y
Post == PrintT(<<"expanded", TLCGet(1)>>)
====
"#;
const REG_CFG: &str = "INIT Init\nNEXT Next\nPOSTCONDITION Post\nCHECK_DEADLOCK FALSE\n";

/// A record whose field names are strings created at run time in the
/// reverse of their text order: "k9" is created first (expanding the
/// initial state) but is a field only of the last states, so the queued
/// states of a checkpoint mention "k8" first. Field order, hence
/// fingerprints, follow the intern order, which the recovered run must
/// restore rather than rebuild from the queue (TLC: 1,753 distinct states,
/// 7,000 generated, depth 19; the whole space, so the counts do not depend
/// on the number of workers).
const REC: &str = r#"---- MODULE CkRec ----
EXTENDS Naturals, Sequences, TLC
VARIABLE r
Key(i) == "k" \o ToString(9 - i)
Init == r = <<>>
Next == \/ \E k \in DOMAIN r : r[k] < 2 /\ r' = [r EXCEPT ![k] = r[k] + 1]
        \/ \E i \in 0..5 : /\ Key(i) \notin DOMAIN r
                           /\ i = 0 => DOMAIN r = {Key(j) : j \in 1..5}
                           /\ r' = [k \in DOMAIN r \cup {Key(i)} |-> IF k \in DOMAIN r THEN r[k] ELSE 0]
Inv == \A k \in DOMAIN r : r[k] \in 0..2
====
"#;
const REC_CFG: &str = "INIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n";

/// 600,000 states over 1,200 levels: long enough to be killed while it runs.
const BIG: &str = r#"---- MODULE CkBig ----
EXTENDS Naturals
VARIABLES x, y
Init == x = 0 /\ y = 0
Next == \/ x < 1199 /\ x' = x + 1 /\ y' = y
        \/ y < 499 /\ y' = y + 1 /\ x' = x
====
"#;
const BIG_CFG: &str = "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n";

/// Variables of the environment that change what a run does.
fn command(dir: &Path, name: &str, args: &[&str], env: &[(&str, &str)]) -> tlx_testkit::cli::Tlx {
    let mut cmd = tlx_testkit::tlx!();
    cmd.args(["check", &format!("{name}.tla"), "-config", &format!("{name}.cfg")]).args(args).dir(dir);
    cmd.envs(env.iter().copied());
    cmd
}

/// `tlx check name.tla` with `args` and environment `env`: exit code and
/// output (stdout and stderr).
fn run(dir: &Path, name: &str, args: &[&str], env: &[(&str, &str)]) -> (i32, String) {
    let out = command(dir, name, args, env).run();
    (out.code, out.text())
}

/// What a recovered run must reproduce: the verdict, counts and depth (with
/// `one` worker the states left on the queue too: after a failure with
/// several, that number varies), and with `exact` the trace (else its
/// length) and the postcondition's output (the registers of worker 0).
fn results(out: &str, exact: bool, one: bool) -> Vec<String> {
    let mut keep = Vec::new();
    let mut states = 0;
    for l in out.lines() {
        if l.starts_with("State ") && l.contains(':') {
            states += 1;
        }
        let verdict =
            l.starts_with("Error:") || l.contains("No error has been found") || l.contains("is violated") || l.contains("was violated");
        let counts = (l.ends_with("states left on queue.") && !l.starts_with("Progress(")) || l.starts_with("The depth");
        let trace = exact
            && (l.starts_with("State ") || l.starts_with("/\\ ") || l.starts_with("Back to state") || l.starts_with("<<\"expanded\""));
        if counts && !one {
            keep.push(l.split(", ").take(2).collect::<Vec<_>>().join(", "));
        } else if verdict || counts || trace {
            keep.push(l.to_string());
        }
    }
    keep.push(format!("{states} states in the trace"));
    keep
}

/// Run until the `abort`-th checkpoint (every `every` states), then
/// recover: the exit code and output of the recovered run, and the
/// output of the aborted one.
fn interrupted(
    dir: &Path,
    name: &str,
    kill: &[&str],
    recover: &[&str],
    env: &[(&str, &str)],
    every: &str,
    abort: &str,
) -> (i32, String, String) {
    let md = dir.join("md");
    assert!(!md.exists(), "tlx must create the metadir");
    let mut e = env.to_vec();
    e.extend([("TLX_CHECKPOINT_STATES", every), ("TLX_CHECKPOINT_ABORT", abort)]);
    let mut args = kill.to_vec();
    args.extend(["-metadir", md.to_str().unwrap()]);
    let (code, killed) = run(dir, name, &args, &e);
    assert_ne!(code, 0, "{killed}");
    assert_eq!(killed.matches("Checkpointing completed at").count(), abort.parse::<usize>().unwrap(), "{killed}");
    assert!(md.join("checkpoint/MANIFEST").is_file(), "{killed}");
    let mut args = recover.to_vec();
    args.extend(["-recover", md.to_str().unwrap()]);
    let (code, out) = run(dir, name, &args, env);
    assert!(out.contains("Starting recovery from checkpoint "), "{out}");
    // (The metadir goes when the recovered run ends.)
    assert!(!md.exists(), "{out}");
    (code, out, killed)
}

/// Killed after a checkpoint and recovered: the same results as the
/// uninterrupted run, for the interpreter and `-compile`, with one worker
/// (the same trace) and others (any number when recovering).
#[test]
fn recovered_runs_match_uninterrupted_ones() {
    for (name, src, cfg, every) in [
        ("CkLive", LIVE, LIVE_CFG, "300"),
        ("CkView", VIEW, VIEW_CFG, "300"),
        ("CkReg", REG, REG_CFG, "300"),
        ("CkRec", REC, REC_CFG, "300"),
    ] {
        let dir = tlx_testkit::TempDir::with_spec(&format!("match-{name}"), src, cfg);
        for tier in [&[][..], &["-compile"]] {
            let one = [tier, &["-workers", "1"]].concat();
            let eight = [tier, &["-workers", "8"]].concat();
            let (code1, want1) = run(&dir, name, &one, &[]);
            let (code8, want8) = run(&dir, name, &eight, &[]);
            assert_eq!(code1, code8, "{want1}\n{want8}");
            let cases: [(&[&str], &[&str], &str, bool); 4] =
                [(&one, &one, &want1, true), (&eight, &eight, &want8, false), (&one, &eight, &want8, false), (&eight, &one, &want1, false)];
            for (kill, recover, want, one) in cases {
                let (code, out, _) = interrupted(&dir, name, kill, recover, &[], every, "2");
                assert_eq!(code, code1, "{name} {kill:?} -> {recover:?}:\n{out}");
                // (VIEW: the same trace also with several workers.)
                let exact = one || name == "CkView";
                assert_eq!(results(&out, exact, one), results(want, exact, one), "{name} {kill:?} -> {recover:?}:\n{out}");
            }
        }
    }
}

/// The behavior graph of a recovered run includes the edges recorded
/// before the checkpoint (liveness does not explore the state space again).
#[test]
fn recovered_liveness_uses_the_recorded_edges() {
    let dir = tlx_testkit::TempDir::with_spec("edges", LIVE, LIVE_CFG);
    for tier in [&[][..], &["-compile"]] {
        let args = [tier, &["-stats"]].concat();
        let (code, out, _) = interrupted(&dir, "CkLive", &args, &args, &[], "300", "3");
        assert_eq!(code, 13, "{out}");
        assert!(out.contains("liveness: edge graph (CSR)"), "{out}");
        assert!(!out.contains("liveness: behavior graph (search again)"), "{out}");
    }
}

/// The disk tier (everything spilled: fingerprint runs, queue segments,
/// trace logs, edges) before and after the checkpoint.
#[test]
fn recovered_runs_with_the_disk_tier() {
    let env = [("TLX_SPILL", "always"), ("TLX_FP_SPILL_SLOTS", "1024"), ("TLX_SEG_BYTES", "4096")];
    for (name, src, cfg) in [("CkLive", LIVE, LIVE_CFG), ("CkView", VIEW, VIEW_CFG)] {
        let dir = tlx_testkit::TempDir::with_spec(&format!("disk-{name}"), src, cfg);
        for tier in [&[][..], &["-compile"]] {
            for workers in ["1", "8"] {
                let args = [tier, &["-workers", workers]].concat();
                let (code, want) = run(&dir, name, &args, &env);
                let (got_code, out, _) = interrupted(&dir, name, &args, &args, &env, "300", "1");
                assert_eq!(got_code, code, "{name} {args:?}:\n{out}");
                let exact = workers == "1" || name == "CkView";
                assert_eq!(results(&out, exact, workers == "1"), results(&want, exact, workers == "1"), "{name} {args:?}:\n{out}");
            }
        }
    }
}

/// `-compile` recovers with the checkpoint's layouts (no pre-run); a
/// layout miss after the recovery resumes from the archive the checkpoint
/// held (or starts over without one).
#[test]
fn layout_miss_after_the_recovery() {
    let dir = tlx_testkit::TempDir::with_spec("miss", REG, REG_CFG);
    for (workers, retain) in [("1", "1024"), ("4", "1024"), ("1", "0")] {
        let env = [("TLX_PRERUN", "1"), ("TLX_RETAIN_MB", retain)];
        let args = ["-compile", "-workers", workers];
        let (code, want) = run(&dir, "CkReg", &args, &env);
        assert_eq!(code, 0, "{want}");
        let (code, out, killed) = interrupted(&dir, "CkReg", &args, &args, &env, "300", "2");
        assert_eq!(code, 0, "{out}");
        assert!(out.contains("compile: recovering with the shapes of attempt"), "{out}");
        assert!(!out.contains("pre-run:"), "{out}");
        assert!(out.contains("layout miss on y"), "the miss happens after the recovery:\n{killed}\n{out}");
        assert_eq!(out.contains("compile: resuming the search at depth"), retain != "0", "{out}");
        assert_eq!(
            results(&out, workers == "1", workers == "1"),
            results(&want, workers == "1", workers == "1"),
            "{workers} {retain}:\n{out}"
        );
        assert!(out.contains("<<\"expanded\", 1891>>") == (workers == "1"), "{out}");
    }
}

/// A checkpoint taken by a recovered run links the archive it recovered
/// (the segments of every worker, as worker 0's) and writes only the rest:
/// recovered from it, a layout miss resumes from the whole archive.
#[test]
fn layout_miss_resumes_from_the_linked_archive() {
    let dir = tlx_testkit::TempDir::with_spec("miss-linked", REG, REG_CFG);
    let env = [("TLX_PRERUN", "1"), ("TLX_RETAIN_MB", "1024")];
    let args = ["-compile", "-workers", "4"];
    let (code, want) = run(&dir, "CkReg", &args, &env);
    assert_eq!(code, 0, "{want}");
    let md = dir.child_path("md");
    let checkpoint = [("TLX_CHECKPOINT_STATES", "300"), ("TLX_CHECKPOINT_ABORT", "1")];
    let e = [&env[..], &checkpoint].concat();
    let (code, out) = run(&dir, "CkReg", &[&args[..], &["-metadir", md.to_str().unwrap()]].concat(), &e);
    assert_ne!(code, 0, "{out}");
    let first: Vec<String> = archive_files(&md);
    assert!(first.iter().any(|f| f.starts_with("archive-3.")), "{first:?}");
    let recover = [&args[..], &["-recover", md.to_str().unwrap()]].concat();
    let (code, out) = run(&dir, "CkReg", &recover, &e);
    assert_ne!(code, 0, "{out}");
    let second = archive_files(&md);
    for f in &first {
        assert!(second.contains(f), "{f} not linked: {second:?}");
    }
    // (Numbered on from the recovered checkpoint: 2.)
    assert!(second.iter().any(|f| f.ends_with(".2")), "{second:?}");
    let (code, out) = run(&dir, "CkReg", &recover, &env);
    assert_eq!(code, 0, "{out}");
    assert!(out.contains("layout miss on y") && out.contains("compile: resuming the search at depth"), "{out}");
    assert_eq!(results(&out, false, false), results(&want, false, false), "{out}");
}

/// The archive's segments in the checkpoint of metadir `md`.
fn archive_files(md: &Path) -> Vec<String> {
    let mut names: Vec<String> = std::fs::read_dir(md.join("checkpoint"))
        .unwrap()
        .map(|e| e.unwrap().file_name().into_string().unwrap())
        .filter(|f| f.starts_with("archive-"))
        .collect();
    names.sort();
    names
}

/// Wait (up to two minutes) for `path` to exist.
fn wait_for(path: &Path, child: &mut std::process::Child) {
    let deadline = Instant::now() + Duration::from_secs(120);
    while !path.exists() {
        if let Some(s) = child.try_wait().unwrap() {
            panic!("tlx ended ({s}) before {} appeared", path.display());
        }
        assert!(Instant::now() < deadline, "{} did not appear", path.display());
        std::thread::sleep(Duration::from_millis(5));
    }
}

/// SIGKILL right after a checkpoint (the process cannot clean anything
/// up), then recover: the same counts and depth.
#[test]
fn sigkill_then_recover() {
    let dir = tlx_testkit::TempDir::with_spec("sigkill", BIG, BIG_CFG);
    let want = |args: &[&str]| results(&run(&dir, "CkBig", args, &[]).1, false, true);
    for args in [&["-workers", "1"][..], &["-workers", "8"], &["-compile", "-workers", "1"], &["-compile", "-workers", "4"]] {
        let md = dir.child_path("md");
        let mut a = args.to_vec();
        a.extend(["-metadir", md.to_str().unwrap()]);
        let mut child = command(&dir, "CkBig", &a, &[("TLX_CHECKPOINT_STATES", "50000")])
            .command()
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .spawn()
            .expect("spawn tlx");
        wait_for(&md.join("checkpoint/MANIFEST"), &mut child);
        child.kill().unwrap();
        child.wait().unwrap();
        let mut a = args.to_vec();
        a.extend(["-recover", md.to_str().unwrap()]);
        let (code, out) = run(&dir, "CkBig", &a, &[]);
        assert_eq!(code, 0, "{args:?}:\n{out}");
        assert_eq!(results(&out, false, true), want(args), "{args:?}:\n{out}");
        assert!(!md.exists());
    }
}

/// SIGINT (Ctrl-C) keeps a committed checkpoint (only the spill files and
/// the lock go) and says how to continue; the run continues from it.
#[test]
fn sigint_keeps_the_checkpoint() {
    let dir = tlx_testkit::TempDir::with_spec("sigint", BIG, BIG_CFG);
    let md = dir.child_path("md");
    let mut cmd = command(
        &dir,
        "CkBig",
        &["-metadir", md.to_str().unwrap()],
        &[("TLX_CHECKPOINT_STATES", "50000"), ("TLX_SPILL", "always"), ("TLX_SEG_BYTES", "4096")],
    );
    cmd.command().stdout(Stdio::null()).stderr(Stdio::piped());
    // A test process started in the background (`cmd &`) has SIGINT
    // ignored, and so would tlx: restore the default dispositions in the
    // child (as tests/signals.rs).
    // SAFETY: `signal` is async-signal-safe (allowed between fork and exec).
    unsafe {
        cmd.command().pre_exec(|| {
            libc::signal(libc::SIGINT, libc::SIG_DFL);
            libc::signal(libc::SIGTERM, libc::SIG_DFL);
            Ok(())
        });
    }
    let mut child = cmd.command().spawn().expect("spawn tlx");
    wait_for(&md.join("checkpoint/MANIFEST"), &mut child);
    // SAFETY: sending a signal to the child.
    unsafe { libc::kill(child.id() as libc::pid_t, libc::SIGINT) };
    let out = child.wait_with_output().unwrap();
    let err = String::from_utf8_lossy(&out.stderr);
    assert_eq!(out.status.code(), Some(130), "{err}");
    assert!(
        err.contains(&format!("tlx: the checkpoint in {} is kept; continue the run with -recover {}", md.display(), md.display())),
        "{err}"
    );
    assert!(md.join("checkpoint/MANIFEST").is_file());
    let left: Vec<_> = std::fs::read_dir(&md).unwrap().flatten().map(|e| e.file_name().into_string().unwrap()).collect();
    assert!(left.iter().all(|n| n.starts_with("checkpoint")), "{left:?}");
    let (code, out) = run(&dir, "CkBig", &["-recover", md.to_str().unwrap()], &[]);
    assert_eq!(code, 0, "{out}");
    assert!(out.contains("600000 states generated") || out.contains("states generated, 600000 distinct"), "{out}");
    assert!(!md.exists());
}

/// A checkpoint is only used by the run it was taken of: another tier,
/// another spec or cfg are refused, as are a damaged checkpoint and a
/// directory without one (exit 255, the checkpoint kept). Other numbers of
/// workers are fine.
#[test]
fn checkpoints_of_other_runs_are_refused() {
    let dir = tlx_testkit::TempDir::with_spec("refuse", VIEW, VIEW_CFG);
    let md = dir.child_path("md");
    let mdp = md.to_str().unwrap();
    let take = || {
        // Refused recoveries deliberately keep the checkpoint; reset it for the next refusal case.
        let _ = std::fs::remove_dir_all(&md);
        let (code, out) = run(&dir, "CkView", &["-metadir", mdp], &[("TLX_CHECKPOINT_STATES", "300"), ("TLX_CHECKPOINT_ABORT", "1")]);
        assert_ne!(code, 0, "{out}");
        assert!(md.join("checkpoint/MANIFEST").is_file());
    };
    take();
    let refused = |args: &[&str], why: &str| {
        let mut a = args.to_vec();
        a.extend(["-recover", mdp]);
        let (code, out) = run(&dir, "CkView", &a, &[]);
        assert_eq!(code, 255, "{args:?}:\n{out}");
        assert!(out.contains(&format!("cannot recover from {mdp}")) && out.contains(why), "{args:?}: {why}:\n{out}");
        assert!(md.join("checkpoint/MANIFEST").is_file(), "{args:?}: the checkpoint is kept");
    };
    refused(&["-compile"], "the checkpoint was taken with the interpreter, this run uses -compile");
    std::fs::write(dir.join("CkView.cfg"), VIEW_CFG.replace("INVARIANT Inv\n", "")).unwrap();
    refused(&[], "the configuration changed since the checkpoint");
    std::fs::write(dir.join("CkView.cfg"), VIEW_CFG).unwrap();
    std::fs::write(dir.join("CkView.tla"), VIEW.replace("% 13", "% 11")).unwrap();
    refused(&[], "the specification (one of its modules) changed since the checkpoint");
    std::fs::write(dir.join("CkView.tla"), VIEW).unwrap();
    // A damaged file: refused when opened (a size that does not match),
    // or when read (a checksum).
    let fpset = md.join("checkpoint/fpset-0");
    let mut b = std::fs::read(&fpset).unwrap();
    b.push(0);
    std::fs::write(&fpset, &b).unwrap();
    refused(&[], "(corrupt checkpoint)");
    b.pop();
    let i = b.len() / 2;
    b[i] ^= 1;
    std::fs::write(&fpset, &b).unwrap();
    refused(&[], "checksum mismatch");
    b[i] ^= 1;
    std::fs::write(&fpset, &b).unwrap();
    // A directory without a checkpoint.
    let (code, out) = run(&dir, "CkView", &["-recover", dir.to_str().unwrap()], &[]);
    assert_eq!(code, 255, "{out}");
    assert!(out.contains("no checkpoint in"), "{out}");
    // Not with simulation or -dump.
    let (code, out) = run(&dir, "CkView", &["-recover", mdp, "-simulate"], &[]);
    assert_eq!(code, 2, "{out}");
    // The checkpoint itself, restored: recovered (with another number of
    // workers).
    let (code, out) = run(&dir, "CkView", &["-recover", mdp, "-workers", "3"], &[]);
    assert_eq!(code, 12, "{out}");
    assert!(!md.exists(), "{out}");
}

/// TLC's messages; a run that ends normally leaves nothing behind (the
/// default metadir, `states/<time>` next to the spec, included).
#[test]
fn checkpoints_leave_nothing_behind() {
    let dir = tlx_testkit::TempDir::with_spec("clean", LIVE, LIVE_CFG);
    let (code, out) = run(&dir, "CkLive", &["-workers", "2"], &[("TLX_CHECKPOINT_STATES", "300")]);
    assert_eq!(code, 13, "{out}");
    assert!(out.matches("Checkpointing of run ").count() >= 3, "{out}");
    assert_eq!(out.matches("Checkpointing of run ").count(), out.matches("Checkpointing completed at (").count(), "{out}");
    assert!(!dir.join("states").exists(), "{out}");
    // `-checkpoint 0`: none.
    let (code, out) = run(&dir, "CkLive", &["-checkpoint", "0"], &[("TLX_CHECKPOINT_STATES", "300")]);
    assert_eq!(code, 13, "{out}");
    assert!(!out.contains("Checkpointing"), "{out}");
}
