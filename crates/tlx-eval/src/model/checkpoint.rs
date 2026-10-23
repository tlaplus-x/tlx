//! Checkpoint persistence of the interpreted model (CODE-03).
//!
//! The string intern table and the `tlx_value::ser` state encoding, plus
//! the `tlx_runtime` `Persist`/`Checkpointed` capabilities of
//! `InterpModel` (`ARCH-10`: every model capability moves with its owner).
//! Extracted from `mod.rs`; the public paths are re-exported there.

use super::*;

/// The checkpoint file of the string intern table (`strings_snapshot`):
/// restored first when recovering (`restore_strings`), since the intern
/// order decides the order of values.
pub const STRINGS_FILE: &str = "strings";

/// The string intern table, for a checkpoint.
pub fn strings_snapshot() -> Vec<u8> {
    let mut w = tlx_value::ser::Writer::new();
    tlx_value::ser::write_intern_table(&mut w);
    w.into_bytes()
}

/// Restore the string intern table of a checkpoint (`strings_snapshot`),
/// before anything else is interned (before the spec is parsed).
pub fn restore_strings(b: &[u8]) -> Result<(), String> {
    let mut r = tlx_value::ser::Reader::new(b);
    let texts = tlx_value::ser::read_intern_table(&mut r).map_err(|e| format!("corrupt string table: {e}"))?;
    r.finish().map_err(|e| format!("corrupt string table: {e}"))?;
    tlx_value::intern::restore(&texts)
}

/// States in checkpoints: the values of the variables (`tlx_value::ser`).
impl tlx_runtime::Persist<State> for InterpModel {
    fn write_state(&self, s: &State, out: &mut Vec<u8>) -> Result<(), String> {
        let mut w = tlx_value::ser::Writer::new();
        for v in s.vals.iter() {
            w.value(v).map_err(|e| format!("cannot write a state to a checkpoint: {e}"))?;
        }
        out.extend_from_slice(w.as_bytes());
        Ok(())
    }

    fn read_state(&self, b: &[u8], depth: u32, fp: u64) -> Result<State, String> {
        let mut r = tlx_value::ser::Reader::new(b);
        let e = |e: tlx_value::ser::DecodeError| format!("corrupt state in the checkpoint: {e}");
        let vals = (0..self.ip.prog.vars.len()).map(|_| r.value()).collect::<Result<Vec<_>, _>>().map_err(e)?;
        r.finish().map_err(e)?;
        Ok(State::new(vals.into(), depth, fp))
    }
}

/// Checkpoints: the string table, and the TLCSet registers (with the
/// counts of the `_POSSIBLE` predicates, which recovery restores).
impl tlx_runtime::Checkpointed for InterpModel {
    fn files(&self) -> Result<Vec<(String, Vec<u8>)>, String> {
        Ok(vec![(STRINGS_FILE.to_string(), strings_snapshot())])
    }

    fn worker_snapshot(&self) -> Result<Vec<u8>, String> {
        self.ip.registers_snapshot()
    }

    fn main_snapshot(&self) -> Result<Vec<u8>, String> {
        self.ip.main_registers_snapshot()
    }

    fn restore_workers(&self, main: &[u8], snaps: &[Vec<u8>]) -> Result<(), String> {
        self.ip.resume_registers(main, snaps)?;
        self.restore_witnessed(main, snaps)
    }
}
