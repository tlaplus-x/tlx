//! Instantiate `ChooseSymCertificate.lean` with this model's exact operations and invariants.

use super::{Emitter, InitCase, InvPlan, StepCase};
use crate::{hir::Expr, optimize::lean::literal};
use std::fmt::Write;

impl Emitter<'_> {
    pub(super) fn output(
        &self,
        initial: &Expr,
        init_cases: &[InitCase],
        step_cases: &[StepCase],
        observation: &str,
        inv: &InvPlan,
    ) -> String {
        let mut out = String::from(include_str!("../../ChooseSymCertificate.lean"));
        self.write_header_and_metadata(&mut out, initial, init_cases.len(), step_cases, inv);
        self.write_branches_and_model(&mut out, init_cases, step_cases, observation);
        out.push_str(include_str!("certificate.lean"));
        out
    }

    fn write_header_and_metadata(&self, out: &mut String, initial: &Expr, init_len: usize, step_cases: &[StepCase], inv: &InvPlan) {
        out.push_str("\nnamespace TlxOptimization.GeneratedChooseSymmetry\n");
        out.push_str(
            "open TlxOptimization ChooseSymRule\n\
             noncomputable section\n\
             set_option linter.unusedVariables false\n\
             set_option maxRecDepth 10000\n",
        );
        writeln!(out, "abbrev GroupCount : Nat := {}", self.groups.len()).unwrap();
        out.push_str("def groupSizes (g : Fin GroupCount) : Nat :=\n  match g.val with\n");
        for (i, g) in self.groups.iter().enumerate() {
            writeln!(out, "  | {i} => {}", g.size).unwrap();
        }
        out.push_str("  | _ => 0\n");
        writeln!(
            out,
            "abbrev MapId := Fin {}\n\
             abbrev SlotId := Fin {}\n\
             abbrev FlagId := Fin {}\n\
             abbrev MsgSetId := Fin {}\n\
             abbrev InitBranchId := Fin {}\n\
             abbrev BranchId := Fin {}",
            self.num_maps,
            self.num_slots,
            self.num_flags,
            self.num_msgs,
            init_len,
            step_cases.len()
        )
        .unwrap();
        writeln!(
            out,
            "def layout : String := {}",
            literal(&format!(
                "Disjoint product of {} full permutation group(s) {:?}; shapes {:?}; maps {}; slots {}; flags {}; msgSets {}; payloads and core contain no moved keys",
                self.groups.len(),
                self.groups.iter().map(|g| &g.keys).collect::<Vec<_>>(),
                self.shapes,
                self.num_maps,
                self.num_slots,
                self.num_flags,
                self.num_msgs
            ))
        )
        .unwrap();
        writeln!(out, "def initialHIR : String := {}", literal(&format!("{initial:#?}"))).unwrap();
        for (i, atom) in self.atoms.iter().enumerate() {
            writeln!(out, "def atom{i}HIR : String := {}", literal(atom)).unwrap();
        }
        for (i, fa) in self.fixed_atoms.iter().enumerate() {
            writeln!(out, "def fixedAtom{i} : String := {}", literal(fa)).unwrap();
        }
        for (i, (_, cv)) in self.const_vals.iter().enumerate() {
            writeln!(out, "def constVal{i} : String := {}", literal(cv)).unwrap();
        }
        for (i, c) in step_cases.iter().enumerate() {
            writeln!(
                out,
                "def branch{i}Keys : String := {}",
                literal(&format!("environment slots: {:?}; other locals belong to W", c.keys))
            )
            .unwrap();
        }

        let amo_str = inv
            .at_most_one_flags
            .iter()
            .map(|&(fid, mask)| format!("(⟨{fid}, by decide⟩, {})", self.mask_lean(mask)))
            .collect::<Vec<_>>()
            .join(", ");
        let const_str = inv.const_val_msgs.iter().map(|&(mid, cid)| format!("(⟨{mid}, by decide⟩, {cid})")).collect::<Vec<_>>().join(", ");
        let unif_str = inv.uniform_val_msgs.iter().map(|&mid| format!("⟨{mid}, by decide⟩")).collect::<Vec<_>>().join(", ");
        writeln!(
            out,
            "def invSpec : InvSpec GroupCount FlagId MsgSetId :=\n\
             \x20 {{ atMostOneFlags := [{amo_str}],\n\
             \x20   constValMsgs := [{const_str}],\n\
             \x20   uniformValMsgs := [{unif_str}] }}"
        )
        .unwrap();
    }

    fn write_branches_and_model(&self, out: &mut String, init_cases: &[InitCase], step_cases: &[StepCase], observation: &str) {
        out.push_str("def initBranch (ib : InitBranchId) : InitBranch GroupCount FlagId MsgSetId :=\n  match ib.val with\n");
        for (i, ic) in init_cases.iter().enumerate() {
            let mut fl_arms = String::new();
            for (fid, fk) in ic.flag_inits.iter().enumerate() {
                let _ = write!(fl_arms, " | {fid} => {}", fk.lean(self));
            }
            let mut ms_arms = String::new();
            for (mid, mk) in ic.msg_inits.iter().enumerate() {
                let _ = write!(ms_arms, " | {mid} => {}", mk.lean(self));
            }
            writeln!(
                out,
                "  | {i} => {{ flagInit := fun f => match f.val with{fl_arms} | _ => FlagInit.empty,\n\
                 \x20          msgInit := fun ms => match ms.val with{ms_arms} | _ => MsgInit.empty }}"
            )
            .unwrap();
        }
        out.push_str("  | _ => { flagInit := fun _ => FlagInit.empty, msgInit := fun _ => MsgInit.empty }\n");

        out.push_str("def stepBranch (b : BranchId) : StepBranch GroupCount MapId SlotId FlagId MsgSetId :=\n  match b.val with\n");
        for (i, sc) in step_cases.iter().enumerate() {
            let ugs = sc.uniform_guards.iter().map(|(mid, expr)| format!("(⟨{mid}, by decide⟩, {expr})")).collect::<Vec<_>>().join(", ");
            let mut fl_arms = String::new();
            for (fid, fk) in sc.flag_steps.iter().enumerate() {
                let _ = write!(fl_arms, " | {fid} => {}", fk.lean(self));
            }
            let mut ms_arms = String::new();
            for (mid, mk) in sc.msg_steps.iter().enumerate() {
                let _ = write!(ms_arms, " | {mid} => {}", mk.lean(self));
            }
            writeln!(
                out,
                "  | {i} => {{ preGuard := {},\n\
                 \x20          uniformGuards := [{ugs}],\n\
                 \x20          choices := [{}],\n\
                 \x20          postGuard := {},\n\
                 \x20          writes := [{}],\n\
                 \x20          slotWrites := [{}],\n\
                 \x20          flagSteps := fun f => match f.val with{fl_arms} | _ => FlagStep.keep,\n\
                 \x20          msgSteps := fun ms => match ms.val with{ms_arms} | _ => MsgStep.keep }}",
                sc.pre_guard,
                sc.choices.join(", "),
                sc.post_guard,
                sc.writes.join(", "),
                sc.slot_writes.join(", ")
            )
            .unwrap();
        }
        out.push_str(
            "  | _ => { preGuard := PureTest.truth false, uniformGuards := [], choices := [],\n\
             \x20          postGuard := ChoiceTest.pure (PureTest.truth false), writes := [], slotWrites := [],\n\
             \x20          flagSteps := fun _ => FlagStep.keep, msgSteps := fun _ => MsgStep.keep }\n",
        );

        writeln!(out, "def observation : ChoiceTest GroupCount MapId SlotId FlagId MsgSetId :=\n  {observation}").unwrap();
        out.push_str(
            "-- C, Meta, V, A and W contain no renamed keys; keyRank and recRank are arbitrary\n\
             -- un-permuted total-order rankings with zero symmetry premises.\n\
             -- Lowering, inferred domains, leaf totality, group closure and runtime canonicalization remain trusted.\n\
             def ops : Operations GroupCount MapId SlotId FlagId MsgSetId InitBranchId BranchId where\n\
             \x20 inv := invSpec\n\
             \x20 initBranch := initBranch\n\
             \x20 stepBranch := stepBranch\n\
             \x20 observation := observation\n\
             variable {C Meta V A W : Type} (sem : Semantics GroupCount groupSizes C MapId SlotId Meta V A InitBranchId BranchId W)\n",
        );
        writeln!(
            out,
            "def model : ChooseSymRule.Model GroupCount groupSizes C MapId SlotId FlagId MsgSetId Meta V A InitBranchId BranchId W where\n\
             \x20 ops := ops\n\
             \x20 sem := sem\n\
             \x20 allIB := List.finRange {}\n\
             \x20 completeIB := fun ib => List.mem_finRange ib\n\
             \x20 allB := List.finRange {}\n\
             \x20 completeB := fun b => List.mem_finRange b\n\
             \x20 opsValid := by decide",
            init_cases.len(),
            step_cases.len()
        )
        .unwrap();
    }
}
