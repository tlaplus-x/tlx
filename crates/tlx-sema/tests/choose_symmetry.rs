use tlx_front::cfg::parse_cfg;
use tlx_sema::{
    hir::{Expr, ExprKind, OpRef, RootSymbol},
    optimize::{choose_symmetry_certificate, symmetry_certificate},
    Program,
};

fn choose_cert_with_invs(name: &str, spec: &str, cfg: &str, inv_names: &[&str], groups: &[Vec<String>]) -> Option<String> {
    let dir = tlx_testkit::TempDir::new("choose-sym-sema-direct");
    let path = dir.write(&format!("{name}.tla"), spec);
    let mut p = Program::load(&path, &[]).unwrap();
    p.resolve_all_root();
    let mut root_expr = |root: &str| {
        let Some(RootSymbol::Def(id)) = p.lookup_root(root) else { panic!("missing {root}") };
        Expr::new(ExprKind::Apply { op: OpRef::Def(id), args: vec![] }, p.defs[id.idx()].span)
    };
    let init = root_expr("Init");
    let next = root_expr("Next");
    let obs: Vec<Expr> = inv_names.iter().map(|n| root_expr(n)).collect();
    choose_symmetry_certificate(&p, &parse_cfg(cfg).unwrap(), &init, &next, &obs, groups)
}

fn cert_with_invs(name: &str, spec: &str, cfg: &str, inv_names: &[&str], groups: &[Vec<String>]) -> Option<String> {
    let dir = tlx_testkit::TempDir::new("choose-sym-sema");
    let path = dir.write(&format!("{name}.tla"), spec);
    let mut p = Program::load(&path, &[]).unwrap();
    p.resolve_all_root();
    let mut root_expr = |root: &str| {
        let Some(RootSymbol::Def(id)) = p.lookup_root(root) else { panic!("missing {root}") };
        Expr::new(ExprKind::Apply { op: OpRef::Def(id), args: vec![] }, p.defs[id.idx()].span)
    };
    let init = root_expr("Init");
    let next = root_expr("Next");
    let obs: Vec<Expr> = inv_names.iter().map(|n| root_expr(n)).collect();
    symmetry_certificate(&p, &parse_cfg(cfg).unwrap(), &init, &next, &obs, groups)
}

fn cert(spec: &str) -> Option<String> {
    cert_with_invs(
        "ChooseSym",
        spec,
        include_str!("../../../proofs/symmetry/ChooseSym.cfg"),
        &["Inv"],
        &[vec!["p1".into(), "p2".into(), "p3".into()]],
    )
}

#[test]
fn choose_sym_showcase_emits_inductive_leader_uniform_msg_and_fold_proof() {
    let proof = cert(include_str!("../../../proofs/symmetry/ChooseSym.tla")).unwrap();
    for needle in [
        "namespace TlxOptimization.GeneratedChooseSymmetry",
        "UniqueKind.atMostOneFlag",
        "ProjKind.msgUniform",
        "ChoiceTest.bindFold",
        "atMostOneFlags := [(⟨0, by decide⟩",
        "constValMsgs := [(⟨0, by decide⟩",
        "opsValid := by decide",
        "theorem inductive_invariant",
        "theorem orbit_key_equivalent",
        "theorem counterexample_lifts",
        "theorem deadlock_preserved",
    ] {
        assert!(proof.contains(needle), "missing {needle}");
    }
}

#[test]
fn cigarette_smokers_pattern_emits_choose_one_and_cardinal_proof() {
    let spec = r#"---- MODULE Smokers ----
EXTENDS Integers, FiniteSets
CONSTANT Ingredients, Offers
VARIABLES smokers, dealer
TypeOK == /\ smokers \in [Ingredients -> [smoking: BOOLEAN]]
          /\ dealer \in Offers \/ dealer = {}
ChooseOne(S, P(_)) == CHOOSE x \in S : P(x) /\ \A y \in S : P(y) => y = x
Init == /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
        /\ dealer \in Offers
startSmoking == /\ dealer /= {}
                /\ smokers' = [r \in Ingredients |-> [smoking |-> {r} \cup dealer = Ingredients]]
                /\ dealer' = {}
stopSmoking == /\ dealer = {}
               /\ LET r == ChooseOne(Ingredients, LAMBDA x : smokers[x].smoking)
                  IN smokers' = [smokers EXCEPT ![r].smoking = FALSE]
               /\ dealer' \in Offers
Next == startSmoking \/ stopSmoking
AtMostOne == Cardinality({r \in Ingredients : smokers[r].smoking}) <= 1
====
"#;
    let cfg = "CONSTANTS\n  Ingredients = {matches, paper, tobacco}\n  Offers = {{matches, paper}, {matches, tobacco}, {paper, tobacco}}\nINIT Init\nNEXT Next\nINVARIANTS TypeOK AtMostOne\n";
    let proof = cert_with_invs("Smokers", spec, cfg, &["TypeOK", "AtMostOne"], &[vec!["matches".into(), "paper".into(), "tobacco".into()]])
        .unwrap();
    for needle in [
        "namespace TlxOptimization.GeneratedChooseSymmetry",
        "UniqueKind.only",
        "FlagInit.cardinal",
        "FlagStep.cardinal",
        "PureExpr.branch",
        "opsValid := by decide",
    ] {
        assert!(proof.contains(needle), "missing {needle}");
    }
}

#[test]
fn projected_comprehension_pinned_msg_and_recursive_op_fold_certify() {
    let spec = r#"---- MODULE ExtraChoices ----
EXTENDS Naturals, FiniteSets
CONSTANT Proc
VARIABLES pc, owner, msgs, round

RECURSIVE Sum(_)
Sum(S) == IF S = {} THEN 0 ELSE LET p == CHOOSE x \in S : TRUE IN pc[p] + Sum(S \ {p})

Init ==
    /\ round = 0
    /\ pc = [p \in Proc |-> 0]
    /\ owner = "none"
    /\ msgs = {[from |-> p, val |-> round] : p \in Proc}

Claim(p) ==
    /\ owner = "none"
    /\ pc[p] < 3
    /\ owner' = p
    /\ pc' = [pc EXCEPT ![p] = @ + 1]
    /\ UNCHANGED <<msgs, round>>

Advance ==
    /\ owner # "none"
    /\ round < 5
    /\ LET who == CHOOSE q \in Proc : q = owner /\ pc[q] >= 0
       IN /\ pc' = [pc EXCEPT ![who] = @]
          /\ owner' = "none"
          /\ round' = round + 1
          /\ msgs' = {[from |-> p, val |-> round + 1] : p \in Proc}

Inv ==
    /\ (CHOOSE r \in {[from |-> p, val |-> round + 5] : p \in Proc} : TRUE).val = round + 5
    /\ (CHOOSE m \in msgs : TRUE).val = round
    /\ (msgs # {} => (CHOOSE m \in msgs : m.val = round).val = round)
    /\ Sum(Proc) >= 0

Next == (\E p \in Proc : Claim(p)) \/ Advance
====
"#;
    let cfg = "CONSTANT Proc = {p1, p2, p3}\nINIT Init\nNEXT Next\nINVARIANT Inv\n";
    let proof = cert_with_invs("ExtraChoices", spec, cfg, &["Inv"], &[vec!["p1".into(), "p2".into(), "p3".into()]]).unwrap();
    for needle in [
        "UniqueKind.eq",
        "ProjKind.keyConst",
        "ProjKind.msgPinned",
        "ProjKind.msgUniform",
        "MsgInit.comprehensionCore",
        "MsgStep.comprehensionAll",
        "uniformValMsgs := [⟨0, by decide⟩]",
        "ChoiceTest.bindFold",
    ] {
        assert!(proof.contains(needle), "missing {needle}");
    }
}

#[test]
fn unsound_and_partial_choices_are_refused() {
    let base = include_str!("../../../proofs/symmetry/ChooseSym.tla");
    for broken in [
        // 1. Breaking inductive atMostOneFlag: allow electing a second leader when one already exists.
        base.replace("/\\ \\A q \\in Proc : q \\notin leaders\n", ""),
        // 2. Breaking inductive atMostOneFlag at Init: start with all processes in `leaders`.
        base.replace("leaders = {}", "leaders = Proc"),
        // 3. Conflicting message values across Init and StepLeader (`7` vs `8`).
        base.replace("val |-> 7]}", "val |-> 8]}"),
        // 4. Unprojected record CHOOSE escaping into equality.
        base.replace(
            "(CHOOSE m \\in msgs : TRUE).val = 7",
            "\\E p \\in Proc : (CHOOSE m \\in msgs : TRUE) = [from |-> p, tag |-> 0, val |-> 7]",
        ),
        // 5. Raw unprojected arbitrary key CHOOSE.
        base.replace("TotalVotes <= 6", "votes[CHOOSE p \\in Proc : TRUE] <= 2"),
        // 6. Key-dependent projected comprehension (`votes[p]` varies by key `p`).
        base.replace("TotalVotes <= 6", "(CHOOSE m \\in {[from |-> p, val |-> votes[p]] : p \\in Proc} : TRUE).val <= 2"),
        // 7. Partial division-by-zero inside CHOOSE predicate (`is_total_in_choose` must reject).
        base.replace("m.tag >= 0", "m.tag >= 0 \\/ 1 \\div 0 = 0"),
        // 8. Projecting a non-uniform metadata field `.tag` (`tag` varies across messages).
        base.replace("(LET m == CHOOSE m \\in msgs : m.tag >= 0 IN m.val) = 7", "(CHOOSE m \\in msgs : TRUE).tag >= 0"),
    ] {
        assert!(cert(&broken).is_none(), "unsound choice spec was wrongly certified:\n{broken}");
    }

    // Asymmetric subset family (`Offers` missing `{paper, tobacco}`) must be refused.
    let asym_smokers = r#"---- MODULE AsymSmokers ----
EXTENDS Integers, FiniteSets
CONSTANT Ingredients, Offers
VARIABLES smokers, dealer
ChooseOne(S, P(_)) == CHOOSE x \in S : P(x) /\ \A y \in S : P(y) => y = x
Init == /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
        /\ dealer \in Offers
Next == /\ dealer = {}
        /\ LET r == ChooseOne(Ingredients, LAMBDA x : smokers[x].smoking)
           IN smokers' = [smokers EXCEPT ![r].smoking = FALSE]
        /\ dealer' \in Offers
Inv == TRUE
====
"#;
    let asym_cfg = "CONSTANTS\n  Ingredients = {matches, paper, tobacco}\n  Offers = {{matches, paper}, {matches, tobacco}}\nINIT Init\nNEXT Next\nINVARIANT Inv\n";
    assert!(cert_with_invs("AsymSmokers", asym_smokers, asym_cfg, &["Inv"], &[vec!["matches".into(), "paper".into(), "tobacco".into()]],)
        .is_none());
}

#[test]
fn choose_uniqueness_fold_and_hoisting_soundness_regressions() {
    let cfg = "CONSTANT Proc = {p1, p2, p3}\nINIT Init\nNEXT Next\nINVARIANT Inv\n";
    let g = &[vec!["p1".into(), "p2".into(), "p3".into()]];

    // 1. Capture-avoiding binder renaming in match_only_pattern:
    // `(y = x \/ pc < 0) => y = x` does NOT substitute `y` for both occurrences of `x` in `x = x`.
    let bad_only = r#"---- MODULE BadOnly ----
EXTENDS Integers
CONSTANT Proc
VARIABLES pc, votes
Init == pc = 0 /\ votes = [p \in Proc |-> 0]
Next ==
    /\ pc = 0
    /\ pc' = 1
    /\ LET picked == CHOOSE x \in Proc : (x = x \/ pc < 0) /\ \A y \in Proc : (y = x \/ pc < 0) => y = x
       IN votes' = [votes EXCEPT ![picked] = 1]
Inv == \A p \in Proc : votes[p] \in 0..1
====
"#;
    assert!(cert_with_invs("BadOnly", bad_only, cfg, &["Inv"], g).is_none());

    // 2. Scalar-slot membership fallback must not drop multiple primed equalities `x' = x /\ x' = Pick`.
    let bad_slot_multi = r#"---- MODULE BadSlotMulti ----
EXTENDS Integers
CONSTANT Proc
VARIABLES x
Pick == CHOOSE p \in Proc : TRUE
Init == x \in Proc
Next == x' \in Proc /\ x' = x /\ x' = Pick
Inv == x \in Proc
====
"#;
    assert!(choose_cert_with_invs("BadSlotMulti", bad_slot_multi, cfg, &["Inv"], g).is_none());

    // 2b. Multiple primed equalities on a scalar slot in a CHOOSE-bearing spec must also be refused.
    let bad_slot_multi_with_leaders = r#"---- MODULE BadSlotMultiLeaders ----
EXTENDS Integers
CONSTANT Proc
VARIABLES x, leaders
Pick == CHOOSE p \in Proc : TRUE
Init == x \in Proc /\ \E p \in Proc : leaders = {p}
Next ==
    /\ x' \in Proc /\ x' = x /\ x' = Pick
    /\ leaders' = {CHOOSE q \in Proc : q \in leaders}
Inv == x \in Proc
====
"#;
    assert!(cert_with_invs("BadSlotMultiLeaders", bad_slot_multi_with_leaders, cfg, &["Inv"], g).is_none());

    // 3. Checked 32-bit partial-sum overflow in CHOOSE sum fold over `{2147483647, 1, -1}`.
    let bad_fold_overflow = r#"---- MODULE BadFoldOverflow ----
EXTENDS Integers, FiniteSets
CONSTANT Proc
VARIABLES votes
RECURSIVE Sum(_)
Sum(S) == IF S = {} THEN 0 ELSE LET p == CHOOSE x \in S : TRUE IN votes[p] + Sum(S \ {p})
Init == votes \in [Proc -> {2147483647, 1, -1}]
Next == UNCHANGED votes
Inv == Sum(Proc) >= -3
====
"#;
    assert!(cert_with_invs("BadFoldOverflow", bad_fold_overflow, cfg, &["Inv"], g).is_none());

    // 3b. Unbounded counter in CHOOSE sum fold must also be refused.
    let bad_fold_unbounded = r#"---- MODULE BadFoldUnbounded ----
EXTENDS Integers, FiniteSets
CONSTANT Proc
VARIABLES votes
RECURSIVE Sum(_)
Sum(S) == IF S = {} THEN 0 ELSE LET p == CHOOSE x \in S : TRUE IN votes[p] + Sum(S \ {p})
Init == votes = [p \in Proc |-> 0]
Next == \E p \in Proc : votes' = [votes EXCEPT ![p] = @ + 1]
Inv == Sum(Proc) >= 0
====
"#;
    assert!(cert_with_invs("BadFoldUnbounded", bad_fold_unbounded, cfg, &["Inv"], g).is_none());

    // 4. Partial `^` (`0 ^ 0`) inside CHOOSE predicate over `tag \in {0, 1}` must be refused.
    let bad_pow = r#"---- MODULE BadPow ----
EXTENDS Integers
CONSTANT Proc
VARIABLES msgs
Init == msgs = {[from |-> p, tag |-> 0, val |-> 7] : p \in Proc}
Next == \E p \in Proc : \E t \in {0, 1} : msgs' = msgs \cup {[from |-> p, tag |-> t, val |-> 7]}
Inv == (CHOOSE m \in msgs : m.tag ^ m.tag = 1).val = 7
====
"#;
    assert!(cert_with_invs("BadPow", bad_pow, cfg, &["Inv"], g).is_none());

    // 4b. Unchecked `+` overflow inside CHOOSE predicate must be refused.
    let bad_plus_overflow = r#"---- MODULE BadPlusOverflow ----
EXTENDS Integers
CONSTANT Proc
VARIABLES msgs
Init == msgs = {[from |-> p, tag |-> 0, val |-> 7] : p \in Proc}
Next == \E p \in Proc : \E t \in {0, 2147483647} : msgs' = msgs \cup {[from |-> p, tag |-> t, val |-> 7]}
Inv == (CHOOSE m \in msgs : m.tag + 1 >= 0).val = 7
====
"#;
    assert!(cert_with_invs("BadPlusOverflow", bad_plus_overflow, cfg, &["Inv"], g).is_none());

    // 5. Earlier write bound to `\E p` must keep pointing at `p` (`KeyRef.bound 1`) after a
    // later variable hoists a `UniqueKind` choice to `KeyRef.bound 0`.
    let hoisted_shift = r#"---- MODULE HoistedShift ----
EXTENDS Integers
CONSTANT Proc
VARIABLES votes, owner, leaders
Init ==
    /\ votes = [p \in Proc |-> 0]
    /\ owner = "none"
    /\ \E p \in Proc : leaders = {p}
Next ==
    \E p \in Proc :
        /\ votes[p] < 1
        /\ votes' = [votes EXCEPT ![p] = @ + 1]
        /\ owner' = CHOOSE q \in Proc : q \in leaders
        /\ UNCHANGED leaders
Inv == \A p \in Proc : votes[p] \in 0..1
====
"#;
    let shift_proof = cert_with_invs("HoistedShift", hoisted_shift, cfg, &["Inv"], g).unwrap();
    assert!(
        shift_proof.contains("(Write.point ⟨0, by decide⟩ (KeyRef.bound 1)"),
        "earlier map write must shift to KeyRef.bound 1 after choice hoisting:\n{shift_proof}"
    );
    assert!(
        shift_proof.contains("⟨⟨0, by decide⟩, (ChoiceSlotExpr.ref (KeyRef.bound 0))⟩"),
        "hoisted slot write must reference KeyRef.bound 0:\n{shift_proof}"
    );

    // 6. Correlated Init (`\E p \in Proc : owner = p /\ leaders = {p}`) shares `keys` witness
    // between `initSetup` and `flagInit`, plus 7 (FinSet) & 8 (postGuard match in branchHasError).
    let correlated_init = r#"---- MODULE CorrelatedInit ----
EXTENDS Integers
CONSTANT Proc
VARIABLES owner, leaders
Init == \E p \in Proc : owner = p /\ leaders = {p}
Next ==
    /\ owner' = CHOOSE q \in Proc : q \in leaders
    /\ UNCHANGED leaders
Inv == owner \in leaders
====
"#;
    let corr_proof = cert_with_invs("CorrelatedInit", correlated_init, cfg, &["Inv"], g).unwrap();
    for needle in [
        "m.sem.initSetup ib st.core st.maps st.slots keys w",
        "theorem insert_idem",
        "theorem insert_comm",
        "FinSet.insert",
        "| some false => False",
    ] {
        assert!(corr_proof.contains(needle), "missing {needle}");
    }
}

#[test]
fn non_boolean_and_incomparable_set_predicates_in_choose_are_refused() {
    let cfg = "CONSTANT Proc = {p1, p2, p3}\nINIT Init\nNEXT Next\nINVARIANT Inv\n";
    let g = &[vec!["p1".into(), "p2".into(), "p3".into()]];

    // 1. Non-boolean CHOOSE predicate in projected MsgSet CHOOSE:
    // `IF m.from = owner THEN TRUE ELSE 1` fails with a non-boolean error when `owner` is not the first element.
    let non_bool_msg = r#"---- MODULE NonBoolMsgPred ----
EXTENDS Integers
CONSTANT Proc
VARIABLES owner, msgs
Init ==
    /\ owner \in Proc
    /\ msgs = {[from |-> p, val |-> 7] : p \in Proc}
Next == UNCHANGED <<owner, msgs>>
Inv == (CHOOSE m \in msgs : IF m.from = owner THEN TRUE ELSE 1).val = 7
====
"#;
    assert!(cert_with_invs("NonBoolMsgPred", non_bool_msg, cfg, &["Inv"], g).is_none());

    // 1b. Non-boolean CHOOSE predicate in comprehension-projected CHOOSE.
    let non_bool_comp = r#"---- MODULE NonBoolCompPred ----
EXTENDS Integers
CONSTANT Proc
VARIABLES owner
Init == owner \in Proc
Next == UNCHANGED owner
Inv == (CHOOSE m \in {[from |-> p, val |-> 7] : p \in Proc} : IF m.from = owner THEN TRUE ELSE 1).val = 7
====
"#;
    assert!(cert_with_invs("NonBoolCompPred", non_bool_comp, cfg, &["Inv"], g).is_none());

    // 1c. Non-boolean CASE predicate and non-boolean unique CHOOSE predicate.
    let non_bool_case = r#"---- MODULE NonBoolCasePred ----
EXTENDS Integers
CONSTANT Proc
VARIABLES owner, msgs
Init ==
    /\ owner \in Proc
    /\ msgs = {[from |-> p, val |-> 7] : p \in Proc}
Next == UNCHANGED <<owner, msgs>>
Inv == (CHOOSE m \in msgs : CASE m.from = owner -> TRUE [] OTHER -> 1).val = 7
====
"#;
    assert!(cert_with_invs("NonBoolCasePred", non_bool_case, cfg, &["Inv"], g).is_none());

    let non_bool_unique = r#"---- MODULE NonBoolUniquePred ----
EXTENDS Integers
CONSTANT Proc
VARIABLES owner, leaders
Init == owner \in Proc /\ \E p \in Proc : leaders = {p}
Next ==
    /\ owner' = CHOOSE q \in Proc : IF q = owner THEN TRUE ELSE 1
    /\ UNCHANGED leaders
Inv == owner \in Proc
====
"#;
    assert!(cert_with_invs("NonBoolUniquePred", non_bool_unique, cfg, &["Inv"], g).is_none());

    // 2. Incomparable element domains in set operations inside CHOOSE predicates:
    // `{1} \subseteq {"x"}`, plus `\cup`, `\cap`, `\`, `=`, `#`, `\in`, `\notin`, `Cardinality({1, "x"})`.
    for (idx, bad_expr) in [
        r#"{1} \subseteq {"x"}"#,
        r#"{1} \cup {"x"} = {1}"#,
        r#"{1} \cap {"x"} = {}"#,
        r#"{1} \ {"x"} = {1}"#,
        r#"{1} = {"x"}"#,
        r#"{1} # {"x"}"#,
        r#"1 \in {"x"}"#,
        r#"1 \notin {"x"}"#,
        r#"Cardinality({1, "x"}) = 2"#,
    ]
    .into_iter()
    .enumerate()
    {
        let spec = format!(
            r#"---- MODULE IncompSet{idx} ----
EXTENDS Integers, FiniteSets
CONSTANT Proc
VARIABLES owner, msgs
Init ==
    /\ owner \in Proc
    /\ msgs = {{[from |-> p, val |-> 7] : p \in Proc}}
Next == UNCHANGED <<owner, msgs>>
Inv == (CHOOSE m \in msgs : IF m.from = owner THEN TRUE ELSE {bad_expr}).val = 7
====
"#
        );
        assert!(
            cert_with_invs(&format!("IncompSet{idx}"), &spec, cfg, &["Inv"], g).is_none(),
            "incomparable set op must be refused: {bad_expr}"
        );
    }

    // 2b. Typed model value `P_1` vs integer or differently-typed `Q_1` must be refused in all set/equality ops.
    let typed_cfg = "CONSTANTS\n  Proc = {p1, p2, p3}\n  TagP = P_1\n  TagQ = Q_1\nINIT Init\nNEXT Next\nINVARIANT Inv\n";
    for (idx, bad_expr) in [
        r#"{TagP} \subseteq {1}"#,
        r#"{TagP} \cup {1} = {TagP}"#,
        r#"{TagP} \cap {1} = {}"#,
        r#"{TagP} \ {1} = {TagP}"#,
        r#"TagP = 1"#,
        r#"TagP # 1"#,
        r#"TagP \in {1}"#,
        r#"TagP \notin {1}"#,
        r#"{TagP} \subseteq {TagQ}"#,
        r#"TagP = TagQ"#,
    ]
    .into_iter()
    .enumerate()
    {
        let spec = format!(
            r#"---- MODULE TypedMv{idx} ----
EXTENDS Integers, FiniteSets
CONSTANTS Proc, TagP, TagQ
VARIABLES owner, msgs
Init ==
    /\ owner \in Proc
    /\ msgs = {{[from |-> p, val |-> 7] : p \in Proc}}
Next == UNCHANGED <<owner, msgs>>
Inv == (CHOOSE m \in msgs : IF m.from = owner THEN TRUE ELSE {bad_expr}).val = 7
====
"#
        );
        assert!(
            cert_with_invs(&format!("TypedMv{idx}"), &spec, typed_cfg, &["Inv"], g).is_none(),
            "typed model value comparison must be refused: {bad_expr}"
        );
    }
}

#[test]
fn choose_fold_guard_prime_and_comprehension_soundness_regressions() {
    let cfg = "CONSTANT Proc = {p1, p2, p3}\nINIT Init\nNEXT Next\nINVARIANT Inv\n";
    let g = &[vec!["p1".to_owned(), "p2".to_owned(), "p3".to_owned()]];

    // `EXTENDS Naturals` has `(0 - 1) \div 2 = 0` (`div_naturals`), so `0 - n` can be `0`
    // and `1 \div (0 - n)` in a CHOOSE/quantifier observation must be refused.
    let nat_div = r#"---- MODULE NatDivZero ----
EXTENDS Naturals
CONSTANT Proc
VARIABLES owner, n
Init == owner \in Proc /\ n = (0 - 1) \div 2
Next == owner' = (CHOOSE p \in Proc : p = owner) /\ UNCHANGED n
Inv == \E p \in Proc : p = owner \/ 1 \div (0 - n) = 1
====
"#;
    assert!(cert_with_invs("NatDivZero", nat_div, cfg, &["Inv"], g).is_none(), "Naturals (-1) \\div 2 = 0 must refuse");

    // Discarded folded record field `z |-> Sum(Proc)` with overflowing partial sums must refuse.
    let fold_discarded_overflow = r#"---- MODULE FoldDiscardedOverflow ----
EXTENDS Integers
CONSTANT Proc
VARIABLES owner, votes
RECURSIVE Sum(_)
Sum(S) == IF S = {} THEN 0 ELSE LET x == CHOOSE y \in S : TRUE IN votes[x] + Sum(S \ {x})
Init ==
    /\ owner \in Proc
    /\ \E p \in Proc : \E q \in Proc \ {p} :
        votes = [r \in Proc |-> IF r = p THEN 2147483647 ELSE IF r = q THEN 1 ELSE 0 - 1]
Next == UNCHANGED <<owner, votes>>
Inv == (CHOOSE r \in {[key |-> p, val |-> 7, z |-> Sum(Proc)] : p \in Proc} : TRUE).val = 7
====
"#;
    assert!(
        cert_with_invs("FoldDiscardedOverflow", fold_discarded_overflow, cfg, &["Inv"], g).is_none(),
        "discarded overflowing fold field must refuse"
    );

    // Discarded function-form fold `Sum[{p}]` where `Sum == [S \in SUBSET leaders |-> ...]`
    // can fail its domain check when `p \notin leaders` and must refuse.
    let fold_discarded_dom = r#"---- MODULE FoldDiscardedDom ----
EXTENDS Integers
CONSTANT Proc
VARIABLES leaders, votes
Sum[S \in SUBSET leaders] == IF S = {} THEN 0 ELSE LET x == CHOOSE y \in S : TRUE IN votes[x] + Sum[S \ {x}]
Init ==
    /\ \E p \in Proc : leaders = {p}
    /\ votes = [r \in Proc |-> 1]
Next == UNCHANGED <<leaders, votes>>
Inv == (CHOOSE r \in {[key |-> p, val |-> 7, z |-> Sum[{p}]] : p \in Proc} : TRUE).val = 7
====
"#;
    assert!(
        cert_with_invs("FoldDiscardedDom", fold_discarded_dom, cfg, &["Inv"], g).is_none(),
        "discarded function-fold with unproved SUBSET domain must refuse"
    );

    // CHOOSE guard after an earlier choice-bearing assignment must refuse so `postGuard`
    // cannot disable a branch before the assignment's empty-witness CHOOSE error is raised.
    let guard_after_choose_assign = r#"---- MODULE GuardAfterChooseAssign ----
CONSTANT Proc
VARIABLE owner
Init == owner \in Proc
Next ==
    /\ owner' = (CHOOSE x \in Proc : x = owner /\ x # owner)
    /\ (CHOOSE y \in Proc : y = owner) # owner
Inv == owner \in Proc
====
"#;
    assert!(
        cert_with_invs("GuardAfterChooseAssign", guard_after_choose_assign, cfg, &["Inv"], g).is_none(),
        "CHOOSE guard after choice-bearing assignment must refuse"
    );

    // Record lowering in `pure_expr` must leave integer field `n |-> 7` intact while
    // splitting Boolean field `same |-> p = owner` (and must NOT substitute TRUE/FALSE for 7).
    let record_field_split = r#"---- MODULE RecordFieldSplit ----
EXTENDS Naturals
CONSTANT Proc
VARIABLES owner, info
Init ==
    /\ owner \in Proc
    /\ info = [p \in Proc |-> [n |-> 7, same |-> FALSE]]
Next ==
    /\ owner' = (CHOOSE x \in Proc : x = owner)
    /\ info' = [p \in Proc |-> [n |-> 7, same |-> (p = owner)]]
Inv == \A p \in Proc : info[p].n = 7 /\ (info[p].same <=> (p = owner))
====
"#;
    let cert = cert_with_invs("RecordFieldSplit", record_field_split, cfg, &["Inv"], g)
        .expect("record with integer + key-equality Boolean field should certify");
    assert!(
        cert.contains(r#"\"n\",\n                Expr {\n                    kind: Num(\n                        7,"#)
            && !cert.contains(r#"\"n\",\n                Expr {\n                    kind: Bool("#),
        "certificate must keep integer literal 7 on field `n` rather than substituting Bool"
    );

    // Synthetic fold cache must distinguish operator fold `A(Proc)` from function fold
    // `B[Proc]` (`B[S \in SUBSET {}]`) so out-of-domain `B[Proc]` is never replaced by `A(Proc)`'s hole.
    let fold_cache_dom = r#"---- MODULE FoldCacheDom ----
EXTENDS Integers
CONSTANT Proc
VARIABLES votes, m1, m2
RECURSIVE A(_)
A(S) == IF S = {} THEN 0 ELSE LET x == CHOOSE y \in S : TRUE IN votes[x] + A(S \ {x})
B[S \in SUBSET {}] == IF S = {} THEN 0 ELSE LET x == CHOOSE y \in S : TRUE IN votes[x] + B[S \ {x}]
Init ==
    /\ votes = [p \in Proc |-> 1]
    /\ m1 = [p \in Proc |-> 0]
    /\ m2 = [p \in Proc |-> 0]
Next ==
    /\ UNCHANGED votes
    /\ m1' = [p \in Proc |-> A(Proc)]
    /\ m2' = [p \in Proc |-> B[Proc]]
Inv == \A p \in Proc : m1[p] >= 0
====
"#;
    assert!(
        cert_with_invs("FoldCacheDom", fold_cache_dom, cfg, &["Inv"], g).is_none(),
        "out-of-domain function fold B[Proc] must not reuse cached hole from A(Proc)"
    );

    // Existential quantifier `\E y \in {} : ...` after a CHOOSE assignment must not hoist
    // ahead of the assignment's empty-witness CHOOSE error.
    let exists_after_choose = r#"---- MODULE ExistsAfterChoose ----
CONSTANT Proc
VARIABLES owner, other
Init == owner \in Proc /\ other \in Proc
Next ==
    /\ owner' = (CHOOSE x \in Proc : x = owner /\ x # owner)
    /\ (\E y \in {} : UNCHANGED other)
Inv == owner \in Proc
====
"#;
    assert!(
        cert_with_invs("ExistsAfterChoose", exists_after_choose, cfg, &["Inv"], g).is_none(),
        "existential bound after CHOOSE assignment must refuse"
    );

    // Primed CHOOSE `((CHOOSE r \in ...).val)'` must not hoist across `Prime` into pre-state
    // (including when an unprimed copy was cached earlier in the same branch).
    let primed_choose_hoist = r#"---- MODULE PrimedChooseHoist ----
EXTENDS Naturals
CONSTANT Proc
VARIABLES n, m
Init == n = 0 /\ m = [p \in Proc |-> 0]
Next ==
    /\ n' = 1
    /\ m' = [p \in Proc |-> ((CHOOSE r \in {[key |-> q, val |-> n] : q \in Proc} : TRUE).val)']
Inv == \A p \in Proc : m[p] = n
====
"#;
    assert!(
        cert_with_invs("PrimedChooseHoist", primed_choose_hoist, cfg, &["Inv"], g).is_none(),
        "hoisting CHOOSE across Prime must refuse"
    );

    let primed_choose_cached = r#"---- MODULE PrimedChooseCached ----
EXTENDS Naturals
CONSTANT Proc
VARIABLES n, pre, post
Init == n = 0 /\ pre = 0 /\ post = 0
Next ==
    /\ n' = 1
    /\ pre' = (CHOOSE r \in {[key |-> q, val |-> n] : q \in Proc} : TRUE).val
    /\ post' = ((CHOOSE r \in {[key |-> q, val |-> n] : q \in Proc} : TRUE).val)'
Inv == post = n
====
"#;
    assert!(
        cert_with_invs("PrimedChooseCached", primed_choose_cached, cfg, &["Inv"], g).is_none(),
        "cached CHOOSE must not rewrite inside Prime"
    );

    // `IF Bad THEN (\E p \in empty : ...) ELSE (\E p \in empty : ...)` must not hoist
    // arm-level existential bounds ahead of the `CHOOSE`-bearing `IF` condition.
    let if_cond_choose = r#"---- MODULE IfCondChooseBeforeArmBounds ----
EXTENDS Naturals
CONSTANT Proc
VARIABLES empty, m
Init == empty = {} /\ m = [p \in Proc |-> 0]
Next ==
    IF (CHOOSE r \in {[key |-> q, val |-> 0] : q \in empty} : TRUE).val = 0
    THEN \E p \in empty : empty' = empty /\ m' = [m EXCEPT ![p] = 1]
    ELSE \E p \in empty : empty' = empty /\ m' = [m EXCEPT ![p] = 2]
Inv == \A p \in Proc : m[p] = 0
====
"#;
    assert!(
        cert_with_invs("IfCondChooseBeforeArmBounds", if_cond_choose, cfg, &["Inv"], g).is_none(),
        "IF condition with CHOOSE before existential arm bounds must refuse"
    );

    // Non-nullary `Id(owner') = ...` in `choose_sym` must also refuse rather than normalizing
    // into an assignment target that `Enumerator::target` rejects.
    let choose_non_nullary_target = r#"---- MODULE ChooseNonNullaryTarget ----
CONSTANT Proc
VARIABLE owner
Id(t) == t
Init == owner \in Proc
Next == Id(owner') = (CHOOSE p \in Proc : TRUE)
Inv == owner \in Proc
====
"#;
    assert!(
        cert_with_invs("ChooseNonNullaryTarget", choose_non_nullary_target, cfg, &["Inv"], g).is_none(),
        "`Id(owner') = CHOOSE ...` must refuse"
    );

    // Message comprehension in `Init` whose payload depends on an enclosing existential
    // witness (`\E a, b \in Proc : msgs = {[from |-> p, val |-> IF a = b THEN 7 ELSE 8] : p \in Proc}`)
    // cannot be represented by core-only `MsgInit.comprehensionCore` and must refuse.
    let msg_init_witness = r#"---- MODULE MsgInitOuterWitness ----
EXTENDS Naturals
CONSTANT Proc
VARIABLE msgs
Init == \E a, b \in Proc : msgs = {[from |-> p, val |-> IF a = b THEN 7 ELSE 8] : p \in Proc}
Next == UNCHANGED msgs
Inv == (CHOOSE m \in msgs : TRUE).val = 7
====
"#;
    assert!(
        cert_with_invs("MsgInitOuterWitness", msg_init_witness, cfg, &["Inv"], g).is_none(),
        "outer Init witness inside message comprehension payload must refuse"
    );
}
