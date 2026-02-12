module

import Mathlib.Tactic.Common

/-! Checks that some utilities are available already when importing `Mathlib.Tactic.Common`. -/

/-- info: Loogle Usage -/
#guard_msgs (substring := true) in
#loogle

/-- Nat.add: ℕ → ℕ → ℕ -/
#guard_msgs (substring := true) in
#find Nat → Nat → Nat

/-- info: trivial : True -/
#guard_msgs (substring := true) in
theorem test_check_tactic : True := by
  -- `#check` is defined in Core, but `#check` as a tactic is defined in Mathlib
  #check trivial
  trivial

/-- info: 0 -/
#guard_msgs in
#simp only [] => 0

/--
info: def _aux_MathlibTest_BasicFiles_TacticCommon___macroRules_termTest_whatsnew_1 : Lean.Macro :=
fun x =>
  have __discr := x;
  if __discr.isOfKind `termTest_whatsnew = true then
    have __discr := __discr.getArg 0;
    do
    let info ← Lean.MonadRef.mkInfoFromRefPos
    let _ ← Lean.getCurrMacroScope
    let _ ← Lean.MonadQuotation.getContext
    pure { raw := Lean.Syntax.node1 info `num (Lean.Syntax.atom info "0") }.raw
  else
    have __discr := x;
    throw Lean.Macro.Exception.unsupportedSyntax

def termTest_whatsnew : Lean.ParserDescr :=
Lean.ParserDescr.node `termTest_whatsnew 1024 (Lean.ParserDescr.symbol "test_whatsnew")

-- Lean.declRangeExt extension: 2 new entries

-- _private.Lean.Compiler.MetaAttr.0.Lean.metaExt extension: 2 new entries

-- _private.Lean.Compiler.MetaAttr.0.Lean.declMetaExt extension: 10 new entries

-- _private.Lean.AddDecl.0.Lean.privateConstKindsExt extension: 2 new entries

-- Lean.Compiler.LCNF.baseExt extension: 2 new entries

-- Lean.Compiler.LCNF.monoExt extension: 10 new entries

-- Lean.IR.declMapExt extension: 11 new entries

-- Lean.Compiler.LCNF.UnreachableBranches.functionSummariesExt extension: 2 new entries

-- Lean.extraModUses extension: 1 new entries

-- Lean.Parser.parserExtension extension: 3 new entries

-- Lean.Elab.macroAttribute extension: 1 new entries
-/
#guard_msgs in
whatsnew in
notation "test_whatsnew" => 0

/-- info: Used 3 heartbeats, which is less than the current maximum of 200000. -/
#guard_msgs in
#count_heartbeats in
theorem test_count_heartbeats : True := trivial

/--
info: Declarations are sorry-free!
---
warning: declaration uses `sorry`
-/
#guard_msgs in
#print sorries in
theorem test_print_sorries : True := by
  sorry

-- Guard against the shake tool modifying our imports
/-- info: [public import Init, import Mathlib.Tactic.Common] -/
#guard_msgs in
run_elab Lean.logInfo m!"{(← Lean.MonadEnv.getEnv).imports}"
