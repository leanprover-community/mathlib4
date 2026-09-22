module

public import Mathlib.Util.TheoremTransform
public import Mathlib.Algebra.Group.Defs

public section

namespace Tests.TheoremTransform

theorem zeroAddCongr {m n : Nat} (h : m = n) : 0 + m = 0 + n := congrArg (0 + ·) h

theorem mulOneCongr {M : Type*} [MulOneClass M] {a b : M} (h : a = b) :
    a * 1 = b * 1 := congrArg (· * 1) h

public meta section

open Lean Meta Elab Mathlib.Tactic.TheoremTransform

-- This module imports no category theory. Importing it registers a usable transformation,
-- including its own normalization policy, without changing the engine or any bundle profile.
initialize register `test_zero_add (ofTemplate "_zeroAdd" ``zeroAddCongr 2
  (simpOnlyNames [``Nat.zero_add] · (config := { decide := false })))

initialize register `test_mul_one (ofTemplate "_mulOne" ``mulOneCongr 4
  (simpOnlyNames [``mul_one] · (config := { decide := false })))

initialize register `test_inapplicable {
  suffix := "_inapplicable"
  apply := fun _ p => do
    guard <| ← isDefEq p.type (mkConst ``True)
    p.value.mvarId!.assign (mkConst ``True.intro)
    let pendingInst ← mkFreshExprMVar (← mkAppM ``Inhabited #[mkConst ``Nat]) .synthetic
    Term.registerSyntheticMVarWithCurrRef pendingInst.mvarId! (.typeClass none)
    Lean.addDecl <| .thmDecl {
      name := `Tests.failedProbeDeclaration
      levelParams := []
      type := mkConst ``True
      value := mkConst ``True.intro }
    logInfo "this message must be rolled back"
    return .error m!"test inapplicability" }

initialize register `test_broken {
  suffix := "_broken"
  apply := fun _ _ => throwError "test transformation implementation error" }

end

end Tests.TheoremTransform
