module

public import MathlibTest.CategoryTheory.TheoremTransformRegistration

open Lean Meta Elab Command Mathlib.Tactic.TheoremTransform

namespace Tests.TheoremTransform

@[transform_lemma test_zero_add]
lemma eq_nat {m n : Nat} (h : m = n) : m = n := h

example {m n : Nat} (h : m = n) : m = n := eq_nat_zeroAdd h

example {m n : Nat} (h : m = n) : m = n := transform_lemma% test_zero_add h

@[transform_lemma test_mul_one]
lemma eq_mul {M : Type*} [MulOneClass M] {a b : M} (h : a = b) : a = b := h

example {M : Type*} [MulOneClass M] {a b : M} (h : a = b) : a = b := eq_mul_mulOne h

example {M : Type*} [MulOneClass M] {a b : M} (h : a = b) : a = b :=
  transform_lemma% test_mul_one h

-- The helper introduces `0 +`; its registered post-processing removes it from the actual type.
run_cmd liftTermElabM do
  let info ← getConstInfo ``eq_nat_zeroAdd
  forallTelescope info.type fun _ type => do
    let some (_, lhs, rhs) := type.eq? | throwError "expected an equality"
    guard <| lhs.isFVar && rhs.isFVar

attribute [transform_lemma test_zero_add] eq_nat_zeroAdd

example {m n : Nat} (h : m = n) : m = n := eq_nat_zeroAdd_zeroAdd h

-- Inapplicability restores proof/type assignments, declarations, and messages.
#guard_msgs in
run_cmd liftTermElabM do
  let type ← mkFreshExprMVar (mkSort .zero)
  let value ← mkFreshExprMVar type
  let before ← getMCtx
  let result ← apply? { transformation := `test_inapplicable } ⟨type, value⟩
  guard <| result matches .error _
  guard <| !(← type.mvarId!.isAssigned) && !(← value.mvarId!.isAssigned)
  guard <| (← getMCtx).decls.toList.length == before.decls.toList.length
  guard <| !(← getEnv).contains `Tests.failedProbeDeclaration

/-- error: test transformation implementation error -/
#guard_msgs in
@[transform_lemma test_broken]
lemma implementation_error : True := trivial

/-- error: the proof template for 'test_zero_add' does not apply -/
#guard_msgs in
@[transform_lemma test_zero_add]
lemma inapplicable : True := trivial

end Tests.TheoremTransform
