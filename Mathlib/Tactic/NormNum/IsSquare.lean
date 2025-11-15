/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Tactic.NormNum.Irrational

/-! # `norm_num` extension for `IsSquare`

This module defines a `norm_num` extension for `IsSquare x` for rational `x`.

## Implementation details
To decide `IsSquare x`, we reduce it to `0 ≤ x ∧ ¬ Irrational √x` and use the existing `norm_num`
extensions for `Irrational` and `LE`.
-/

namespace Tactic.NormNum

section Lemmas

private lemma IsSquare_nat_iff_not_Irrational_sqrt (n : ℕ) :
    ¬ Irrational √(n : ℝ) ↔ IsSquare n := by
  simp [irrational_sqrt_natCast_iff]

private lemma IsSquare_int_iff_not_Irrational_sqrt (n : ℤ) (h : 0 ≤ n) :
    ¬ Irrational √(n : ℝ) ↔ IsSquare n := by
  rw [irrational_sqrt_intCast_iff]
  simp [h]

private lemma IsSquare_rat_iff_not_Irrational_sqrt (n : ℚ) (h : 0 ≤ n) :
    ¬ Irrational √(n : ℝ) ↔ IsSquare n := by
  rw [irrational_sqrt_ratCast_iff]
  simp [h]

end Lemmas

open Qq Lean Elab.Tactic Mathlib.Meta.NormNum

/-- `norm_num` extension that decides `IsSquare x` for rational `x`. -/
@[norm_num IsSquare _]
def evalIsSquare : NormNumExt where eval {u α} e := do
  let 0 := u | failure
  let ~q(Prop) := α | failure
  match e with
  | ~q(@IsSquare ℕ _ $x) =>
    let e' := q(¬ Irrational (√($x : ℝ)))
    let ⟨b, br⟩ ← deriveBoolOfIff e' e q(IsSquare_nat_iff_not_Irrational_sqrt $x)
    return .ofBoolResult br
  | ~q(@IsSquare ℤ _ $x) =>
    let e₁ := q(0 ≤ $x)
    let ⟨b₁, br₁⟩ ← deriveBool e₁
    match b₁ with
    | false =>
      return .isFalse (x := q(IsSquare $x)) q(fun h ↦ $br₁ h.nonneg)
    | true =>
    let e₂ := q(¬ Irrational √($x : ℝ))
    let ⟨b, br⟩ ← deriveBoolOfIff e₂ e q(IsSquare_int_iff_not_Irrational_sqrt $x $br₁)
    return .ofBoolResult br
  | ~q(@IsSquare ℚ _ $x) =>
    let e₁ := q(0 ≤ $x)
    let ⟨b₁, br₁⟩ ← deriveBool e₁
    match b₁ with
    | false =>
      return .isFalse (x := q(IsSquare $x)) q(fun h ↦ $br₁ h.nonneg)
    | true =>
    let e₂ := q(¬ Irrational √($x : ℝ))
    let ⟨b, br⟩ ← deriveBoolOfIff e₂ e q(IsSquare_rat_iff_not_Irrational_sqrt $x $br₁)
    return .ofBoolResult br
  | _ => failure

end Tactic.NormNum
