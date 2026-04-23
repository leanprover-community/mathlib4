/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Algebra.Group.Torsion
import Mathlib.Algebra.Module.Rat
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Algebra.Ring.Commute
import Mathlib.Analysis.CStarAlgebra.Unitization
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike


/-! # The Fuglede–Putnam–Rosenblum theorem

Let `A` be a C⋆-algebra, and let `a b x : A`. The Fuglede–Putnam–Rosenblum theorem states that
if `a` and `b` are normal and `x` intertwines `a` and `b` (i.e., `SemiconjBy x a b`, that is,
`x * a = b * x`), then `x` also intertwines `star a` and `star b`. Fuglede's original result
[fuglede1950] was for `a = b` (i.e., if `x` commutes with `a`, then `x` also commutes with
`star a`), and Putnam [putnam1951] extended it to intertwining elements.

Rosenblum [rosenblum1958] later gave the elementary proof formalized here using Liouville's theorem
which proceeds as follows. Consider the map `f : ℂ → A` given by
`z ↦ exp (z • star b) * x * exp (z • star (-a))`.
When `x` intertwines `a` and `b` (i.e., `SemiconjBy x a b`), then it also intertwines
`exp (star z • a)` and `exp (star z • b)`. Then the map `f` can be realized as `z ↦ u * x * v` for
fixed unitaries `u` and `v`. In fact, `u = exp (I • 2 • ℑ (z • star b))` and
`v = exp (I • 2 • ℑ (star z • a))`; it is here that normality of `a` and `b` is used to ensure that
`exp (star z • a) * exp (- star (z • a)) = exp (I • 2 • ℑ (star z • a))` and likewise for `b`.
Therefore `‖f z‖ = ‖x‖` for all `z`, and since `f` is clearly entire, by Liouville's theorem,
`f` is constant. Evaluating at `z = 0` proves that `f z = x` for all `z`. Therefore,
`exp (z • star b) * x = x * exp (z • star a)`. Differentiating both sides and evaluating at `z = 0`
proves that `star b * x = x * star a`, as desired.

In a follow-up paper, Cater [cater1961] proved a number of related results using similar techniques.
We include one of these below, `isStarNormal_iff_forall_exp_mul_exp_mem_unitary`,
but the proof is independent of the Fuglede–Putnam–Rosenblum theorem.

## Main results

+ `fuglede_putnam_rosenblum`: If `a` and `b` are normal elements in a C⋆-algebra `A` which
  are interwined by `x` (i.e., `SemiconjBy x a b`, that is, `x * a = b * x`), then `star a` and
  `star b` are also intertwined by `x`.
+ `isStarNormal_iff_forall_exp_mul_exp_mem_unitary`: A characterization of normal elements in a
  C⋆-algebra in terms of exponentials.

## References

+ [fuglede1950] Bent Fuglede, "A commutativity theorem for normal operators"
+ [putnam1951] C. R. Putnam, "On normal operators in Hilbert space"
+ [rosenblum1958] M. Rosenblum, "On a theorem of Fuglede and Putnam"
+ [cater1961] S. Cater, "Observations on a paper by Rosenblum"

-/


open NormedSpace selfAdjoint Bornology Complex
open scoped ComplexStarModule

variable {A : Type*} [CStarAlgebra A] {a b x : A} [IsStarNormal a] [IsStarNormal b]

/-- The map `expMulMulExp : ℂ → A` given by `z ↦ exp (z • star b) * x * exp (z • star (-a))` for
fixed `a b x : A`. -/
noncomputable def expMulMulExp (a b x : A) (z : ℂ) : A := exp (z • star b) * x * exp (z • star (-a))

lemma expMulMulExp_eq_expUnitary_mul_mul_expUnitary (h : SemiconjBy x a b) (z : ℂ) :
    expMulMulExp a b x z =
      expUnitary ((2 : ℝ) • ℑ (z • star b)) * x * expUnitary ((2 : ℝ) • ℑ (star z • a)) := by
  let _ : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A
  nth_rw 1 [expMulMulExp, ← (h.smul_right (star z)).exp_neg_mul_mul_exp_eq_self]
  simp_rw [← mul_assoc, mul_assoc (_ * _ * x)]
  congr!
  all_goals
    simp [imaginaryPart_apply_coe, smul_comm (2 : ℝ) I, smul_smul I I, sub_eq_add_neg]
    grind [exp_add_of_commute, Commute.smul_right, Commute.neg_right]

lemma expMulMulExp_const (h : SemiconjBy x a b) (z : ℂ) : expMulMulExp a b x z = x := by
  have hf : Differentiable ℂ (expMulMulExp a b x : ℂ → A) := by unfold expMulMulExp; fun_prop
  have : IsBounded (Set.range (expMulMulExp a b x)) := by
    apply Metric.isBounded_sphere (x := (0 : A)) (r := ‖x‖) |>.subset
    rintro - ⟨z, hz, rfl⟩
    rw [mem_sphere_iff_norm, sub_zero, expMulMulExp_eq_expUnitary_mul_mul_expUnitary h z,
      CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]
  simpa [expMulMulExp] using hf.apply_eq_apply_of_bounded this z 0

/- This is not public because it is superseded by `SemiconjBy.star_right`. -/
lemma SemiconjBy.star_right_of_unital (h : SemiconjBy x a b) :
    SemiconjBy x (star a) (star b) := by
  suffices key : ∀ z : ℂ, x * exp (z • star a) = exp (z • star b) * x by
    have (a : A) : HasDerivAt (fun z : ℂ ↦ exp (z • a)) a 0 := by
      simpa using hasDerivAt_exp_smul_const a (0 : ℂ)
    apply (this (star a)).const_mul x |>.unique
    simpa [key] using (this (star b)).mul_const x
  intro z
  let _ : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A
  let _ := invertibleExp (z • star a)
  simpa [← mul_assoc, ← invOf_exp, expMulMulExp] using
    congr($(expMulMulExp_const h z) * exp (z • star a)).symm

/-- **Fuglede–Putnam–Rosenblum**: If `a` and `b` are normal elements in a C⋆-algebra `A` which
are interwined by `x`, then `star a` and `star b` are also intertwined by `x`. -/
public lemma SemiconjBy.star_right {A : Type*} [NonUnitalCStarAlgebra A] {a b x : A}
    (ha : IsStarNormal a) (hb : IsStarNormal b) (h : SemiconjBy x a b) :
    SemiconjBy x (star a) (star b) := by
  apply Unitization.inr_injective (R := ℂ)
  simp only [Unitization.inr_mul, Unitization.inr_star]
  apply SemiconjBy.star_right_of_unital
  simpa [SemiconjBy] using mod_cast h.eq

public alias fuglede_putnam_rosenblum := SemiconjBy.star_right

/-- **Fuglede–Putnam–Rosenblum**: If `a` is a normal element in a C⋆-algebra `A` which
commutes with `x`, then `star a` commutes with `x`. -/
public lemma IsStarNormal.commute_star_right {A : Type*} [NonUnitalCStarAlgebra A] {a x : A}
    (ha : IsStarNormal a) (h : Commute x a) :
    Commute x (star a) :=
  h.semiconjBy.star_right ha ha

/-- **Fuglede–Putnam–Rosenblum**: If `a` is a normal element in a C⋆-algebra `A` which
commutes with `x`, then `star a` commutes with `x`. -/
public lemma IsStarNormal.commute_star_left {A : Type*} [NonUnitalCStarAlgebra A] {a x : A}
    (ha : IsStarNormal a) (h : Commute a x) :
    Commute (star a) x :=
  ha.commute_star_right h.symm |>.symm

/-- A characterization of normal elements in a C⋆-algebra in terms of exponentials. -/
public lemma isStarNormal_iff_forall_exp_mul_exp_mem_unitary {a : A} :
    IsStarNormal a ↔ ∀ x : ℝ, exp (x • a) * exp (-x • star a) ∈ unitary A := by
  let _ : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A
  have : IsAddTorsionFree A := IsAddTorsionFree.of_module_rat A
  refine ⟨fun ha x ↦ ?_, fun ha ↦ ?_⟩
  /- If `a` is normal, then clearly `exp (x • a) * exp (- x • star a) = exp (I • x • 2 • ℑ a)`
  and the latter is clearly an exponential unitary. -/
  · convert (selfAdjoint.expUnitary (x • (2 : ℝ) • ℑ a)).2
    have hcomm := star_comm_self (x := a) |>.symm.smul_left x |>.smul_right (-x)
    rw [← exp_add_of_commute hcomm]
    simp [imaginaryPart_apply_coe, smul_comm (2 : ℝ) I, smul_comm x I, smul_smul I I, smul_add x,
      sub_eq_add_neg]
  /- Take any `x : ℝ` and suppose `u := exp (x • a) * exp (- x • a)` is unitary. Then
  `exp (- x • a) * exp (x • star a) = star u = u⁻¹ = exp (x • star a) * exp (- x • a)`. -/
  · have key : ∀ x : ℝ, exp (- x • a) * exp (x • star a) = exp (x • star a) * exp (- x • a) := by
      intro x
      let u : unitary A := ⟨_, ha x⟩
      convert congr(($(Unitary.star_eq_inv u) : A))
      · simp [u, star_exp]
      · simp_rw [u, ← Unitary.val_inv_toUnits_apply, neg_smul, ← Units.mul_eq_one_iff_eq_inv,
          Unitary.val_toUnits_apply]
        let _ := invertibleExp (𝔸 := A)
        rw [mul_assoc]
        simp [← invOf_exp]
    /- Compute the second derivative with respect to `x` of each side of this expression and
    evaluate at `x = 0`. -/
    have h_deriv (a b c : A) (y : ℝ) :
        deriv (fun x : ℝ ↦ exp (x • a) * c * exp (x • b)) y =
          exp (y • a) * (a * c + c * b) * exp (y • b) := by
      rw [mul_add, add_mul, ← mul_assoc _ a, ← mul_assoc _ c b, mul_assoc _ b]
      exact (hasDerivAt_exp_smul_const a y).mul_const c |>.mul
        (hasDerivAt_exp_smul_const' b y) |>.deriv
    have h_deriv₂ (a b : A) :
        deriv (fun y ↦ deriv (fun x : ℝ ↦ exp (x • a) * exp (x • b)) y) 0 =
          a ^ 2 + 2 • (a * b) + b ^ 2 := by
      conv => enter [1, 1, y, 1, x, 1]; rw [← mul_one (exp (x • a))]
      simp_rw [h_deriv, zero_smul, NormedSpace.exp_zero, mul_one, one_mul]
      noncomm_ring
    have h₃ := h_deriv₂ (-a) (star a)
    have h₄ := h_deriv₂ (star a) (-a)
    simp only [smul_neg, even_two, Even.neg_pow, neg_smul] at h₃ h₄ key
    /- By `key`, these second derivatives evaluated at zero must be equal, so we find
    `a ^ 2 + 2 • (- a * star a) + (star a) ^ 2 = star ^ 2 + 2 • (star a * a) + a ^ 2`,
    and then elementary algebra shows `star a * a = a * star a`, so `a` is normal.  -/
    simp_rw [key] at h₃
    rw [h₃] at h₄
    rw [isStarNormal_iff, commute_iff_eq]
    apply nsmul_right_injective two_ne_zero
    rw [← sub_eq_zero] at h₄ ⊢
    rw [← h₄]
    noncomm_ring
