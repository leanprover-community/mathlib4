/-
Copyright (c) 2026 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/
module

public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Multiset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.RingTheory.LocalRing.Basic
meta import Mathlib.Tactic.Attr.Register
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.SetLike

/-!
# Approximate roots and polynomials in a normed field

In this file, we prove several approximation lemmas on a normed field.

## Main results
- `Polynomial.exists_roots_norm_sub_lt_of_norm_coeff_sub_lt` :  **Continuity of Roots.**
Let `f` and `g` be two monic polynomials such that `g` splits. If the coefficients of two
polynomials `f` and `g` are sufficiently close, then every root of `f` has a corresponding root
of `g` nearby.

- `Polynomial.exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt` : Let `K` be a
dense subfield of a normed field `L`. Every monic polynomial in `L` can be approximated by
a monic polynomial in `K` of the same degree.

## TODO
Use the fact that `f.discr` is polynomial of the coefficients of `f` to show that
every polynomial `f` can be approximated by a *separable* polynomial. This result can be used
to show that the completion a separably closed field is algebraically closed, upgrading the
current theorem `IsAlgClosed.of_denseRange`.

## Tags
Approximation, polynomial, normed field, continuity of roots
-/

@[expose] public section

variable {K L : Type*}

namespace Polynomial

section ContinuityOfRoots

variable [NormedField K] [NormedField L] [NormedAlgebra K L] {f g : Polynomial K}
  {f g : Polynomial K} {ε : ℝ}

/-- **Continuity of Roots.** Let `f` and `g` be two monic polynomials with `g` splits.
If the coefficients of two polynomials `f` and `g` are sufficiently close, then every root of `f`
has a corresponding root of `g` nearby. -/
theorem exists_roots_norm_sub_lt_of_norm_coeff_sub_lt (hε : 0 < ε) {a : K} (ha : f.eval a = 0)
    (hfm : f.Monic) (hgm : g.Monic) (hdeg : g.natDegree = f.natDegree)
    (hcoeff : ∀ i : ℕ, ‖g.coeff i - f.coeff i‖ < ε) (hg : g.Splits) :
    ∃ b ∈ g.roots, ‖a - b‖ < ((f.natDegree + 1) * ε) ^ (f.natDegree : ℝ)⁻¹ * max ‖a‖ 1 := by
  -- Let `a` be a root of `f`. To show there exists a root `b` of `g` such that `‖a - b‖` is small,
  -- it suffices to show that `∏ (b ∈ g.roots) ‖a - b‖` is small.
  suffices this : (g.roots.map fun x => ‖a - x‖).prod <
      ((f.natDegree + 1) * ε) * (max ‖a‖ 1) ^ (f.natDegree : ℝ) by
    by_contra! h
    have := Multiset.prod_map_le_prod_map₀ (fun b ↦ ((f.natDegree + 1) * ε) ^ (f.natDegree : ℝ)⁻¹ *
        (‖a‖ ⊔ 1)) (fun b ↦ ‖a - b‖) (by intros; positivity) h
    simp only [Multiset.map_const', hg.natDegree_eq_card_roots.symm ▸ hdeg, Multiset.prod_replicate,
      mul_pow, ← Real.rpow_natCast,
      ← Real.rpow_mul (by positivity : ((f.natDegree + 1) * ε) > 0).le] at this
    rw [inv_mul_cancel₀, Real.rpow_one] at this
    · linarith
    · simp only [ne_eq, Nat.cast_eq_zero, hfm, Monic.natDegree_eq_zero]
      intro h
      simp [h] at ha
  -- `∏ (b ∈ g.roots) ‖a - b‖ = ‖g(a)‖ = ‖(g - f)(a)‖` is small since every
  -- coefficient of `‖g - f‖` is small.
  calc
  _ = (g.roots.map (fun x ↦ NormedField.toMulRingNorm K (a - x))).prod := rfl
  _ = ‖(g.roots.map (fun x ↦ a - x)).prod‖ := by
    rw [g.roots.prod_hom' (NormedField.toMulRingNorm K) (fun x : K ↦ a - x)]
    rfl
  _ = ‖g.eval a‖ := by
    congr
    rw [hg.eval_eq_prod_roots_of_monic hgm]
  _ ≤ ‖g.eval a - f.eval a‖ + ‖f.eval a‖ := by
    convert norm_add_le (g.eval a - f.eval a) (f.eval a)
    simp
  _ = ‖(∑ i ∈ Finset.range (g.natDegree + 1), C (g.coeff i - f.coeff i) * X ^ i).eval a‖ := by
    rw [← eval_sub]
    simp only [ha, norm_zero, add_zero]
    rw [(g - f).as_sum_range' (g.natDegree + 1)]
    · congr
      simp [← C_mul_X_pow_eq_monomial]
    · simpa [hdeg, Nat.lt_succ_iff] using g.natDegree_sub_le f
  _ ≤ ∑ i ∈ Finset.range (g.natDegree + 1), ‖(g.coeff i - f.coeff i) * a ^ i‖ := by
    have := norm_sum_le (Finset.range (g.natDegree + 1))
        (fun i ↦ (C (g.coeff i - f.coeff i) * X ^ i).eval a)
    simpa [eval_mul, eval_finset_sum] using this
    -- The following tactic does not work here:
    -- simpa [eval_mul, eval_finset_sum] using norm_sum_le (Finset.range (g.natDegree + 1))
    --     (fun i ↦ (C (g.coeff i - f.coeff i) * X ^ i).eval a)
  _ < _ := by
    rw [hdeg]
    convert Finset.sum_lt_sum_of_nonempty (g := fun i ↦ ε * (‖a‖ ⊔ 1) ^ ↑f.natDegree)
        (Finset.nonempty_range_add_one) ?_
    · simp [mul_assoc]
    · simp only [Finset.mem_range, norm_mul, norm_pow]
      intro i hi
      apply mul_lt_mul_of_lt_of_le_of_nonneg_of_pos
      · simpa [← map_sub] using hcoeff i
      · refine (pow_le_pow_left₀ (norm_nonneg a) (le_max_left ‖a‖ 1) i).trans ?_
        exact pow_le_pow_right₀ (le_max_right ‖a‖ 1) (Nat.le_of_lt_succ hi)
      all_goals positivity

/-- **Continuity of Roots.** A variation of
`Polynomial.exists_roots_norm_sub_lt_of_norm_coeff_sub_lt` allowing roots of `g` lives in a
field extension. -/
theorem exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt (hε : 0 < ε) {a : L} (ha : f.aeval a = 0)
    (hfm : f.Monic) (hgm : g.Monic) (hdeg : g.natDegree = f.natDegree)
    (hcoeff : ∀ i : ℕ, ‖g.coeff i - f.coeff i‖ < ε) (hg : (g.map (algebraMap K L)).Splits) :
    ∃ b ∈ g.aroots L, ‖a - b‖ < ((f.natDegree + 1) * ε) ^ (f.natDegree : ℝ)⁻¹ * max ‖a‖ 1 := by
  obtain ⟨b, h1, h2⟩ := exists_roots_norm_sub_lt_of_norm_coeff_sub_lt hε
      (f := f.map (algebraMap K L)) (by simpa using ha) (hfm.map _) (hgm.map _)
      (by simpa using hdeg) (by simpa [← map_sub] using hcoeff) hg
  use b, h1
  simpa using h2

end ContinuityOfRoots

section Approximation

variable [Field K] [NormedField L] [Algebra K L]

/-- If `K` is a dense subfield of `L`, then every monic polynomial in `L` can be
approximated by a monic polynomial in `K` of the same degree. -/
theorem exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt
    (hd : DenseRange (algebraMap K L)) {f : Polynomial L} (hf : f.Monic) {ε : ℝ} (hε : ε > 0) :
    ∃ g : Polynomial K, g.Monic ∧ f.natDegree = g.natDegree ∧ ∀ n : ℕ,
    ‖(g.map (algebraMap K L)).coeff n - f.coeff n‖ < ε := by
  by_cases h : f.natDegree = 0
  · use 1
    rw [hf.natDegree_eq_zero.mp]
    · simp only [monic_one, natDegree_one, Polynomial.map_one, sub_self, norm_zero, hε,
      implies_true, and_self]
    · exact h
  choose c hc using fun i ↦ Metric.denseRange_iff.mp hd (f.coeff i) ε hε
  have hdeg : (C 1 * X ^ f.natDegree + ∑ i < f.natDegree, C (c i) * X ^ i).natDegree
      = f.natDegree := by
    calc
      _ = (C (1 : K) * X ^ f.natDegree).natDegree := by
        apply Polynomial.natDegree_add_eq_left_of_natDegree_lt
        simp only [map_one, one_mul, natDegree_pow, natDegree_X, mul_one]
        rw [← Nat.le_sub_one_iff_lt (Nat.pos_of_ne_zero h)]
        apply Polynomial.natDegree_sum_le_of_forall_le
        refine fun i hi ↦ (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
        simpa [Nat.le_sub_one_iff_lt (Nat.pos_of_ne_zero h)] using hi
      _ = f.natDegree := by
        simp
  use C 1 * X ^ f.natDegree + ∑ i < f.natDegree, C (c i) * X ^ i
  refine ⟨?_, hdeg.symm, fun n ↦ ?_⟩
  · rw [Monic, leadingCoeff, hdeg]
    simp
  · rcases lt_trichotomy n f.natDegree with h | h | h
    · simpa [h, ne_of_lt h, ← dist_eq_norm_sub'] using hc n
    · simp [h, hf, hε]
    · simp [not_lt_of_gt h, ne_of_gt h, coeff_eq_zero_of_natDegree_lt h, hε]

end Approximation

end Polynomial
