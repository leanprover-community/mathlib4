/-
 Copyright (c) 2025 William Coram. All rights reserved.
 Released under Apache 2.0 license as described in the file LICENSE.
 Authors: William Coram
-/
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.RingTheory.MvPowerSeries.Basic

/-!
# Gauss norm for multivariate power series
This file defines the Gauss norm for power series. Given a multivariate power series `f`, a
function `v : R → ℝ` and a tuple `c` of real numbers, the Gauss norm is defined as the supremum of
the set of all values of `v (coeff t f) * ∏ i : t.support, c i` for all `t : σ →₀ ℕ`.
## Main Definitions and Results
* `MvPowerSeries.gaussNormC` is the supremum of the set of all values of
  `v (coeff t f) * ∏ i : t.support, c i`for all `t : σ →₀ ℕ`, where `f` is a multivariate power
  series, `v : R → ℝ` is a function and `c` is a tuple of real numbers.
* `MvPowerSeries.gaussNormC_nonneg`: if `v` is a non-negative function, then the Gauss norm is
  non-negative.
* `MvPowerSeries.gaussNormC_eq_zero_iff`: if `v` is a non-negative function and `v x = 0 ↔ x = 0`
  for all `x : R` and `c` is positive, then the Gauss norm is zero if and only if the power series
  is zero.
* `Mv.gaussNormC_nonarchimedean`: if `v` is a non-negative non-archimedean function and the set of
  values `v (coeff t f) * ∏ i : t.support, c i` is bounded above (similarily for `g`), then the
  Gauss norm is non-archimedean.
-/

@[expose] public section

open MvPowerSeries

variable {R F σ : Type*} [Semiring R] [FunLike F R ℝ] (v : F) (c : σ → ℝ) (f : MvPowerSeries σ R)

/-- Given a multivariate power series `f` in, a function `v : R → ℝ` and a real number `c`,
  the Gauss norm is defined as the supremum of the set of all values of
  `v (coeff t f) * ∏ i : t.support, c i` for all `t : σ →₀ ℕ`. -/
noncomputable def gaussNormC : ℝ :=
  sSup {a : ℝ | ∃ t : σ →₀ ℕ, a = v (coeff t f) * ∏ i ∈ t.support, (c i) ^ (t i)}

@[simp]
theorem gaussNormC_zero [ZeroHomClass F R ℝ] : gaussNormC v c 0 = 0 := by simp [gaussNormC]

private lemma gaussNormC_nonempty :
    {a | ∃ t : σ →₀ ℕ, a = v (coeff t f) * ∏ i ∈ t.support, (c i) ^ (t i)}.Nonempty := by
  use v (f.coeff 0) * ∏ i ∈ (0 : σ →₀ ℕ).support, (c i) ^ ((0 : σ →₀ ℕ) i), 0

lemma le_gaussNormC (hbd : BddAbove {a | ∃ t : σ →₀ ℕ, a = v (coeff t f) *
      ∏ i ∈ t.support, (c i) ^ (t i)}) (t : σ →₀ ℕ) :
    v (coeff t f) * ∏ i ∈ t.support, (c i) ^ (t i) ≤ gaussNormC v c f := by
  apply le_csSup hbd
  use t

theorem gaussNormC_nonneg [NonnegHomClass F R ℝ] : 0 ≤  gaussNormC v c f := by
  rw [gaussNormC]
  by_cases h : BddAbove {a | ∃ t : σ →₀ ℕ, a = v (coeff t f) * ∏ i ∈ t.support,(c i) ^ (t i)}
  · simp_rw [Real.le_sSup_iff h <| gaussNormC_nonempty v c f, Set.mem_setOf_eq, zero_add,
      existsAndEq, true_and]
    intro ε hε
    use 0
    simpa using lt_of_lt_of_le hε <| apply_nonneg v (f.constantCoeff)
  · simp only [h, not_false_eq_true, csSup_of_not_bddAbove, Real.sSup_empty, le_refl]

@[simp]
theorem gaussNormC_eq_zero_iff [ZeroHomClass F R ℝ] [NonnegHomClass F R ℝ] {v : F}
    (h_eq_zero : ∀ x : R, v x = 0 → x = 0) (hc : ∀ i, 0 < c i)
    (hbd : BddAbove {a | ∃ t : σ →₀ ℕ, a = v (coeff t f) * ∏ i ∈ t.support, (c i) ^ (t i)})  :
     gaussNormC v c f = 0 ↔ f = 0 := by
  refine ⟨?_, fun hf ↦ by simp [hf]⟩
  contrapose!
  intro hf
  apply ne_of_gt
  obtain ⟨n, hn⟩ := (MvPowerSeries.ne_zero_iff_exists_coeff_ne_zero f).mp hf
  calc
  0 < v (f.coeff n) * ∏ i ∈ n.support, (c i) ^ (n i) := by
    apply mul_pos _ (by exact Finset.prod_pos fun i a ↦ (fun i ↦ pow_pos (hc ↑i) (n ↑i)) i)
    specialize h_eq_zero (f.coeff n)
    simp_all only [ne_eq]
    positivity
  _ ≤ sSup {x | ∃ t, x = v (f.coeff t) * ∏ i ∈ t.support, (c i) ^ (t i)} := by
    rw [Real.le_sSup_iff hbd <| gaussNormC_nonempty v c f]
    simp only [Set.mem_setOf_eq, ↓existsAndEq, true_and]
    intro ε hε
    use n
    simp [hε]

@[simp]
theorem gaussNormC_nonarchimedean (f g : MvPowerSeries σ R) (hc : 0 ≤ c)
    (hv1 : ∀ x y, v (x + y) ≤ max (v x) (v y)) (hv2 : ∀ x, 0 ≤ v x)
    (hbfd : BddAbove {a | ∃ t : σ →₀ ℕ, a = v (coeff t f) * ∏ i ∈ t.support, (c i) ^ (t i)})
    (hbgd : BddAbove {a | ∃ t : σ →₀ ℕ, a = v (coeff t g) * ∏ i ∈ t.support, (c i) ^ (t i)}) :
    gaussNormC v c (f + g) ≤ max (gaussNormC v c f) (gaussNormC v c g) := by
  have H (t : σ →₀ ℕ) : 0 ≤ ∏ i ∈ t.support, c i ^ t i :=
    Finset.prod_nonneg (fun i hi ↦ pow_nonneg (hc i) (t i))
  have Final (t : σ →₀ ℕ) : v ((coeff t) (f + g)) * ∏ i ∈ t.support, c ↑i ^ t ↑i ≤
      max (v ((coeff t) f) * ∏ i ∈ t.support, c ↑i ^ t ↑i)
      (v ((coeff t) g) * ∏ i ∈ t.support, c ↑i ^ t ↑i) := by
    specialize hv1 (coeff t f) (coeff t g)
    rcases max_choice (v ((coeff t) f)) (v ((coeff t) g)) with h | h
    · have : max (v ((coeff t) f) * ∏ i ∈ t.support, c ↑i ^ t ↑i)
          (v ((coeff t) g) * ∏ i ∈ t.support, c ↑i ^ t ↑i) =
          (v ((coeff t) f) * ∏ i ∈ t.support, c ↑i ^ t ↑i) := by
        simp only [sup_eq_left]
        exact mul_le_mul_of_nonneg (by aesop) (by aesop) (by aesop) (H t)
      simp_rw [this]
      exact mul_le_mul_of_nonneg (by aesop) (by aesop) (by aesop) (H t)
    · have : max (v ((coeff t) f) * ∏ i ∈ t.support, c ↑i ^ t ↑i)
          (v ((coeff t) g) * ∏ i ∈ t.support, c ↑i ^ t ↑i) =
          (v ((coeff t) g) * ∏ i ∈ t.support, c ↑i ^ t ↑i) := by
        simp only [sup_eq_right]
        exact mul_le_mul_of_nonneg (by aesop) (by aesop) (by aesop) (H t)
      simp_rw [this]
      exact mul_le_mul_of_nonneg (by aesop) (by aesop) (by aesop) (H t)
  refine Real.sSup_le ?_ ?_
  · simp only [Set.mem_setOf_eq, forall_exists_index, forall_eq_apply_imp_iff]
    refine fun t ↦ calc
    _ ≤ _ := Final t
    _ ≤ max (sSup {a | ∃ t, a = v ((coeff t) f) * ∏ i ∈ t.support, c i ^ t i})
        (sSup {a | ∃ t, a = v ((coeff t) g) * ∏ i ∈ t.support, c i ^ t i}) := by
      simp only [le_sup_iff]
      rcases max_choice (v ((coeff t) f) * ∏ i ∈ t.support, c i ^ t i)
        (v ((coeff t) g) * ∏ i ∈ t.support, c i ^ t i) with h | h
      · left
        simp_rw [h, Real.le_sSup_iff hbfd <| gaussNormC_nonempty v c f, Set.mem_setOf_eq,
          existsAndEq, true_and]
        intro ε hε
        use t
        simp [hε]
      · right
        simp_rw [h, Real.le_sSup_iff hbgd <| gaussNormC_nonempty v c g, Set.mem_setOf_eq,
          existsAndEq, true_and]
        intro ε hε
        use t
        simp [hε]
  · simp only [le_sup_iff]
    left
    refine Real.sSup_nonneg ?_
    simp only [Set.mem_setOf_eq, forall_exists_index, forall_eq_apply_imp_iff]
    exact fun t ↦ mul_nonneg (hv2 (coeff t f)) (H t)
