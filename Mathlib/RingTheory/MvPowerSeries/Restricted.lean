/-
Copyright (c) 2025 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
module

public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic

/-!
# Multivariate restricted power series

`IsRestricted` : We say a multivariate power series over a normed ring `R` is restricted for a
tuple `c` if `‖coeff t f‖ * ∏ i ∈ t.support, c i ^ t i → 0` under the cofinite filter.

-/

@[expose] public section

open MvPowerSeries Filter
open scoped Topology Pointwise

/-- A multivariate power series over a normed ring `R` is restricted for a
  tuple `c` if `‖coeff t f‖ * ∏ i ∈ t.support, c i ^ t i → 0` under the cofinite filter. -/
def IsRestricted {R : Type*} [NormedRing R] {σ : Type*} (c : σ → ℝ) (f : MvPowerSeries σ R) :=
  Tendsto (fun (t : σ →₀ ℕ) ↦ ‖coeff t f‖ * t.prod (c · ^ ·)) cofinite (𝓝 0)

lemma isRestricted_iff_abs {R : Type*} [NormedRing R] {σ : Type*} (c : σ → ℝ)
    (f : MvPowerSeries σ R) : IsRestricted c f ↔ IsRestricted |c| f := by
  simp [IsRestricted, NormedAddCommGroup.tendsto_nhds_zero, Finsupp.prod]

lemma zero {R : Type*} [NormedRing R] {σ : Type*} (c : σ → ℝ) :
    IsRestricted c (0 : MvPowerSeries σ R) := by
  simpa [IsRestricted] using tendsto_const_nhds

/-- The set of `‖coeff t f‖ * ∏ i : t.support, c i ^ t i` for a given power series `f`
  and tuple `c`. -/
def convergenceSet {R : Type*} [NormedRing R] {σ : Type*} (c : σ → ℝ) (f : MvPowerSeries σ R) :
  Set ℝ := {‖coeff t f‖ * t.prod (c · ^ ·) | t : σ →₀ ℕ}

lemma monomial {R : Type*} [NormedRing R] {σ : Type*} (c : σ → ℝ) (n : σ →₀ ℕ) (a : R) :
    IsRestricted c (monomial n a) := by
  classical
  refine tendsto_nhds_of_eventually_eq (Set.Subsingleton.finite ?_)
  aesop (add simp [Set.Subsingleton, coeff_monomial])

lemma one {R : Type*} [NormedRing R] {σ : Type*} (c : σ → ℝ) :
    IsRestricted c (1 : MvPowerSeries σ R) := by
  exact monomial c 0 1

lemma C {R : Type*} [NormedRing R] {σ : Type*} (c : σ → ℝ) (a : R) :
    IsRestricted c (C (σ := σ) a) := by
  simpa [monomial_zero_eq_C_apply] using monomial c 0 a

lemma add {R : Type*} [NormedRing R] {σ : Type*} (c : σ → ℝ) {f g : MvPowerSeries σ R}
    (hf : IsRestricted c f) (hg : IsRestricted c g) : IsRestricted c (f + g) := by
  rw [isRestricted_iff_abs, IsRestricted] at *
  refine tendsto_const_nhds.squeeze (add_zero (0 : ℝ) ▸ hf.add hg) (fun n ↦ ?_) fun n ↦ ?_
  · dsimp [Finsupp.prod]; positivity -- TODO: add positivity extension for Finsupp.prod
  rw [← add_mul]
  exact mul_le_mul_of_nonneg_right (norm_add_le ..) (by dsimp [Finsupp.prod]; positivity)

lemma neg {R : Type*} [NormedRing R] {σ : Type*} (c : σ → ℝ) {f : MvPowerSeries σ R}
    (hf : IsRestricted c f) : IsRestricted c (-f) := by
  rw [isRestricted_iff_abs, IsRestricted] at *
  simpa [IsRestricted] using hf

lemma smul {R : Type*} [NormedRing R] {σ : Type*} (c : σ → ℝ) {f : MvPowerSeries σ R}
    (hf : IsRestricted c f) (r : R) : IsRestricted c (r • f) := by
  rw [isRestricted_iff_abs, IsRestricted] at *
  refine tendsto_const_nhds.squeeze ((hf.const_mul ‖r‖).trans_eq (by simp)) (fun n ↦ ?_) fun n ↦ ?_
  · dsimp [Finsupp.prod]; positivity
  simp only [map_smul, smul_eq_mul, Pi.abs_apply, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (by dsimp [Finsupp.prod]; positivity)

lemma nsmul {R : Type*} [NormedRing R] {σ : Type*} (c : σ → ℝ) (n : ℕ)
    (f : MvPowerSeries σ R) (hf : IsRestricted c f) : IsRestricted c (n • f) := by
  convert smul c hf (n : R)
  ext _ _
  simp_rw [map_smul, smul_eq_mul, map_nsmul, nsmul_eq_mul]

lemma zsmul {R : Type*} [NormedRing R] {σ : Type*} (c : σ → ℝ) (n : ℤ)
    (f : MvPowerSeries σ R) (hf : IsRestricted c f) : IsRestricted c (n • f) := by
  convert smul c hf (n : R)
  ext _ _
  simp_rw [map_smul, smul_eq_mul, map_zsmul, zsmul_eq_mul]

open IsUltrametricDist

lemma tendsto_antidiagonal {M S : Type*} [AddMonoid M] [Finset.HasAntidiagonal M]
    {f g : M → S} [NormedRing S] [IsUltrametricDist S] {C : M → ℝ}
    (hC : ∀ a b, C (a + b) = C a * C b) (hf : Tendsto (fun i ↦ ‖f i‖ * C i) cofinite (𝓝 0))
    (hg : Tendsto (fun i ↦ ‖g i‖ * C i) cofinite (𝓝 0)) :
    Tendsto (fun a ↦ ‖∑ p ∈ Finset.antidiagonal a, (f p.1 * g p.2)‖ * C a) cofinite (𝓝 0) := by
  obtain ⟨F, Fpos, hF⟩ := (bddAbove_iff_exists_ge 1).mp
    (Tendsto.bddAbove_range_of_cofinite (Filter.Tendsto.norm hf))
  obtain ⟨G, Gpos, hG⟩ := (bddAbove_iff_exists_ge 1).mp
    (Tendsto.bddAbove_range_of_cofinite (Filter.Tendsto.norm hg))
  simp only [norm_mul, Real.norm_eq_abs, Set.mem_range, forall_exists_index,
    forall_apply_eq_imp_iff] at hF hG
  simp only [NormedAddCommGroup.tendsto_nhds_zero, gt_iff_lt, Real.norm_eq_abs, eventually_cofinite,
    not_lt] at *
  intro ε hε
  let I := {x | ε / G ≤ |‖f x‖ * C x|}
  let J := {x | ε / F ≤ |‖g x‖ * C x|}
  specialize hf (ε / G) (by positivity)
  specialize hg (ε / F) (by positivity)
  refine Set.Finite.subset (s := I + J) (Set.Finite.add (by aesop) (by aesop)) ?_
  by_contra h
  obtain ⟨t, ht, ht'⟩ := Set.not_subset.mp h
  simp only [abs_mul, abs_norm] at *
  have hh (i j : M) (ht_eq : t = i + j) : i ∉ I ∨ j ∉ J := by
    simp_rw [ht_eq] at ht'
    contrapose ht'
    simp only [not_or, not_not] at *
    use i; use ht'.1; use j; use ht'.2
  have hij (i j : M) (ht_eq : t = i + j) : ‖f i * g j‖ * |C t| < ε := by
      calc
      _ ≤ ‖f i‖ * ‖g j‖ * |C t| :=
        mul_le_mul_of_nonneg (norm_mul_le _ _) (le_refl _) (norm_nonneg _) (abs_nonneg _)
      _ ≤ ‖f i‖ * ‖g j‖ * (|C i| * |C j|) :=
        mul_le_mul_of_nonneg (le_refl _) (by simp [ht_eq, hC]) (by positivity) (by positivity)
      _ = (‖f i‖ * |C i|) * (‖g j‖ * |C j|) := by
        ring
      _ < ε := by
        rcases hh i j ht_eq with hi | hj
        · rw [← div_mul_cancel₀ ε (show G ≠ 0 by grind)]
          exact mul_lt_mul_of_nonneg_of_pos (by aesop) (hG j)
            (mul_nonneg (by positivity) (by positivity)) (by positivity)
        · rw [← div_mul_cancel₀ ε (show F ≠ 0 by grind), mul_comm]
          exact mul_lt_mul_of_nonneg_of_pos (by aesop) (hF i)
            (mul_nonneg (by positivity) (by positivity)) (by positivity)
  have Final : ‖∑ p ∈ Finset.antidiagonal t, f p.1 * g p.2‖ * |C t| < ε := by
    obtain ⟨k, hk, leq⟩ := exists_norm_finset_sum_le (Finset.antidiagonal t) (fun a ↦ f a.1 * g a.2)
    calc
    _ ≤ ‖f k.1 * g k.2‖ * |C t| := by
      exact mul_le_mul_of_nonneg (leq) (le_refl _) (by positivity) (by positivity)
    _ < ε := by
      have : (Finset.antidiagonal t).Nonempty := by
        refine Finset.nonempty_def.mpr ?_
        use (t, 0)
        simp
      have : t = k.1 + k.2 := by
        specialize hk this
        simp only [Finset.mem_antidiagonal] at hk
        exact hk.symm
      exact hij k.1 k.2 this
  grind

-- golfed from an aristotle proof
private lemma mul_extracted {σ : Type*} (c : σ → ℝ) (a b : σ →₀ ℕ) :
    ∏ i ∈ (a + b).support, |c| i ^ (a + b) i =
    (∏ i ∈ a.support, |c| i ^ a i) * ∏ i ∈ b.support, |c| ↑i ^ b i := by
  rw [Finset.prod_subset (Finsupp.support_mono (self_le_add_left b a)),
    Finset.prod_subset (Finsupp.support_mono (self_le_add_right a b))]
  · simp only [Pi.abs_apply, Finsupp.coe_add, Pi.add_apply,pow_add, Finset.prod_mul_distrib]
  all_goals aesop

lemma mul {R : Type*} [NormedRing R] [IsUltrametricDist R] {σ : Type*} (c : σ → ℝ)
    {f g : MvPowerSeries σ R} (hf : IsRestricted c f) (hg : IsRestricted c g) :
    IsRestricted c (f * g) := by
  classical
  rw [isRestricted_iff_abs, IsRestricted] at *
  exact tendsto_antidiagonal (by simp [Finsupp.prod_add_index', pow_add]) hf hg
