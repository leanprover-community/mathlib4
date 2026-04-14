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
public import Mathlib.Algebra.Order.Antidiag.Prod

/-!
# Multivariate restricted power series

`IsRestricted` : We say a multivariate power series over a normed ring `R` is restricted for a
tuple `c` if `‖coeff t f‖ * ∏ i ∈ t.support, c i ^ t i → 0` under the cofinite filter.

-/

@[expose] public section

namespace MvPowerSeries

open Filter
open scoped Topology Pointwise

variable {R : Type*} [NormedRing R] {σ : Type*}

/-- A multivariate powe0r series over a normed ring `R` is restricted for a
  tuple `c` if `‖coeff t f‖ * ∏ i ∈ t.support, c i ^ t i → 0` under the cofinite filter. -/
def IsRestricted (c : σ → ℝ) (f : MvPowerSeries σ R) :=
  Tendsto (fun (t : σ →₀ ℕ) ↦ ‖coeff t f‖ * t.prod (c · ^ ·)) cofinite (𝓝 0)

@[simp]
lemma isRestricted_abs_iff (c : σ → ℝ) (f : MvPowerSeries σ R) :
    IsRestricted |c| f ↔ IsRestricted c f := by
  simp [IsRestricted, NormedAddGroup.tendsto_nhds_zero, Finsupp.prod]

lemma isRestricted_zero (c : σ → ℝ) : IsRestricted c (0 : MvPowerSeries σ R) := by
  simpa [IsRestricted] using tendsto_const_nhds

lemma isRestricted_monomial (c : σ → ℝ) (n : σ →₀ ℕ) (a : R) :
    IsRestricted c (monomial n a) := by
  classical
  refine tendsto_nhds_of_eventually_eq (Set.Subsingleton.finite ?_)
  aesop (add simp [Set.Subsingleton, coeff_monomial])

lemma isRestricted_one (c : σ → ℝ) : IsRestricted c (1 : MvPowerSeries σ R) :=
  isRestricted_monomial c 0 1

lemma isRestricted_C (c : σ → ℝ) (a : R) : IsRestricted c (C a) := by
  simpa [monomial_zero_eq_C_apply] using isRestricted_monomial c 0 a

lemma isRestricted.add (c : σ → ℝ) {f g : MvPowerSeries σ R} (hf : IsRestricted c f)
    (hg : IsRestricted c g) : IsRestricted c (f + g) := by
  rw [← isRestricted_abs_iff, IsRestricted] at *
  refine tendsto_const_nhds.squeeze (add_zero (0 : ℝ) ▸ hf.add hg) (fun n ↦ ?_) fun n ↦ ?_
  · dsimp [Finsupp.prod]; positivity -- TODO: add positivity extension for Finsupp.prod
  rw [← add_mul]
  exact mul_le_mul_of_nonneg_right (norm_add_le ..) (by dsimp [Finsupp.prod]; positivity)

lemma isRestricted.neg (c : σ → ℝ) {f : MvPowerSeries σ R} (hf : IsRestricted c f) :
    IsRestricted c (-f) := by
  rw [← isRestricted_abs_iff, IsRestricted] at *
  simpa [IsRestricted] using hf

open IsUltrametricDist

/- TODO: Find a home for this lemma. -/
lemma tendsto_sup'_antidiagonal_cofinite
    {M R : Type*} [AddMonoid M] [Finset.HasAntidiagonal M] {f : M × M → R}
    [LinearOrder R] {F : Filter R} (hf : Tendsto f cofinite F) :
    Tendsto (fun a ↦ (Finset.antidiagonal a).sup' (Finset.nonempty_antidiagonal _) f)
      cofinite F := by
  intro U hU
  refine ((((hf hU).image Prod.fst)).add ((hf hU).image Prod.snd)).subset ?_
  simp only [Set.subset_def, Set.mem_compl_iff, Set.mem_preimage]
  intro x hx
  obtain ⟨i, hi, e⟩ := Finset.exists_mem_eq_sup' (Finset.nonempty_antidiagonal x) f
  obtain rfl : i.1 + i.2 = x := by simpa using hi
  exact Set.add_mem_add (by simpa using ⟨i.2, e ▸ hx⟩) (by simpa using ⟨i.1, e ▸ hx⟩)

lemma tendsto_antidiagonal {M S : Type*} [AddMonoid M] [Finset.HasAntidiagonal M] [NormedRing S]
    [IsUltrametricDist S] {C : M → ℝ} (hC : ∀ a b, C (a + b) = C a * C b) {f g : M → S}
    (hf : Tendsto (fun i ↦ ‖f i‖ * C i) cofinite (𝓝 0))
    (hg : Tendsto (fun i ↦ ‖g i‖ * C i) cofinite (𝓝 0)) :
    Tendsto (fun a ↦ ‖∑ p ∈ Finset.antidiagonal a, (f p.1 * g p.2)‖ * C a) cofinite (𝓝 0) := by
  wlog hC' : 0 ≤ C generalizing C
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa using this (C := |C|) (by simp [hC]) (by simpa using hf.norm)
      (by simpa using hg.norm) (fun _ => by simp)
  refine .squeeze tendsto_const_nhds
    (tendsto_sup'_antidiagonal_cofinite (tendsto_mul_cofinite_nhds_zero hf hg))
    (fun x => by simpa using (mul_nonneg (by simp) (hC' x))) fun a ↦ ?_
  have : 0 ≤ C a := hC' a
  grw [(Finset.nonempty_antidiagonal _).norm_sum_le_sup'_norm, Finset.sup'_mul₀ this]
  refine Finset.sup'_mono_fun fun x hx ↦ ?_
  grw [mul_mul_mul_comm, ← hC, Finset.mem_antidiagonal.mp hx, ← norm_mul_le]

lemma isRestricted.mul [IsUltrametricDist R] (c : σ → ℝ) {f g : MvPowerSeries σ R}
    (hf : IsRestricted c f) (hg : IsRestricted c g) : IsRestricted c (f * g) := by
  classical
  rw [← isRestricted_abs_iff, IsRestricted] at *
  exact tendsto_antidiagonal (by simp [Finsupp.prod_add_index', pow_add]) hf hg

/-- Additive subgroup structure on `MvPowerSeries σ R`. -/
instance isAddSubgroup : (σ → ℝ) → AddSubgroup (MvPowerSeries σ R) :=
  fun c => {carrier := IsRestricted c
            zero_mem' := isRestricted_zero c
            add_mem' := isRestricted.add c
            neg_mem' := isRestricted.neg c}

variable [IsUltrametricDist R]

/-- Ring structure on `MvPowerSeries σ R`. -/
instance isSubring :  (σ → ℝ) → Subring (MvPowerSeries σ R) :=
  fun c => {__ := isAddSubgroup c
            one_mem' := isRestricted_one c
            mul_mem' := isRestricted.mul c}

variable (R) in
/-- The type of restricted `MvPowerSeries σ R`. -/
def Restricted (c : σ → ℝ) : Type _ := isSubring (R := R) c

/-- Ring structure on `Restricted R c`. -/
noncomputable
instance (c : σ → ℝ) : Ring (Restricted R c) :=
  Subring.toRing (isSubring c)

end MvPowerSeries
