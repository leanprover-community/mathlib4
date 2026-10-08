/-
Copyright (c) 2025 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Dynamics.BirkhoffSum.Average
public import Mathlib.Dynamics.BirkhoffSum.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Algebra.Order.Group.PartialSups
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Maximal ergodic theorem.

We prove the maximal ergodic theorem for a measure-preserving map `f` and an integrable function
`g`.

## Main definitions

* `birkhoffMax f g n`: the maximum of `birkhoffSum f g i` for `i` ranging from `0` to `n`.
* `birkhoffSumSup f g`: the supremum of the Birkhoff sums of `g` along orbits of `f`.
* `birkhoffAverageSup f g`: the maximal ergodic operator, defined as the supremum of the
  Birkhoff averages of `g` along orbits of `f`.

## Main results

* `setIntegral_birkhoffSumSup_nonneg`: for a measure-preserving `f`, the integral of an integrable
  `g` over the set where `birkhoffSumSup f g` is positive is non-negative.
* `const_mul_distribution_birkhoffAverageSup_le_integral`: the cumulative distribution function of
  `birkhoffAverageSup` at `a` is less than or equal to the integral of `g` on the set where
  `a < birkhoffAverageSup f g x`.
* `const_mul_distribution_birkhoffAverageSup_le_norm`: the operator `birkhoffAverageSup` satisfies a
   weak-type inequality.
-/

open MeasureTheory Measure MeasurableSpace Filter Topology

variable {α M : Type*} {f : α → α} {g : α → M} {m n : ℕ} {x : α}

@[expose]
public section BirkhoffMax

/-- The maximum of the Birkhoff sums of `g` along orbits of `f` from `0` to `n`. -/
def birkhoffMax [AddCommMonoid M] [SemilatticeSup M]
    (f : α → α) (g : α → M) : ℕ →o (α → M) :=
  partialSups (birkhoffSum f g)

lemma birkhoffMax_mono [AddCommMonoid M] [SemilatticeSup M] : Monotone (birkhoffMax f g) :=
  (birkhoffMax ..).mono

@[gcongr]
lemma birkhoffMax_apply_monotone [AddCommMonoid M] [SemilatticeSup M] (h : m ≤ n) :
    birkhoffMax f g m x ≤ birkhoffMax f g n x :=
  (birkhoffMax ..).mono h _

lemma birkhoffMax_nonneg [AddCommMonoid M] [SemilatticeSup M] : 0 ≤ birkhoffMax f g n x :=
  (birkhoffMax ..).mono n.zero_le x

variable [AddCommGroup M]

variable [SemilatticeSup M] [IsOrderedAddMonoid M] in
lemma birkhoffMax_succ :
    birkhoffMax f g (n + 1) x = 0 ⊔ (g x + birkhoffMax f g n (f x)) := by
  have : birkhoffSum f g ∘ (· + 1) = (g + birkhoffSum f g · ∘ f) :=
    funext <| fun k ↦ birkhoffSum_succ' ..
  rw [birkhoffMax, partialSups_add_one', this, partialSups_const_add]
  simp [Pi.partialSups_apply]

variable [LinearOrder M] [IsOrderedAddMonoid M]

lemma birkhoffMax_succ' (hpos : 0 < birkhoffMax f g (n + 1) x) :
    birkhoffMax f g (n + 1) x = g x + birkhoffMax f g n (f x) := by
  rw [birkhoffMax_succ, birkhoffMax, lt_sup_iff] at hpos
  rcases hpos with h | h
  · grind
  · rw [birkhoffMax_succ, birkhoffMax, sup_of_le_right h.le]

lemma birkhoffMax_le_self_add_comp (hpos : 0 < birkhoffMax f g n x) :
    birkhoffMax f g n x ≤ g x + birkhoffMax f g n (f x) := by
  rcases n with _ | n
  · simp [birkhoffMax] at *
  · rw [birkhoffMax_succ' hpos]
    gcongr
    simp

end BirkhoffMax

variable {g : α → ℝ}

@[fun_prop]
public lemma measurable_birkhoffMax [MeasurableSpace α] (hf : Measurable f) (hg : Measurable g) :
    Measurable (birkhoffMax f g n) := by
  unfold birkhoffMax
  induction n <;> measurability

section MeasurePreserving

attribute [local fun_prop] MeasurePreserving.integrable_comp_of_integrable

variable [MeasurableSpace α] (μ : Measure α := by volume_tac)

@[fun_prop]
public lemma aestronglyMeasurable_birkhoffMax
    (hf : MeasurePreserving f μ μ) (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (birkhoffMax f g n) μ := by
  unfold birkhoffMax
  induction n <;> measurability

@[fun_prop]
public lemma integrable_birkhoffMax (hf : MeasurePreserving f μ μ) (hg : Integrable g μ) :
    Integrable (birkhoffMax f g n) μ := by
  unfold birkhoffMax
  induction n with
  | zero => simp
  | succ n hn => simpa using hn.sup (by fun_prop)

lemma birkhoffMax_integral_le (hf : MeasurePreserving f μ μ) (hg : Integrable g μ) :
    ∫ x, birkhoffMax f g n x ∂μ ≤
    ∫ x in (birkhoffMax f g n).support, g x ∂μ +
    ∫ x in (birkhoffMax f g n).support, birkhoffMax f g n (f x) ∂μ := by
  rw [← integral_add hg.restrict (.restrict (by fun_prop)), ← setIntegral_support]
  apply setIntegral_mono_on₀
  · exact Integrable.integrableOn (by fun_prop)
  · exact Integrable.integrableOn (by fun_prop)
  · exact AEStronglyMeasurable.nullMeasurableSet_support (by fun_prop)
  · grind [birkhoffMax_le_self_add_comp, birkhoffMax_nonneg, Function.mem_support]

lemma setIntegral_birkhoffMax_support_nonneg (hf : MeasurePreserving f μ μ) (hg : Integrable g μ) :
    0 ≤ ∫ x in (birkhoffMax f g n).support, g x ∂μ := by
  have hg₁ : AEStronglyMeasurable (birkhoffMax f g n) μ := by fun_prop
  calc
    0 ≤ ∫ x in (birkhoffMax f g n).supportᶜ, birkhoffMax f g n (f x) ∂μ :=
      integral_nonneg (fun x ↦ birkhoffMax_nonneg)
    _ = ∫ x, birkhoffMax f g n (f x) ∂μ -
        ∫ x in (birkhoffMax f g n).support, birkhoffMax f g n (f x) ∂μ :=
      setIntegral_compl₀ hg₁.nullMeasurableSet_support (by fun_prop)
    _ = ∫ x, birkhoffMax f g n x ∂μ -
        ∫ x in (birkhoffMax f g n).support, birkhoffMax f g n (f x) ∂μ := by
      rw [← integral_map hf.aemeasurable (hf.map_eq.symm ▸ hg₁), hf.map_eq]
    _ ≤ ∫ x in (birkhoffMax f g n).support, g x ∂μ := by
      grind [birkhoffMax_integral_le]

end MeasurePreserving

noncomputable section BirkhoffSup

/-- The supremum of the Birkhoff sums of `g` along orbits of `f`. -/
@[expose]
public def birkhoffSumSup (f : α → α) (g : α → ℝ) (x : α) : EReal :=
  ⨆ n, ↑(birkhoffSum f g n x)

@[fun_prop]
public lemma measurable_birkhoffSumSup [MeasurableSpace α] (hf : Measurable f) (hg : Measurable g) :
    Measurable (birkhoffSumSup f g) := by fun_prop [birkhoffSumSup]

lemma birkhoffSumSup_eq_iSup_birkhoffMax :
    birkhoffSumSup f g x = ⨆ n, ↑(birkhoffMax f g n x) := by
  simp [birkhoffMax, birkhoffSumSup, Pi.partialSups_apply, ← EReal.coe_orderEmbedding,
    ← map_partialSups]

/-- The maximal ergodic operator: the supremum of the Birkhoff averages of `g`. -/
@[expose]
public def birkhoffAverageSup (f : α → α) (g : α → ℝ) (x : α) : EReal :=
  ⨆ n, ↑(birkhoffAverage ℝ f g n x)

@[fun_prop]
lemma measurable_birkhoffAverageSup [MeasurableSpace α] (hf : Measurable f) (hg : Measurable g) :
    Measurable (birkhoffAverageSup f g) := by fun_prop [birkhoffAverageSup]

end BirkhoffSup

lemma setOf_birkhoffSumSup_pos_eq_iUnion_birkhoffMax_support :
    {x | 0 < birkhoffSumSup f g x} = ⋃ n : ℕ, (birkhoffMax f g n).support := by
  simp_rw [birkhoffSumSup_eq_iSup_birkhoffMax, lt_iSup_iff, Set.ofPred_exists, EReal.coe_pos,
    birkhoffMax_nonneg.lt_iff_ne, Function.support, ne_comm]

theorem lt_birkhoffAverage_iff_lt_birkhoffSum {a : ℝ} (ha : 0 ≤ a) :
    a < birkhoffAverage ℝ f g n x ↔ 0 < birkhoffSum f (g - fun _ ↦ a) n x := by
  by_cases! hn : n = 0
  · simpa [hn]
  calc
    _ ↔ birkhoffAverage ℝ f (fun x ↦ a) n x < birkhoffAverage ℝ f g n x := by
      rw [birkhoffAverage_const ℝ]
    _ ↔ _ := by
      simp [birkhoffAverage, birkhoffSum_sub, field]

theorem lt_birkhoffAverageSup_iff_lt_birkhoffSumSup {a : ℝ} (ha : 0 ≤ a) :
    a < birkhoffAverageSup f g x ↔ 0 < birkhoffSumSup f (g - fun _ ↦ a) x := by
  simp [birkhoffAverageSup, birkhoffSumSup, lt_iSup_iff, lt_birkhoffAverage_iff_lt_birkhoffSum ha]

section MeasurePreserving

variable [MeasurableSpace α] (μ : Measure α)

section Real

variable {g : α → ℝ}

lemma tendsto_setIntegral_birkhoffMax_support
    (hf : MeasurePreserving f μ μ) (hg : Integrable g μ) :
    Tendsto (fun n ↦ ∫ x in (birkhoffMax f g n).support, g x ∂μ) atTop
    (𝓝 <| ∫ x in {x | 0 < birkhoffSumSup f g x}, g x ∂ μ) := by
  rw [setOf_birkhoffSumSup_pos_eq_iUnion_birkhoffMax_support]
  apply tendsto_setIntegral_of_monotone₀ _ _ hg.integrableOn
  · intros
    exact AEStronglyMeasurable.nullMeasurableSet_support (by measurability)
  · intro i j hij x
    grind [birkhoffMax_nonneg, (birkhoffMax f g).mono hij x, Function.mem_support]

/-- The integral of `g` over the set where `birkhoffSumSup f g` is positive is non-negative. -/
public theorem setIntegral_birkhoffSumSup_nonneg
    (hf : MeasurePreserving f μ μ) (hg : Integrable g μ) :
    0 ≤ ∫ x in {x | 0 < birkhoffSumSup f g x}, g x ∂μ := by
  apply ge_of_tendsto' (tendsto_setIntegral_birkhoffMax_support μ hf hg)
  grind [setIntegral_birkhoffMax_support_nonneg]

variable [IsFiniteMeasure μ]

/-- The cumulative distribution function of `birkhoffAverageSup` at `a` is less than or equal to the
integral of `g` on the set where `a < birkhoffAverageSup f g x`. -/
public theorem const_mul_distribution_birkhoffAverageSup_le_integral
    (hf : MeasurePreserving f μ μ) (hg : Integrable g μ) (a : ℝ) (ha : 0 ≤ a) :
    a * μ.real {x | a < birkhoffAverageSup f g x}
    ≤ ∫ x in {x | a < birkhoffAverageSup f g x}, g x ∂μ := by
  calc
    _ = ∫ x in {x | 0 < birkhoffSumSup f (g - fun _ ↦ a) x}, a ∂μ := by
      simp [lt_birkhoffAverageSup_iff_lt_birkhoffSumSup ha, field]
    _ ≤ ∫ x in {x | 0 < birkhoffSumSup f (g - fun _ ↦ a) x}, a ∂μ +
        ∫ x in {x | 0 < birkhoffSumSup f (g - fun _ ↦ a) x}, g x - a ∂μ :=
      le_add_of_nonneg_right (setIntegral_birkhoffSumSup_nonneg μ hf (by fun_prop))
    _ = ∫ x in {x | a < birkhoffAverageSup f g x}, g x ∂μ := by
      rw [← integral_add (by fun_prop) (by fun_prop)]
      simp [lt_birkhoffAverageSup_iff_lt_birkhoffSumSup ha]

end Real

section NormedAddCommGroup

variable [NormedAddCommGroup M] {g : α → M} [IsFiniteMeasure μ]

/-- Maximal ergodic theorem: the operator `birkhoffAverageSup` satisfies a weak-type inequality. -/
public theorem const_mul_distribution_birkhoffAverageSup_le_norm
    (hf : MeasurePreserving f μ μ) (hg : Integrable g μ) (a : ℝ) :
    a * μ.real {x | a < birkhoffAverageSup f (‖g ·‖) x} ≤ ∫ x, ‖g x‖ ∂μ := by
  by_cases! ha : 0 ≤ a; swap
  · calc
      _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha.le (by positivity)
      _ ≤ _ := by positivity
  calc
    _ ≤ ∫ x in {x | a < birkhoffAverageSup f (‖g ·‖) x}, ‖g x‖ ∂μ :=
      const_mul_distribution_birkhoffAverageSup_le_integral μ hf hg.norm a ha
    _ ≤ ∫ x, ‖g x‖ ∂μ :=
      setIntegral_le_integral hg.norm (ae_of_all _ (norm_nonneg <| g ·))

end NormedAddCommGroup

end MeasurePreserving
