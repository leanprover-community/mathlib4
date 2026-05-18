/-
Copyright (c) 2025 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Algebra.Order.Group.PartialSups
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Data.Real.StarOrdered
public import Mathlib.Dynamics.BirkhoffSum.Average

/-!
# Maximal ergodic theorem.

We prove the maximal ergodic theorem for a measure-preserving map `f` and an integrable function
`g`. The maximal ergodic operator `birkhoffAverageSup f g x` is defined as the supremum of the
Birkhoff averages of `g` over all `n`. Moreover, we show some results about the auxiliary definition
`birkhoffMax f g n`, defined as the maximum of the Birkhoff sums ranging between `0` and `n`.

## Main results

* `distribution_birkhoffAverageSup_le_integral`: the cumulative distribution function of
  `birkhoffAverageSup` at `a` is less than or equal to the integral of `g` on the set where
  `a < birkhoffAverageSup f g x`.
* `iSup_distribution_birkhoffAverageSup_le_norm`: the operator `birkhoffAverageSup` satisfies a
   weak-type inequality.
-/

open MeasureTheory Measure MeasurableSpace Filter Topology

variable {α M : Type*} {f : α → α} {g : α → M} {n : ℕ} {x : α}

@[expose]
public section BirkhoffMax

/-- The maximum of `birkhoffSum f g i` for `i` ranging from `0` to `n`. -/
def birkhoffMax [AddCommMonoid M] [SemilatticeSup M]
    (f : α → α) (g : α → M) : ℕ →o (α → M) :=
  partialSups (birkhoffSum f g)

lemma birkhoffMax_nonneg [AddCommMonoid M] [SemilatticeSup M] : 0 ≤ birkhoffMax f g n x :=
  (birkhoffMax ..).mono n.zero_le x

variable [AddCommGroup M]

variable [SemilatticeSup M] [IsOrderedAddMonoid M] in
lemma birkhoffMax_succ :
    birkhoffMax f g (n + 1) x = 0 ⊔ (g x + birkhoffMax f g n (f x)) := by
  have : birkhoffSum f g ∘ (· + 1) = (g + birkhoffSum f g · ∘ f) :=
    funext₂ <| fun k x ↦ birkhoffSum_succ' ..
  rw [birkhoffMax, partialSups_add_one', this, partialSups_const_add]
  simp [partialSups]

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
  · apply le_of_eq_of_le (birkhoffMax_succ' hpos)
    apply add_le_add_right
    apply birkhoffMax f g |>.mono (by omega)

end BirkhoffMax

variable {g : α → ℝ}

-- TODO: move elsewhere
@[fun_prop]
public lemma birkhoffSum_measurable [MeasurableSpace α] (hf : Measurable f) (hg : Measurable g) :
    Measurable (birkhoffSum f g n) := by
  apply Finset.measurable_sum
  measurability

@[fun_prop]
public lemma birkhoffMax_measurable [MeasurableSpace α] (hf : Measurable f) (hg : Measurable g) :
    Measurable (birkhoffMax f g n) := by
  unfold birkhoffMax
  induction n <;> measurability

section MeasurePreserving

variable [MeasurableSpace α] (μ : Measure α := by volume_tac) (hf : MeasurePreserving f μ μ)
  (hg : Integrable g μ)

include hf

-- todo: move elsewhere
@[fun_prop]
lemma birkhoffSum_aestronglyMeasurable (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (birkhoffSum f g n) μ := by
  apply Finset.aestronglyMeasurable_fun_sum
  exact fun i _ ↦ hg.comp_measurePreserving (hf.iterate i)

@[fun_prop]
lemma birkhoffMax_aestronglyMeasurable (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (birkhoffMax f g n) μ := by
  unfold birkhoffMax
  induction n <;> measurability

include hg

-- todo: move elsewhere
lemma birkhoffSum_integrable : Integrable (birkhoffSum f g n) μ :=
  integrable_finsetSum _ fun _ _ ↦ (hf.iterate _).integrable_comp_of_integrable hg

lemma birkhoffMax_integrable : Integrable (birkhoffMax f g n) μ := by
  unfold birkhoffMax
  induction n with
  | zero => exact integrable_zero ..
  | succ n hn => simpa using Integrable.sup hn (birkhoffSum_integrable μ hf hg)

lemma birkhoffMax_integral_le :
    ∫ x, birkhoffMax f g n x ∂μ ≤
    ∫ x in (birkhoffMax f g n).support, g x ∂μ +
    ∫ x in (birkhoffMax f g n).support, birkhoffMax f g n (f x) ∂μ := by
  have := hf.integrable_comp_of_integrable (birkhoffMax_integrable μ hf hg (n := n))
  rw [←integral_add hg.restrict, ←setIntegral_support]
  · apply setIntegral_mono_on₀
    · exact (birkhoffMax_integrable μ hf hg).restrict
    · exact .add hg.restrict this.restrict
    · exact AEStronglyMeasurable.nullMeasurableSet_support (by measurability)
    · intro x hx
      rw [Function.mem_support] at hx
      apply birkhoffMax_le_self_add_comp
      exact birkhoffMax_nonneg |>.lt_of_ne hx.symm
  · exact this.restrict

lemma setIntegral_birkhoffMax_support_nonneg :
    0 ≤ ∫ x in (birkhoffMax f g n).support, g x ∂μ := by
  have hg₁ : AEStronglyMeasurable (birkhoffMax f g n) μ := by measurability
  have hg₂ : Integrable (birkhoffMax f g n) μ := birkhoffMax_integrable μ hf hg
  have hg₃ : Integrable (birkhoffMax f g n ∘ f) μ := hf.integrable_comp_of_integrable hg₂
  calc
    0 ≤ ∫ x in (birkhoffMax f g n).supportᶜ, birkhoffMax f g n (f x) ∂μ := by
      exact integral_nonneg (fun x ↦ birkhoffMax_nonneg)
    _ = ∫ x, birkhoffMax f g n (f x) ∂μ -
        ∫ x in (birkhoffMax f g n).support, birkhoffMax f g n (f x) ∂μ := by
      exact setIntegral_compl₀ hg₁.nullMeasurableSet_support hg₃
    _ = ∫ x, birkhoffMax f g n x ∂μ -
        ∫ x in (birkhoffMax f g n).support, birkhoffMax f g n (f x) ∂μ := by
      rw [←integral_map hf.aemeasurable (hf.map_eq.symm ▸ hg₁), hf.map_eq]
    _ ≤ ∫ x in (birkhoffMax f g n).support, g x ∂μ := by
      grw [birkhoffMax_integral_le μ hf hg]
      grind

end MeasurePreserving

noncomputable section BirkhoffSup

def birkhoffSumSup (f : α → α) (g : α → ℝ) (x : α) : EReal :=
  ⨆ n, ↑(birkhoffSum f g n x)

lemma birkhoffSumSup_eq_iSup_birkhoffMax :
    birkhoffSumSup f g x = ⨆ n, ↑(birkhoffMax f g n x) := by
  simp [birkhoffMax, Pi.partialSups_apply, ←map_partialSups' EReal.coe_max, birkhoffSumSup]

@[expose]
public def birkhoffAverageSup (f : α → α) (g : α → ℝ) (x : α) : EReal :=
  ⨆ n, ↑(birkhoffAverage ℝ f g n x)

end BirkhoffSup

lemma setOf_birkhoffSumSup_pos_eq_iUnion_birkhoffMax_support :
    {x | 0 < birkhoffSumSup f g x} = ⋃ n : ℕ, (birkhoffMax f g n).support := by
  simp_rw [birkhoffSumSup_eq_iSup_birkhoffMax, lt_iSup_iff, Set.setOf_exists, EReal.coe_pos,
    birkhoffMax_nonneg.lt_iff_ne, Function.support, ne_comm]

theorem lt_birkhoffAverage_iff_lt_birkhoffSum {a : ℝ} (hn : 0 < n) :
    a < birkhoffAverage ℝ f g n x ↔ 0 < birkhoffSum f (g - fun _ ↦ a) n x := by
  nth_rw 2 [←smul_lt_smul_iff_of_pos_left (a := (↑n : ℝ)⁻¹) (by positivity)]
  rw [smul_zero, ←birkhoffAverage, birkhoffAverage_sub]
  simp only [Pi.sub_apply, sub_pos]
  nth_rw 2 [birkhoffAverage_of_comp_eq _ rfl (by positivity)]

theorem lt_birkhoffAverageSup_iff_lt_birkhoffSumSup {a : ℝ} (ha : 0 < a) :
    a < birkhoffAverageSup f g x ↔ 0 < birkhoffSumSup f (g - fun _ ↦ a) x := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have ⟨n, hn⟩ := lt_iSup_iff.mp h
    apply lt_iSup_iff.mpr (.intro n _)
    norm_cast at *
    rwa [←lt_birkhoffAverage_iff_lt_birkhoffSum]
    by_contra!
    apply Nat.eq_zero_of_le_zero at this
    simp only [this, birkhoffAverage_zero'] at hn
    exact lt_asymm hn ha
  · have ⟨n, hn⟩ := lt_iSup_iff.mp h
    apply lt_iSup_iff.mpr (.intro n _)
    norm_cast at *
    rwa [lt_birkhoffAverage_iff_lt_birkhoffSum]
    by_contra!
    apply Nat.eq_zero_of_le_zero at this
    simp only [this, birkhoffSum_zero'] at hn
    exact lt_irrefl 0 hn

section MeasurePreserving

variable {f : α → α} [MeasurableSpace α] (μ : Measure α := by volume_tac)
  (hf : MeasurePreserving f μ μ)

include hf

section Real

variable {g : α → ℝ} (hg : Integrable g μ)

include hg

lemma tendsto_setIntegral_birkhoffMax_support :
    Tendsto (fun n ↦ ∫ x in (birkhoffMax f g n).support, g x ∂μ) atTop
    (𝓝 <| ∫ x in {x | 0 < birkhoffSumSup f g x}, g x ∂ μ) := by
  rw [setOf_birkhoffSumSup_pos_eq_iUnion_birkhoffMax_support]
  apply tendsto_setIntegral_of_monotone₀ _ _ hg.integrableOn
  · intros
    exact AEStronglyMeasurable.nullMeasurableSet_support (by measurability)
  · intro i j hij x
    grind [birkhoffMax_nonneg, (birkhoffMax f g).mono hij x, Function.mem_support]

theorem setIntegral_birkhoffSumSup_nonneg :
    0 ≤ ∫ x in {x | 0 < birkhoffSumSup f g x}, g x ∂μ := by
  apply ge_of_tendsto' (tendsto_setIntegral_birkhoffMax_support μ hf hg)
  intro n
  exact setIntegral_birkhoffMax_support_nonneg μ hf hg

variable [IsFiniteMeasure μ]

/-- The cumulative distribution function of `birkhoffAverageSup` at `a` is less than or equal to the
integral of `g` on the set where `a < birkhoffAverageSup f g x`. -/
public theorem distribution_birkhoffAverageSup_le_integral (a : ℝ) (ha : 0 < a) :
    a * μ.real {x | a < birkhoffAverageSup f g x}
    ≤ ∫ x in {x | a < birkhoffAverageSup f g x}, g x ∂μ := by
  have p₁ := Integrable.sub hg (integrable_const a)
  calc
    _ = ∫ x in {x | 0 < birkhoffSumSup f (g - fun _ ↦ a) x}, a ∂μ := by
      simp [lt_birkhoffAverageSup_iff_lt_birkhoffSumSup ha]
      ring
    _ ≤ ∫ x in {x | 0 < birkhoffSumSup f (g - fun _ ↦ a) x}, a ∂μ +
        ∫ x in {x | 0 < birkhoffSumSup f (g - fun _ ↦ a) x}, g x - a ∂μ := by
      exact le_add_of_nonneg_right (setIntegral_birkhoffSumSup_nonneg μ hf p₁)
    _ = ∫ x in {x | a < birkhoffAverageSup f g x}, g x ∂μ := by
      rw [←integral_add (integrable_const a).restrict]
      · simp [lt_birkhoffAverageSup_iff_lt_birkhoffSumSup ha]
      · exact p₁.restrict

end Real

section NormedAddCommGroup

variable {E : Type*} [NormedAddCommGroup E] {g : α → E} (hg : Integrable g μ) [IsFiniteMeasure μ]

include hg

/-- Maximal ergodic theorem: the operator `birkhoffAverageSup` satisfies a weak-type inequality. -/
public theorem iSup_distribution_birkhoffAverageSup_le_norm :
    ⨆ a : ℝ, a * μ.real {x | a < birkhoffAverageSup f (‖g ·‖) x} ≤ ∫ x, ‖g x‖ ∂μ := by
  refine ciSup_le fun a ↦ ?_
  by_cases! ha : 0 < a; swap
  · apply mul_nonpos_of_nonpos_of_nonneg ha measureReal_nonneg |>.trans
    exact integral_nonneg (fun _ ↦ norm_nonneg _)
  calc
    _ ≤ ∫ x in {x | a < birkhoffAverageSup f (‖g ·‖) x}, ‖g x‖ ∂μ := by
      exact distribution_birkhoffAverageSup_le_integral μ hf hg.norm a ha
    _ ≤ ∫ x, ‖g x‖ ∂μ := by
      exact setIntegral_le_integral hg.norm (ae_of_all _ (norm_nonneg <| g ·))

end NormedAddCommGroup

end MeasurePreserving
