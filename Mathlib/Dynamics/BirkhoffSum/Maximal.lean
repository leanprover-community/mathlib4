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
import Mathlib.Dynamics.BirkhoffSum.Average

/-!
# Maximal ergodic theorem.

We define the set `birkhoffAverageSupSet f g a` of points `x` where the supremum of
`birkhoffAverage ℝ f g n x` for varying `n` is greater than `a`. Then, we show its
measure multiplied by `a` is bounded above by the integral of `g` on this set. In particular,
for a positive `g`, this integral is bounded above by the `L1` norm of `g`, so for `g`
taking values in a `NormedAddCommGroup`, we get an inequality involving the norm.

## Main results

* `meas_birkhoffAverageSupSet_smul_const_le_integral`: the measure of `birkhoffAverageSupSet f g a`
   multiplied by `a` is bounded above by the integral of `g` on the same set.
* `meas_birkhoffAverageSupSet_smul_const_le_norm`: the measure of `birkhoffAverageSupSet f ‖g‖ a`
   multiplied by `a` is bounded above by the `L1` norm of `g`.
-/

variable {α : Type*} {f : α → α}

open MeasureTheory Measure MeasurableSpace Filter Topology

section BirkhoffMax

/-- The maximum of `birkhoffSum f g i` for `i` ranging from `0` to `n`. -/
def birkhoffMax (f : α → α) (g : α → ℝ) : ℕ →o (α → ℝ) :=
  partialSups (birkhoffSum f g)

lemma birkhoffMax_nonneg {g n} :
    0 ≤ birkhoffMax f g n := by
  apply (le_partialSups_of_le _ n.zero_le).trans'
  rfl

lemma birkhoffMax_succ {g n} :
    birkhoffMax f g (n + 1) = 0 ⊔ (g + birkhoffMax f g n ∘ f) := by
  have : birkhoffSum f g ∘ Nat.succ = fun k ↦ g + birkhoffSum f g k ∘ f := by
    funext
    exact birkhoffSum_succ' ..
  erw [partialSups_succ', this, partialSups_const_add, birkhoffSum_zero']
  funext
  simp [birkhoffMax, partialSups]

lemma birkhoffMax_succ' {g n x} (hpos : 0 < birkhoffMax f g (n + 1) x) :
    birkhoffMax f g (n + 1) x = g x + birkhoffMax f g n (f x) := by
  erw [birkhoffMax_succ, lt_sup_iff] at hpos
  cases hpos with
  | inl h => absurd h; exact lt_irrefl 0
  | inr h =>
    erw [birkhoffMax_succ, Pi.sup_apply, sup_of_le_right h.le]
    rfl

lemma birkhoffMax_comp_le_succ {g n} :
    birkhoffMax f g n ≤ birkhoffMax f g (n + 1) := by
  gcongr
  exact n.le_succ

lemma birkhoffMax_le_birkhoffMax {g n x} (hpos : 0 < birkhoffMax f g n x) :
    birkhoffMax f g n x ≤ g x + birkhoffMax f g n (f x) := by
  match n with
  | 0 => absurd hpos; exact lt_irrefl 0
  | n + 1 =>
    apply le_of_eq_of_le (birkhoffMax_succ' hpos)
    apply add_le_add_right
    exact birkhoffMax_comp_le_succ (f x)

lemma birkhoffMax_pos_of_mem_support {g n x}
    (hx : x ∈ (birkhoffMax f g n).support) : 0 < birkhoffMax f g n x := by
  apply lt_or_gt_of_ne at hx
  cases hx with
  | inl h =>
    absurd h; exact (birkhoffMax_nonneg x).not_gt
  | inr h => exact h

-- TODO: move elsewhere
@[measurability]
lemma birkhoffSum_measurable [MeasurableSpace α] {f : α → α} (hf : Measurable f) {g : α → ℝ}
    (hg : Measurable g) {n} : Measurable (birkhoffSum f g n) := by
  apply Finset.measurable_sum
  measurability

-- TODO: move elsewhere
@[measurability]
lemma birkhoffMax_measurable [MeasurableSpace α] (hf : Measurable f) {g : α → ℝ}
    (hg : Measurable g) {n} : Measurable (birkhoffMax f g n) := by
  unfold birkhoffMax
  induction n <;> measurability

section MeasurePreserving

variable {f : α → α} [MeasurableSpace α] (μ : Measure α := by volume_tac) {g : α → ℝ} {n}
  (hf : MeasurePreserving f μ μ) (hg : Integrable g μ)

include hf

-- todo: move elsewhere
@[measurability]
lemma birkhoffSum_aestronglyMeasurable (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (birkhoffSum f g n) μ := by
  apply Finset.aestronglyMeasurable_fun_sum
  exact fun i _ => hg.comp_measurePreserving (hf.iterate i)

-- todo: move elsewhere
@[measurability]
lemma birkhoffMax_aestronglyMeasurable (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (birkhoffMax f g n) μ := by
  unfold birkhoffMax
  induction n <;> measurability

include hg

-- todo: move elsewhere
lemma birkhoffSum_integrable : Integrable (birkhoffSum f g n) μ :=
  integrable_finset_sum _ fun _ _ ↦ (hf.iterate _).integrable_comp_of_integrable hg

-- todo: move elsewhere
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
      exact birkhoffMax_le_birkhoffMax (birkhoffMax_pos_of_mem_support hx)
  · exact this.restrict

lemma setIntegral_nonneg_on_birkhoffMax_support :
    0 ≤ ∫ x in (birkhoffMax f g n).support, g x ∂μ := by
  have hg₁ : AEStronglyMeasurable (birkhoffMax f g n) μ := by measurability
  have hg₂ : Integrable (birkhoffMax f g n) μ := birkhoffMax_integrable μ hf hg
  have hg₃ : Integrable (birkhoffMax f g n ∘ f) μ := hf.integrable_comp_of_integrable hg₂
  calc
    0 ≤ ∫ x in (birkhoffMax f g n).supportᶜ, birkhoffMax f g n (f x) ∂μ := by
      exact integral_nonneg (fun x  => birkhoffMax_nonneg (f x))
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

end BirkhoffMax

def birkhoffSupSet (f : α → α) (g : α → ℝ) : Set α :=
  {x | ∃ n : ℕ, 0 < birkhoffSum f g n x}

lemma birkhoffSupSet_eq_iSup_birkhoffMax_support {f : α → α} {g : α → ℝ} :
    birkhoffSupSet f g = ⋃ n : ℕ, (birkhoffMax f g n).support := by
  ext x
  simp only [birkhoffSupSet, Set.mem_setOf_eq, Set.mem_iUnion, Function.mem_support]
  constructor
  · refine fun ⟨n, hn⟩ => ⟨n, ?_⟩
    apply ne_of_gt (hn.trans_le _)
    exact le_partialSups (birkhoffSum f g) _ _
  · rintro ⟨n, hn⟩
    apply lt_or_gt_of_ne at hn
    cases hn with
    | inl h => absurd h; exact not_lt_of_ge (birkhoffMax_nonneg x)
    | inr h =>
      rw [birkhoffMax, Pi.partialSups_apply] at h
      rcases exists_partialSups_eq (birkhoffSum f g · x) n with ⟨m, _, hm₂⟩
      exact ⟨m, hm₂ ▸ h⟩

public def birkhoffAverageSupSet (f : α → α) (g : α → ℝ) (a : ℝ) : Set α :=
  {x | ∃ n : ℕ, a < birkhoffAverage ℝ f g n x}

theorem birkhoffAverage_iff_birkhoffSum {f : α → α} {x n g} {a : ℝ} (hn : 0 < n) :
    a < birkhoffAverage ℝ f g n x ↔ 0 < birkhoffSum f (g - fun _ ↦ a) n x := by
  nth_rw 2 [←smul_lt_smul_iff_of_pos_left (a := (↑n : ℝ)⁻¹) (by positivity)]
  rw [smul_zero, ←birkhoffAverage, birkhoffAverage_sub]
  simp only [Pi.sub_apply, sub_pos]
  nth_rw 2 [birkhoffAverage_of_comp_eq rfl hn.ne']

theorem birkhoffAverageSupSet_eq_birkhoffSupSet {f : α → α} {g a} (ha : 0 < a) :
    birkhoffAverageSupSet f g a = birkhoffSupSet f (g - fun _ ↦ a) := by
  unfold birkhoffAverageSupSet birkhoffSupSet
  have {n x} : a < birkhoffAverage ℝ f g n x ↔ 0 < birkhoffSum f (g - fun _ ↦ a) n x := by
    cases n with
    | zero =>
      refine ⟨fun h => ?_, fun h => ?_⟩
      · exfalso; rw [birkhoffAverage_zero] at h; exact lt_asymm ha h
      · exfalso; rw [birkhoffSum_zero] at h; exact lt_irrefl 0 h
    | succ n => exact birkhoffAverage_iff_birkhoffSum (by positivity)
  conv =>
    enter [1, 1, x, 1, n]
    rw [this]

section MeasurePreserving

variable {f : α → α} [MeasurableSpace α] (μ : Measure α := by volume_tac) {n}
  (hf : MeasurePreserving f μ μ)

include hf

section Real

variable {g : α → ℝ} (hg : Integrable g μ)

include hg

lemma tendsto_setIntegral_on_birkhoffMax_support_birkhoffSupSet :
    Tendsto (fun n ↦ ∫ x in (birkhoffMax f g n).support, g x ∂μ) atTop
            (𝓝 <| ∫ x in birkhoffSupSet f g, g x ∂ μ) := by
  rw [birkhoffSupSet_eq_iSup_birkhoffMax_support]
  apply tendsto_setIntegral_of_monotone₀ _ _ hg.integrableOn
  · intros
    exact AEStronglyMeasurable.nullMeasurableSet_support (by measurability)
  · intro i j hij x
    have : 0 ≤ birkhoffMax f g i x := birkhoffMax_nonneg x
    have := (birkhoffMax f g).mono hij x
    grind [Function.mem_support]
theorem setIntegral_nonneg_on_birkhoffSupSet :
    0 ≤ ∫ x in birkhoffSupSet f g, g x ∂μ := by
  apply ge_of_tendsto' (tendsto_setIntegral_on_birkhoffMax_support_birkhoffSupSet μ hf hg)
  intro n
  exact setIntegral_nonneg_on_birkhoffMax_support μ hf hg

variable [IsFiniteMeasure μ]

/-- **Maximal ergodic theorem**: The measure of the set where the supremum of the Birkhoff
averages of `g` is greater than `a`, multiplied by `a`, is bounded above by the integral of
`g` on this set. -/
public theorem meas_birkhoffAverageSupSet_smul_const_le_integral (a : ℝ) (ha : 0 < a) :
    μ.real (birkhoffAverageSupSet f g a) • a ≤ ∫ x in birkhoffAverageSupSet f g a, g x ∂μ := by
  have p₁ := Integrable.sub hg (integrable_const a)
  calc
    _ = ∫ x in birkhoffSupSet f (g - fun _ ↦ a), a ∂μ := by
      rw [setIntegral_const, birkhoffAverageSupSet_eq_birkhoffSupSet ha]
    _ ≤ ∫ x in birkhoffSupSet f (g - fun _ ↦ a), a ∂μ +
        ∫ x in birkhoffSupSet f (g - fun _ ↦ a), g x - a ∂μ := by
      exact le_add_of_nonneg_right (setIntegral_nonneg_on_birkhoffSupSet μ hf p₁)
    _ = ∫ x in birkhoffAverageSupSet f g a, g x ∂μ := by
      rw [← integral_add, birkhoffAverageSupSet_eq_birkhoffSupSet ha]
      · rcongr; grind
      · exact (integrable_const a).restrict
      · exact p₁.restrict

end Real

section NormedAddCommGroup

variable {E : Type*} [NormedAddCommGroup E] {g : α → E} (hg : Integrable g μ) [IsFiniteMeasure μ]

include hg

/-- **Maximal ergodic theorem** for group-valued functions: The measure of the set where
the supremum of the Birkhoff averages of `‖g‖` is greater than `a`, multiplied by `a`, is
bounded above by the norm of `g`. -/
public theorem meas_birkhoffAverageSupSet_smul_const_le_norm (a : ℝ) (ha : 0 < a) :
    μ.real (birkhoffAverageSupSet f (fun x ↦ ‖g x‖) a) • a ≤ ∫ x, ‖g x‖ ∂μ :=
  calc
    _ ≤ ∫ x in birkhoffAverageSupSet f (fun x ↦ ‖g x‖) a, ‖g x‖ ∂μ := by
      exact meas_birkhoffAverageSupSet_smul_const_le_integral μ hf hg.norm a ha
    _ ≤ ∫ x, ‖g x‖ ∂μ := by
      exact setIntegral_le_integral hg.norm (ae_of_all _ (norm_nonneg <| g ·))

end NormedAddCommGroup

end MeasurePreserving
