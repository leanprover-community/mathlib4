/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Rémy Degenne
-/
module

public import Mathlib.Probability.Process.Filtration
public import Mathlib.Topology.Instances.Discrete

/-!
# Adapted and progressively measurable processes

This file defines the related notions of a process `u` being `Adapted`, `StronglyAdapted`
or `StronglyProgressive` (progressively measurable) with respect to a filter `f`, and proves
some basic facts about them.

## Main definitions

* `MeasureTheory.Adapted`: a sequence of functions `u` is said to be adapted to a
  filtration `f` if at each point in time `i`, `u i` is `f i`-measurable
* `MeasureTheory.StronglyAdapted`: a sequence of functions `u` is said to be strongly adapted to a
  filtration `f` if at each point in time `i`, `u i` is `f i`-strongly measurable
* `MeasureTheory.IsStronglyProgressive`: a sequence of functions `u` is said to be strongly
  progressive with respect to a filtration `f` if at each point in time `i`, `u` restricted to
  `Set.Iic i × Ω` is strongly measurable with respect to the product `MeasurableSpace` structure
  where the σ-algebra used for `Ω` is `f i`.

## Main results

* `StronglyAdapted.isStronglyProgressive_of_continuous`: a continuous strongly adapted process is
  strongly progressive.

## Tags

adapted, progressively measurable

-/

@[expose] public section

open Filter Order TopologicalSpace

open scoped MeasureTheory NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω ι : Type*} {m : MeasurableSpace Ω} [Preorder ι] {f : Filtration ι m}

section Adapted

variable {β : ι → Type*} [∀ i, MeasurableSpace (β i)] {u v : (i : ι) → Ω → β i}

/-- A sequence of functions `u` is adapted to a filtration `f` if for all `i`,
`u i` is `f i`-measurable.

The definition known as `Adapted` before 2026-01-13 is now `StronglyAdapted`. -/
def Adapted (f : Filtration ι m) (u : (i : ι) → Ω → β i) : Prop :=
  ∀ i : ι, Measurable[f i] (u i)

namespace Adapted

@[to_additive]
protected theorem mul [∀ i, Mul (β i)] [∀ i, MeasurableMul₂ (β i)]
    (hu : Adapted f u) (hv : Adapted f v) :
    Adapted f (u * v) := fun i => (hu i).mul (hv i)

@[to_additive]
protected theorem div [∀ i, Div (β i)] [∀ i, MeasurableDiv₂ (β i)]
    (hu : Adapted f u) (hv : Adapted f v) :
    Adapted f (u / v) := fun i => (hu i).div (hv i)

@[to_additive]
protected theorem inv [∀ i, Group (β i)] [∀ i, MeasurableInv (β i)] (hu : Adapted f u) :
    Adapted f u⁻¹ := fun i => (hu i).inv

protected theorem smul {𝕂 : Type*} [MeasurableSpace 𝕂]
    [∀ i, SMul 𝕂 (β i)] [∀ i, MeasurableSMul 𝕂 (β i)] (c : 𝕂) (hu : Adapted f u) :
    Adapted f (c • u) := fun i => (hu i).const_smul c

protected theorem measurable {i : ι} (hf : Adapted f u) : Measurable[m] (u i) :=
  (hf i).mono (f.le i) (by rfl)

theorem measurable_le {i j : ι} (hf : Adapted f u) (hij : i ≤ j) : Measurable[f j] (u i) :=
  (hf i).mono (f.mono hij) (by rfl)

end Adapted

theorem adapted_const' (f : Filtration ι m) (x : (i : ι) → β i) : Adapted f fun i _ ↦ x i :=
  fun _ ↦ measurable_const

theorem adapted_const {β : Type*} [MeasurableSpace β] (f : Filtration ι m) (x : β) :
    Adapted f fun _ _ ↦ x := adapted_const' _ _

end Adapted

section StronglyAdapted

variable {β : ι → Type*} [∀ i, TopologicalSpace (β i)] {u v : (i : ι) → Ω → β i}

/-- A sequence of functions `u` is strongly adapted to a filtration `f` if for all `i`,
`u i` is `f i`-strongly measurable. -/
def StronglyAdapted (f : Filtration ι m) (u : (i : ι) → Ω → β i) : Prop :=
  ∀ i : ι, StronglyMeasurable[f i] (u i)

namespace StronglyAdapted

@[to_additive]
protected theorem mul [∀ i, Mul (β i)] [∀ i, ContinuousMul (β i)]
    (hu : StronglyAdapted f u) (hv : StronglyAdapted f v) :
    StronglyAdapted f (u * v) := fun i => (hu i).mul (hv i)

@[to_additive sub]
protected theorem div' [∀ i, Div (β i)] [∀ i, ContinuousDiv (β i)]
    (hu : StronglyAdapted f u) (hv : StronglyAdapted f v) :
    StronglyAdapted f (u / v) := fun i => (hu i).div' (hv i)

@[to_additive]
protected theorem inv [∀ i, Group (β i)] [∀ i, ContinuousInv (β i)] (hu : StronglyAdapted f u) :
    StronglyAdapted f u⁻¹ := fun i => (hu i).inv

protected theorem smul [∀ i, SMul ℝ (β i)] [∀ i, ContinuousConstSMul ℝ (β i)]
    (c : ℝ) (hu : StronglyAdapted f u) :
    StronglyAdapted f (c • u) := fun i => (hu i).const_smul c

/-- The norm of a strongly adapted process is strongly adapted. -/
protected lemma norm {β : ι → Type*} {u : (i : ι) → Ω → β i} [∀ i, SeminormedAddCommGroup (β i)]
    (hu : StronglyAdapted f u) :
    StronglyAdapted f (fun t ω ↦ ‖u t ω‖) := fun t ↦ (hu t).norm

protected theorem stronglyMeasurable {i : ι} (hf : StronglyAdapted f u) :
    StronglyMeasurable[m] (u i) := (hf i).mono (f.le i)

theorem stronglyMeasurable_le {i j : ι} (hf : StronglyAdapted f u) (hij : i ≤ j) :
    StronglyMeasurable[f j] (u i) := (hf i).mono (f.mono hij)

end StronglyAdapted

theorem StronglyAdapted.adapted [mΒ : ∀ i, MeasurableSpace (β i)] [∀ i, BorelSpace (β i)]
    [∀ i, PseudoMetrizableSpace (β i)] (hf : StronglyAdapted f u) :
    Adapted f u := fun _ ↦ (hf _).measurable

theorem Adapted.stronglyAdapted [mΒ : ∀ i, MeasurableSpace (β i)]
    [∀ i, OpensMeasurableSpace (β i)] [∀ i, PseudoMetrizableSpace (β i)]
    [∀ i, SecondCountableTopology (β i)] (hf : Adapted f u) :
    StronglyAdapted f u := fun _ ↦ (hf _).stronglyMeasurable

theorem stronglyAdapted_iff_adapted [mΒ : ∀ i, MeasurableSpace (β i)]
    [∀ i, BorelSpace (β i)] [∀ i, PseudoMetrizableSpace (β i)]
    [∀ i, SecondCountableTopology (β i)] :
    StronglyAdapted f u ↔ Adapted f u := ⟨fun h ↦ h.adapted, fun h ↦ h.stronglyAdapted⟩

theorem stronglyAdapted_const' (f : Filtration ι m) (x : (i : ι) → β i) :
    StronglyAdapted f fun i _ ↦ x i :=
  fun _ ↦ stronglyMeasurable_const

theorem stronglyAdapted_const {β : Type*} [TopologicalSpace β] (f : Filtration ι m) (x : β) :
    StronglyAdapted f fun _ _ ↦ x :=
  stronglyAdapted_const' _ _

variable (β) in
theorem stronglyAdapted_zero' [∀ i, Zero (β i)] (f : Filtration ι m) :
    StronglyAdapted f (0 : (i : ι) → Ω → β i) :=
  fun i ↦ @stronglyMeasurable_zero Ω (β i) (f i) _ _

theorem stronglyAdapted_zero (β : Type*) [TopologicalSpace β] [Zero β] (f : Filtration ι m) :
    StronglyAdapted f (0 : ι → Ω → β) :=
  fun i ↦ @stronglyMeasurable_zero Ω β (f i) _ _

theorem Filtration.stronglyAdapted_natural [∀ i, MetrizableSpace (β i)]
    [mβ : ∀ i, MeasurableSpace (β i)] [∀ i, BorelSpace (β i)]
    (hum : ∀ i, StronglyMeasurable[m] (u i)) :
    StronglyAdapted (Filtration.natural u hum) u := by
  intro i
  refine StronglyMeasurable.mono ?_ (le_iSup₂_of_le i (le_refl i) le_rfl)
  rw [stronglyMeasurable_iff_measurable_separable]
  exact ⟨measurable_iff_comap_le.2 le_rfl, (hum i).isSeparable_range⟩

end StronglyAdapted

variable {β : Type*} [TopologicalSpace β] {u v : ι → Ω → β}

/-- Strongly progressive process. A sequence of functions `u` is said to be strongly
progressive with respect to a filtration `f` if at each point in time `i`, `u` restricted to
`Set.Iic i × Ω` is strongly measurable with respect to the product `MeasurableSpace` structure
where the σ-algebra used for `Ω` is `f i`.
The usual definition uses the interval `[0,i]`, which we replace by `Set.Iic i`. We recover the
usual definition for index types `ℝ≥0` or `ℕ`. -/
def IsStronglyProgressive [MeasurableSpace ι] (f : Filtration ι m) (u : ι → Ω → β) : Prop :=
  ∀ i, StronglyMeasurable[Subtype.instMeasurableSpace.prod (f i)] fun p : Set.Iic i × Ω => u p.1 p.2

theorem isStronglyProgressive_const [MeasurableSpace ι] (f : Filtration ι m) (b : β) :
    IsStronglyProgressive f (fun _ _ => b : ι → Ω → β) := fun i =>
  @stronglyMeasurable_const _ _ (Subtype.instMeasurableSpace.prod (f i)) _ _

namespace IsStronglyProgressive

variable [MeasurableSpace ι]

protected theorem stronglyAdapted (h : IsStronglyProgressive f u) : StronglyAdapted f u := by
  intro i
  have : u i = (fun p : Set.Iic i × Ω => u p.1 p.2) ∘ fun x => (⟨i, Set.mem_Iic.mpr le_rfl⟩, x) :=
    rfl
  rw [this]
  exact (h i).comp_measurable measurable_prodMk_left

protected theorem comp {t : ι → Ω → ι} [TopologicalSpace ι] [BorelSpace ι] [PseudoMetrizableSpace ι]
    (h : IsStronglyProgressive f u) (ht : IsStronglyProgressive f t) (ht_le : ∀ i ω, t i ω ≤ i) :
    IsStronglyProgressive f fun i ω => u (t i ω) ω := by
  intro i
  have : (fun p : ↥(Set.Iic i) × Ω => u (t (p.fst : ι) p.snd) p.snd) =
    (fun p : ↥(Set.Iic i) × Ω => u (p.fst : ι) p.snd) ∘ fun p : ↥(Set.Iic i) × Ω =>
      (⟨t (p.fst : ι) p.snd, Set.mem_Iic.mpr ((ht_le _ _).trans p.fst.prop)⟩, p.snd) := rfl
  rw [this]
  exact (h i).comp_measurable ((ht i).measurable.subtype_mk.prodMk measurable_snd)

section Arithmetic

@[to_additive]
protected theorem mul [Mul β] [ContinuousMul β] (hu : IsStronglyProgressive f u)
    (hv : IsStronglyProgressive f v) : IsStronglyProgressive f fun i ω => u i ω * v i ω := fun i =>
  (hu i).mul (hv i)

@[to_additive]
protected theorem finsetProd' {γ} [CommMonoid β] [ContinuousMul β] {U : γ → ι → Ω → β}
    {s : Finset γ} (h : ∀ c ∈ s, IsStronglyProgressive f (U c)) :
    IsStronglyProgressive f (∏ c ∈ s, U c) :=
  Finset.prod_induction U (IsStronglyProgressive f) (fun _ _ => .mul)
    (isStronglyProgressive_const _ 1) h

@[deprecated (since := "2026-04-08")]
protected alias finset_sum' := MeasureTheory.IsStronglyProgressive.finsetSum'

@[to_additive existing, deprecated (since := "2026-04-08")]
protected alias finset_prod' := MeasureTheory.IsStronglyProgressive.finsetProd'

@[to_additive]
protected theorem finsetProd {γ} [CommMonoid β] [ContinuousMul β] {U : γ → ι → Ω → β}
    {s : Finset γ} (h : ∀ c ∈ s, IsStronglyProgressive f (U c)) :
    IsStronglyProgressive f fun i a => ∏ c ∈ s, U c i a := by
  convert IsStronglyProgressive.finsetProd' h using 1; ext (i a); simp only [Finset.prod_apply]

@[deprecated (since := "2026-04-08")]
protected alias finset_sum := MeasureTheory.IsStronglyProgressive.finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
protected alias finset_prod := MeasureTheory.IsStronglyProgressive.finsetProd

@[to_additive]
protected theorem inv [Group β] [ContinuousInv β] (hu : IsStronglyProgressive f u) :
    IsStronglyProgressive f fun i ω => (u i ω)⁻¹ := fun i => (hu i).inv

@[to_additive sub]
protected theorem div' [Group β] [ContinuousDiv β] (hu : IsStronglyProgressive f u)
    (hv : IsStronglyProgressive f v) : IsStronglyProgressive f fun i ω => u i ω / v i ω := fun i =>
  (hu i).div' (hv i)

/-- The norm of a strongly progressive process is strongly progressive. -/
protected lemma norm {β : Type*} {u : ι → Ω → β} [SeminormedAddCommGroup β]
    (hu : IsStronglyProgressive f u) :
    IsStronglyProgressive f fun t ω ↦ ‖u t ω‖ := fun t ↦ (hu t).norm

end Arithmetic

end IsStronglyProgressive

theorem isStronglyProgressive_of_tendsto' {γ} [MeasurableSpace ι] [PseudoMetrizableSpace β]
    (fltr : Filter γ) [fltr.NeBot] [fltr.IsCountablyGenerated] {U : γ → ι → Ω → β}
    (h : ∀ l, IsStronglyProgressive f (U l)) (h_tendsto : Tendsto U fltr (𝓝 u)) :
    IsStronglyProgressive f u := by
  intro i
  apply @stronglyMeasurable_of_tendsto (Set.Iic i × Ω) β γ
    (MeasurableSpace.prod _ (f i)) _ _ fltr _ _ _ _ fun l => h l i
  rw [tendsto_pi_nhds] at h_tendsto ⊢
  exact fun _ ↦ Tendsto.apply_nhds (h_tendsto _) _

theorem isStronglyProgressive_of_tendsto [MeasurableSpace ι] [PseudoMetrizableSpace β]
    {U : ℕ → ι → Ω → β} (h : ∀ l, IsStronglyProgressive f (U l))
    (h_tendsto : Tendsto U atTop (𝓝 u)) : IsStronglyProgressive f u :=
  isStronglyProgressive_of_tendsto' atTop h h_tendsto

/-- A continuous and strongly adapted process is strongly progressive. -/
theorem StronglyAdapted.isStronglyProgressive_of_continuous [TopologicalSpace ι] [MetrizableSpace ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [OpensMeasurableSpace ι]
    [PseudoMetrizableSpace β] (h : StronglyAdapted f u) (hu_cont : ∀ ω, Continuous fun i => u i ω) :
    IsStronglyProgressive f u := fun i =>
  @stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable _ _ (Set.Iic i) _ _ _ _ _ _ _
    (f i) _ (fun ω => (hu_cont ω).comp continuous_induced_dom) fun j => (h j).mono (f.mono j.prop)

/-- For filtrations indexed by a discrete order, `StronglyAdapted` and `IsStronglyProgressive` are
equivalent. This lemma provides `StronglyAdapted f u → IsStronglyProgressive f u`.
See `IsStronglyProgressive.stronglyAdapted` for the reverse direction, which is true more generally.
-/
theorem StronglyAdapted.isStronglyProgressive_of_discrete [TopologicalSpace ι] [DiscreteTopology ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [OpensMeasurableSpace ι]
    [PseudoMetrizableSpace β] (h : StronglyAdapted f u) : IsStronglyProgressive f u :=
  h.isStronglyProgressive_of_continuous fun _ => continuous_of_discreteTopology

@[deprecated (since := "2026-04-24")] alias ProgMeasurable := IsStronglyProgressive

@[deprecated (since := "2026-04-24")] alias progMeasurable_const := isStronglyProgressive_const

@[deprecated (since := "2026-04-24")]
alias ProgMeasurable.stronglyAdapted := IsStronglyProgressive.stronglyAdapted

@[deprecated (since := "2026-04-24")] alias ProgMeasurable.comp := IsStronglyProgressive.comp

@[deprecated (since := "2026-04-24")] alias ProgMeasurable.add := IsStronglyProgressive.add

@[to_additive existing, deprecated (since := "2026-04-24")]
alias ProgMeasurable.mul := IsStronglyProgressive.mul

@[deprecated (since := "2026-04-24")]
alias ProgMeasurable.finset_sum' := IsStronglyProgressive.finsetSum'

@[to_additive existing, deprecated (since := "2026-04-24")]
alias ProgMeasurable.finset_prod' := IsStronglyProgressive.finsetProd'

@[deprecated (since := "2026-04-24")]
alias ProgMeasurable.finset_sum := IsStronglyProgressive.finsetSum

@[to_additive existing, deprecated (since := "2026-04-24")]
alias ProgMeasurable.finset_prod := IsStronglyProgressive.finsetProd

@[deprecated (since := "2026-04-24")]
alias ProgMeasurable.neg := IsStronglyProgressive.neg

@[to_additive existing, deprecated (since := "2026-04-24")]
alias ProgMeasurable.inv := IsStronglyProgressive.inv

@[deprecated (since := "2026-04-24")] alias ProgMeasurable.sub := IsStronglyProgressive.sub

@[to_additive existing ProgMeasurable.sub, deprecated (since := "2026-04-24")]
alias ProgMeasurable.div' := IsStronglyProgressive.div'

@[deprecated (since := "2026-04-24")] alias ProgMeasurable.norm := IsStronglyProgressive.norm

@[deprecated (since := "2026-04-24")]
alias progMeasurable_of_tendsto := isStronglyProgressive_of_tendsto

@[deprecated (since := "2026-04-24")]
alias progMeasurable_of_tendsto' := isStronglyProgressive_of_tendsto'

@[deprecated (since := "2026-04-24")]
alias StronglyAdapted.progMeasurable_of_continuous :=
  StronglyAdapted.isStronglyProgressive_of_continuous

@[deprecated (since := "2026-04-24")]
alias StronglyAdapted.progMeasurable_of_discrete :=
  StronglyAdapted.isStronglyProgressive_of_discrete

end MeasureTheory
