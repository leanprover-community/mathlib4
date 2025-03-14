/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.Process.Filtration
import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal

/-!
# Factorization of a map from measurability

Consider `f : X → Y` and `g : X → Z` and assume that `g` is measurable with respect to the pullback
along `f`. Then `g` factors though `f`, which means that there exists `h : Y → Z` such that
`g = h ∘ f`.

Under certain assumptions, the factorization map `h` is measurable. This is the content of the
[Doob-Dynkin lemma](https://en.wikipedia.org/wiki/Doob–Dynkin_lemma):
see `exists_eq_measurable_comp`.
-/

namespace MeasureTheory

open Filter Filtration Set TopologicalSpace

open scoped Topology

variable {X Y Z : Type*} [mY : MeasurableSpace Y] {f : X → Y} {g : X → Z}

section FactorsThrough

/-- If a function `g` is measurable with respect to the pullback along some function `f`,
then to prove `g x = g y` it is enough to prove `f x = f y`. -/
theorem _root_.Measurable.factorsThrough [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (hg : Measurable[mY.comap f] g) : g.FactorsThrough f := by
  refine fun x₁ x₂ h ↦ eq_of_mem_singleton ?_
  obtain ⟨s, -, hs⟩ := hg (measurableSet_singleton (g x₂))
  rw [← mem_preimage, ← hs, mem_preimage, h, ← mem_preimage, hs]
  rfl

/-- If a function `g` is strongly measurable with respect to the pullback along some function `f`,
then to prove `g x = g y` it is enough to prove `f x = f y`.

Under certain assumptions, the factorization map `h` is measurable
(see `exists_eq_measurable_comp`). -/
theorem StronglyMeasurable.factorsThrough [TopologicalSpace Z]
    [PseudoMetrizableSpace Z] [T1Space Z] (hg : StronglyMeasurable[mY.comap f] g) :
    g.FactorsThrough f := by
  borelize Z
  exact hg.measurable.factorsThrough

variable {ι : Type*} [MetricSpace Z] [CompleteSpace Z] [Countable ι] {l : Filter ι}
  [l.IsCountablyGenerated] {f : ι → X → Z}

theorem StronglyMeasurable.measurableSet_exists_tendsto [MeasurableSpace X]
    (hf : ∀ i, StronglyMeasurable (f i)) :
    MeasurableSet {x | ∃ c, Tendsto (f · x) l (𝓝 c)} := by
  by_cases hl : l.NeBot
  swap; · simp_all
  let s := closure (⋃ i, range (f i))
  have : PolishSpace s :=
    { toSecondCountableTopology := @UniformSpace.secondCountable_of_separable s _ _
        (IsSeparable.iUnion (fun i ↦ (hf i).isSeparable_range)).closure.separableSpace
      complete := ⟨inferInstance, rfl, isClosed_closure.completeSpace_coe⟩ }
  let g i x : s := ⟨f i x, subset_closure <| Set.mem_iUnion.2 ⟨i, ⟨x, rfl⟩⟩⟩
  borelize Z
  have mg i : Measurable (g i) := (hf i).measurable.subtype_mk
  convert MeasureTheory.measurableSet_exists_tendsto mg with x
  · refine ⟨fun ⟨c, hc⟩ ↦ ⟨⟨c, ?_⟩, tendsto_subtype_rng.2 hc⟩,
      fun ⟨c, hc⟩ ↦ ⟨c, tendsto_subtype_rng.1 hc⟩⟩
    exact mem_closure_of_tendsto hc (Eventually.of_forall fun i ↦ Set.mem_iUnion.2 ⟨i, ⟨x, rfl⟩⟩)
  infer_instance

theorem stronglyMeasurable_limUnder [MeasurableSpace X] [hZ : Nonempty Z]
    (hf : ∀ i, StronglyMeasurable (f i)) :
    StronglyMeasurable (fun x ↦ limUnder l (f · x)) := by
  obtain rfl | hl := eq_or_neBot l
  · simp only [limUnder, Filter.map_bot]
    exact stronglyMeasurable_const
  borelize Z
  let z_ := Classical.choice hZ
  rw [stronglyMeasurable_iff_measurable_separable]; constructor
  · let conv := {x | ∃ c, Tendsto (f · x) l (𝓝 c)}
    have mconv : MeasurableSet conv := StronglyMeasurable.measurableSet_exists_tendsto hf
    have : (fun x ↦ limUnder l (f · x)) = ((↑) : conv → X).extend
        (fun x : conv ↦ limUnder l (f · x)) (fun _ ↦ z_) := by
      ext x
      by_cases hx : x ∈ conv
      · rw [Function.extend_val_apply hx]
      · rw [Function.extend_val_apply' hx, limUnder_of_not_tendsto hx]
    rw [this]
    refine (MeasurableEmbedding.subtype_coe mconv).measurable_extend ?_ measurable_const
    refine measurable_of_tendsto_metrizable' l
      (fun i ↦ (hf i).measurable.comp measurable_subtype_coe)
      (tendsto_pi_nhds.2 fun ⟨x, ⟨c, hc⟩⟩ ↦ ?_)
    rwa [hc.limUnder_eq]
  · let s := closure (⋃ i, range (f i)) ∪ {z_}
    have hs : IsSeparable s := (IsSeparable.iUnion (fun i ↦ (hf i).isSeparable_range)).closure.union
      (finite_singleton z_).isSeparable
    refine hs.mono ?_
    rintro - ⟨x, rfl⟩
    by_cases hx : ∃ c, Tendsto (f · x) l (𝓝 c)
    · obtain ⟨c, hc⟩ := hx
      simp_rw [hc.limUnder_eq]
      exact subset_union_left <| mem_closure_of_tendsto hc
        (Eventually.of_forall fun i ↦ Set.mem_iUnion.2 ⟨i, ⟨x, rfl⟩⟩)
    · simp_rw [limUnder_of_not_tendsto hx]
      exact subset_union_right (mem_singleton z_)

/-- If a function `g` is strongly measurable with respect to the pullback along some function `f`,
then there exists some measurable function `h : Y → Z` such that `g = h ∘ f`. -/
theorem exists_eq_measurable_comp {Z : Type*} [Nonempty Z] [MeasurableSpace Z]
    [StandardBorelSpace Z]
    {f :  X → Y} {g : X → Z} (hg : Measurable[mY.comap f] g) :
    ∃ h : Y → Z, Measurable h ∧ g = h ∘ f := by
  obtain ⟨T, _, _, _, _, _, _, h⟩ : ∃ (T : Type) (_ : TopologicalSpace T) (_ : MeasurableSpace T)
    (_ : AddZeroClass T), PolishSpace T ∧ ContinuousAdd T ∧ BorelSpace T ∧ Nonempty (Z ≃ᵐ T) := by
    by_cases hZ : Countable Z
    · cases finite_or_infinite Z
      · let φ := PolishSpace.Equiv.measurableEquiv (Finite.equivFin Z)
        have : NeZero (Nat.card Z) := ⟨Nat.card_pos.ne'⟩
        refine ⟨Fin (Nat.card Z), inferInstance, inferInstance, inferInstance, inferInstance,
          inferInstance, inferInstance, ⟨φ⟩⟩
      · let φ : Z ≃ᵐ ℕ := PolishSpace.Equiv.measurableEquiv
          (Classical.choice nonempty_equiv_of_countable)
        refine ⟨ℕ, inferInstance, inferInstance, inferInstance, inferInstance,
          inferInstance, inferInstance, ⟨φ⟩⟩
    · let φ : Z ≃ᵐ ℝ := PolishSpace.measurableEquivOfNotCountable hZ
        (Set.countable_univ_iff.not.1 Cardinal.not_countable_real)
      refine
        ⟨ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
          inferInstance, inferInstance, ⟨φ⟩⟩
  let mX : MeasurableSpace X := mY.comap f
  let φ := Classical.choice h
  borelize T
  have : StronglyMeasurable (φ ∘ g) := φ.measurable.comp hg |>.stronglyMeasurable
  suffices ∃ h : Y → T, Measurable h ∧ φ ∘ g = h ∘ f by
    obtain ⟨h, mh, hh⟩ := this
    refine ⟨φ.symm ∘ h, φ.symm.measurable.comp mh, ?_⟩
    rw [Function.comp_assoc, ← hh, ← Function.comp_assoc, φ.symm_comp_self, Function.id_comp]
  refine this.induction (fun g ↦ ∃ h : Y → T, Measurable h ∧ g = h ∘ f)
    (fun c s hs ↦ ?_) ?_ ?_ (φ ∘ g)
  · obtain ⟨t, ht, rfl⟩ := hs
    exact ⟨t.indicator fun _ ↦ c, measurable_const.indicator ht, rfl⟩
  · rintro - - - - - ⟨h₁, mh₁, rfl⟩ ⟨h₂, mh₂, rfl⟩
    exact ⟨h₁ + h₂, mh₁.add mh₂, rfl⟩
  · intro g h mg h_ind mh h_lim
    choose i mi hi using h_ind
    letI := upgradePolishSpace T
    refine ⟨fun y ↦ limUnder atTop (i · y),
      stronglyMeasurable_limUnder (fun n ↦ (mi n).stronglyMeasurable) |>.measurable, ?_⟩
    ext x
    rw [Function.comp_apply, Tendsto.limUnder_eq]
    simp_all

theorem exists_eq_measurable_comp' [hZ : Nonempty Z]
    {f :  X → Y} {g : X → Z} (hg : StronglyMeasurable[mY.comap f] g) :
    ∃ h : Y → Z, StronglyMeasurable h ∧ g = h ∘ f := by
  obtain _ | hX := isEmpty_or_nonempty X
  · exact ⟨fun _ ↦ Classical.choice hZ, stronglyMeasurable_const, funext fun x ↦ isEmptyElim x⟩
  let mX : MeasurableSpace X := mY.comap f
  borelize Z
  let s := closure (range g)
  have : PolishSpace s :=
    { toSecondCountableTopology := @UniformSpace.secondCountable_of_separable s _ _
        hg.isSeparable_range.closure.separableSpace
      complete := ⟨inferInstance, rfl, isClosed_closure.completeSpace_coe⟩ }
  letI := upgradeStandardBorel s
  let j : X → s := fun x ↦ ⟨g x, subset_closure ⟨x, rfl⟩⟩
  have : Measurable j := hg.measurable.subtype_mk
  have _ : Nonempty s := ⟨j (Classical.choice hX)⟩
  obtain ⟨h, mh, hh⟩ := exists_eq_measurable_comp this
  refine ⟨Subtype.val ∘ h, stronglyMeasurable_iff_measurable_separable.2
    ⟨measurable_subtype_coe.comp mh, (IsSeparable.of_subtype s).mono fun y ⟨x, hy⟩ ↦ hy ▸ (h x).2⟩,
    funext fun _ ↦ ?_⟩
  rw [Function.comp_assoc, ← hh]; rfl

end FactorsThrough

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)] {f : (Π i, X i) → Z}

section piLE

variable [Preorder ι] {i : ι}

/-- If a function is measurable with respect to the σ-algebra generated by the
first coordinates, then it only depends on those first coordinates. -/
theorem _root_.Measurable.dependsOn_of_piLE [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (hf : Measurable[piLE i] f) : DependsOn f (Iic i) :=
  dependsOn_iff_factorsThrough.2 hf.factorsThrough

/-- If a function is strongly measurable with respect to the σ-algebra generated by the
first coordinates, then it only depends on those first coordinates. -/
theorem StronglyMeasurable.dependsOn_of_piLE [TopologicalSpace Z] [PseudoMetrizableSpace Z]
    [T1Space Z] (hf : StronglyMeasurable[piLE i] f) : DependsOn f (Iic i) :=
  dependsOn_iff_factorsThrough.2 hf.factorsThrough

end piLE

section piFinset

variable {s : Finset ι}

/-- If a function is measurable with respect to the σ-algebra generated by the
first coordinates, then it only depends on those first coordinates. -/
theorem _root_.Measurable.dependsOn_of_piFinset [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (hf : Measurable[piFinset s] f) : DependsOn f s :=
  dependsOn_iff_factorsThrough.2 hf.factorsThrough

/-- If a function is strongly measurable with respect to the σ-algebra generated by the
first coordinates, then it only depends on those first coordinates. -/
theorem StronglyMeasurable.dependsOn_of_piFinset [TopologicalSpace Z] [PseudoMetrizableSpace Z]
    [T1Space Z] (hf : StronglyMeasurable[piFinset s] f) : DependsOn f s :=
  dependsOn_iff_factorsThrough.2 hf.factorsThrough

end piFinset

end MeasureTheory
