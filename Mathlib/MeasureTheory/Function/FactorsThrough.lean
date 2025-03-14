/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.Process.Filtration

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

theorem stronglyMeasurable_limUnder [MeasurableSpace X] [hZ : Nonempty Z] [l.NeBot]
    (hf : ∀ i, StronglyMeasurable (f i)) :
    StronglyMeasurable (fun x ↦ limUnder l (f · x)) := by
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
    refine  measurable_of_tendsto_metrizable' l
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
theorem exists_eq_measurable_comp [AddZeroClass Z] [ContinuousAdd Z]
    {f :  X → Y} {g : X → Z} (hg : StronglyMeasurable[mY.comap f] g) :
    ∃ h : Y → Z, StronglyMeasurable h ∧ g = h ∘ f := by
  let mX : MeasurableSpace X := mY.comap f
  refine hg.induction (fun g ↦ ∃ h : Y → Z, StronglyMeasurable h ∧ g = h ∘ f)
    (fun c s hs ↦ ?_) ?_ ?_ g
  · obtain ⟨t, ht, rfl⟩ := hs
    exact ⟨t.indicator fun _ ↦ c, stronglyMeasurable_const.indicator ht, rfl⟩
  · rintro - - - - - ⟨h₁, mh₁, rfl⟩ ⟨h₂, mh₂, rfl⟩
    exact ⟨h₁ + h₂, mh₁.add mh₂, rfl⟩
  · intro g h mg h_ind mh h_lim
    choose i mi hi using h_ind
    refine ⟨fun y ↦ limUnder atTop (i · y), stronglyMeasurable_limUnder mi, ?_⟩
    ext x
    rw [Function.comp_apply, Tendsto.limUnder_eq]
    simp_all

lemma piecewise_comp {α β γ : Type*} (s : Set β) (f g : β → γ) (h : α → β)
    [∀ i, Decidable (i ∈ s)]  [∀ i, Decidable (i ∈ h⁻¹' s)] :
    (s.piecewise f g) ∘ h = (h⁻¹' s).piecewise (f ∘ h) (g ∘ h) := by
  ext x
  by_cases hx : h x ∈ s
  · simp only [hx, piecewise_eq_of_mem, mem_preimage, Function.comp_apply]
  · rw [Function.comp_apply, piecewise_eq_of_not_mem s f g hx,
      piecewise_eq_of_not_mem (h⁻¹' s) (f ∘ h) (g ∘ h) _, Function.comp_apply]
    rwa [mem_preimage]

theorem exists_eq_measurable_comp' [Nonempty Z] {f : X → Y} {g : X → Z}
    (hg : StronglyMeasurable[mY.comap f] g) :
    ∃ h : Y → Z, StronglyMeasurable h ∧ g = h ∘ f := by
  classical
  let mX : MeasurableSpace X := mY.comap f
  apply hg.induction' (fun g ↦ ∃ h : Y → Z, StronglyMeasurable h ∧ g = h ∘ f)
  · intro c
    refine ⟨fun _ ↦ c, stronglyMeasurable_const, ?_⟩
    ext x
    rw [SimpleFunc.coe_const, Function.const_apply, Function.comp_apply]
  · rintro f' g' s s_mes f_mes' g_mes' ⟨F, F_mes, F_f⟩ ⟨G, G_mes, G_g⟩
    rw [MeasurableSpace.measurableSet_comap] at s_mes
    obtain ⟨s', s_mes', f_s⟩ := s_mes
    refine ⟨s'.piecewise F G, F_mes.piecewise s_mes' G_mes, ?_⟩
    rw [piecewise_comp, f_s, F_f, G_g]
  · rintro gn g gn_mes gn_Gn g_mes gn_g
    choose G Gn_mes Gn_gn using gn_Gn
    refine ⟨fun y ↦ limUnder atTop (fun x ↦ G x y), stronglyMeasurable_limUnder Gn_mes, ?_⟩
    ext x
    rw [Function.comp_apply, Tendsto.limUnder_eq]
    refine Filter.Tendsto.congr (f₁ := fun n ↦ gn n x) (fun n ↦ ?_) (gn_g x)
    simp only [Gn_gn n, Function.comp_apply]

#check exists_eq_measurable_comp'

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
