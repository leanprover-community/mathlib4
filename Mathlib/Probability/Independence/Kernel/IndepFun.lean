/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Independence.Kernel.Indep
public import Mathlib.MeasureTheory.MeasurableSpace.Pi
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Independence of random variables with respect to a kernel and a measure

A family of random variables is independent if the corresponding `σ`-algebras are independent.
Independence of families of sets and `σ`-algebras is covered in the `Indep` file.
This file deals with independence of random variables specifically.

Note that we define independence with respect to a kernel and a measure. This notion of independence
is a generalization of both independence and conditional independence.
For conditional independence, `κ` is the conditional kernel `ProbabilityTheory.condExpKernel` and
`μ` is the ambient measure. For (non-conditional) independence, `κ = Kernel.const Unit μ` and the
measure is the Dirac measure on `Unit`.

## Main definition

* `ProbabilityTheory.Kernel.iIndepFun`: independence of a family of functions (random variables).
  Variant for two functions: `ProbabilityTheory.Kernel.IndepFun`.
-/

@[expose] public section

open Set MeasureTheory MeasurableSpace

namespace ProbabilityTheory.Kernel

variable {α Ω ι β β' γ γ' : Type*} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω}
  {κ η : Kernel α Ω} {μ : Measure α} {f : Ω → β} {g : Ω → β'}

section Definitions

/-- A family of functions defined on the same space `Ω` and taking values in possibly different
spaces, each with a measurable space structure, is independent if the family of measurable space
structures they generate on `Ω` is independent. For a function `g` with codomain having measurable
space structure `m`, the generated measurable space structure is `MeasurableSpace.comap g m`. -/
def iIndepFun {β : ι → Type*} [m : ∀ x : ι, MeasurableSpace (β x)]
    (f : ∀ x : ι, Ω → β x) (κ : Kernel α Ω)
    (μ : Measure α := by volume_tac) : Prop :=
  iIndep (m := fun x ↦ MeasurableSpace.comap (f x) (m x)) κ μ

/-- Two functions are independent if the two measurable space structures they generate are
independent. For a function `f` with codomain having measurable space structure `m`, the generated
measurable space structure is `MeasurableSpace.comap f m`. -/
def IndepFun [mβ : MeasurableSpace β] [mγ : MeasurableSpace γ]
    (f : Ω → β) (g : Ω → γ) (κ : Kernel α Ω)
    (μ : Measure α := by volume_tac) : Prop :=
  Indep (MeasurableSpace.comap f mβ) (MeasurableSpace.comap g mγ) κ μ

end Definitions

section ByDefinition

variable {β : ι → Type*} {mβ : ∀ i, MeasurableSpace (β i)}
  {_mα : MeasurableSpace α} {m : ι → MeasurableSpace Ω} {_mΩ : MeasurableSpace Ω}
  {κ η : Kernel α Ω} {μ : Measure α}
  {π : ι → Set (Set Ω)} {s : ι → Set Ω} {S : Finset ι} {f : ∀ x : ι, Ω → β x}
  {s1 s2 : Set (Set Ω)} {ι' : Type*} {g : ι' → ι}

@[simp] lemma iIndepFun_zero_right {β : ι → Type*} {m : ∀ x : ι, MeasurableSpace (β x)}
    {f : ∀ x : ι, Ω → β x} : iIndepFun f κ 0 := by simp [iIndepFun]

@[simp] lemma indepFun_zero_right {β} [MeasurableSpace β] [MeasurableSpace γ]
    {f : Ω → β} {g : Ω → γ} : IndepFun f g κ 0 := by simp [IndepFun]

@[simp] lemma indepFun_zero_left {β} [MeasurableSpace β] [MeasurableSpace γ]
    {f : Ω → β} {g : Ω → γ} : IndepFun f g (0 : Kernel α Ω) μ := by simp [IndepFun]

lemma iIndepFun_congr {β : ι → Type*} {m : ∀ x : ι, MeasurableSpace (β x)}
    {f : ∀ x : ι, Ω → β x} (h : κ =ᵐ[μ] η) : iIndepFun f κ μ ↔ iIndepFun f η μ :=
  iIndep_congr h

alias ⟨iIndepFun.congr, _⟩ := iIndepFun_congr

lemma indepFun_congr {β} [MeasurableSpace β] [MeasurableSpace γ]
    {f : Ω → β} {g : Ω → γ} (h : κ =ᵐ[μ] η) : IndepFun f g κ μ ↔ IndepFun f g η μ :=
  indep_congr h

alias ⟨IndepFun.congr, _⟩ := indepFun_congr

@[nontriviality, simp]
lemma iIndepFun.of_subsingleton [Subsingleton ι] {β : ι → Type*} {m : ∀ i, MeasurableSpace (β i)}
    {f : ∀ i, Ω → β i} [IsMarkovKernel κ] : iIndepFun f κ μ := by
  simp [iIndepFun]

protected lemma iIndepFun.iIndep (hf : iIndepFun f κ μ) :
    iIndep (fun x ↦ (mβ x).comap (f x)) κ μ := hf

lemma iIndepFun.ae_isProbabilityMeasure (h : iIndepFun f κ μ) :
    ∀ᵐ a ∂μ, IsProbabilityMeasure (κ a) :=
  h.iIndep.ae_isProbabilityMeasure

lemma iIndepFun.meas_biInter (hf : iIndepFun f κ μ)
    (hs : ∀ i, i ∈ S → MeasurableSet[(mβ i).comap (f i)] (s i)) :
    ∀ᵐ a ∂μ, κ a (⋂ i ∈ S, s i) = ∏ i ∈ S, κ a (s i) := hf.iIndep.meas_biInter hs

lemma iIndepFun.meas_iInter [Fintype ι] (hf : iIndepFun f κ μ)
    (hs : ∀ i, MeasurableSet[(mβ i).comap (f i)] (s i)) :
    ∀ᵐ a ∂μ, κ a (⋂ i, s i) = ∏ i, κ a (s i) := hf.iIndep.meas_iInter hs

lemma IndepFun.meas_inter {β} [mβ : MeasurableSpace β] [mγ : MeasurableSpace γ]
    {f : Ω → β} {g : Ω → γ} (hfg : IndepFun f g κ μ)
    {s t : Set Ω} (hs : MeasurableSet[mβ.comap f] s) (ht : MeasurableSet[mγ.comap g] t) :
    ∀ᵐ a ∂μ, κ a (s ∩ t) = κ a s * κ a t := hfg _ _ hs ht

lemma iIndepFun.precomp (hg : Function.Injective g) (h : iIndepFun f κ μ) :
    iIndepFun (fun i ↦ f (g i)) κ μ :=
  iIndep.precomp hg h

lemma iIndepFun.of_precomp (hg : Function.Surjective g) (h : iIndepFun (fun i ↦ f (g i)) κ μ) :
    iIndepFun f κ μ :=
  iIndep.of_precomp hg h

lemma iIndepFun_precomp_of_bijective (hg : Function.Bijective g) :
    iIndepFun (fun i ↦ f (g i)) κ μ ↔ iIndepFun f κ μ :=
  ⟨.of_precomp hg.surjective, .precomp hg.injective⟩

end ByDefinition

theorem iIndepFun.indepFun {β : ι → Type*} {m : ∀ x, MeasurableSpace (β x)} {f : ∀ i, Ω → β i}
    (hf_Indep : iIndepFun f κ μ) {i j : ι} (hij : i ≠ j) : IndepFun (f i) (f j) κ μ :=
  hf_Indep.indep hij

theorem indepFun_iff_measure_inter_preimage_eq_mul {mβ : MeasurableSpace β}
    {mβ' : MeasurableSpace β'} :
    IndepFun f g κ μ ↔
      ∀ s t, MeasurableSet s → MeasurableSet t
        → ∀ᵐ a ∂μ, κ a (f ⁻¹' s ∩ g ⁻¹' t) = κ a (f ⁻¹' s) * κ a (g ⁻¹' t) := by
  constructor <;> intro h
  · refine fun s t hs ht => h (f ⁻¹' s) (g ⁻¹' t) ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
  · rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩; exact h s t hs ht

alias ⟨IndepFun.measure_inter_preimage_eq_mul, _⟩ := indepFun_iff_measure_inter_preimage_eq_mul

theorem iIndepFun_iff_measure_inter_preimage_eq_mul {ι : Type*} {β : ι → Type*}
    (m : ∀ x, MeasurableSpace (β x)) (f : ∀ i, Ω → β i) :
    iIndepFun f κ μ ↔
      ∀ (S : Finset ι) {sets : ∀ i : ι, Set (β i)} (_H : ∀ i, i ∈ S → MeasurableSet[m i] (sets i)),
        ∀ᵐ a ∂μ, κ a (⋂ i ∈ S, (f i) ⁻¹' (sets i)) = ∏ i ∈ S, κ a ((f i) ⁻¹' (sets i)) := by
  refine ⟨fun h S sets h_meas => h _ fun i hi_mem => ⟨sets i, h_meas i hi_mem, rfl⟩, ?_⟩
  intro h S setsΩ h_meas
  classical
  let setsβ : ∀ i : ι, Set (β i) := fun i =>
    dite (i ∈ S) (fun hi_mem => (h_meas i hi_mem).choose) fun _ => Set.univ
  have h_measβ : ∀ i ∈ S, MeasurableSet[m i] (setsβ i) := by
    intro i hi_mem
    simp_rw [setsβ, dif_pos hi_mem]
    exact (h_meas i hi_mem).choose_spec.1
  have h_preim : ∀ i ∈ S, setsΩ i = f i ⁻¹' setsβ i := by
    intro i hi_mem
    simp_rw [setsβ, dif_pos hi_mem]
    exact (h_meas i hi_mem).choose_spec.2.symm
  simp_all

alias ⟨iIndepFun.measure_inter_preimage_eq_mul, _⟩ := iIndepFun_iff_measure_inter_preimage_eq_mul

theorem iIndepFun.congr' {β : ι → Type*} {mβ : ∀ i, MeasurableSpace (β i)}
    {f g : Π i, Ω → β i} (hf : iIndepFun f κ μ)
    (h : ∀ i, ∀ᵐ a ∂μ, f i =ᵐ[κ a] g i) :
    iIndepFun g κ μ := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at hf ⊢
  intro S sets hmeas
  have : ∀ᵐ a ∂μ, ∀ i ∈ S, f i =ᵐ[κ a] g i :=
    (ae_ball_iff (Finset.countable_toSet S)).2 (fun i hi ↦ h i)
  filter_upwards [this, hf S hmeas] with a ha h'a
  have A i (hi : i ∈ S) : (κ a) (g i ⁻¹' sets i) = (κ a) (f i ⁻¹' sets i) := by
    apply measure_congr
    filter_upwards [ha i hi] with ω hω
    change (g i ω ∈ sets i) = (f i ω ∈ sets i)
    simp [hω]
  have B : (κ a) (⋂ i ∈ S, g i ⁻¹' sets i) = (κ a) (⋂ i ∈ S, f i ⁻¹' sets i) := by
    apply measure_congr
    filter_upwards [(ae_ball_iff (Finset.countable_toSet S)).2 ha] with ω hω
    change (ω ∈ ⋂ i ∈ S, g i ⁻¹' sets i) = (ω ∈ ⋂ i ∈ S, f i ⁻¹' sets i)
    simp +contextual [hω]
  convert h'a using 2 with i hi
  exact A i hi

theorem iIndepFun_congr' {β : ι → Type*} {mβ : ∀ i, MeasurableSpace (β i)}
    {f g : Π i, Ω → β i} (h : ∀ i, ∀ᵐ a ∂μ, f i =ᵐ[κ a] g i) :
    iIndepFun f κ μ ↔ iIndepFun g κ μ where
  mp h' := h'.congr' h
  mpr h' := by
    refine h'.congr' fun i ↦ ?_
    filter_upwards [h i] with a ha using ha.symm

lemma iIndepFun.comp {β γ : ι → Type*} {mβ : ∀ i, MeasurableSpace (β i)}
    {mγ : ∀ i, MeasurableSpace (γ i)} {f : ∀ i, Ω → β i}
    (h : iIndepFun f κ μ) (g : ∀ i, β i → γ i) (hg : ∀ i, Measurable (g i)) :
    iIndepFun (fun i ↦ g i ∘ f i) κ μ := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  refine fun t s hs ↦ ?_
  have := h t (sets := fun i ↦ g i ⁻¹' (s i)) (fun i a ↦ hg i (hs i a))
  filter_upwards [this] with a ha
  simp_rw [Set.preimage_comp]
  exact ha

lemma iIndepFun.comp₀ {β γ : ι → Type*} {mβ : ∀ i, MeasurableSpace (β i)}
    {mγ : ∀ i, MeasurableSpace (γ i)} {f : ∀ i, Ω → β i}
    (h : iIndepFun f κ μ) (g : ∀ i, β i → γ i)
    (hf : ∀ i, AEMeasurable (f i) (κ ∘ₘ μ)) (hg : ∀ i, AEMeasurable (g i) ((κ ∘ₘ μ).map (f i))) :
    iIndepFun (fun i ↦ g i ∘ f i) κ μ := by
  have h : iIndepFun (fun i ↦ ((hg i).mk (g i)) ∘ f i) κ μ :=
    iIndepFun.comp h (fun i ↦ (hg i).mk (g i)) fun i ↦ (hg i).measurable_mk
  have h_ae i := ae_of_ae_map (hf i) (hg i).ae_eq_mk.symm
  exact iIndepFun.congr' h fun i ↦ Measure.ae_ae_of_ae_comp (h_ae i)

theorem indepFun_iff_indepSet_preimage {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    [IsZeroOrMarkovKernel κ] (hf : Measurable f) (hg : Measurable g) :
    IndepFun f g κ μ ↔
      ∀ s t, MeasurableSet s → MeasurableSet t → IndepSet (f ⁻¹' s) (g ⁻¹' t) κ μ := by
  refine indepFun_iff_measure_inter_preimage_eq_mul.trans ?_
  constructor <;> intro h s t hs ht <;> specialize h s t hs ht
  · rwa [indepSet_iff_measure_inter_eq_mul (hf hs) (hg ht) κ μ]
  · rwa [← indepSet_iff_measure_inter_eq_mul (hf hs) (hg ht) κ μ]

@[symm]
nonrec theorem IndepFun.symm {_ : MeasurableSpace β} {_ : MeasurableSpace β'}
    (hfg : IndepFun f g κ μ) : IndepFun g f κ μ := hfg.symm

theorem IndepFun.congr' {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    {f' : Ω → β} {g' : Ω → β'} (hfg : IndepFun f g κ μ)
    (hf : ∀ᵐ a ∂μ, f =ᵐ[κ a] f') (hg : ∀ᵐ a ∂μ, g =ᵐ[κ a] g') :
    IndepFun f' g' κ μ := by
  rintro _ _ ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩
  filter_upwards [hf, hg, hfg _ _ ⟨_, hA, rfl⟩ ⟨_, hB, rfl⟩] with a hf' hg' hfg'
  have h1 : f ⁻¹' A =ᵐ[κ a] f' ⁻¹' A := hf'.fun_comp A
  have h2 : g ⁻¹' B =ᵐ[κ a] g' ⁻¹' B := hg'.fun_comp B
  rwa [← measure_congr h1, ← measure_congr h2, ← measure_congr (h1.inter h2)]

theorem IndepFun.comp {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    {mγ : MeasurableSpace γ} {mγ' : MeasurableSpace γ'} {φ : β → γ} {ψ : β' → γ'}
    (hfg : IndepFun f g κ μ) (hφ : Measurable φ) (hψ : Measurable ψ) :
    IndepFun (φ ∘ f) (ψ ∘ g) κ μ := by
  rintro _ _ ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩
  apply hfg
  · exact ⟨φ ⁻¹' A, hφ hA, Set.preimage_comp.symm⟩
  · exact ⟨ψ ⁻¹' B, hψ hB, Set.preimage_comp.symm⟩

theorem IndepFun.comp₀ {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    {mγ : MeasurableSpace γ} {mγ' : MeasurableSpace γ'} {φ : β → γ} {ψ : β' → γ'}
    (hfg : IndepFun f g κ μ)
    (hf : AEMeasurable f (κ ∘ₘ μ)) (hg : AEMeasurable g (κ ∘ₘ μ))
    (hφ : AEMeasurable φ ((κ ∘ₘ μ).map f)) (hψ : AEMeasurable ψ ((κ ∘ₘ μ).map g)) :
    IndepFun (φ ∘ f) (ψ ∘ g) κ μ := by
  have h : IndepFun ((hφ.mk φ) ∘ f) ((hψ.mk ψ) ∘ g) κ μ := by
    refine IndepFun.comp hfg hφ.measurable_mk hψ.measurable_mk
  have hφ_ae := ae_of_ae_map hf hφ.ae_eq_mk
  have hψ_ae := ae_of_ae_map hg hψ.ae_eq_mk
  refine IndepFun.congr' h ?_ ?_
  · filter_upwards [Measure.ae_ae_of_ae_comp (hφ_ae)] with a haφ
    filter_upwards [haφ] with ω hωφ
    simp [hωφ]
  · filter_upwards [Measure.ae_ae_of_ae_comp (hψ_ae)] with a haψ
    filter_upwards [haψ] with ω hωψ
    simp [hωψ]

lemma indepFun_const_left {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    [IsZeroOrMarkovKernel κ] (c : β') (X : Ω → β) :
    IndepFun (fun _ ↦ c) X κ μ := by
  rw [IndepFun, MeasurableSpace.comap_const]
  exact indep_bot_left _

lemma indepFun_const_right {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    [IsZeroOrMarkovKernel κ] (X : Ω → β) (c : β') :
    IndepFun X (fun _ ↦ c) κ μ :=
  (indepFun_const_left c X).symm

theorem IndepFun.neg_right {_mβ : MeasurableSpace β} {_mβ' : MeasurableSpace β'} [Neg β']
    [MeasurableNeg β'] (hfg : IndepFun f g κ μ) :
    IndepFun f (-g) κ μ := hfg.comp measurable_id measurable_neg

theorem IndepFun.neg_left {_mβ : MeasurableSpace β} {_mβ' : MeasurableSpace β'} [Neg β]
    [MeasurableNeg β] (hfg : IndepFun f g κ μ) :
    IndepFun (-f) g κ μ := hfg.comp measurable_neg measurable_id

/-- Two random variables `f, g` are independent given a kernel `κ` and a measure `μ` iff
`μ ⊗ₘ κ.map (fun ω ↦ (f ω, g ω)) = μ ⊗ₘ (κ.map f ×ₖ κ.map g)`. -/
theorem indepFun_iff_compProd_map_prod_eq_compProd_prod_map_map
    {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
    [IsFiniteMeasure μ] [IsFiniteKernel κ] {f : Ω → β} {g : Ω → γ}
    (hf : Measurable f) (hg : Measurable g) :
    IndepFun f g κ μ ↔ μ ⊗ₘ κ.map (fun ω ↦ (f ω, g ω)) = μ ⊗ₘ (κ.map f ×ₖ κ.map g) := by
  classical
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [Measure.ext_prod₃_iff]
    intro u s t hu hs ht
    rw [Measure.compProd_apply (hu.prod (hs.prod ht)),
      Measure.compProd_apply (hu.prod (hs.prod ht))]
    refine lintegral_congr_ae ?_
    have h_set_eq ω : Prod.mk ω ⁻¹' u ×ˢ s ×ˢ t = if ω ∈ u then s ×ˢ t else ∅ := by ext; simp
    simp_rw [h_set_eq]
    filter_upwards [h s t hs ht] with ω hω
    by_cases hωu : ω ∈ u
    swap; · simp [hωu]
    simp only [hωu, ↓reduceIte]
    rw [map_apply _ (by fun_prop), Measure.map_apply (by fun_prop) (hs.prod ht),
      mk_preimage_prod, hω, prod_apply_prod, map_apply' _ (by fun_prop), map_apply' _ (by fun_prop)]
    exacts [ht, hs]
  · intro s t hs ht
    rw [Measure.ext_prod₃_iff] at h
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite ?_ ?_ ?_
    · exact Kernel.measurable_coe _ ((hf hs).inter (hg ht))
    · exact (Kernel.measurable_coe _ (hf hs)).mul (Kernel.measurable_coe _ (hg ht))
    intro u hu hμu
    specialize h hu hs ht
    rw [Measure.compProd_apply_prod hu (hs.prod ht),
      Measure.compProd_apply_prod hu (hs.prod ht)] at h
    convert h with ω ω
    · rw [map_apply' _ (by fun_prop) _ (hs.prod ht), mk_preimage_prod]
    · rw [prod_apply_prod, map_apply' _ (by fun_prop) _ hs, map_apply' _ (by fun_prop) _ ht]

section iIndepFun
variable {β : ι → Type*} {m : ∀ i, MeasurableSpace (β i)} {f : ∀ i, Ω → β i}


/-- If `f` is a family of mutually independent random variables (`iIndepFun m f μ`) and `S, T` are
two disjoint finite index sets, then the tuple formed by `f i` for `i ∈ S` is independent of the
tuple `(f i)_i` for `i ∈ T`. -/
theorem iIndepFun.indepFun_finset (S T : Finset ι) (hST : Disjoint S T)
    (hf_Indep : iIndepFun f κ μ) (hf_meas : ∀ i, Measurable (f i)) :
    IndepFun (fun a (i : S) => f i a) (fun a (i : T) => f i a) κ μ := by
  rcases eq_or_ne μ 0 with rfl | hμ
  · simp
  obtain ⟨η, η_eq, hη⟩ : ∃ (η : Kernel α Ω), κ =ᵐ[μ] η ∧ IsMarkovKernel η :=
    exists_ae_eq_isMarkovKernel hf_Indep.ae_isProbabilityMeasure hμ
  apply IndepFun.congr (Filter.EventuallyEq.symm η_eq)
  -- We introduce π-systems, built from the π-system of boxes which generates `MeasurableSpace.pi`.
  let πSβ := Set.pi (Set.univ : Set S) ''
    Set.pi (Set.univ : Set S) fun i => { s : Set (β i) | MeasurableSet[m i] s }
  let πS := { s : Set Ω | ∃ t ∈ πSβ, (fun a (i : S) => f i a) ⁻¹' t = s }
  have hπS_pi : IsPiSystem πS := by exact IsPiSystem.comap (@isPiSystem_pi _ _ ?_) _
  have hπS_gen : (MeasurableSpace.pi.comap fun a (i : S) => f i a) = generateFrom πS := by
    rw [generateFrom_pi.symm, comap_generateFrom]
    congr
  let πTβ := Set.pi (Set.univ : Set T) ''
      Set.pi (Set.univ : Set T) fun i => { s : Set (β i) | MeasurableSet[m i] s }
  let πT := { s : Set Ω | ∃ t ∈ πTβ, (fun a (i : T) => f i a) ⁻¹' t = s }
  have hπT_pi : IsPiSystem πT := by exact IsPiSystem.comap (@isPiSystem_pi _ _ ?_) _
  have hπT_gen : (MeasurableSpace.pi.comap fun a (i : T) => f i a) = generateFrom πT := by
    rw [generateFrom_pi.symm, comap_generateFrom]
    congr
  -- To prove independence, we prove independence of the generating π-systems.
  refine IndepSets.indep (Measurable.comap_le (measurable_pi_iff.mpr fun i => hf_meas i))
    (Measurable.comap_le (measurable_pi_iff.mpr fun i => hf_meas i)) hπS_pi hπT_pi hπS_gen hπT_gen
    ?_
  rintro _ _ ⟨s, ⟨sets_s, hs1, hs2⟩, rfl⟩ ⟨t, ⟨sets_t, ht1, ht2⟩, rfl⟩
  simp only [Set.mem_univ_pi, Set.mem_setOf_eq] at hs1 ht1
  rw [← hs2, ← ht2]
  classical
  let sets_s' : ∀ i : ι, Set (β i) := fun i =>
    dite (i ∈ S) (fun hi => sets_s ⟨i, hi⟩) fun _ => Set.univ
  have h_sets_s'_eq : ∀ {i} (hi : i ∈ S), sets_s' i = sets_s ⟨i, hi⟩ := by
    intro i hi; simp_rw [sets_s', dif_pos hi]
  have h_sets_s'_univ : ∀ {i} (_hi : i ∈ T), sets_s' i = Set.univ := by
    intro i hi; simp_rw [sets_s', dif_neg (Finset.disjoint_right.mp hST hi)]
  let sets_t' : ∀ i : ι, Set (β i) := fun i =>
    dite (i ∈ T) (fun hi => sets_t ⟨i, hi⟩) fun _ => Set.univ
  have h_sets_t'_univ : ∀ {i} (_hi : i ∈ S), sets_t' i = Set.univ := by
    intro i hi; simp_rw [sets_t', dif_neg (Finset.disjoint_left.mp hST hi)]
  have h_meas_s' : ∀ i ∈ S, MeasurableSet (sets_s' i) := by
    intro i hi; rw [h_sets_s'_eq hi]; exact hs1 _
  have h_meas_t' : ∀ i ∈ T, MeasurableSet (sets_t' i) := by
    intro i hi; simp_rw [sets_t', dif_pos hi]; exact ht1 _
  have h_eq_inter_S : (fun (ω : Ω) (i : ↥S) =>
    f (↑i) ω) ⁻¹' Set.pi Set.univ sets_s = ⋂ i ∈ S, f i ⁻¹' sets_s' i := by
    ext1 x
    simp_rw [Set.mem_preimage, Set.mem_univ_pi, Set.mem_iInter]
    grind
  have h_eq_inter_T : (fun (ω : Ω) (i : ↥T) => f (↑i) ω) ⁻¹' Set.pi Set.univ sets_t
    = ⋂ i ∈ T, f i ⁻¹' sets_t' i := by
    ext1 x
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_iInter]
    constructor <;> intro h
    · intro i hi; simp_rw [sets_t', dif_pos hi]; exact h ⟨i, hi⟩
    · rintro ⟨i, hi⟩; specialize h i hi; simp_rw [sets_t', dif_pos hi] at h; exact h
  replace hf_Indep := hf_Indep.congr η_eq
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at hf_Indep
  have h_Inter_inter :
    ((⋂ i ∈ S, f i ⁻¹' sets_s' i) ∩ ⋂ i ∈ T, f i ⁻¹' sets_t' i) =
      ⋂ i ∈ S ∪ T, f i ⁻¹' (sets_s' i ∩ sets_t' i) := by
    ext1 x
    simp_rw [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Finset.mem_union]
    constructor <;> intro h
    · grind
    · exact ⟨fun i hi => (h i (Or.inl hi)).1, fun i hi => (h i (Or.inr hi)).2⟩
  have h_meas_inter : ∀ i ∈ S ∪ T, MeasurableSet (sets_s' i ∩ sets_t' i) := by
    intro i hi_mem
    rw [Finset.mem_union] at hi_mem
    rcases hi_mem with hi_mem | hi_mem
    · rw [h_sets_t'_univ hi_mem, Set.inter_univ]
      exact h_meas_s' i hi_mem
    · rw [h_sets_s'_univ hi_mem, Set.univ_inter]
      exact h_meas_t' i hi_mem
  filter_upwards [hf_Indep S h_meas_s', hf_Indep T h_meas_t', hf_Indep (S ∪ T) h_meas_inter]
    with a h_indepS h_indepT h_indepST
  rw [h_eq_inter_S, h_eq_inter_T, h_indepS, h_indepT, h_Inter_inter, h_indepST,
    Finset.prod_union hST]
  congr 1
  · refine Finset.prod_congr rfl fun i hi => ?_
    rw [h_sets_t'_univ hi, Set.inter_univ]
  · refine Finset.prod_congr rfl fun i hi => ?_
    rw [h_sets_s'_univ hi, Set.univ_inter]

theorem iIndepFun.indepFun_finset₀ (S T : Finset ι) (hST : Disjoint S T)
    (hf_Indep : iIndepFun f κ μ) (hf_meas : ∀ i, AEMeasurable (f i) (κ ∘ₘ μ)) :
    IndepFun (fun a (i : S) ↦ f i a) (fun a (i : T) ↦ f i a) κ μ := by
  have h : IndepFun (fun a (i : S) ↦ (hf_meas i).mk (f i) a)
      (fun a (i : T) ↦ (hf_meas i).mk (f i) a) κ μ := by
    refine iIndepFun.indepFun_finset S T hST ?_ fun i ↦ (hf_meas i).measurable_mk
    exact iIndepFun.congr' hf_Indep fun i ↦ Measure.ae_ae_of_ae_comp (hf_meas i).ae_eq_mk
  refine IndepFun.congr' h ?_ ?_
  · have : ∀ᵐ (a : α) ∂μ, ∀ (i : S), f i =ᵐ[κ a] (hf_meas i).mk := by
      rw [ae_all_iff]
      exact fun i ↦ Measure.ae_ae_of_ae_comp (hf_meas i).ae_eq_mk
    filter_upwards [this] with a ha
    filter_upwards [ae_all_iff.2 ha] with b hb
    ext i
    exact (hb i).symm
  · have : ∀ᵐ (a : α) ∂μ, ∀ (i : T), f i =ᵐ[κ a] (hf_meas i).mk := by
      rw [ae_all_iff]
      exact fun i ↦ Measure.ae_ae_of_ae_comp (hf_meas i).ae_eq_mk
    filter_upwards [this] with a ha
    filter_upwards [ae_all_iff.2 ha] with b hb
    ext i
    exact (hb i).symm

theorem iIndepFun.indepFun_prodMk (hf_Indep : iIndepFun f κ μ)
    (hf_meas : ∀ i, Measurable (f i)) (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) :
    IndepFun (fun a => (f i a, f j a)) (f k) κ μ := by
  classical
  have h_right :
      f k = (fun p : ∀ j : ({k} : Finset ι), β j => p ⟨k, Finset.mem_singleton_self k⟩) ∘
        fun a (j : ({k} : Finset ι)) => f j a :=
    rfl
  have h_meas_right : Measurable fun p : ∀ j : ({k} : Finset ι),
      β j => p ⟨k, Finset.mem_singleton_self k⟩ :=
    measurable_pi_apply _
  let s : Finset ι := {i, j}
  have h_left : (fun ω => (f i ω, f j ω)) = (fun p : ∀ l : s, β l =>
      (p ⟨i, Finset.mem_insert_self i _⟩,
        p ⟨j, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩)) ∘
        fun a (j : s) => f j a := by
    ext1 a
    simp only
    constructor
  have h_meas_left : Measurable fun p : ∀ l : s, β l =>
      (p ⟨i, Finset.mem_insert_self i _⟩,
        p ⟨j, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩) :=
    Measurable.prod (measurable_pi_apply _) (measurable_pi_apply _)
  rw [h_left, h_right]
  refine (hf_Indep.indepFun_finset s {k} ?_ hf_meas).comp h_meas_left h_meas_right
  rw [Finset.disjoint_singleton_right]
  simp only [s, Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨hik.symm, hjk.symm⟩

theorem iIndepFun.indepFun_prodMk₀ (hf_Indep : iIndepFun f κ μ)
    (hf_meas : ∀ i, AEMeasurable (f i) (κ ∘ₘ μ)) (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) :
    IndepFun (fun a ↦ (f i a, f j a)) (f k) κ μ := by
  have h : IndepFun (fun a ↦ ((hf_meas i).mk (f i) a, (hf_meas j).mk (f j) a))
      ((hf_meas k).mk (f k)) κ μ := by
    refine iIndepFun.indepFun_prodMk ?_ (fun i ↦ (hf_meas i).measurable_mk) _ _ _ hik hjk
    exact iIndepFun.congr' hf_Indep fun i ↦ Measure.ae_ae_of_ae_comp (hf_meas i).ae_eq_mk
  refine IndepFun.congr' h ?_ ?_
  · filter_upwards [Measure.ae_ae_of_ae_comp (hf_meas i).ae_eq_mk,
      Measure.ae_ae_of_ae_comp (hf_meas j).ae_eq_mk] with a hi hj
    filter_upwards [hi, hj] with ω hωi hωj
    rw [← hωi, ← hωj]
  · exact Measure.ae_ae_of_ae_comp (hf_meas k).ae_eq_mk.symm

open Finset in
lemma iIndepFun.indepFun_prodMk_prodMk (hf_indep : iIndepFun f κ μ)
    (hf_meas : ∀ i, Measurable (f i))
    (i j k l : ι) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    IndepFun (fun a ↦ (f i a, f j a)) (fun a ↦ (f k a, f l a)) κ μ := by
  classical
  let g (i j : ι) (v : Π x : ({i, j} : Finset ι), β x) : β i × β j :=
    ⟨v ⟨i, mem_insert_self _ _⟩, v ⟨j, mem_insert_of_mem <| mem_singleton_self _⟩⟩
  have hg (i j : ι) : Measurable (g i j) := by fun_prop
  exact (hf_indep.indepFun_finset {i, j} {k, l} (by aesop) hf_meas).comp (hg i j) (hg k l)

theorem iIndepFun.indepFun_prodMk_prodMk₀ (hf_indep : iIndepFun f κ μ)
    (hf_meas : ∀ i, AEMeasurable (f i) (κ ∘ₘ μ))
    (i j k l : ι) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    IndepFun (fun a ↦ (f i a, f j a)) (fun a ↦ (f k a, f l a)) κ μ := by
  have h : IndepFun (fun a ↦ ((hf_meas i).mk (f i) a, (hf_meas j).mk (f j) a))
      (fun a ↦ ((hf_meas k).mk (f k) a, (hf_meas l).mk (f l) a)) κ μ := by
    refine iIndepFun.indepFun_prodMk_prodMk ?_ (fun i ↦ (hf_meas i).measurable_mk) _ _ _ _ hik hil
      hjk hjl
    exact iIndepFun.congr' hf_indep fun i ↦ Measure.ae_ae_of_ae_comp (hf_meas i).ae_eq_mk
  refine IndepFun.congr' h ?_ ?_
  · filter_upwards [Measure.ae_ae_of_ae_comp (hf_meas i).ae_eq_mk,
      Measure.ae_ae_of_ae_comp (hf_meas j).ae_eq_mk] with a hi hj
    filter_upwards [hi, hj] with ω hωi hωj
    rw [← hωi, ← hωj]
  · filter_upwards [Measure.ae_ae_of_ae_comp (hf_meas k).ae_eq_mk,
      Measure.ae_ae_of_ae_comp (hf_meas l).ae_eq_mk] with a hk hl
    filter_upwards [hk, hl] with ω hωk hωl
    rw [← hωk, ← hωl]

end iIndepFun

section Mul
variable {β : Type*} {m : MeasurableSpace β} [Mul β] [MeasurableMul₂ β] {f : ι → Ω → β}

@[to_additive]
lemma iIndepFun.indepFun_mul_left (hf_indep : iIndepFun f κ μ)
    (hf_meas : ∀ i, Measurable (f i)) (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) :
    IndepFun (f i * f j) (f k) κ μ := by
  have : IndepFun (fun ω => (f i ω, f j ω)) (f k) κ μ :=
    hf_indep.indepFun_prodMk hf_meas i j k hik hjk
  simpa using this.comp (measurable_fst.mul measurable_snd) measurable_id

@[to_additive]
lemma iIndepFun.indepFun_mul_left₀ (hf_indep : iIndepFun f κ μ)
    (hf_meas : ∀ i, AEMeasurable (f i) (κ ∘ₘ μ)) (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) :
    IndepFun (f i * f j) (f k) κ μ := by
  have : IndepFun (fun ω => (f i ω, f j ω)) (f k) κ μ :=
    hf_indep.indepFun_prodMk₀ hf_meas i j k hik hjk
  simpa using this.comp (measurable_fst.mul measurable_snd) measurable_id

@[to_additive]
lemma iIndepFun.indepFun_mul_right (hf_indep : iIndepFun f κ μ)
    (hf_meas : ∀ i, Measurable (f i)) (i j k : ι) (hij : i ≠ j) (hik : i ≠ k) :
    IndepFun (f i) (f j * f k) κ μ :=
  (hf_indep.indepFun_mul_left hf_meas _ _ _ hij.symm hik.symm).symm

@[to_additive]
lemma iIndepFun.indepFun_mul_right₀ (hf_indep : iIndepFun f κ μ)
    (hf_meas : ∀ i, AEMeasurable (f i) (κ ∘ₘ μ)) (i j k : ι) (hij : i ≠ j) (hik : i ≠ k) :
    IndepFun (f i) (f j * f k) κ μ :=
  (hf_indep.indepFun_mul_left₀ hf_meas _ _ _ hij.symm hik.symm).symm

@[to_additive]
lemma iIndepFun.indepFun_mul_mul (hf_indep : iIndepFun f κ μ)
    (hf_meas : ∀ i, Measurable (f i))
    (i j k l : ι) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    IndepFun (f i * f j) (f k * f l) κ μ :=
  (hf_indep.indepFun_prodMk_prodMk hf_meas i j k l hik hil hjk hjl).comp
    measurable_mul measurable_mul

@[to_additive]
lemma iIndepFun.indepFun_mul_mul₀ (hf_indep : iIndepFun f κ μ)
    (hf_meas : ∀ i, AEMeasurable (f i) (κ ∘ₘ μ))
    (i j k l : ι) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    IndepFun (f i * f j) (f k * f l) κ μ :=
  (hf_indep.indepFun_prodMk_prodMk₀ hf_meas i j k l hik hil hjk hjl).comp
    measurable_mul measurable_mul

end Mul

section Div
variable {β : Type*} {m : MeasurableSpace β} [Div β] [MeasurableDiv₂ β] {f : ι → Ω → β}

@[to_additive]
lemma iIndepFun.indepFun_div_left (hf_indep : iIndepFun f κ μ)
    (hf_meas : ∀ i, Measurable (f i)) (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) :
    IndepFun (f i / f j) (f k) κ μ := by
  have : IndepFun (fun ω => (f i ω, f j ω)) (f k) κ μ :=
    hf_indep.indepFun_prodMk hf_meas i j k hik hjk
  simpa using this.comp (measurable_fst.div measurable_snd) measurable_id

@[to_additive]
lemma iIndepFun.indepFun_div_left₀ (hf_indep : iIndepFun f κ μ)
    (hf_meas : ∀ i, AEMeasurable (f i) (κ ∘ₘ μ)) (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) :
    IndepFun (f i / f j) (f k) κ μ := by
  have : IndepFun (fun ω => (f i ω, f j ω)) (f k) κ μ :=
    hf_indep.indepFun_prodMk₀ hf_meas i j k hik hjk
  simpa using this.comp (measurable_fst.div measurable_snd) measurable_id

@[to_additive]
lemma iIndepFun.indepFun_div_right (hf_indep : iIndepFun f κ μ)
    (hf_meas : ∀ i, Measurable (f i)) (i j k : ι) (hij : i ≠ j) (hik : i ≠ k) :
    IndepFun (f i) (f j / f k) κ μ :=
  (hf_indep.indepFun_div_left hf_meas _ _ _ hij.symm hik.symm).symm

@[to_additive]
lemma iIndepFun.indepFun_div_right₀ (hf_indep : iIndepFun f κ μ)
    (hf_meas : ∀ i, AEMeasurable (f i) (κ ∘ₘ μ)) (i j k : ι) (hij : i ≠ j) (hik : i ≠ k) :
    IndepFun (f i) (f j / f k) κ μ :=
  (hf_indep.indepFun_div_left₀ hf_meas _ _ _ hij.symm hik.symm).symm

@[to_additive]
lemma iIndepFun.indepFun_div_div (hf_indep : iIndepFun f κ μ)
    (hf_meas : ∀ i, Measurable (f i))
    (i j k l : ι) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    IndepFun (f i / f j) (f k / f l) κ μ :=
  (hf_indep.indepFun_prodMk_prodMk hf_meas i j k l hik hil hjk hjl).comp
    measurable_div measurable_div

@[to_additive]
lemma iIndepFun.indepFun_div_div₀ (hf_indep : iIndepFun f κ μ)
    (hf_meas : ∀ i, AEMeasurable (f i) (κ ∘ₘ μ))
    (i j k l : ι) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    IndepFun (f i / f j) (f k / f l) κ μ :=
  (hf_indep.indepFun_prodMk_prodMk₀ hf_meas i j k l hik hil hjk hjl).comp
    measurable_div measurable_div

end Div

section CommMonoid
variable {β : Type*} {m : MeasurableSpace β} [CommMonoid β] [MeasurableMul₂ β] {f : ι → Ω → β}

@[to_additive]
theorem iIndepFun.indepFun_finset_prod_of_notMem (hf_Indep : iIndepFun f κ μ)
    (hf_meas : ∀ i, Measurable (f i)) {s : Finset ι} {i : ι} (hi : i ∉ s) :
    IndepFun (∏ j ∈ s, f j) (f i) κ μ := by
  classical
  have h_right : f i =
    (fun p : ({i} : Finset ι) → β => p ⟨i, Finset.mem_singleton_self i⟩) ∘
    fun a (j : ({i} : Finset ι)) => f j a := rfl
  have h_meas_right : Measurable fun p : ({i} : Finset ι) → β =>
      p ⟨i, Finset.mem_singleton_self i⟩ := measurable_pi_apply _
  have h_left : ∏ j ∈ s, f j = (fun p : s → β => ∏ j, p j) ∘ fun a (j : s) => f j a := by
    ext1 a
    simp only [Function.comp_apply]
    have : (∏ j : ↥s, f (↑j) a) = (∏ j : ↥s, f ↑j) a := by rw [Finset.prod_apply]
    rw [this, Finset.prod_coe_sort]
  have h_meas_left : Measurable fun p : s → β => ∏ j, p j :=
    Finset.univ.measurable_fun_prod fun (j : ↥s) (_H : j ∈ Finset.univ) => measurable_pi_apply j
  rw [h_left, h_right]
  exact
    (hf_Indep.indepFun_finset s {i} (Finset.disjoint_singleton_left.mpr hi).symm hf_meas).comp
      h_meas_left h_meas_right

@[to_additive]
theorem iIndepFun.indepFun_finset_prod_of_notMem₀ (hf_Indep : iIndepFun f κ μ)
    (hf_meas : ∀ i, AEMeasurable (f i) (κ ∘ₘ μ)) {s : Finset ι} {i : ι} (hi : i ∉ s) :
    IndepFun (∏ j ∈ s, f j) (f i) κ μ := by
  have h : IndepFun (∏ j ∈ s, (hf_meas j).mk (f j)) ((hf_meas i).mk (f i)) κ μ := by
    refine iIndepFun.indepFun_finset_prod_of_notMem ?_ (fun i ↦ (hf_meas i).measurable_mk) hi
    exact iIndepFun.congr' hf_Indep fun i ↦ Measure.ae_ae_of_ae_comp (hf_meas i).ae_eq_mk
  refine IndepFun.congr' h ?_ ?_
  · have : ∀ᵐ a ∂μ, ∀ (i : s), f i =ᵐ[κ a] (hf_meas i).mk := by
      rw [ae_all_iff]
      exact fun i ↦ Measure.ae_ae_of_ae_comp (hf_meas i).ae_eq_mk
    filter_upwards [this] with a ha
    filter_upwards [ae_all_iff.2 ha] with ω hω
    simp only [Finset.prod_apply]
    exact Finset.prod_congr rfl fun i hi ↦ (hω ⟨i, hi⟩).symm
  · exact Measure.ae_ae_of_ae_comp (hf_meas i).ae_eq_mk.symm


@[to_additive]
theorem iIndepFun.indepFun_prod_range_succ {f : ℕ → Ω → β}
    (hf_Indep : iIndepFun f κ μ) (hf_meas : ∀ i, Measurable (f i)) (n : ℕ) :
    IndepFun (∏ j ∈ Finset.range n, f j) (f n) κ μ :=
  hf_Indep.indepFun_finset_prod_of_notMem hf_meas Finset.notMem_range_self

@[to_additive]
theorem iIndepFun.indepFun_prod_range_succ₀ {f : ℕ → Ω → β}
    (hf_Indep : iIndepFun f κ μ) (hf_meas : ∀ i, AEMeasurable (f i) (κ ∘ₘ μ)) (n : ℕ) :
    IndepFun (∏ j ∈ Finset.range n, f j) (f n) κ μ :=
  hf_Indep.indepFun_finset_prod_of_notMem₀ hf_meas Finset.notMem_range_self

end CommMonoid

theorem iIndepSet.iIndepFun_indicator [Zero β] [One β] {m : MeasurableSpace β} {s : ι → Set Ω}
    (hs : iIndepSet s κ μ) :
    iIndepFun (fun n => (s n).indicator fun _ω => (1 : β)) κ μ := by
  classical
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  rintro S π _hπ
  simp_rw [Set.indicator_const_preimage_eq_union]
  apply hs _ fun i _hi ↦ ?_
  have hsi : MeasurableSet[generateFrom {s i}] (s i) :=
    measurableSet_generateFrom (Set.mem_singleton _)
  refine
    MeasurableSet.union (MeasurableSet.ite' (fun _ => hsi) fun _ => ?_)
      (MeasurableSet.ite' (fun _ => hsi.compl) fun _ => ?_)
  · exact @MeasurableSet.empty _ (generateFrom {s i})
  · exact @MeasurableSet.empty _ (generateFrom {s i})

variable {mβ : MeasurableSpace β} {X : ι → Ω → α} {Y : ι → Ω → β}
  {f : _ → Set Ω} {t : ι → Set β} {s : Finset ι}

/-- The probability of an intersection of preimages conditioning on another intersection factors
into a product. -/
lemma iIndepFun.cond_iInter [Finite ι] (hY : ∀ i, Measurable (Y i))
    (hindep : iIndepFun (fun i ω ↦ (X i ω, Y i ω)) κ μ)
    (hf : ∀ i ∈ s, MeasurableSet[mα.comap (X i)] (f i))
    (hy : ∀ᵐ a ∂μ, ∀ i ∉ s, κ a (Y i ⁻¹' t i) ≠ 0) (ht : ∀ i, MeasurableSet (t i)) :
    ∀ᵐ a ∂μ, (κ a)[⋂ i ∈ s, f i | ⋂ i, Y i ⁻¹' t i] = ∏ i ∈ s, (κ a)[f i | Y i in t i] := by
  classical
  cases nonempty_fintype ι
  let g (i' : ι) := if i' ∈ s then Y i' ⁻¹' t i' ∩ f i' else Y i' ⁻¹' t i'
  have hYt i : MeasurableSet[(mα.prod mβ).comap fun ω ↦ (X i ω, Y i ω)] (Y i ⁻¹' t i) :=
    ⟨.univ ×ˢ t i, .prod .univ (ht _), by ext; simp⟩
  have hg i : MeasurableSet[(mα.prod mβ).comap fun ω ↦ (X i ω, Y i ω)] (g i) := by
    by_cases hi : i ∈ s <;> simp only [hi, ↓reduceIte, g]
    · obtain ⟨A, hA, hA'⟩ := hf i hi
      exact (hYt _).inter ⟨A ×ˢ .univ, hA.prod .univ, by ext; simp [← hA']⟩
    · exact hYt _
  filter_upwards [hy, hindep.ae_isProbabilityMeasure, hindep.meas_iInter hYt, hindep.meas_iInter hg]
    with a hy _ hYt hg
  calc
    _ = (κ a (⋂ i, Y i ⁻¹' t i))⁻¹ * κ a ((⋂ i, Y i ⁻¹' t i) ∩ ⋂ i ∈ s, f i) := by
      rw [cond_apply]; exact .iInter fun i ↦ hY i (ht i)
    _ = (κ a (⋂ i, Y i ⁻¹' t i))⁻¹ * κ a (⋂ i, g i) := by
      congr 2
      calc
        _ = (⋂ i, Y i ⁻¹' t i) ∩ ⋂ i, if i ∈ s then f i else .univ := by
          congr 1
          simp only [Set.iInter_ite, Set.iInter_univ, Set.inter_univ]
        _ = ⋂ i, Y i ⁻¹' t i ∩ (if i ∈ s then f i else .univ) := by rw [Set.iInter_inter_distrib]
        _ = _ := Set.iInter_congr fun i ↦ by by_cases hi : i ∈ s <;> simp [hi, g]
    _ = (∏ i, κ a (Y i ⁻¹' t i))⁻¹ * κ a (⋂ i, g i) := by
      rw [hYt]
    _ = (∏ i, κ a (Y i ⁻¹' t i))⁻¹ * ∏ i, κ a (g i) := by
      rw [hg]
    _ = ∏ i, (κ a (Y i ⁻¹' t i))⁻¹ * κ a (g i) := by
      rw [Finset.prod_mul_distrib, ENNReal.prod_inv_distrib]
      exact fun _ _ i _ _ ↦ .inr <| measure_ne_top _ _
    _ = ∏ i, if i ∈ s then (κ a)[f i | Y i ⁻¹' t i] else 1 := by
      refine Finset.prod_congr rfl fun i _ ↦ ?_
      by_cases hi : i ∈ s
      · simp only [hi, ↓reduceIte, g, cond_apply (hY i (ht i))]
      · simp only [hi, ↓reduceIte, g, ENNReal.inv_mul_cancel (hy i hi) (measure_ne_top _ _)]
    _ = _ := by simp

-- TODO: We can't state `Kernel.iIndepFun.cond` (the `Kernel` analogue of
-- `ProbabilityTheory.iIndepFun.cond`) because we don't have a version of `ProbabilityTheory.cond`
-- for kernels

end ProbabilityTheory.Kernel
