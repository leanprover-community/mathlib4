/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Independence.Conditional.CondIndep
public import Mathlib.MeasureTheory.MeasurableSpace.Pi

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


variable {ι ι' Ω γ γ' β β' : Type*} {mΩ₀ : MeasurableSpace Ω}

section Definitions

/-- A family of functions defined on the same space `Ω` and taking values in possibly different
spaces, each with a measurable space structure, is independent if the family of measurable space
structures they generate on `Ω` is independent. For a function `g` with codomain having measurable
space structure `m`, the generated measurable space structure is `MeasurableSpace.comap g m`. -/
def iCondIndepFun (P : Measure[mΩ₀] Ω := by volume_tac) (mΩ : MeasurableSpace Ω) {β : ι → Type*}
    [m : ∀ x : ι, MeasurableSpace (β x)] (f : ∀ x : ι, Ω → β x)  : Prop :=
  iCondIndep P mΩ (m := fun x ↦ MeasurableSpace.comap (f x) (m x))

/-- Two functions are independent if the two measurable space structures they generate are
independent. For a function `f` with codomain having measurable space structure `m`, the generated
measurable space structure is `MeasurableSpace.comap f m`. -/
def CondIndepFun (P : Measure[mΩ₀] Ω := by volume_tac) (mΩ : MeasurableSpace Ω)
    [mβ : MeasurableSpace β] [mγ : MeasurableSpace γ] (f : Ω → β) (g : Ω → γ) : Prop :=
  CondIndep P mΩ (MeasurableSpace.comap f mβ) (MeasurableSpace.comap g mγ)

end Definitions

section ByDefinition

-- variable {β : ι → Type*} {mβ : ∀ i, MeasurableSpace (β i)}
--   {_mα : MeasurableSpace α} {m : ι → MeasurableSpace Ω} {_mΩ : MeasurableSpace Ω}
--   {κ η : Kernel α Ω} {μ : Measure α}
--   {π : ι → Set (Set Ω)} {s : ι → Set Ω} {S : Finset ι} {f : ∀ x : ι, Ω → β x}
--   {s1 s2 : Set (Set Ω)} {ι' : Type*} {g : ι' → ι}

-- @[simp] lemma iIndepFun_zero_right {β : ι → Type*} {m : ∀ x : ι, MeasurableSpace (β x)}
--     {f : ∀ x : ι, Ω → β x} : iIndepFun f κ 0 := by simp [iIndepFun]

-- @[simp] lemma indepFun_zero_right {β} [MeasurableSpace β] [MeasurableSpace γ]
--     {f : Ω → β} {g : Ω → γ} : IndepFun f g κ 0 := by simp [IndepFun]

-- @[simp] lemma indepFun_zero_left {β} [MeasurableSpace β] [MeasurableSpace γ]
--     {f : Ω → β} {g : Ω → γ} : IndepFun f g (0 : Kernel α Ω) μ := by simp [IndepFun]

-- lemma iIndepFun_congr {β : ι → Type*} {m : ∀ x : ι, MeasurableSpace (β x)}
--     {f : ∀ x : ι, Ω → β x} (h : κ =ᵐ[μ] η) : iIndepFun f κ μ ↔ iIndepFun f η μ :=
--   iIndep_congr h

-- alias ⟨iIndepFun.congr, _⟩ := iIndepFun_congr

-- lemma indepFun_congr {β} [MeasurableSpace β] [MeasurableSpace γ]
--     {f : Ω → β} {g : Ω → γ} (h : κ =ᵐ[μ] η) : IndepFun f g κ μ ↔ IndepFun f g η μ :=
--   indep_congr h

-- alias ⟨IndepFun.congr, _⟩ := indepFun_congr

variable {P : Measure[mΩ₀] Ω} {mΩ : MeasurableSpace Ω} {S : Finset ι} {s : ι → Set Ω}
  {β : ι → Type*} {m : ∀ i, MeasurableSpace (β i)} {f : ∀ i, Ω → β i} {g : ι' → ι}

@[nontriviality, simp]
lemma iCondIndepFun.of_subsingleton (hm : mΩ ≤ mΩ₀) [SigmaFinite (P.trim hm)] [Subsingleton ι] :
    iCondIndepFun P mΩ f := by simp [iCondIndepFun, hm]

protected lemma iCondIndepFun.iCondIndep (hf : iCondIndepFun P mΩ f) :
    iCondIndep P mΩ (fun x ↦ (m x).comap (f x)) := hf

lemma iCondIndepFun.meas_biInter (hf : iCondIndepFun P mΩ f)
    (hs : ∀ i, i ∈ S → MeasurableSet[(m i).comap (f i)] (s i)) :
    P⁻⸨⋂ i ∈ S, s i| mΩ⸩ =ᵐ[P] ∏ i ∈ S, P⁻⸨s i| mΩ⸩ := hf.iCondIndep.meas_biInter hs

lemma iCondIndepFun.meas_iInter [Fintype ι] (hf : iCondIndepFun P mΩ f)
    (hs : ∀ i, MeasurableSet[(m i).comap (f i)] (s i)) :
    P⁻⸨⋂ i, s i| mΩ⸩ =ᵐ[P] ∏ i, P⁻⸨s i| mΩ⸩ := hf.iCondIndep.meas_iInter hs

lemma CondIndepFun.meas_inter {β} [mβ : MeasurableSpace β] [mγ : MeasurableSpace γ]
    {f : Ω → β} {g : Ω → γ} (hfg : CondIndepFun P mΩ f g)
    {s t : Set Ω} (hs : MeasurableSet[mβ.comap f] s) (ht : MeasurableSet[mγ.comap g] t) :
    P⁻⸨s ∩ t| mΩ⸩ =ᵐ[P] P⁻⸨s| mΩ⸩ * P⁻⸨t| mΩ⸩ := hfg _ _ hs ht

lemma iCondIndepFun.precomp (hg : Function.Injective g) (h : iCondIndepFun P mΩ f) :
    iCondIndepFun P mΩ (fun i ↦ f (g i)) :=
  iCondIndep.precomp hg h

lemma iCondIndepFun.of_precomp (hg : Function.Surjective g)
    (h : iCondIndepFun P mΩ (fun i ↦ f (g i))) :
    iCondIndepFun P mΩ f :=
  iCondIndep.of_precomp hg h

lemma iCondIndepFun_precomp_of_bijective (hg : Function.Bijective g) :
    iCondIndepFun P mΩ (fun i ↦ f (g i))  ↔ iCondIndepFun P mΩ f :=
  ⟨.of_precomp hg.surjective, .precomp hg.injective⟩

end ByDefinition

variable {P : Measure[mΩ₀] Ω} {mΩ : MeasurableSpace Ω} {f : Ω → β} {g : Ω → β'}

-- {S : Finset ι} {s : ι → Set Ω}
-- {β : ι → Type*} {m : ∀ i, MeasurableSpace (β i)} {f : ∀ i, Ω → β i} {g : ι' → ι}

theorem iCondIndepFun.condIndepFun {β : ι → Type*} {m : ∀ x, MeasurableSpace (β x)}
    {f : ∀ i, Ω → β i} (hf_Indep : iCondIndepFun P mΩ f) {i j : ι} (hij : i ≠ j) :
    CondIndepFun P mΩ (f i) (f j) :=
  hf_Indep.condIndep hij

theorem condIndepFun_iff_measure_inter_preimage_eq_mul {mβ : MeasurableSpace β}
    {mβ' : MeasurableSpace β'} :
    CondIndepFun P mΩ f g  ↔
      ∀ s t, MeasurableSet s → MeasurableSet t
        → P⁻⸨f ⁻¹' s ∩ g ⁻¹' t| mΩ⸩ =ᵐ[P] P⁻⸨f ⁻¹' s| mΩ⸩ * P⁻⸨g ⁻¹' t| mΩ⸩ := by
  constructor <;> intro h
  · refine fun s t hs ht => h (f ⁻¹' s) (g ⁻¹' t) ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
  · rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩; exact h s t hs ht

alias ⟨CondIndepFun.measure_inter_preimage_eq_mul, _⟩ :=
  condIndepFun_iff_measure_inter_preimage_eq_mul

theorem iCondIndepFun_iff_measure_inter_preimage_eq_mul {ι : Type*} {β : ι → Type*}
    (m : ∀ x, MeasurableSpace (β x)) (f : ∀ i, Ω → β i) :
    iCondIndepFun P mΩ f ↔
      ∀ (S : Finset ι) {s : ∀ i : ι, Set (β i)} (_H : ∀ i, i ∈ S → MeasurableSet[m i] (s i)),
        P⁻⸨⋂ i ∈ S, (f i) ⁻¹' (s i)| mΩ⸩ =ᵐ[P] ∏ i ∈ S, P⁻⸨(f i) ⁻¹' (s i)| mΩ⸩  := by
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

alias ⟨iCondIndepFun.measure_inter_preimage_eq_mul, _⟩ :=
  iCondIndepFun_iff_measure_inter_preimage_eq_mul

lemma iCondIndepFun.comp {β γ : ι → Type*} {mβ : ∀ i, MeasurableSpace (β i)}
    {mγ : ∀ i, MeasurableSpace (γ i)} {f : ∀ i, Ω → β i}
    (h : iCondIndepFun P mΩ f) (g : ∀ i, β i → γ i) (hg : ∀ i, Measurable (g i)) :
    iCondIndepFun P mΩ (fun i ↦ g i ∘ f i) := by
  rw [iCondIndepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  refine fun t s hs ↦ ?_
  have := h t (s := fun i ↦ g i ⁻¹' (s i)) (fun i a ↦ hg i (hs i a))
  filter_upwards [this] with a ha
  simp_rw [Set.preimage_comp]
  exact ha

set_option backward.isDefEq.respectTransparency false in
theorem iCondIndepFun.congr' {β : ι → Type*} {mβ : ∀ i, MeasurableSpace (β i)}
    {f g : Π i, Ω → β i} (hf : iCondIndepFun P mΩ f) (h : ∀ i, f i =ᵐ[P] g i) :
    iCondIndepFun P mΩ g := by
  rw [iCondIndepFun_iff_measure_inter_preimage_eq_mul] at hf ⊢
  intro S sets hmeas
  have : ∀ᵐ ω ∂P, ∀ i ∈ S, f i ω = g i ω := by
    rw [eventually_finset_ball]
    intro i _
    exact h i
  have h' : ∀ᵐ ω ∂P, ∀ i ∈ S, (P⁻⸨g i ⁻¹' sets i| mΩ⸩) ω = (P⁻⸨f i ⁻¹' sets i| mΩ⸩) ω := by
    rw [eventually_finset_ball]
    intro i _
    apply condLExp_congr_ae
    sorry
     -- need condLExp and condLProb theorems
  have h'' : P⁻⸨⋂ i ∈ S, g i ⁻¹' sets i| mΩ⸩ =ᵐ[P] P⁻⸨⋂ i ∈ S, f i ⁻¹' sets i| mΩ⸩ := by
    gcongr
    sorry
  filter_upwards [h', h'', hf S hmeas] with ω hω h'ω h''ω
  rw [h'ω, h''ω, Finset.prod_apply, Finset.prod_apply]
  exact Finset.prod_congr rfl (fun i hi ↦ by simp [hω i hi])

theorem iCondIndepFun_congr' {β : ι → Type*} {mβ : ∀ i, MeasurableSpace (β i)}
    {f g : Π i, Ω → β i} (h : ∀ i, f i =ᵐ[P] g i) :
    iCondIndepFun P mΩ f ↔ iCondIndepFun P mΩ g :=
  ⟨fun h' ↦ iCondIndepFun.congr' h' h, fun h' ↦ iCondIndepFun.congr' h' (fun i ↦ h i |>.symm)⟩

lemma iCondIndepFun.comp₀ {β γ : ι → Type*} {mβ : ∀ i, MeasurableSpace (β i)}
    {mγ : ∀ i, MeasurableSpace (γ i)} {f : ∀ i, Ω → β i}
    (h : iCondIndepFun P mΩ f) (g : ∀ i, β i → γ i)
    (hf : ∀ i, AEMeasurable[mΩ₀] (f i) P)
    (hg : ∀ i, AEMeasurable[mβ i] (g i) (@Measure.map _ _ mΩ₀ _ (f i) P)) :
    iCondIndepFun P mΩ (fun i ↦ g i ∘ f i) := by
  have h : iCondIndepFun P mΩ (fun i ↦ ((hg i).mk (g i)) ∘ f i) :=
    iCondIndepFun.comp h (fun i ↦ (hg i).mk (g i)) fun i ↦ (hg i).measurable_mk
  have h_ae i := ae_of_ae_map (hf i) (hg i).ae_eq_mk.symm
  refine iCondIndepFun.congr' h fun i ↦ ?_
  -- TODO: more appropriate fn
  exact Measure.AbsolutelyContinuous.ae_eq (fun ⦃s⦄ a ↦ a) (h_ae i)

theorem condIndepFun_iff_indepSet_preimage (hm : mΩ ≤ mΩ₀) [SigmaFinite (P.trim hm)]
    {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    (hf : Measurable[mΩ₀] f) (hg : Measurable[mΩ₀] g) :
    CondIndepFun P mΩ f g ↔
      ∀ s t, MeasurableSet s → MeasurableSet t → CondIndepSet P mΩ (f ⁻¹' s) (g ⁻¹' t) := by
  refine condIndepFun_iff_measure_inter_preimage_eq_mul.trans ?_
  constructor <;> intro h s t hs ht <;> specialize h s t hs ht
  · rwa [condIndepSet_iff_measure_inter_eq_mul hm (hf hs) (hg ht)]
  · rwa [← condIndepSet_iff_measure_inter_eq_mul hm (hf hs) (hg ht)]

@[symm]
nonrec theorem CondIndepFun.symm {_ : MeasurableSpace β} {_ : MeasurableSpace β'}
    (hfg : CondIndepFun P mΩ f g) : CondIndepFun P mΩ g f := hfg.symm

theorem CondIndepFun.congr' {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    {f' : Ω → β} {g' : Ω → β'} (hfg : CondIndepFun P mΩ f g)
    (hf : f =ᵐ[P] f') (hg : g =ᵐ[P] g') :
    CondIndepFun P mΩ f' g' := by
  rintro _ _ ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩
  sorry

  -- filter_upwards [hf, hg, hfg _ _ ⟨_, hA, rfl⟩ ⟨_, hB, rfl⟩] with a hf' hg' hfg'
  -- have h1 : f ⁻¹' A = f' ⁻¹' A := by sorry -- hf'.fun_comp A
  -- have h2 : g ⁻¹' B = g' ⁻¹' B := by sorry --hg'.fun_comp B
  -- rw [← h2, ← h1, hfg']

theorem CondIndepFun.comp {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    {mγ : MeasurableSpace γ} {mγ' : MeasurableSpace γ'} {φ : β → γ} {ψ : β' → γ'}
    (hfg : CondIndepFun P mΩ f g) (hφ : Measurable φ) (hψ : Measurable ψ) :
    CondIndepFun P mΩ (φ ∘ f) (ψ ∘ g) := by
  rintro _ _ ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩
  apply hfg
  · exact ⟨φ ⁻¹' A, hφ hA, Set.preimage_comp.symm⟩
  · exact ⟨ψ ⁻¹' B, hψ hB, Set.preimage_comp.symm⟩

theorem CondIndepFun.comp₀ {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    {mγ : MeasurableSpace γ} {mγ' : MeasurableSpace γ'} {φ : β → γ} {ψ : β' → γ'}
    (hfg : CondIndepFun P mΩ f g)
    (hf : AEMeasurable f P) (hg : AEMeasurable g P)
    (hφ : AEMeasurable φ (@Measure.map _ _ mΩ₀ _ f P))
    (hψ : AEMeasurable ψ (@Measure.map _ _ mΩ₀ _ g P)) :
    CondIndepFun P mΩ (φ ∘ f) (ψ ∘ g) := by
  have h : CondIndepFun P mΩ ((hφ.mk φ) ∘ f) ((hψ.mk ψ) ∘ g) := by
    refine CondIndepFun.comp hfg hφ.measurable_mk hψ.measurable_mk
  have hφ_ae := ae_of_ae_map hf hφ.ae_eq_mk
  have hψ_ae := ae_of_ae_map hg hψ.ae_eq_mk
  refine CondIndepFun.congr' h ?_ ?_
  -- TODO: Better exact proofs
  · exact Filter.EventuallyEq.symm (Measure.AbsolutelyContinuous.ae_eq (fun ⦃s⦄ a ↦ a) hφ_ae)
  · exact Filter.EventuallyEq.symm (Measure.AbsolutelyContinuous.ae_eq (fun ⦃s⦄ a ↦ a) hψ_ae)

lemma condIndepFun_const_left (hm : mΩ ≤ mΩ₀) [SigmaFinite (P.trim hm)]
    {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'} (c : β') (X : Ω → β) :
    CondIndepFun P mΩ (fun _ ↦ c) X := by
  rw [CondIndepFun, MeasurableSpace.comap_const]
  exact condIndep_bot_left hm _

lemma condIndepFun_const_right (hm : mΩ ≤ mΩ₀) [SigmaFinite (P.trim hm)]
    {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'} (X : Ω → β) (c : β') :
    CondIndepFun P mΩ X (fun _ ↦ c) :=
  (condIndepFun_const_left hm c X).symm

theorem CondIndepFun.neg_right {_mβ : MeasurableSpace β} {_mβ' : MeasurableSpace β'} [Neg β']
    [MeasurableNeg β'] (hfg : CondIndepFun P mΩ f g) :
    CondIndepFun P mΩ f (-g) := hfg.comp measurable_id measurable_neg

theorem CondIndepFun.neg_left {_mβ : MeasurableSpace β} {_mβ' : MeasurableSpace β'} [Neg β]
    [MeasurableNeg β] (hfg : CondIndepFun P mΩ f g) :
    CondIndepFun P mΩ (-f) g := hfg.comp measurable_neg measurable_id

section iIndepFun
variable {β : ι → Type*} {m : ∀ i, MeasurableSpace (β i)} {f : ∀ i, Ω → β i}

set_option backward.isDefEq.respectTransparency false in
/-- If `f` is a family of mutually independent random variables (`iIndepFun m f μ`) and `S, T` are
two disjoint finite index sets, then the tuple formed by `f i` for `i ∈ S` is independent of the
tuple `(f i)_i` for `i ∈ T`. -/
theorem iCondIndepFun.condIndepFun_finset (hm : mΩ ≤ mΩ₀) [SigmaFinite (P.trim hm)] (S T : Finset ι)
    (hST : Disjoint S T) (hf_Indep : iCondIndepFun P mΩ f) (hf_meas : ∀ i, Measurable[mΩ₀] (f i)) :
    CondIndepFun P mΩ (fun a (i : S) => f i a) (fun a (i : T) => f i a) := by
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
  refine CondIndepSets.condIndep hm (Measurable.comap_le (by measurability))
    (Measurable.comap_le (by measurability)) hπS_pi hπT_pi hπS_gen hπT_gen ?_
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
  rw [iCondIndepFun_iff_measure_inter_preimage_eq_mul] at hf_Indep
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
  rw [h_eq_inter_S, h_eq_inter_T, Pi.mul_apply, h_indepS, h_indepT, h_Inter_inter, h_indepST,
    Finset.prod_union hST]
  simp only [Pi.mul_apply, Finset.prod_apply]
  congr 1
  · exact Finset.prod_congr rfl fun i hi => by simp [h_sets_t'_univ hi]
  · exact Finset.prod_congr rfl fun i hi => by simp [h_sets_s'_univ hi]

theorem iCondIndepFun.condIndepFun_finset₀ (hm : mΩ ≤ mΩ₀) [SigmaFinite (P.trim hm)]
    (S T : Finset ι) (hST : Disjoint S T)
    (hf_Indep : iCondIndepFun P mΩ f) (hf_meas : ∀ i, AEMeasurable (f i) P) :
    CondIndepFun P mΩ (fun a (i : S) ↦ f i a) (fun a (i : T) ↦ f i a) := by
  have h : CondIndepFun P mΩ (fun a (i : S) ↦ (hf_meas i).mk (f i) a)
      (fun a (i : T) ↦ (hf_meas i).mk (f i) a) := by
    refine iCondIndepFun.condIndepFun_finset hm S T hST ?_ fun i ↦ (hf_meas i).measurable_mk
    exact iCondIndepFun.congr' hf_Indep fun i ↦ AEMeasurable.ae_eq_mk (hf_meas i)
  refine CondIndepFun.congr' h ?_ ?_
  · have : ∀ᵐ ω ∂P, ∀ (i : S), f i ω = (hf_meas i).mk _ ω := by
      rw [ae_all_iff]
      refine fun i ↦ AEMeasurable.ae_eq_mk (hf_meas i)
    filter_upwards [this] with a ha
    ext i
    exact (ha i).symm
  · have : ∀ᵐ ω ∂P, ∀ (i : T), f i ω = (hf_meas i).mk _ ω := by
      rw [ae_all_iff]
      refine fun i ↦ AEMeasurable.ae_eq_mk (hf_meas i)
    filter_upwards [this] with a ha
    ext i
    exact (ha i).symm

theorem iCondIndepFun.condIndepFun_prodMk (hm : mΩ ≤ mΩ₀) [SigmaFinite (P.trim hm)]
    (hf_Indep : iCondIndepFun P mΩ f) (hf_meas : ∀ i, Measurable[mΩ₀] (f i))
    (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) :
    CondIndepFun P mΩ (fun a => (f i a, f j a)) (f k) := by
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
  refine (hf_Indep.condIndepFun_finset hm s {k} ?_ hf_meas).comp h_meas_left h_meas_right
  rw [Finset.disjoint_singleton_right]
  simp only [s, Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨hik.symm, hjk.symm⟩

theorem iCondIndepFun.condIndepFun_prodMk₀ (hm : mΩ ≤ mΩ₀) [SigmaFinite (P.trim hm)]
    (hf_Indep : iCondIndepFun P mΩ f) (hf_meas : ∀ i, AEMeasurable (f i) P)
    (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) :
    CondIndepFun P mΩ (fun a ↦ (f i a, f j a)) (f k) := by
  have h : CondIndepFun P mΩ (fun a ↦ ((hf_meas i).mk (f i) a, (hf_meas j).mk (f j) a))
      ((hf_meas k).mk (f k)) := by
    refine iCondIndepFun.condIndepFun_prodMk hm ?_ (fun i ↦ (hf_meas i).measurable_mk) _ _ _ hik hjk
    exact iCondIndepFun.congr' hf_Indep fun i ↦ AEMeasurable.ae_eq_mk (hf_meas i)
  refine CondIndepFun.congr' h ?_ ?_
  · exact Filter.EventuallyEq.prodMk (hf_meas i).ae_eq_mk.symm (hf_meas j).ae_eq_mk.symm
  · exact (hf_meas k).ae_eq_mk.symm

open Finset in
lemma iCondIndepFun.condIndepFun_prodMk_prodMk (hm : mΩ ≤ mΩ₀) [SigmaFinite (P.trim hm)]
    (hf_indep : iCondIndepFun P mΩ f) (hf_meas : ∀ i, Measurable[mΩ₀] (f i))
    (i j k l : ι) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    CondIndepFun P mΩ (fun a ↦ (f i a, f j a)) (fun a ↦ (f k a, f l a)) := by
  classical
  let g (i j : ι) (v : Π x : ({i, j} : Finset ι), β x) : β i × β j :=
    ⟨v ⟨i, mem_insert_self _ _⟩, v ⟨j, mem_insert_of_mem <| mem_singleton_self _⟩⟩
  have hg (i j : ι) : Measurable (g i j) := by fun_prop
  exact (hf_indep.condIndepFun_finset hm {i, j} {k, l} (by aesop) hf_meas).comp (hg i j) (hg k l)

theorem iCondIndepFun.condIndepFun_prodMk_prodMk₀ (hm : mΩ ≤ mΩ₀) [SigmaFinite (P.trim hm)]
    (hf_indep : iCondIndepFun P mΩ f) (hf_meas : ∀ i, AEMeasurable (f i) P)
    (i j k l : ι) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    CondIndepFun P mΩ (fun a ↦ (f i a, f j a)) (fun a ↦ (f k a, f l a)) := by
  have h : CondIndepFun P mΩ (fun a ↦ ((hf_meas i).mk (f i) a, (hf_meas j).mk (f j) a))
      (fun a ↦ ((hf_meas k).mk (f k) a, (hf_meas l).mk (f l) a)) := by
    refine iCondIndepFun.condIndepFun_prodMk_prodMk hm ?_ (fun i ↦ (hf_meas i).measurable_mk)
      _ _ _ _ hik hil hjk hjl
    exact iCondIndepFun.congr' hf_indep fun i ↦ AEMeasurable.ae_eq_mk (hf_meas i)
  refine CondIndepFun.congr' h ?_ ?_
  · exact Filter.EventuallyEq.prodMk (hf_meas i).ae_eq_mk.symm (hf_meas j).ae_eq_mk.symm
  · exact Filter.EventuallyEq.prodMk (hf_meas k).ae_eq_mk.symm (hf_meas l).ae_eq_mk.symm

end iIndepFun

section Mul
variable {β : Type*} {m : MeasurableSpace β} [Mul β] [MeasurableMul₂ β] {f : ι → Ω → β}

@[to_additive]
lemma iCondIndepFun.condIndepFun_mul_left (hm : mΩ ≤ mΩ₀) [SigmaFinite (P.trim hm)]
    (hf_indep : iCondIndepFun P mΩ f) (hf_meas : ∀ i, Measurable[mΩ₀] (f i))
    (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) :
    CondIndepFun P mΩ (f i * f j) (f k) := by
  have : CondIndepFun P mΩ (fun ω => (f i ω, f j ω)) (f k) :=
    hf_indep.condIndepFun_prodMk hm hf_meas i j k hik hjk
  simpa using this.comp (measurable_fst.mul measurable_snd) measurable_id

@[to_additive]
lemma iCondIndepFun.condIndepFun_mul_left₀ (hm : mΩ ≤ mΩ₀) [SigmaFinite (P.trim hm)]
    (hf_indep : iCondIndepFun P mΩ f) (hf_meas : ∀ i, AEMeasurable[mΩ₀] (f i) P)
    (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) :
    CondIndepFun P mΩ (f i * f j) (f k) := by
  have : CondIndepFun P mΩ (fun ω => (f i ω, f j ω)) (f k) :=
    hf_indep.condIndepFun_prodMk₀ hm hf_meas i j k hik hjk
  simpa using this.comp (measurable_fst.mul measurable_snd) measurable_id

@[to_additive]
lemma iCondIndepFun.condIndepFun_mul_right (hm : mΩ ≤ mΩ₀) [SigmaFinite (P.trim hm)]
    (hf_indep : iCondIndepFun P mΩ f) (hf_meas : ∀ i, Measurable[mΩ₀] (f i))
    (i j k : ι) (hij : i ≠ j) (hik : i ≠ k) :
    CondIndepFun P mΩ (f i) (f j * f k) :=
  (hf_indep.condIndepFun_mul_left hm hf_meas _ _ _ hij.symm hik.symm).symm

@[to_additive]
lemma iCondIndepFun.condIndepFun_mul_right₀ (hm : mΩ ≤ mΩ₀) [SigmaFinite (P.trim hm)]
    (hf_indep : iCondIndepFun P mΩ f) (hf_meas : ∀ i, AEMeasurable[mΩ₀] (f i) P)
    (i j k : ι) (hij : i ≠ j) (hik : i ≠ k) :
    CondIndepFun P mΩ (f i) (f j * f k) :=
  (hf_indep.condIndepFun_mul_left₀ hm hf_meas _ _ _ hij.symm hik.symm).symm

@[to_additive]
lemma iCondIndepFun.condIndepFun_mul_mul (hm : mΩ ≤ mΩ₀) [SigmaFinite (P.trim hm)]
    (hf_indep : iCondIndepFun P mΩ f) (hf_meas : ∀ i, Measurable[mΩ₀] (f i))
    (i j k l : ι) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    CondIndepFun P mΩ (f i * f j) (f k * f l) :=
  (hf_indep.condIndepFun_prodMk_prodMk hm hf_meas i j k l hik hil hjk hjl).comp
    measurable_mul measurable_mul

@[to_additive]
lemma iCondIndepFun.condIndepFun_mul_mul₀ (hm : mΩ ≤ mΩ₀) [SigmaFinite (P.trim hm)]
    (hf_indep : iCondIndepFun P mΩ f) (hf_meas : ∀ i, AEMeasurable (f i) P)
    (i j k l : ι) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    CondIndepFun P mΩ (f i * f j) (f k * f l) :=
  (hf_indep.condIndepFun_prodMk_prodMk₀ hm hf_meas i j k l hik hil hjk hjl).comp
    measurable_mul measurable_mul

end Mul

section Div
variable {β : Type*} {m : MeasurableSpace β} [Div β] [MeasurableDiv₂ β] {f : ι → Ω → β}

@[to_additive]
lemma iCondIndepFun.condIndepFun_div_left (hm : mΩ ≤ mΩ₀) [SigmaFinite (P.trim hm)]
    (hf_indep : iCondIndepFun P mΩ f) (hf_meas : ∀ i, Measurable[mΩ₀] (f i)) (i j k : ι)
    (hik : i ≠ k) (hjk : j ≠ k) :
    CondIndepFun P mΩ (f i / f j) (f k) := by
  have : CondIndepFun P mΩ (fun ω => (f i ω, f j ω)) (f k) :=
    hf_indep.condIndepFun_prodMk hm hf_meas i j k hik hjk
  simpa using this.comp (measurable_fst.div measurable_snd) measurable_id

@[to_additive]
lemma iCondIndepFun.condIndepFun_div_left₀ (hm : mΩ ≤ mΩ₀) [SigmaFinite (P.trim hm)]
    (hf_indep : iCondIndepFun P mΩ f) (hf_meas : ∀ i, AEMeasurable[mΩ₀] (f i) P)
    (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) :
    CondIndepFun P mΩ (f i / f j) (f k) := by
  have : CondIndepFun P mΩ (fun ω => (f i ω, f j ω)) (f k) :=
    hf_indep.condIndepFun_prodMk₀ hm hf_meas i j k hik hjk
  simpa using this.comp (measurable_fst.div measurable_snd) measurable_id

@[to_additive]
lemma iCondIndepFun.condIndepFun_div_right (hm : mΩ ≤ mΩ₀) [SigmaFinite (P.trim hm)]
    (hf_indep : iCondIndepFun P mΩ f) (hf_meas : ∀ i, Measurable[mΩ₀] (f i))
    (i j k : ι) (hij : i ≠ j) (hik : i ≠ k) :
    CondIndepFun P mΩ (f i) (f j / f k) :=
  (hf_indep.condIndepFun_div_left hm hf_meas _ _ _ hij.symm hik.symm).symm


lemma iCondIndepFun.condIndepFun_div_right₀ (hm : mΩ ≤ mΩ₀) [SigmaFinite (P.trim hm)]
    (hf_indep : iCondIndepFun P mΩ f) (hf_meas : ∀ i, AEMeasurable (f i) P)
    (i j k : ι) (hij : i ≠ j) (hik : i ≠ k) :
    CondIndepFun P mΩ (f i) (f j / f k) :=
  (hf_indep.condIndepFun_div_left₀ hm hf_meas _ _ _ hij.symm hik.symm).symm

@[to_additive]
lemma iCondIndepFun.condIndepFun_div_div (hm : mΩ ≤ mΩ₀) [SigmaFinite (P.trim hm)]
    (hf_indep : iCondIndepFun P mΩ f) (hf_meas : ∀ i, Measurable[mΩ₀] (f i))
    (i j k l : ι) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    CondIndepFun P mΩ (f i / f j) (f k / f l) :=
  (hf_indep.condIndepFun_prodMk_prodMk hm hf_meas i j k l hik hil hjk hjl).comp
    measurable_div measurable_div

@[to_additive]
lemma iCondIndepFun.condIndepFun_div_div₀ (hm : mΩ ≤ mΩ₀) [SigmaFinite (P.trim hm)]
    (hf_indep : iCondIndepFun P mΩ f) (hf_meas : ∀ i, AEMeasurable (f i) P)
    (i j k l : ι) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    CondIndepFun P mΩ (f i / f j) (f k / f l) :=
  (hf_indep.condIndepFun_prodMk_prodMk₀ hm hf_meas i j k l hik hil hjk hjl).comp
    measurable_div measurable_div

end Div

section CommMonoid
variable {β : Type*} {m : MeasurableSpace β} [CommMonoid β] [MeasurableMul₂ β] {f : ι → Ω → β}

@[to_additive]
theorem iCondIndepFun.condIndepFun_finset_prod_of_notMem (hm : mΩ ≤ mΩ₀) [SigmaFinite (P.trim hm)]
    (hf_Indep : iCondIndepFun P mΩ f) (hf_meas : ∀ i, Measurable[mΩ₀] (f i)) {s : Finset ι} {i : ι}
    (hi : i ∉ s) :
    CondIndepFun P mΩ (∏ j ∈ s, f j) (f i) := by
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
    (hf_Indep.condIndepFun_finset hm s {i} (Finset.disjoint_singleton_left.mpr hi).symm hf_meas).comp
      h_meas_left h_meas_right

@[to_additive]
theorem iCondIndepFun.condIndepFun_finset_prod_of_notMem₀ (hm : mΩ ≤ mΩ₀) [SigmaFinite (P.trim hm)]
    (hf_Indep : iCondIndepFun P mΩ f) (hf_meas : ∀ i, AEMeasurable (f i) P)
    {s : Finset ι} {i : ι} (hi : i ∉ s) :
    CondIndepFun P mΩ (∏ j ∈ s, f j) (f i) := by
  have h : CondIndepFun P mΩ (∏ j ∈ s, (hf_meas j).mk (f j)) ((hf_meas i).mk (f i)) := by
    sorry
  sorry
  --   refine iIndepFun.indepFun_finset_prod_of_notMem ?_ (fun i ↦ (hf_meas i).measurable_mk) hi
  --   exact iIndepFun.congr' hf_Indep fun i ↦ Measure.ae_ae_of_ae_comp (hf_meas i).ae_eq_mk
  -- refine IndepFun.congr' h ?_ ?_
  -- · have : ∀ᵐ a ∂μ, ∀ (i : s), f i =ᵐ[κ a] (hf_meas i).mk := by
  --     rw [ae_all_iff]
  --     exact fun i ↦ Measure.ae_ae_of_ae_comp (hf_meas i).ae_eq_mk
  --   filter_upwards [this] with a ha
  --   filter_upwards [ae_all_iff.2 ha] with ω hω
  --   simp only [Finset.prod_apply]
  --   exact Finset.prod_congr rfl fun i hi ↦ (hω ⟨i, hi⟩).symm
  -- · exact Measure.ae_ae_of_ae_comp (hf_meas i).ae_eq_mk.symm


@[to_additive]
theorem iCondIndepFun.condIndepFun_prod_range_succ (hm : mΩ ≤ mΩ₀) [SigmaFinite (P.trim hm)]
    {f : ℕ → Ω → β} (hf_Indep : iCondIndepFun P mΩ f) (hf_meas : ∀ i, Measurable[mΩ₀] (f i))
    (n : ℕ) : CondIndepFun P mΩ (∏ j ∈ Finset.range n, f j) (f n) :=
  hf_Indep.condIndepFun_finset_prod_of_notMem hm hf_meas Finset.notMem_range_self

@[to_additive]
theorem iCondIndepFun.condIndepFun_prod_range_succ₀ (hm : mΩ ≤ mΩ₀) [SigmaFinite (P.trim hm)]
    {f : ℕ → Ω → β} (hf_Indep : iCondIndepFun P mΩ f) (hf_meas : ∀ i, AEMeasurable (f i) P) (n : ℕ) :
    CondIndepFun P mΩ (∏ j ∈ Finset.range n, f j) (f n) :=
  hf_Indep.condIndepFun_finset_prod_of_notMem₀ hm hf_meas Finset.notMem_range_self

end CommMonoid

theorem iCondIndepSet.iCondIndepFun_indicator [Zero β] [One β] {m : MeasurableSpace β}
    {s : ι → Set Ω} (hs : iCondIndepSet P mΩ s) :
    iCondIndepFun P mΩ (fun n => (s n).indicator fun _ω => (1 : β)) := by
  classical
  rw [iCondIndepFun_iff_measure_inter_preimage_eq_mul]
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

-- variable {α : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
--     {X : ι → Ω → α} {Y : ι → Ω → β} {f : _ → Set Ω} {t : ι → Set β} {s : Finset ι}

-- /-- The probability of an intersection of preimages conditioning on another intersection factors
-- into a product. -/
-- lemma iIndepFun.cond_iInter [Finite ι] (hY : ∀ i, Measurable (Y i))
--     (hindep : iCondIndepFun P mΩ (fun i ω ↦ (X i ω, Y i ω)))
--     (hf : ∀ i ∈ s, MeasurableSet[mα.comap (X i)] (f i))
--     (hy : ∀ᵐ a ∂μ, ∀ i ∉ s, κ a (Y i ⁻¹' t i) ≠ 0) (ht : ∀ i, MeasurableSet (t i)) :
--     ∀ᵐ a ∂μ, (κ a)[⋂ i ∈ s, f i | ⋂ i, Y i ⁻¹' t i] = ∏ i ∈ s, (κ a)[f i | Y i in t i] := by
--   classical
--   cases nonempty_fintype ι
--   let g (i' : ι) := if i' ∈ s then Y i' ⁻¹' t i' ∩ f i' else Y i' ⁻¹' t i'
--   have hYt i : MeasurableSet[(mα.prod mβ).comap fun ω ↦ (X i ω, Y i ω)] (Y i ⁻¹' t i) :=
--     ⟨.univ ×ˢ t i, .prod .univ (ht _), by ext; simp⟩
--   have hg i : MeasurableSet[(mα.prod mβ).comap fun ω ↦ (X i ω, Y i ω)] (g i) := by
--     by_cases hi : i ∈ s <;> simp only [hi, ↓reduceIte, g]
--     · obtain ⟨A, hA, hA'⟩ := hf i hi
--       exact (hYt _).inter ⟨A ×ˢ .univ, hA.prod .univ, by ext; simp [← hA']⟩
--     · exact hYt _
--   filter_upwards [hy, hindep.ae_isProbabilityMeasure, hindep.meas_iInter hYt, hindep.meas_iInter hg]
--     with a hy _ hYt hg
--   calc
--     _ = (κ a (⋂ i, Y i ⁻¹' t i))⁻¹ * κ a ((⋂ i, Y i ⁻¹' t i) ∩ ⋂ i ∈ s, f i) := by
--       rw [cond_apply]; exact .iInter fun i ↦ hY i (ht i)
--     _ = (κ a (⋂ i, Y i ⁻¹' t i))⁻¹ * κ a (⋂ i, g i) := by
--       congr 2
--       calc
--         _ = (⋂ i, Y i ⁻¹' t i) ∩ ⋂ i, if i ∈ s then f i else .univ := by
--           congr 1
--           simp only [Set.iInter_ite, Set.iInter_univ, Set.inter_univ]
--         _ = ⋂ i, Y i ⁻¹' t i ∩ (if i ∈ s then f i else .univ) := by rw [Set.iInter_inter_distrib]
--         _ = _ := Set.iInter_congr fun i ↦ by by_cases hi : i ∈ s <;> simp [hi, g]
--     _ = (∏ i, κ a (Y i ⁻¹' t i))⁻¹ * κ a (⋂ i, g i) := by
--       rw [hYt]
--     _ = (∏ i, κ a (Y i ⁻¹' t i))⁻¹ * ∏ i, κ a (g i) := by
--       rw [hg]
--     _ = ∏ i, (κ a (Y i ⁻¹' t i))⁻¹ * κ a (g i) := by
--       rw [Finset.prod_mul_distrib, ENNReal.prod_inv_distrib]
--       exact fun _ _ i _ _ ↦ .inr <| measure_ne_top _ _
--     _ = ∏ i, if i ∈ s then (κ a)[f i | Y i ⁻¹' t i] else 1 := by
--       refine Finset.prod_congr rfl fun i _ ↦ ?_
--       by_cases hi : i ∈ s
--       · simp only [hi, ↓reduceIte, g, cond_apply (hY i (ht i))]
--       · simp only [hi, ↓reduceIte, g, ENNReal.inv_mul_cancel (hy i hi) (measure_ne_top _ _)]
--     _ = _ := by simp

end ProbabilityTheory.Kernel
