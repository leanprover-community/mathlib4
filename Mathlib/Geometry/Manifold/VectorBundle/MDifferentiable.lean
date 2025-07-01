/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions


/-!
# Differentiability of functions in vector bundles

-/

open Bundle Set PartialHomeomorph ContinuousLinearMap Pretrivialization Filter

open scoped Manifold Bundle Topology

section


variable {𝕜 B B' F M : Type*} {E : B → Type*}

variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)] {EB : Type*}
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  (IB : ModelWithCorners 𝕜 EB HB) (E' : B → Type*) [∀ x, Zero (E' x)] {EM : Type*}
  [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  {n : ℕ∞}

variable [TopologicalSpace B] [ChartedSpace HB B] [FiberBundle F E]


/-- Characterization of differentiable functions into a vector bundle. -/
theorem mdifferentiableWithinAt_totalSpace (f : M → TotalSpace F E) {s : Set M} {x₀ : M} :
    MDifferentiableWithinAt IM (IB.prod 𝓘(𝕜, F)) f s x₀ ↔
      MDifferentiableWithinAt IM IB (fun x => (f x).proj) s x₀ ∧
      MDifferentiableWithinAt IM 𝓘(𝕜, F)
        (fun x ↦ (trivializationAt F E (f x₀).proj (f x)).2) s x₀ := by
  simp +singlePass only [mdifferentiableWithinAt_iff_target]
  rw [and_and_and_comm, ← FiberBundle.continuousWithinAt_totalSpace, and_congr_right_iff]
  intro hf
  simp_rw [modelWithCornersSelf_prod, FiberBundle.extChartAt, Function.comp_def,
    PartialEquiv.trans_apply, PartialEquiv.prod_coe, PartialEquiv.refl_coe,
    extChartAt_self_apply, modelWithCornersSelf_coe, Function.id_def, ← chartedSpaceSelf_prod]
  refine (mdifferentiableWithinAt_prod_iff _).trans (and_congr ?_ Iff.rfl)
  have h1 : (fun x => (f x).proj) ⁻¹' (trivializationAt F E (f x₀).proj).baseSet ∈ 𝓝[s] x₀ :=
    ((FiberBundle.continuous_proj F E).continuousWithinAt.comp hf (mapsTo_image f s))
      ((Trivialization.open_baseSet _).mem_nhds (mem_baseSet_trivializationAt F E _))
  refine EventuallyEq.mdifferentiableWithinAt_iff (eventually_of_mem h1 fun x hx => ?_) ?_
  · simp_rw [Function.comp, PartialHomeomorph.coe_coe, Trivialization.coe_coe]
    rw [Trivialization.coe_fst']
    exact hx
  · simp only [mfld_simps]

theorem mdifferentiableAt_totalSpace (f : M → TotalSpace F E) {x₀ : M} :
    MDifferentiableAt IM (IB.prod 𝓘(𝕜, F)) f x₀ ↔
      MDifferentiableAt IM IB (fun x => (f x).proj) x₀ ∧
      MDifferentiableAt IM 𝓘(𝕜, F)
        (fun x ↦ (trivializationAt F E (f x₀).proj (f x)).2) x₀ := by
  simpa [← mdifferentiableWithinAt_univ] using mdifferentiableWithinAt_totalSpace _ f

/-- Characterization of differentiable sections of a vector bundle at a point within a set
in term of the preferred trivialization at that point. -/
theorem mdifferentiableWithinAt_section (s : Π b, E b) {u : Set B} {b₀ : B} :
    MDifferentiableWithinAt IB (IB.prod 𝓘(𝕜, F)) (fun b ↦ TotalSpace.mk' F b (s b)) u b₀ ↔
      MDifferentiableWithinAt IB 𝓘(𝕜, F) (fun b ↦ (trivializationAt F E b₀ (s b)).2) u b₀ := by
  rw [mdifferentiableWithinAt_totalSpace]
  change MDifferentiableWithinAt _ _ id _ _ ∧ _ ↔ _
  simp [mdifferentiableWithinAt_id]

/-- Characterization of differentiable sections of a vector bundle at a point within a set
in term of the preferred trivialization at that point. -/
theorem mdifferentiableAt_section (s : Π b, E b) {b₀ : B} :
    MDifferentiableAt IB (IB.prod 𝓘(𝕜, F)) (fun b ↦ TotalSpace.mk' F b (s b)) b₀ ↔
      MDifferentiableAt IB 𝓘(𝕜, F) (fun b ↦ (trivializationAt F E b₀ (s b)).2) b₀ := by
  simpa [← mdifferentiableWithinAt_univ] using mdifferentiableWithinAt_section _ _

variable [(x : B) → AddCommMonoid (E x)] [(x : B) → Module 𝕜 (E x)]
         [VectorBundle 𝕜 F E] [ContMDiffVectorBundle 1 F E IB]

lemma MDifferentiableWithinAt.coordChange
    {e : Trivialization F TotalSpace.proj} [MemTrivializationAtlas e]
    (e' : Trivialization F TotalSpace.proj)  [MemTrivializationAtlas e']
    {f : M → TotalSpace F E} {s : Set M} {x₀ : M}
    (hex₀ : (f x₀).proj ∈ e.baseSet) (he'x₀ : (f x₀).proj ∈ e'.baseSet)
    (hf : MDifferentiableWithinAt IM IB (fun x ↦ (f x).proj) s x₀)
    (he'f : MDifferentiableWithinAt IM 𝓘(𝕜, F) (fun x ↦ (e' (f x)).2) s x₀) :
    MDifferentiableWithinAt IM 𝓘(𝕜, F) (fun x ↦ (e (f x)).2) s x₀ := by
  have : ∀ᶠ x in 𝓝[s] x₀, (e (f x)).2 = e'.coordChangeL 𝕜 e (f x).proj (e' (f x)).2 := by
    have mem : ∀ᶠ x in 𝓝[s] x₀, (f x).proj ∈ e'.baseSet ∩ e.baseSet := by
      exact  hf.continuousWithinAt <|
        (e'.open_baseSet.eventually_mem he'x₀).and (e.open_baseSet.eventually_mem hex₀)
    filter_upwards [mem] with x hx
    rw [e'.coordChangeL_apply e hx, e'.symm_proj_apply (f x) hx.1]
  apply Filter.EventuallyEq.mdifferentiableWithinAt_iff this ?_ |>.1
  · let c := Trivialization.coordChangeL 𝕜 e' e
    have bar : MDifferentiableWithinAt IM 𝓘(𝕜, F →L[𝕜] F)
        (fun x : M ↦ (c (f x).proj : F →L[𝕜] F)) s x₀ := by
      exact contMDiffAt_coordChangeL he'x₀ hex₀ |>.mdifferentiableAt le_rfl
        |>.comp_mdifferentiableWithinAt x₀ hf
    exact bar.clm_apply he'f
  rw [e'.coordChangeL_apply e ⟨he'x₀, hex₀⟩, e'.symm_proj_apply (f x₀) he'x₀]

theorem mdifferentiableWithinAt_coordChange
    {e e' : Trivialization F TotalSpace.proj} [MemTrivializationAtlas e] [MemTrivializationAtlas e']
    {f : M → TotalSpace F E} {s : Set M} {x₀ : M}
    (hex₀ : (f x₀).proj ∈ e.baseSet) (he'x₀ : (f x₀).proj ∈ e'.baseSet)
    (hf : MDifferentiableWithinAt IM IB (fun x ↦ (f x).proj) s x₀) :
    MDifferentiableWithinAt IM 𝓘(𝕜, F) (fun x ↦ (e (f x)).2) s x₀ ↔
    MDifferentiableWithinAt IM 𝓘(𝕜, F) (fun x ↦ (e' (f x)).2) s x₀ :=
  ⟨hf.coordChange IB e he'x₀ hex₀, hf.coordChange IB e' hex₀ he'x₀⟩

theorem mdifferentiableAt_change_triv
    {e e' : Trivialization F TotalSpace.proj} [MemTrivializationAtlas e] [MemTrivializationAtlas e']
    {f : M → TotalSpace F E} {x₀ : M}
    (hex₀ : (f x₀).proj ∈ e.baseSet) (he'x₀ : (f x₀).proj ∈ e'.baseSet)
    (hf : MDifferentiableAt IM IB (fun x ↦ (f x).proj) x₀) :
    MDifferentiableAt IM 𝓘(𝕜, F) (fun x ↦ (e (f x)).2) x₀ ↔
    MDifferentiableAt IM 𝓘(𝕜, F) (fun x ↦ (e' (f x)).2) x₀ := by
  simpa [← mdifferentiableWithinAt_univ] using mdifferentiableWithinAt_coordChange IB hex₀ he'x₀ hf

/-- Characterization of differentiable functions into a vector bundle in terms
of any trivialization. Version at a point within at set. -/
theorem Trivialization.mdifferentiableWithinAt_totalSpace_iff
    (e : Trivialization F (TotalSpace.proj : TotalSpace F E → B)) [MemTrivializationAtlas e]
    (f : M → TotalSpace F E) {s : Set M} {x₀ : M}
    (hex₀ : (f x₀).proj ∈ e.baseSet) :
    MDifferentiableWithinAt IM (IB.prod 𝓘(𝕜, F)) f s x₀ ↔
      MDifferentiableWithinAt IM IB (fun x => (f x).proj) s x₀ ∧
      MDifferentiableWithinAt IM 𝓘(𝕜, F)
        (fun x ↦ (e (f x)).2) s x₀ := by
  rw [mdifferentiableWithinAt_totalSpace]
  apply and_congr_right
  intro hf
  rw [mdifferentiableWithinAt_coordChange IB hex₀ (FiberBundle.mem_baseSet_trivializationAt' _) hf]

/-- Characterization of differentiable functions into a vector bundle in terms
of any trivialization. Version at a point. -/
theorem Trivialization.mdifferentiableAt_totalSpace_iff
    (e : Trivialization F (TotalSpace.proj : TotalSpace F E → B)) [MemTrivializationAtlas e]
    (f : M → TotalSpace F E) {x₀ : M}
    (hex₀ : (f x₀).proj ∈ e.baseSet) :
    MDifferentiableAt IM (IB.prod 𝓘(𝕜, F)) f x₀ ↔
      MDifferentiableAt IM IB (fun x => (f x).proj) x₀ ∧
      MDifferentiableAt IM 𝓘(𝕜, F)
        (fun x ↦ (e (f x)).2) x₀ := by
  rw [mdifferentiableAt_totalSpace]
  apply and_congr_right
  intro hf
  rw [mdifferentiableAt_change_triv IB hex₀ (FiberBundle.mem_baseSet_trivializationAt' _) hf]

/-- Characterization of differentiable sections a vector bundle in terms
of any trivialization. Version at a point within at set. -/
theorem Trivialization.mdifferentiableWithinAt_section_iff
    (e : Trivialization F (TotalSpace.proj : TotalSpace F E → B)) [MemTrivializationAtlas e]
    (s : Π b : B, E b) {u : Set B} {b₀ : B}
    (hex₀ : b₀ ∈ e.baseSet) :
    MDifferentiableWithinAt IB (IB.prod 𝓘(𝕜, F)) (fun b ↦ TotalSpace.mk' F b (s b)) u b₀ ↔
      MDifferentiableWithinAt IB 𝓘(𝕜, F) (fun x ↦ (e (s x)).2) u b₀ := by
  rw [e.mdifferentiableWithinAt_totalSpace_iff IB]
  · change MDifferentiableWithinAt IB IB id u b₀ ∧ _ ↔ _
    simp [mdifferentiableWithinAt_id]
  simp [hex₀]

/-- Characterization of differentiable functions into a vector bundle in terms
of any trivialization. Version at a point. -/
theorem Trivialization.mdifferentiableAt_section_iff
    (e : Trivialization F (TotalSpace.proj : TotalSpace F E → B)) [MemTrivializationAtlas e]
    (s : Π b : B, E b) {b₀ : B}
    (hex₀ : b₀ ∈ e.baseSet) :
    MDifferentiableAt IB (IB.prod 𝓘(𝕜, F)) (fun b ↦ TotalSpace.mk' F b (s b)) b₀ ↔
      MDifferentiableAt IB 𝓘(𝕜, F) (fun x ↦ (e (s x)).2) b₀ := by
  simpa [← mdifferentiableWithinAt_univ] using e.mdifferentiableWithinAt_section_iff IB s hex₀
end

section contMDiff_addsmulfinsum_section

variable {𝕜 B B' F M : Type*} {E : B → Type*}

variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)] {EB : Type*}
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  (I : ModelWithCorners 𝕜 EB HB) -- (E' : B → Type*) [∀ x, Zero (E' x)] {EM : Type*}
  -- [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM]
  -- {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  -- {n : ℕ∞}

variable [TopologicalSpace B] [ChartedSpace HB B] [FiberBundle F E]

variable [(x : B) → AddCommMonoid (E x)] [(x : B) → Module 𝕜 (E x)]
         [VectorBundle 𝕜 F E]

-- Proofs taken from SmoothSection: TODO golf those with these lemmas!
-- XXX: also add sub, neg, nsmul, zsmul lemmas?

variable {I V}

variable {f : B → 𝕜} {a : 𝕜} {s t : Π x : B, E x} {u : Set B} {x₀ : B}

omit [ContMDiffVectorBundle 1 F E I] in
lemma mdifferentiableWithinAt_add_section
    (hs : MDifferentiableWithinAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (s x)) u x₀)
    (ht : MDifferentiableWithinAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (t x)) u x₀) :
    MDifferentiableWithinAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x ((s + t) x)) u x₀ := by
  rw [mdifferentiableWithinAt_section] at hs ht ⊢
  set e := trivializationAt F E x₀

  refine (hs.add ht).congr_of_eventuallyEq ?_ ?_
  · apply eventually_of_mem (U := e.baseSet)
    · exact mem_nhdsWithin_of_mem_nhds <|
        (e.open_baseSet.mem_nhds <| mem_baseSet_trivializationAt F E x₀)
    · intro x hx
      apply (e.linear 𝕜 hx).1
  · apply (e.linear 𝕜 (FiberBundle.mem_baseSet_trivializationAt' x₀)).1

omit [ContMDiffVectorBundle 1 F E I] in
lemma mdifferentiableAt_add_section
    (hs : MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (s x)) x₀)
    (ht : MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (t x)) x₀) :
    MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x ((s + t) x)) x₀ := by
  rw [mdifferentiableAt_section] at hs ht ⊢
  set e := trivializationAt F E x₀
  refine (hs.add ht).congr_of_eventuallyEq ?_
  refine eventually_of_mem (e.open_baseSet.mem_nhds <| mem_baseSet_trivializationAt F E x₀) ?_
  intro x hx
  apply (e.linear 𝕜 hx).1

lemma mdifferentiableOn_add_section
    (hs : MDifferentiableOn I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (s x)) u)
    (ht : MDifferentiableOn I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (t x)) u) :
    MDifferentiableOn I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x ((s + t) x)) u :=
  fun x₀ hx₀ ↦ mdifferentiableWithinAt_add_section (hs x₀ hx₀) (ht x₀ hx₀)

lemma mdifferentiable_add_section
    (hs : MDifferentiable I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (s x)))
    (ht : MDifferentiable I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (t x))) :
    MDifferentiable I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x ((s + t) x)) :=
  fun x₀ ↦ mdifferentiableAt_add_section (hs x₀) (ht x₀)

lemma mdifferentiableWithinAt_smul_section
    (hs : MDifferentiableWithinAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (s x)) u x₀)
    (hf : MDifferentiableWithinAt I 𝓘(𝕜) f u x₀) :
    MDifferentiableWithinAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (f x • s x)) u x₀ := by
  rw [mdifferentiableWithinAt_section] at hs ⊢
  set e := trivializationAt F E x₀
  refine (hf.smul hs).congr_of_eventuallyEq ?_ ?_
  · apply eventually_of_mem (U := e.baseSet)
    · exact mem_nhdsWithin_of_mem_nhds <|
        (e.open_baseSet.mem_nhds <| mem_baseSet_trivializationAt F E x₀)
    · intro x hx
      apply (e.linear 𝕜 hx).2
  · apply (e.linear 𝕜 (FiberBundle.mem_baseSet_trivializationAt' x₀)).2

lemma mdifferentiableAt_smul_section
    (hs : MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (s x)) x₀)
    (hf : MDifferentiableAt I 𝓘(𝕜) f x₀) :
    MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (f x • s x)) x₀ := by
  rw [mdifferentiableAt_section] at hs ⊢
  set e := trivializationAt F E x₀
  refine (hf.smul hs).congr_of_eventuallyEq ?_
  refine eventually_of_mem (e.open_baseSet.mem_nhds <| mem_baseSet_trivializationAt F E x₀) ?_
  intro x hx
  apply (e.linear 𝕜 hx).2

lemma mdifferentiableOn_smul_section
    (hs : MDifferentiableOn I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (s x)) u)
    (hf : MDifferentiableOn I 𝓘(𝕜) f u) :
    MDifferentiableOn I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (f x • s x)) u :=
  fun x₀ hx₀ ↦ mdifferentiableWithinAt_smul_section (hs x₀ hx₀) (hf x₀ hx₀)

lemma mdifferentiable_smul_section
    (hs : MDifferentiable I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (s x)))
    (hf : MDifferentiable I 𝓘(𝕜) f) :
    MDifferentiable I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (f x • s x)) :=
  fun x₀ ↦ mdifferentiableAt_smul_section (hs x₀) (hf x₀)

lemma mdifferentiableWithinAt_smul_const_section
    (hs : MDifferentiableWithinAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (s x)) u x₀) :
    MDifferentiableWithinAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (a • s x)) u x₀ :=
  mdifferentiableWithinAt_smul_section hs mdifferentiableWithinAt_const

lemma mdifferentiableAt_smul_const_section
    (hs : MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (s x)) x₀) :
    MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (a • s x)) x₀ :=
  mdifferentiableAt_smul_section hs mdifferentiableAt_const

lemma mdifferentiableOn_smul_const_section
    (hs : MDifferentiableOn I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (s x)) u) :
    MDifferentiableOn I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (a • s x)) u :=
  mdifferentiableOn_smul_section hs mdifferentiableOn_const

lemma mdifferentiable_smul_const_section
    (hs : MDifferentiable I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (s x))) :
    MDifferentiable I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (a • s x)) :=
  fun x₀ ↦ mdifferentiableAt_smul_const_section (hs x₀)

lemma mdifferentiableWithinAt_finsum_section {ι : Type*} {s : Finset ι} {t : ι → (x : B) → E x}
    (hs : ∀ i, MDifferentiableWithinAt I (I.prod 𝓘(𝕜, F))
                 (fun x ↦ TotalSpace.mk' F x (t i x)) u x₀) :
    MDifferentiableWithinAt I (I.prod 𝓘(𝕜, F))
      (fun x ↦ TotalSpace.mk' F x (∑ i ∈ s, (t i x))) u x₀ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    -- TODO: x₀ ∈ u should not be required -> add mdifferentiableWithinAt_zeroSection!
    apply MDifferentiable.mdifferentiableOn
    · apply  ContMDiff.mdifferentiable _ le_rfl
      apply contMDiff_zeroSection
    · sorry -- x₀ ∈ u...
  | insert i s hi h =>
    simpa [Finset.sum_insert hi] using mdifferentiableWithinAt_add_section (hs i) h

lemma mdifferentiableAt_finsum_section {ι : Type*} {s : Finset ι} {t : ι → (x : B) → E x} {x₀ : B}
    (hs : ∀ i, MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (t i x)) x₀) :
    MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (∑ i ∈ s, (t i x))) x₀ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
     apply ContMDiff.mdifferentiable _ le_rfl
     apply contMDiff_zeroSection
  | insert i s hi h =>
    simpa [Finset.sum_insert hi] using mdifferentiableWithinAt_add_section (hs i) h

lemma mdifferentiableOn_finsum_section {ι : Type*} {s : Finset ι} {t : ι → (x : B) → E x}
    (hs : ∀ i, MDifferentiableOn I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (t i x)) u) :
    MDifferentiableOn I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (∑ i ∈ s, (t i x))) u :=
  fun x₀ hx₀ ↦ mdifferentiableWithinAt_finsum_section fun i ↦ hs i x₀ hx₀

lemma mdifferentiable_finsum_section {ι : Type*} {s : Finset ι} {t : ι → (x : B) → E x}
    (hs : ∀ i, MDifferentiable I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (t i x))) :
    MDifferentiable I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (∑ i ∈ s, (t i x))) :=
  fun x₀ ↦ mdifferentiableAt_finsum_section fun i ↦ (hs i) x₀

end contMDiff_addsmulfinsum_section

section

/- Declare two manifolds `B₁` and `B₂` (with models `IB₁ : HB₁ → EB₁` and `IB₂ : HB₂ → EB₂`),
and two vector bundles `E₁` and `E₂` respectively over `B₁` and `B₂` (with model fibers
`F₁` and `F₂`).

Also a third manifold `M`, which will be the source of all our maps.
-/
variable {𝕜 F₁ F₂ B₁ B₂ M : Type*} {E₁ : B₁ → Type*} {E₂ : B₂ → Type*} [NontriviallyNormedField 𝕜]
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)] [∀ x, AddCommGroup (E₂ x)]
  [∀ x, Module 𝕜 (E₂ x)] [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  {EB₁ : Type*}
  [NormedAddCommGroup EB₁] [NormedSpace 𝕜 EB₁] {HB₁ : Type*} [TopologicalSpace HB₁]
  {IB₁ : ModelWithCorners 𝕜 EB₁ HB₁} [TopologicalSpace B₁] [ChartedSpace HB₁ B₁]
  {EB₂ : Type*}
  [NormedAddCommGroup EB₂] [NormedSpace 𝕜 EB₂] {HB₂ : Type*} [TopologicalSpace HB₂]
  {IB₂ : ModelWithCorners 𝕜 EB₂ HB₂} [TopologicalSpace B₂] [ChartedSpace HB₂ B₂]
  {EM : Type*}
  [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  {n : ℕ∞} [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  {b₁ : M → B₁} {b₂ : M → B₂} {m₀ : M}
  {ϕ : Π (m : M), E₁ (b₁ m) →L[𝕜] E₂ (b₂ m)} {v : Π (m : M), E₁ (b₁ m)} {s : Set M}

/-- Consider a differentiable map `v : M → E₁` to a vector bundle, over a basemap `b₁ : M → B₁`, and
another basemap `b₂ : M → B₂`. Given linear maps `ϕ m : E₁ (b₁ m) → E₂ (b₂ m)` depending
differentiably on `m`, one can apply `ϕ m` to `g m`, and the resulting map is differentiable.

Note that the differentiability of `ϕ` can not be always be stated as differentiability of a map
into a manifold, as the pullback bundles `b₁ *ᵖ E₁` and `b₂ *ᵖ E₂` only make sense when `b₁`
and `b₂` are globally smooth, but we want to apply this lemma with only local information.
Therefore, we formulate it using differentiability of `ϕ` read in coordinates.

Version for `MDifferentiableWithinAt`. We also give a version for `MDifferentiableAt`, but no
version for `MDifferentiableOn` or `MDifferentiable` as our assumption, written in coordinates,
only makes sense around a point.
-/
lemma MDifferentiableWithinAt.clm_apply_of_inCoordinates
    (hϕ : MDifferentiableWithinAt IM 𝓘(𝕜, F₁ →L[𝕜] F₂)
      (fun m ↦ inCoordinates F₁ E₁ F₂ E₂ (b₁ m₀) (b₁ m) (b₂ m₀) (b₂ m) (ϕ m)) s m₀)
    (hv : MDifferentiableWithinAt IM (IB₁.prod 𝓘(𝕜, F₁)) (fun m ↦ (v m : TotalSpace F₁ E₁)) s m₀)
    (hb₂ : MDifferentiableWithinAt IM IB₂ b₂ s m₀) :
    MDifferentiableWithinAt IM (IB₂.prod 𝓘(𝕜, F₂))
      (fun m ↦ (ϕ m (v m) : TotalSpace F₂ E₂)) s m₀ := by
  rw [mdifferentiableWithinAt_totalSpace] at hv ⊢
  refine ⟨hb₂, ?_⟩
  apply (MDifferentiableWithinAt.clm_apply hϕ hv.2).congr_of_eventuallyEq_insert
  have A : ∀ᶠ m in 𝓝[insert m₀ s] m₀, b₁ m ∈ (trivializationAt F₁ E₁ (b₁ m₀)).baseSet := by
    apply hv.1.insert.continuousWithinAt
    apply (trivializationAt F₁ E₁ (b₁ m₀)).open_baseSet.mem_nhds
    exact FiberBundle.mem_baseSet_trivializationAt' (b₁ m₀)
  have A' : ∀ᶠ m in 𝓝[insert m₀ s] m₀, b₂ m ∈ (trivializationAt F₂ E₂ (b₂ m₀)).baseSet := by
    apply hb₂.insert.continuousWithinAt
    apply (trivializationAt F₂ E₂ (b₂ m₀)).open_baseSet.mem_nhds
    exact FiberBundle.mem_baseSet_trivializationAt' (b₂ m₀)
  filter_upwards [A, A'] with m hm h'm
  rw [inCoordinates_eq hm h'm]
  simp only [coe_comp', ContinuousLinearEquiv.coe_coe, Trivialization.continuousLinearEquivAt_apply,
    Trivialization.continuousLinearEquivAt_symm_apply, Function.comp_apply]
  congr
  rw [Trivialization.symm_apply_apply_mk (trivializationAt F₁ E₁ (b₁ m₀)) hm (v m)]

/-- Consider a differentiable map `v : M → E₁` to a vector bundle, over a basemap `b₁ : M → B₁`, and
another basemap `b₂ : M → B₂`. Given linear maps `ϕ m : E₁ (b₁ m) → E₂ (b₂ m)` depending
differentiably on `m`, one can apply `ϕ m` to `g m`, and the resulting map is differentiable.

Note that the differentiability of `ϕ` can not be always be stated as differentiability of a map
into a manifold, as the pullback bundles `b₁ *ᵖ E₁` and `b₂ *ᵖ E₂` only make sense when `b₁`
and `b₂` are globally smooth, but we want to apply this lemma with only local information.
Therefore, we formulate it using differentiability of `ϕ` read in coordinates.

Version for `MDifferentiableAt`. We also give a version for `MDifferentiableWithinAt`,
but no version for `MDifferentiableOn` or `MDifferentiable` as our assumption, written
in coordinates, only makes sense around a point.
-/
lemma MDifferentiableAt.clm_apply_of_inCoordinates
    (hϕ : MDifferentiableAt IM 𝓘(𝕜, F₁ →L[𝕜] F₂)
      (fun m ↦ inCoordinates F₁ E₁ F₂ E₂ (b₁ m₀) (b₁ m) (b₂ m₀) (b₂ m) (ϕ m)) m₀)
    (hv : MDifferentiableAt IM (IB₁.prod 𝓘(𝕜, F₁)) (fun m ↦ (v m : TotalSpace F₁ E₁)) m₀)
    (hb₂ : MDifferentiableAt IM IB₂ b₂ m₀) :
    MDifferentiableAt IM (IB₂.prod 𝓘(𝕜, F₂)) (fun m ↦ (ϕ m (v m) : TotalSpace F₂ E₂)) m₀ := by
  rw [← mdifferentiableWithinAt_univ] at hϕ hv hb₂ ⊢
  exact MDifferentiableWithinAt.clm_apply_of_inCoordinates hϕ hv hb₂

end
