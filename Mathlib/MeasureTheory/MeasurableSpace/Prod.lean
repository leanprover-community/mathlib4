/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.PiSystem

/-!
# The product sigma algebra

This file talks about the measurability of operations on binary functions.
-/

assert_not_exists MeasureTheory.Measure

noncomputable section

open Set MeasurableSpace

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- The product of generated σ-algebras is the one generated by rectangles, if both generating sets
  are countably spanning. -/
theorem generateFrom_prod_eq {α β} {C : Set (Set α)} {D : Set (Set β)} (hC : IsCountablySpanning C)
    (hD : IsCountablySpanning D) :
    @Prod.instMeasurableSpace _ _ (generateFrom C) (generateFrom D) =
      generateFrom (image2 (· ×ˢ ·) C D) := by
  apply le_antisymm
  · refine sup_le ?_ ?_ <;> rw [comap_generateFrom] <;> apply generateFrom_le <;>
      rintro _ ⟨s, hs, rfl⟩
    · rcases hD with ⟨t, h1t, h2t⟩
      rw [← prod_univ, ← h2t, prod_iUnion]
      apply MeasurableSet.iUnion
      intro n
      apply measurableSet_generateFrom
      exact ⟨s, hs, t n, h1t n, rfl⟩
    · rcases hC with ⟨t, h1t, h2t⟩
      rw [← univ_prod, ← h2t, iUnion_prod_const]
      apply MeasurableSet.iUnion
      rintro n
      apply measurableSet_generateFrom
      exact mem_image2_of_mem (h1t n) hs
  · apply generateFrom_le
    rintro _ ⟨s, hs, t, ht, rfl⟩
    dsimp only
    rw [prod_eq]
    apply (measurable_fst _).inter (measurable_snd _)
    · exact measurableSet_generateFrom hs
    · exact measurableSet_generateFrom ht

/-- If `C` and `D` generate the σ-algebras on `α` resp. `β`, then rectangles formed by `C` and `D`
  generate the σ-algebra on `α × β`. -/
theorem generateFrom_eq_prod {C : Set (Set α)} {D : Set (Set β)} (hC : generateFrom C = ‹_›)
    (hD : generateFrom D = ‹_›) (h2C : IsCountablySpanning C) (h2D : IsCountablySpanning D) :
    generateFrom (image2 (· ×ˢ ·) C D) = Prod.instMeasurableSpace := by
  rw [← hC, ← hD, generateFrom_prod_eq h2C h2D]

/-- The product σ-algebra is generated from boxes, i.e. `s ×ˢ t` for sets `s : Set α` and
  `t : Set β`. -/
lemma generateFrom_prod :
    generateFrom (image2 (· ×ˢ ·) { s : Set α | MeasurableSet s } { t : Set β | MeasurableSet t }) =
      Prod.instMeasurableSpace :=
  generateFrom_eq_prod generateFrom_measurableSet generateFrom_measurableSet
    isCountablySpanning_measurableSet isCountablySpanning_measurableSet

/-- Rectangles form a π-system. -/
lemma isPiSystem_prod :
    IsPiSystem (image2 (· ×ˢ ·) { s : Set α | MeasurableSet s } { t : Set β | MeasurableSet t }) :=
  isPiSystem_measurableSet.prod isPiSystem_measurableSet

lemma MeasurableEmbedding.prodMap {α β γ δ : Type*} {mα : MeasurableSpace α}
    {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ} {f : α → β}
    {g : γ → δ} (hg : MeasurableEmbedding g) (hf : MeasurableEmbedding f) :
    MeasurableEmbedding (Prod.map g f) := by
  refine ⟨hg.injective.prodMap hf.injective, ?_, ?_⟩
  · exact (hg.measurable.comp measurable_fst).prodMk (hf.measurable.comp measurable_snd)
  · intro s hs
    -- Induction using the π-system of rectangles
    induction s, hs using induction_on_inter generateFrom_prod.symm isPiSystem_prod with
    | empty =>
      simp only [Set.image_empty, MeasurableSet.empty]
    | basic s hs =>
      obtain ⟨t₁, ht₁, t₂, ht₂, rfl⟩ := hs
      simp_rw [Prod.map, ← prod_image_image_eq]
      exact (hg.measurableSet_image.mpr ht₁).prod (hf.measurableSet_image.mpr ht₂)
    | compl s _ ihs =>
      rw [← range_diff_image (hg.injective.prodMap hf.injective), range_prod_map]
      exact .diff (.prod hg.measurableSet_range hf.measurableSet_range) ihs
    | iUnion f _ _ ihf =>
      simpa only [image_iUnion] using .iUnion ihf

@[deprecated (since := "2024-12-11")]
alias MeasurableEmbedding.prod_mk := MeasurableEmbedding.prodMap

lemma MeasurableEmbedding.prodMk_left {β γ : Type*} [MeasurableSingletonClass α]
    {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
    (x : α) {f : γ → β} (hf : MeasurableEmbedding f) :
    MeasurableEmbedding (fun y ↦ (x, f y)) where
  injective := by
    intro y y'
    simp only [Prod.mk.injEq, true_and]
    exact fun h ↦ hf.injective h
  measurable := Measurable.prodMk measurable_const hf.measurable
  measurableSet_image' := by
    intro s hs
    convert (MeasurableSet.singleton x).prod (hf.measurableSet_image.mpr hs)
    ext x
    simp [Prod.ext_iff, eq_comm, ← exists_and_left, and_left_comm]

@[deprecated (since := "2025-03-05")]
alias MeasurableEmbedding.prod_mk_left := MeasurableEmbedding.prodMk_left

lemma measurableEmbedding_prodMk_left [MeasurableSingletonClass α] (x : α) :
    MeasurableEmbedding (Prod.mk x : β → α × β) :=
  MeasurableEmbedding.prodMk_left x MeasurableEmbedding.id

@[deprecated (since := "2025-03-05")]
alias measurableEmbedding_prod_mk_left := measurableEmbedding_prodMk_left

lemma MeasurableEmbedding.prodMk_right {β γ : Type*} [MeasurableSingletonClass α]
    {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
    {f : γ → β} (hf : MeasurableEmbedding f) (x : α) :
    MeasurableEmbedding (fun y ↦ (f y, x)) :=
  MeasurableEquiv.prodComm.measurableEmbedding.comp (hf.prodMk_left _)

@[deprecated (since := "2025-03-05")]
alias MeasurableEmbedding.prod_mk_right := MeasurableEmbedding.prodMk_right

lemma measurableEmbedding_prod_mk_right [MeasurableSingletonClass α] (x : α) :
    MeasurableEmbedding (fun y ↦ (y, x) : β → β × α) :=
  MeasurableEmbedding.prodMk_right MeasurableEmbedding.id x
