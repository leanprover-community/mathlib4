/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Thickening in uniform spaces

## Main definitions
* `UniformSpace.thicken s U`, the thickening of `s` by an entourage `U`.
-/

namespace UniformSpace
section Thicken

open Set UniformSpace
open scoped Uniformity

variable {α : Type*}

/-- Symmetric entourage -/
def flip (U : Set (α × α)) :=
  Prod.swap⁻¹' U

scoped[Uniformity] notation:max U "ᶠˡ" => flip U

lemma isSymmetricRel_iff {U : Set (α × α)} :
    IsSymmetricRel U ↔ Uᶠˡ = U := by rfl

lemma mem_flip {x y : α} {U : Set (α × α)} :
    (x, y) ∈ U ↔ (y, x) ∈ Uᶠˡ := by
  rw [flip, mem_preimage, Prod.swap_prod_mk]

lemma flip_flip {U : Set (α × α)} :
    (Uᶠˡ)ᶠˡ = U := by
  rw [flip, flip, ← preimage_comp, Prod.swap_swap_eq, preimage_id]

lemma flip_inter {U V : Set (α × α)} :
    (U ∩ V)ᶠˡ = Uᶠˡ ∩ Vᶠˡ := preimage_inter

lemma flip_iInter {ι : Sort*} {U : ι → Set (α × α)} :
    (⋂ i, U i)ᶠˡ = ⋂ i, (U i)ᶠˡ := preimage_iInter

lemma flip_biInter {ι : Type*} {s : Set ι} {U : ι → Set (α × α)} :
    (⋂ i ∈ s, U i)ᶠˡ = ⋂ i ∈ s, (U i)ᶠˡ := preimage_iInter₂

lemma flip_union {U V : Set (α × α)} :
    (U ∪ V)ᶠˡ = Uᶠˡ ∪ Vᶠˡ := preimage_union

lemma flip_iUnion {ι : Sort*} {U : ι → Set (α × α)} :
    (⋃ i, U i)ᶠˡ = ⋃ i, (U i)ᶠˡ := preimage_iUnion

lemma flip_biUnion {ι : Type*} {s : Set ι} {U : ι → Set (α × α)} :
    (⋃ i ∈ s, U i)ᶠˡ = ⋃ i ∈ s, (U i)ᶠˡ := preimage_iUnion₂

lemma flip_preimage {β : Type*} {f : β → α} {U : Set (α × α)} :
    ((Prod.map f f)⁻¹' U)ᶠˡ = (Prod.map f f)⁻¹' Uᶠˡ := by
  rw [flip, flip, ← preimage_comp, Prod.map_comp_swap f f, preimage_comp]

lemma flip_comp {U V : Set (α × α)} :
    (U ○ V)ᶠˡ = Vᶠˡ ○ Uᶠˡ := by
  ext x
  simp only [flip, compRel, mem_preimage, mem_setOf_eq, Prod.swap_prod_mk, Prod.fst_swap,
    Prod.snd_swap]
  tauto

lemma isSymmetricRel_comp_flip_self (U : Set (α × α)) :
    IsSymmetricRel (U ○ Uᶠˡ) := by
  rw [isSymmetricRel_iff, flip_comp, flip_flip]

lemma isSymmetricRel_flip_comp_self (U : Set (α × α)) :
    IsSymmetricRel (Uᶠˡ ○ U) := by
  rw [isSymmetricRel_iff, flip_comp, flip_flip]

lemma ball_flip {x y : α} {U : Set (α × α)} :
    y ∈ ball x U ↔ x ∈ ball y Uᶠˡ := by
  rw [ball, ball, mem_preimage, mem_preimage]
  exact mem_flip

lemma idRel_flip :
    idRelᶠˡ = @idRel α := by
  ext x
  rw [flip, mem_idRel, mem_preimage, mem_idRel, Prod.fst_swap, Prod.snd_swap]
  tauto

lemma flip_subset_flip {U V : Set (α × α)} :
    Uᶠˡ ⊆ Vᶠˡ ↔ U ⊆ V :=
  preimage_subset_preimage_iff fun x _ ↦ ⟨Prod.swap x, Prod.swap_swap x⟩

lemma idRel_sub_flip {U : Set (α × α)} :
    idRel ⊆ Uᶠˡ ↔ idRel ⊆ U := by
  rw [← idRel_flip, flip_subset_flip, idRel_flip]

lemma isOpen_flip [UniformSpace α] {U : Set (α × α)} :
    IsOpen Uᶠˡ ↔ IsOpen U := by
  refine ⟨fun h ↦ ?_, fun h ↦ continuous_swap.isOpen_preimage U h⟩
  rw [← flip_flip (U := U)]
  exact continuous_swap.isOpen_preimage Uᶠˡ h

lemma flip_mem_uniformity [UniformSpace α] {U : Set (α × α)} :
    Uᶠˡ ∈ 𝓤 α ↔ U ∈ 𝓤 α := by
  refine ⟨fun h ↦ ?_, fun h ↦ UniformSpace.symm h⟩
  rw [← flip_flip (U := U)]
  exact UniformSpace.symm h

lemma comp_flip_mem_entourage [UniformSpace α] {U : Set (α × α)} (h : U ∈ 𝓤 α) :
    ∃ V ∈ 𝓤 α, V ○ Vᶠˡ ⊆ U := by
  obtain ⟨V, V_uni, V_symm, V_U⟩ := comp_symm_mem_uniformity_sets h
  exact ⟨V, V_uni, (isSymmetricRel_iff.1 V_symm).symm ▸ V_U⟩








def thicken (s : Set α) (U : Set (α × α)) :=
  ⋃ x ∈ s, ball x U

lemma thicken_def {s : Set α} {U : Set (α × α)} {x : α} :
    x ∈ thicken s U ↔ ∃ y ∈ s, x ∈ ball y U := by
  simp only [thicken, mem_iUnion, exists_prop]

lemma mem_thicken {s : Set α} {U : Set (α × α)} {x y : α} (hy : y ∈ s) (h : x ∈ ball y U) :
    x ∈ thicken s U :=
  thicken_def.2 ⟨y, hy, h⟩

lemma thicken_mono_left {s t : Set α} (h : s ⊆ t) (U : Set (α × α)) :
    thicken s U ⊆ thicken t U :=
  biUnion_subset_biUnion_left h

lemma thicken_mono_right (s : Set α) {U V : Set (α × α)} (h : U ⊆ V) :
    thicken s U ⊆ thicken s V :=
  biUnion_mono (subset_refl s) (fun x _  ↦ ball_mono h x)

@[simp]
lemma thicken_empty {U : Set (α × α)} :
    thicken ∅ U = ∅ :=
  biUnion_empty (fun x ↦ ball x U)

@[simp]
lemma thicken_singleton (x : α) (U : Set (α × α)) :
    thicken {x} U = ball x U :=
  biUnion_singleton x (fun y ↦ ball y U)

lemma ball_sub_thicken {s : Set α} (U : Set (α × α)) {x : α} (h : x ∈ s) :
    ball x U ⊆ thicken s U :=
  subset_biUnion_of_mem (u := fun y ↦ ball y U) h

theorem thicken_idRel {s : Set α} :
    thicken s idRel = s := by
  ext x
  simp only [thicken, ball, mem_iUnion, mem_preimage, mem_idRel, exists_prop, exists_eq_right]

lemma thicken_compRel {s : Set α} {U V : Set (α × α)} :
    thicken (thicken s U) V = thicken s (U ○ V) := by
  apply subset_antisymm <;> intro x x_s
  · obtain ⟨y, y_s, y_x⟩ := thicken_def.1 x_s
    obtain ⟨z, z_s, z_y⟩ := thicken_def.1 y_s
    exact mem_thicken z_s (prodMk_mem_compRel z_y y_x)
  · obtain ⟨z, z_s, z_x⟩ := thicken_def.1 x_s
    obtain ⟨y, z_y, y_x⟩ := mem_compRel.1 z_x
    exact mem_thicken (mem_thicken z_s z_y) y_x

theorem self_subset_thicken  {s : Set α} {U : Set (α × α)} (h : idRel ⊆ U) :
    s ⊆ thicken s U :=
  thicken_idRel.symm.trans_subset (thicken_mono_right s h)

lemma thicken_union {s t : Set α} {U : Set (α × α)} :
    thicken (s ∪ t) U = (thicken s U) ∪ (thicken t U) := biUnion_union s t _

lemma thicken_iUnion {ι : Sort*} {s : ι → Set α} {U : Set (α × α)} :
    thicken (⋃ i, s i) U = ⋃ i, thicken (s i) U := biUnion_iUnion s _

lemma thicken_biUnion {β : Type*} {s : β → Set α} {t : Set β} {U : Set (α × α)} :
    thicken (⋃ i ∈ t, s i) U = ⋃ i ∈ t, thicken (s i) U := by
  rw [biUnion_eq_iUnion, biUnion_eq_iUnion]
  exact thicken_iUnion

lemma thicken_inter {s t : Set α} {U : Set (α × α)} :
    thicken (s ∩ t) U ⊆ (thicken s U) ∩ (thicken t U) := by
  intro x x_st
  obtain ⟨y, y_st, x_y⟩ := thicken_def.1 x_st
  exact ⟨thicken_def.2 ⟨y, y_st.1, x_y⟩, thicken_def.2 ⟨y, y_st.2, x_y⟩⟩

lemma thicken_iInter {ι : Sort*} {s : ι → Set α} {U : Set (α × α)} :
    thicken (⋂ i, s i) U ⊆ ⋂ i, thicken (s i) U := by
  refine fun x x_s ↦ mem_iInter.2 fun i ↦ ?_
  obtain ⟨y, y_s, x_y⟩ := thicken_def.1 x_s
  exact thicken_def.2 ⟨y, (mem_iInter.1 y_s) i, x_y⟩

lemma thicken_biInter {β : Type*} {s : β → Set α} {t : Set β} {U : Set (α × α)} :
    thicken (⋂ i ∈ t, s i) U ⊆ ⋂ i ∈ t, thicken (s i) U := by
  refine fun x x_st ↦ mem_iInter₂.2 fun i i_t ↦ ?_
  obtain ⟨y, y_st, x_y⟩ := thicken_def.1 x_st
  exact thicken_def.2 ⟨y, (mem_iInter₂.1 y_st) i i_t, x_y⟩

-- TODO : Version avec une base d'entourages.
lemma mem_closure_iff_thicken [UniformSpace α] {s : Set α} :
    closure s = ⋂ U ∈ 𝓤 α, thicken s U := by
  ext x
  rw [mem_closure_iff_ball, mem_iInter₂]
  apply Iff.intro <;> intro h U U_uni
  · obtain ⟨y, y_x, y_s⟩ := h (flip_mem_uniformity.2 U_uni)
    exact ball_sub_thicken U y_s (ball_flip.2 y_x)
  · obtain ⟨y, y_s, y_x⟩ := thicken_def.1 (h Uᶠˡ (flip_mem_uniformity.2 U_uni))
    exact ⟨y, ball_flip.2 y_x, y_s⟩

lemma closure_subset_thicken [UniformSpace α] {s : Set α} {U : Set (α × α)} (h : U ∈ 𝓤 α) :
    closure s ⊆ thicken s U := by
  rw [mem_closure_iff_thicken]
  exact biInter_subset_of_mem h

lemma closure_thicken [UniformSpace α] {s : Set α} {U : Set (α × α)} :
    closure (thicken s U) = ⋂ V ∈ 𝓤 α, thicken s (U ○ V) := by
  simp only [mem_closure_iff_thicken, thicken_compRel]

lemma isOpen_thicken [UniformSpace α] {s : Set α} {U : Set (α × α)} (h : IsOpen U) :
    IsOpen (thicken s U) :=
  isOpen_biUnion fun x _ ↦ isOpen_ball x h

lemma thicken_closure_of_isOpen [UniformSpace α] {s : Set α} {U : Set (α × α)} (h : IsOpen U) :
    thicken (closure s) U = thicken s U := by
  refine subset_antisymm ?_ (thicken_mono_left subset_closure U)
  intro x x_s
  obtain ⟨y, y_s, y_x⟩ := thicken_def.1 x_s
  rw [ball_flip] at y_x
  obtain ⟨z, z_x, z_s⟩ := mem_closure_iff.1 y_s (ball x Uᶠˡ) (isOpen_ball x (isOpen_flip.2 h)) y_x
  rw [← ball_flip] at z_x
  exact thicken_def.2 ⟨z, z_s, z_x⟩

lemma disjoint_thicken {s t : Set α} {U V : Set (α × α)} :
    Disjoint (thicken s U) (thicken t V) ↔ Disjoint (thicken s (U ○ Vᶠˡ)) t := by
  simp only [disjoint_iff_inter_eq_empty, eq_empty_iff_forall_not_mem]
  refine ⟨fun h y y_st ↦ ?_, fun h z z_st ↦ ?_⟩
  · obtain ⟨x, x_s, y_x⟩ := thicken_def.1 y_st.1
    obtain ⟨z, x_z, z_y⟩ := mem_compRel.1 y_x
    exact h z ⟨thicken_def.2 ⟨x, x_s, x_z⟩, thicken_def.2 ⟨y, y_st.2, z_y⟩⟩
  · obtain ⟨x, x_s, z_x⟩ := thicken_def.1 z_st.1
    obtain ⟨y, y_t, z_y⟩ := thicken_def.1 z_st.2
    apply h y ⟨thicken_def.2 ⟨x, x_s, mem_ball_comp z_x (ball_flip.1 z_y)⟩, y_t⟩



open scoped Topology
-- Alternative proof of Disjoint.exists_uniform_thickening.
-- TODO : Remove the TODO on Disjoint.exists_uniform_thickening.
lemma Disjoint.exists_uniform_thickening' [UniformSpace α] {s t : Set α} (hs : IsCompact s)
    (ht : IsClosed t) (hst : Disjoint s t) :
    ∃ U ∈ 𝓤 α, Disjoint (thicken s U) (thicken t U) := by
  have : tᶜ ∈ 𝓝ˢ s := ht.isOpen_compl.mem_nhdsSet.mpr hst.le_compl_right
  obtain ⟨U, hU, hUAB⟩ := (hs.nhdsSet_basis_uniformity (𝓤 α).basis_sets).mem_iff.1 this
  obtain ⟨V, hV, hVU⟩ := comp_flip_mem_entourage hU
  rw [subset_compl_iff_disjoint_left, id_eq, disjoint_comm, ← thicken] at hUAB
  exact ⟨V, hV, disjoint_thicken.2 (hUAB.mono_left (thicken_mono_right s hVU))⟩



end Thicken

end UniformSpace
