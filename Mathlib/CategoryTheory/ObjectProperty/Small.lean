/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.ObjectProperty.CompleteLattice
import Mathlib.CategoryTheory.ObjectProperty.Equivalence
import Mathlib.CategoryTheory.ObjectProperty.Opposite
import Mathlib.CategoryTheory.EssentiallySmall

/-!
# Smallness of a property of objects

In this file, given `P : ObjectProperty C`, we define
`ObjectProperty.Small.{w} P` as an abbreviation for `Small.{w} (Subtype P)`.

-/

universe w' w v u

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C]

/-- A property of objects is small relative to a universe `w`
if the corresponding subtype is. -/
@[pp_with_univ]
protected abbrev Small (P : ObjectProperty C) : Prop := _root_.Small.{w} (Subtype P)

instance (P : ObjectProperty C) [ObjectProperty.Small.{w} P] :
    Small.{w} P.FullSubcategory :=
  small_of_surjective (f := fun (x : Subtype P) ↦ ⟨x.1, x.2⟩) (fun x ↦ ⟨⟨x.1, x.2⟩, rfl⟩)

lemma Small.of_le {P Q : ObjectProperty C} [ObjectProperty.Small.{w} Q] (h : P ≤ Q) :
    ObjectProperty.Small.{w} P :=
  small_of_injective (Subtype.map_injective h Function.injective_id)

instance (P : ObjectProperty C) [ObjectProperty.Small.{w} P] :
    ObjectProperty.Small.{w} P.op :=
  small_of_injective P.subtypeOpEquiv.injective

instance (P : ObjectProperty Cᵒᵖ) [ObjectProperty.Small.{w} P] :
    ObjectProperty.Small.{w} P.unop := by
  simpa only [← small_congr P.unop.subtypeOpEquiv]

instance {ι : Type*} (X : ι → C) [Small.{w} ι] :
    ObjectProperty.Small.{w} (ofObj X) :=
  small_of_surjective (f := fun i ↦ ⟨X i, by simp⟩) (by rintro ⟨_, ⟨i⟩⟩; simp)

instance (X Y : C) : ObjectProperty.Small.{w} (.pair X Y) := by
  dsimp [pair]
  infer_instance

instance {P Q : ObjectProperty C} [ObjectProperty.Small.{w} Q] :
    ObjectProperty.Small.{w} (P ⊓ Q) :=
  Small.of_le inf_le_right

instance {P Q : ObjectProperty C} [ObjectProperty.Small.{w} P] :
    ObjectProperty.Small.{w} (P ⊓ Q) :=
  Small.of_le inf_le_left

instance {P Q : ObjectProperty C} [ObjectProperty.Small.{w} P] [ObjectProperty.Small.{w} Q] :
    ObjectProperty.Small.{w} (P ⊔ Q) :=
  small_of_surjective (f := fun (x : Subtype P ⊕ Subtype Q) ↦ match x with
      | .inl x => ⟨x.1, Or.inl x.2⟩
      | .inr x => ⟨x.1, Or.inr x.2⟩)
    (by rintro ⟨x, hx | hx⟩ <;> aesop)

instance {α : Type*} (P : α → ObjectProperty C)
    [∀ a, ObjectProperty.Small.{w} (P a)] [Small.{w} α] :
    ObjectProperty.Small.{w} (⨆ a, P a) :=
  small_of_surjective (f := fun (x : Σ a, Subtype (P a)) ↦ ⟨x.2.1, by aesop⟩)
    (fun ⟨x, hx⟩ ↦ by aesop)

/-- A property of objects is essentially small relative to a universe `w`
if it is contained in the closure by isomorphisms of a small property. -/
@[pp_with_univ]
protected class EssentiallySmall (P : ObjectProperty C) : Prop where
  exists_small_le' (P) : ∃ (Q : ObjectProperty C) (_ : ObjectProperty.Small.{w} Q),
    P ≤ Q.isoClosure

lemma EssentiallySmall.exists_small_le (P : ObjectProperty C)
    [ObjectProperty.EssentiallySmall.{w} P] :
    ∃ (Q : ObjectProperty C) (_ : ObjectProperty.Small.{w} Q), Q ≤ P ∧ P ≤ Q.isoClosure := by
  obtain ⟨Q, _, hQ⟩ := exists_small_le' P
  let P' := Q ⊓ P.isoClosure
  have h (X' : Subtype P') : ∃ (X : Subtype P), Nonempty (X'.1 ≅ X.1) :=
    ⟨⟨X'.2.2.choose, X'.2.2.choose_spec.choose⟩, X'.2.2.choose_spec.choose_spec⟩
  choose φ hφ using h
  refine ⟨fun X ↦ X ∈ Set.range (Subtype.val ∘ φ), ?_, ?_, ?_⟩
  · exact small_of_surjective (f := fun X ↦ ⟨(φ X).1, by tauto⟩)
      (by rintro ⟨_, Z, rfl⟩; exact ⟨Z, rfl⟩)
  · intro X hX
    simp only [Set.mem_range, Function.comp_apply, Subtype.exists] at hX
    obtain ⟨Y, hY, rfl⟩ := hX
    exact (φ ⟨Y, hY⟩).2
  · intro X hX
    obtain ⟨Y, hY, ⟨e⟩⟩ := hQ _ hX
    let Z : Subtype P' := ⟨Y, hY, ⟨X, hX, ⟨e.symm⟩⟩⟩
    exact ⟨_, ⟨Z, rfl⟩, ⟨e ≪≫ (hφ Z).some⟩⟩

instance (P : ObjectProperty C) [ObjectProperty.Small.{w} P] :
    ObjectProperty.EssentiallySmall.{w} P where
  exists_small_le' := ⟨P, inferInstance, le_isoClosure P⟩

instance (P : ObjectProperty C) [ObjectProperty.EssentiallySmall.{w} P] :
    ObjectProperty.EssentiallySmall.{w} P.isoClosure where
  exists_small_le' := by
    obtain ⟨Q, _, _, _⟩ := EssentiallySmall.exists_small_le.{w} P
    exact ⟨Q, inferInstance, by rwa [isoClosure_le_iff]⟩

lemma EssentiallySmall.exists_small (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
    [ObjectProperty.EssentiallySmall.{w} P] :
    ∃ (P₀ : ObjectProperty C) (_ : ObjectProperty.Small.{w} P₀), P = P₀.isoClosure := by
  obtain ⟨Q, _, hQ₁, hQ₂⟩ := exists_small_le P
  exact ⟨Q, inferInstance, le_antisymm hQ₂ (by rwa [isoClosure_le_iff])⟩

lemma EssentiallySmall.of_le {P Q : ObjectProperty C}
    [ObjectProperty.EssentiallySmall.{w} Q] (h : P ≤ Q) :
    ObjectProperty.EssentiallySmall.{w} P where
  exists_small_le' := by
    obtain ⟨R, _, hR⟩ := EssentiallySmall.exists_small_le' Q
    exact ⟨R, inferInstance, h.trans hR⟩

instance {P Q : ObjectProperty C}
    [ObjectProperty.EssentiallySmall.{w} P] [ObjectProperty.EssentiallySmall.{w} Q] :
    ObjectProperty.EssentiallySmall.{w} (P ⊔ Q) := by
  obtain ⟨P', _, hP'⟩ := EssentiallySmall.exists_small_le' P
  obtain ⟨Q', _, hQ'⟩ := EssentiallySmall.exists_small_le' Q
  refine ⟨P' ⊔ Q', inferInstance, ?_⟩
  simp only [sup_le_iff]
  constructor
  · exact hP'.trans (monotone_isoClosure le_sup_left)
  · exact hQ'.trans (monotone_isoClosure le_sup_right)

instance {α : Type*} (P : α → ObjectProperty C)
    [∀ a, ObjectProperty.EssentiallySmall.{w} (P a)] [Small.{w} α] :
    ObjectProperty.EssentiallySmall.{w} (⨆ a, P a) where
  exists_small_le' := by
    have h (a : α) := EssentiallySmall.exists_small_le' (P a)
    choose Q _ hQ using h
    refine ⟨⨆ a, Q a, inferInstance, ?_⟩
    simp only [iSup_le_iff]
    intro a
    exact (hQ a).trans (monotone_isoClosure (le_iSup Q a))

instance (P : ObjectProperty C) [LocallySmall.{w} C]
    [ObjectProperty.EssentiallySmall.{w} P] : EssentiallySmall.{w} P.FullSubcategory := by
  obtain ⟨Q, _, h₁, h₂⟩ := EssentiallySmall.exists_small_le P
  have := (isEquivalence_ιOfLE_iff h₁).2 h₂
  rw [← essentiallySmall_congr (ιOfLE h₁).asEquivalence]
  exact essentiallySmall_of_small_of_locallySmall _

lemma exists_equivalence_iff (P : ObjectProperty C) [LocallySmall.{w'} C] :
    (∃ (J : Type w) (_ : Category.{w'} J), Nonempty (P.FullSubcategory ≌ J)) ↔
      ObjectProperty.EssentiallySmall.{w} P := by
  refine ⟨fun ⟨J, _, ⟨e⟩⟩ ↦ ?_, fun _ ↦ ?_⟩
  · exact ⟨.ofObj (e.inverse ⋙ P.ι).obj, inferInstance,
      fun X hX ↦ ⟨_, ⟨⟨(e.functor.obj ⟨X, hX⟩)⟩, ⟨P.ι.mapIso (e.unitIso.app ⟨X, hX⟩)⟩⟩⟩⟩
  · obtain ⟨Q, _, h₁, h₂⟩ := EssentiallySmall.exists_small_le.{w} P
    rw [← isEquivalence_ιOfLE_iff h₁] at h₂
    exact ⟨_, _, ⟨((ιOfLE h₁).asEquivalence.symm.trans
      (Shrink.equivalence.{w} Q.FullSubcategory)).trans (ShrinkHoms.equivalence.{w'} _)⟩⟩

end ObjectProperty

lemma exists_equivalence_iff_of_locallySmall
    (C : Type u) [Category.{v} C] [LocallySmall.{w'} C] :
    (∃ (J : Type w) (_ : Category.{w'} J), Nonempty (C ≌ J)) ↔
      ObjectProperty.EssentiallySmall.{w} (C := C) ⊤ := by
  rw [← ObjectProperty.exists_equivalence_iff]
  exact ⟨fun ⟨J, _, ⟨e⟩⟩ ↦ ⟨J, _, ⟨(ObjectProperty.topEquivalence C).trans e⟩⟩,
    fun ⟨J, _, ⟨e⟩⟩ ↦ ⟨J, _, ⟨(ObjectProperty.topEquivalence C).symm.trans e⟩⟩⟩

end CategoryTheory
