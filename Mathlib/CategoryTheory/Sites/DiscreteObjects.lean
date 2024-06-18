/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Adjunction.DiscreteObjects
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.DenseSubsite
/-!

# Discrete objects in sheaf categories.
-/

open CategoryTheory Limits Functor Adjunction Opposite

namespace CategoryTheory.Sheaf

variable {C : Type*} [Category C]
variable (J : GrothendieckTopology C) (A : Type*) [Category A] [HasWeakSheafify J A]
  [(constantSheaf J A).Faithful] [(constantSheaf J A).Full] {t : C} (ht : IsTerminal t)

/--
A sheaf is discrete if it is discrete object of the "underlying object" functor from the sheaf
category to the target category.
-/
abbrev IsDiscrete (F : Sheaf J A) : Prop :=
  haveI := HasDiscreteObjects.mk' _ (constantSheafAdj J A ht)
  CategoryTheory.IsDiscrete ((sheafSections J A).obj (op t)) F

theorem isDiscrete_iff_mem_essImage (F : Sheaf J A) {t : C} (ht : IsTerminal t) :
    haveI := HasDiscreteObjects.mk' _ (constantSheafAdj J A ht)
    F.IsDiscrete J A ht ↔ F ∈ (constantSheaf J A).essImage :=
  CategoryTheory.isDiscrete_iff_mem_essImage _ (constantSheafAdj J A ht) _

section

universe w v u
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (A : Type w) [Category.{max u v} A]
  [HasWeakSheafify J A]
  {t : C} (ht : IsTerminal t)

variable {D : Type u} [Category.{v} D] (K : GrothendieckTopology D) [HasWeakSheafify K A]
variable (G : C ⥤ D) [G.Full] [G.Faithful]
  [∀ (X : Dᵒᵖ), HasLimitsOfShape (StructuredArrow X G.op) A]
  [G.IsCoverDense K] [G.IsContinuous J K] [G.IsCocontinuous J K] (ht' : IsTerminal (G.obj t))

variable [(constantSheaf J A).Faithful] [(constantSheaf J A).Full]

open Functor.IsCoverDense

noncomputable example :
    let e : Sheaf J A ≌ Sheaf K A :=
      sheafEquivOfCoverPreservingCoverLifting G J K A
    e.inverse ⋙ (sheafSections J A).obj (op t) ≅ (sheafSections K A).obj (op (G.obj t)) :=
  Iso.refl _

/--
The constant sheaf functor commutes up to isomorphism with any equivalence of sheaf categories.

This is an auxiliary definition used to prove `Sheaf.isDiscrete_iff` below, which says that the
property of a sheaf of being a discrete object is invariant under equivalence of sheaf categories.
-/
noncomputable def equivCommuteConstant :
    let e : Sheaf J A ≌ Sheaf K A :=
      sheafEquivOfCoverPreservingCoverLifting G J K A
    constantSheaf J A ⋙ e.functor ≅ constantSheaf K A :=
  let e : Sheaf J A ≌ Sheaf K A :=
      sheafEquivOfCoverPreservingCoverLifting G J K A
  (Adjunction.leftAdjointUniq ((constantSheafAdj J A ht).comp e.toAdjunction)
    (constantSheafAdj K A ht'))

/--
The constant sheaf functor commutes up to isomorphism with any equivalence of sheaf categories.

This is an auxiliary definition used to prove `Sheaf.isDiscrete_iff` below, which says that the
property of a sheaf of being a discrete object is invariant under equivalence of sheaf categories.
-/
noncomputable def equivCommuteConstant' :
    let e : Sheaf J A ≌ Sheaf K A :=
      sheafEquivOfCoverPreservingCoverLifting G J K A
    constantSheaf J A ≅ constantSheaf K A ⋙ e.inverse :=
  let e : Sheaf J A ≌ Sheaf K A :=
      sheafEquivOfCoverPreservingCoverLifting G J K A
  isoWhiskerLeft (constantSheaf J A) e.unitIso ≪≫
    isoWhiskerRight (equivCommuteConstant J A ht K G ht') e.inverse

/--
The property of a sheaf of being a discrete object is invariant under equivalence of sheaf
categories.
-/
lemma isDiscrete_iff (F : Sheaf K A) :
    let e : Sheaf J A ≌ Sheaf K A :=
      sheafEquivOfCoverPreservingCoverLifting G J K A
    haveI : (constantSheaf K A).Faithful :=
      Functor.Faithful.of_iso (equivCommuteConstant J A ht K G ht')
    haveI : (constantSheaf K A).Full :=
      Functor.Full.of_iso (equivCommuteConstant J A ht K G ht')
    (e.inverse.obj F).IsDiscrete J A ht ↔ IsDiscrete K A ht' F := by
  intro e
  simp only [isDiscrete_iff_mem_essImage]
  constructor
  · intro ⟨Y, ⟨i⟩⟩
    let j : (constantSheaf K A).obj Y ≅ F :=
      (equivCommuteConstant J A ht K G ht').symm.app _ ≪≫ e.functor.mapIso i ≪≫ e.counitIso.app _
    exact ⟨_, ⟨j⟩⟩
  · intro ⟨Y, ⟨i⟩⟩
    let j : (constantSheaf J A).obj Y ≅ e.inverse.obj F :=
      (equivCommuteConstant' J A ht K G ht').app _ ≪≫ e.inverse.mapIso i
    exact ⟨_, ⟨j⟩⟩

end

end CategoryTheory.Sheaf
