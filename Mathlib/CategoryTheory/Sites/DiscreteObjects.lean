/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Adjunction.DiscreteObjects
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.DenseSubsite
import Mathlib.CategoryTheory.Sites.PreservesSheafification
/-!

# Discrete objects in sheaf categories.

-/

open CategoryTheory Limits Functor Adjunction Opposite

namespace CategoryTheory.Sheaf

variable {C : Type*} [Category C]
variable (J : GrothendieckTopology C) (A : Type*) [Category A] [HasWeakSheafify J A]
  [(constantSheaf J A).Faithful] [(constantSheaf J A).Full] {t : C} (ht : IsTerminal t)

/--
A sheaf is discrete if it is a discrete object of the "underlying object" functor from the sheaf
category to the target category.
-/
abbrev IsDiscrete (F : Sheaf J A) : Prop :=
  haveI := HasDiscreteObjects.mk' _ (constantSheafAdj J A ht)
  CategoryTheory.IsDiscrete ((sheafSections J A).obj (op t)) F

theorem isDiscrete_iff_isIso_counit_app (F : Sheaf J A) :
    haveI := HasDiscreteObjects.mk' _ (constantSheafAdj J A ht)
    F.IsDiscrete ht ↔ IsIso ((constantSheafAdj J A ht).counit.app F) :=
  CategoryTheory.isDiscrete_iff_isIso_counit_app _ (constantSheafAdj J A ht) _

theorem isDiscrete_iff_mem_essImage (F : Sheaf J A) {t : C} (ht : IsTerminal t) :
    haveI := HasDiscreteObjects.mk' _ (constantSheafAdj J A ht)
    F.IsDiscrete J A ht ↔ F ∈ (constantSheaf J A).essImage :=
  CategoryTheory.isDiscrete_iff_mem_essImage _ (constantSheafAdj J A ht) _

section

universe w' w v u
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (A : Type w) [Category.{w'} A]
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

universe r s
variable {A : Type w} [Category.{w'} A] {B : Type s} [Category.{r} B] (U : A ⥤ B)
  [HasWeakSheafify J A] [HasWeakSheafify J B]
variable [(constantSheaf J A).Faithful] [(constantSheaf J A).Full]
variable [(constantSheaf J B).Faithful] [(constantSheaf J B).Full] [J.PreservesSheafification U]
variable (F : Sheaf J A) [J.HasSheafCompose U]

noncomputable def constantCommuteCompose :
    constantSheaf J A ⋙ sheafCompose J U ≅ U ⋙ constantSheaf J B :=
  Functor.associator _ _ _ ≪≫ (isoWhiskerLeft (const Cᵒᵖ)
    (sheafComposeNatIso J U (sheafificationAdjunction J A) (sheafificationAdjunction J B)).symm) ≪≫
    (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (compConstIso _ _).symm _

noncomputable def constantCommuteCompose' (X : A) :
    ((constantSheaf J A).obj X).val ⋙ U ≅ ((constantSheaf J B).obj (U.obj X)).val :=
  (sheafifyComposeIso J U ((const Cᵒᵖ).obj X)).symm ≪≫
    (presheafToSheaf J B ⋙ sheafToPresheaf J B).mapIso (constComp Cᵒᵖ X U)

theorem sheafCompose_reflects_discrete [(sheafCompose J U).ReflectsIsomorphisms]
    [h : ((sheafCompose J U).obj F).IsDiscrete J B ht] :
    F.IsDiscrete J A ht := by
  rw [isDiscrete_iff_isIso_counit_app] at h ⊢
  let j := constantCommuteCompose' J U (F.val.obj ⟨t⟩)
  let fcounit := (constantSheafAdj J A ht).counit.app F
  let fff := (sheafCompose J U).map fcounit
  let gcounit := ((constantSheafAdj J B ht).counit.app ((sheafCompose J U).obj F))
  have h : (sheafifyComposeIso J U ((const Cᵒᵖ).obj (F.val.obj { unop := t }))).hom ≫ fff.val =
      ((presheafToSheaf J B ⋙ sheafToPresheaf J B).mapIso
        (constComp Cᵒᵖ _ U)).hom ≫ gcounit.val := by
    apply sheafify_hom_ext _ _ _ ((sheafCompose J U).obj F).cond
    simp only [sheafCompose_obj_val, id_obj, comp_obj, flip_obj_obj, sheafToPresheaf_obj,
      sheafComposeIso_hom_fac_assoc, mapIso_hom, Functor.comp_map, sheafToPresheaf_map]
    change _ = (sheafificationAdjunction J _ ).unit.app _ ≫ ((sheafToPresheaf J B).map _) ≫ _
    erw [Adjunction.unit_naturality_assoc]
    simp only [const_obj_obj, const_obj_map, id_obj, constComp, comp_obj, sheafToPresheaf_obj,
      sheafificationAdjunction_unit_app]
    ext
    simp only [comp_obj, const_obj_obj, NatTrans.comp_app, whiskerRight_app, Category.id_comp]
    simp only [comp_obj, flip_obj_obj, sheafToPresheaf_obj, id_obj, constantSheafAdj,
      Adjunction.comp, evaluation_obj_obj, NatTrans.comp_app, associator_hom_app, whiskerLeft_app,
      whiskerRight_app, map_comp, instCategorySheaf_comp_val, sheafCompose_obj_val,
      sheafCompose_map_val, instCategorySheaf_id_val, sheafificationAdjunction_counit_app_val,
      NatTrans.id_app, sheafifyMap_sheafifyLift, Category.comp_id, Category.id_comp, fff, fcounit,
      gcounit]
    erw [Functor.map_id, Category.id_comp, ← NatTrans.comp_app]
    simp only [toSheafify_sheafifyLift, ← Functor.map_comp, ← NatTrans.comp_app,
      sheafifyMap_sheafifyLift, Category.comp_id,
      constantPresheafAdj, comp_obj, evaluation_obj_obj, id_obj, op_unop,
      mkOfUnitCounit_counit, Functor.comp_map]
  have : gcounit.val = j.inv ≫ fff.val := by
    simp only [comp_obj, flip_obj_obj, sheafToPresheaf_obj, sheafCompose_obj_val, id_obj,
      constantCommuteCompose', Iso.trans_inv, mapIso_inv, Functor.comp_map, sheafToPresheaf_map,
      Iso.symm_inv, Category.assoc, h, mapIso_hom, j, ← Sheaf.instCategorySheaf_comp_val,
      Iso.map_inv_hom_id_assoc]
  have : j.hom ≫ gcounit.val = fff.val := by simp [this]
  have : IsIso ((sheafToPresheaf J B).map fff) := by
    simp only [comp_obj, flip_obj_obj, sheafToPresheaf_obj, sheafCompose_obj_val, id_obj,
      sheafToPresheaf_map, ← this]
    change IsIso (_ ≫ ((sheafToPresheaf _ _).map gcounit))
    infer_instance
  have : IsIso fff := by
    apply ReflectsIsomorphisms.reflects (sheafToPresheaf J B) _
  apply ReflectsIsomorphisms.reflects (sheafCompose J U) _

theorem sheafCompose_preserves_discrete [h : F.IsDiscrete J A ht] :
    ((sheafCompose J U).obj F).IsDiscrete J B ht := by
  rw [isDiscrete_iff_mem_essImage] at h ⊢
  obtain ⟨Y, ⟨i⟩⟩ := h
  exact ⟨U.obj Y, ⟨(constantCommuteCompose J U).symm.app _ ≪≫ (sheafCompose J U).mapIso i⟩⟩

end

end CategoryTheory.Sheaf
