/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
/-!

# The constant sheaf

We define the constant sheaf functor (the sheafification of the constant presheaf)
`constantSheaf : D ⥤ Sheaf J D` and prove that it is left adjoint to evaluation at a terminal
object (see `constantSheafAdj`).

We also define a predicate on sheaves, `Sheaf.IsConstant`, saying that a sheaf is in the
essential image of the constant sheaf functor.

## Main results

* `Sheaf.isConstant_iff_isIso_counit_app`: Provided that the constant sheaf functor is fully
  faithful, a sheaf is constant if and only if the counit of the constant sheaf adjunction applied
  to it is an isomorphism.

* `Sheaf.isConstant_iff_of_equivalence` : The property of a sheaf of being constant is invariant
  under equivalence of sheaf categories.

* `Sheaf.isConstant_iff_forget` : Given a "forgetful" functor `U : D ⥤ B` a sheaf `F : Sheaf J D` is
  constant if and only if the sheaf given by postcomposition with `U` is constant.
-/

namespace CategoryTheory

open Limits Opposite Category Functor Sheaf Adjunction

variable {C : Type*} [Category C] (J : GrothendieckTopology C)
variable (D : Type*) [Category D]

/-- The constant presheaf functor is left adjoint to evaluation at a terminal object. -/
@[simps! unit_app counit_app_app]
noncomputable def constantPresheafAdj {T : C} (hT : IsTerminal T) :
    Functor.const Cᵒᵖ ⊣ (evaluation Cᵒᵖ D).obj (op T) where
  unit := (Functor.constCompEvaluationObj D (op T)).hom
  counit := {
    app := fun F => {
      app := fun ⟨X⟩ => F.map (IsTerminal.from hT X).op
      naturality := fun _ _ _ => by
        simp only [Functor.comp_obj, Functor.const_obj_obj, Functor.id_obj, Functor.const_obj_map,
          Category.id_comp, ← Functor.map_comp]
        congr
        simp }
    naturality := by intros; ext; simp /- Note: `aesop` works but is kind of slow -/ }

variable [HasWeakSheafify J D]

/--
The functor which maps an object of `D` to the constant sheaf at that object, i.e. the
sheafification of the constant presheaf.
-/
noncomputable def constantSheaf : D ⥤ Sheaf J D := Functor.const Cᵒᵖ ⋙ (presheafToSheaf J D)

/-- The constant sheaf functor is left adjoint to evaluation at a terminal object. -/
@[simps! counit_app]
noncomputable def constantSheafAdj {T : C} (hT : IsTerminal T) :
    constantSheaf J D ⊣ (sheafSections J D).obj (op T) :=
  (constantPresheafAdj D hT).comp (sheafificationAdjunction J D)

variable {D}

namespace Sheaf

/--
A sheaf is constant if it is in the essential image of the constant sheaf functor.
-/
class IsConstant (F : Sheaf J D) : Prop where
  mem_essImage : (constantSheaf J D).essImage F

lemma mem_essImage_of_isConstant (F : Sheaf J D) [IsConstant J F] :
    (constantSheaf J D).essImage F :=
  IsConstant.mem_essImage

lemma isConstant_congr {F G : Sheaf J D} (i : F ≅ G) [IsConstant J F] : IsConstant J G where
  mem_essImage := essImage.ofIso i F.mem_essImage_of_isConstant

lemma isConstant_of_iso {F : Sheaf J D} {X : D} (i : F ≅ (constantSheaf J D).obj X) :
    IsConstant J F := ⟨_, ⟨i.symm⟩⟩

lemma isConstant_iff_mem_essImage {L : D ⥤ Sheaf J D} {T : C} (hT : IsTerminal T)
    (adj : L ⊣ (sheafSections J D).obj ⟨T⟩)
    (F : Sheaf J D) : IsConstant J F ↔ L.essImage F := by
  rw [essImage_eq_of_natIso (adj.leftAdjointUniq (constantSheafAdj J D hT))]
  exact ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩

lemma isConstant_of_isIso_counit_app (F : Sheaf J D) [HasTerminal C]
    [IsIso <| (constantSheafAdj J D terminalIsTerminal).counit.app F] : IsConstant J F where
  mem_essImage := ⟨_, ⟨asIso <| (constantSheafAdj J D terminalIsTerminal).counit.app F⟩⟩

instance [(constantSheaf J D).Faithful] [(constantSheaf J D).Full] (F : Sheaf J D)
    [IsConstant J F] {T : C} (hT : IsTerminal T) :
    IsIso ((constantSheafAdj J D hT).counit.app F) := by
  rw [isIso_counit_app_iff_mem_essImage]
  exact F.mem_essImage_of_isConstant

/--
If the constant sheaf functor is fully faithful, then a sheaf is constant if and only if the
counit of the constant sheaf adjunction applied to it is an isomorphism.
-/
lemma isConstant_iff_isIso_counit_app [(constantSheaf J D).Faithful] [(constantSheaf J D).Full]
    (F : Sheaf J D) {T : C} (hT : IsTerminal T) :
      IsConstant J F ↔ (IsIso <| (constantSheafAdj J D hT).counit.app F) :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ ⟨_, ⟨asIso <| (constantSheafAdj J D hT).counit.app F⟩⟩⟩

/--
A variant of `isConstant_iff_isIso_counit_app` for a general left adjoint to evaluation at a
terminal object.
-/
lemma isConstant_iff_isIso_counit_app' {L : D ⥤ Sheaf J D} {T : C} (hT : IsTerminal T)
    (adj : L ⊣ (sheafSections J D).obj ⟨T⟩)
    [L.Faithful] [L.Full] (F : Sheaf J D) : IsConstant J F ↔ IsIso (adj.counit.app F) :=
  (isConstant_iff_mem_essImage J hT adj F).trans (isIso_counit_app_iff_mem_essImage adj).symm

end Sheaf

section Equivalence
variable {C' : Type*} [Category C'] (K : GrothendieckTopology C') [HasWeakSheafify K D]
variable (G : C ⥤ C') [∀ (X : (C')ᵒᵖ), HasLimitsOfShape (StructuredArrow X G.op) D]
  [G.IsDenseSubsite J K] {T : C} (hT : IsTerminal T) (hT' : IsTerminal (G.obj T))

open IsDenseSubsite

variable (D) in
/--
The constant sheaf functor commutes up to isomorphism the equivalence of sheaf categories induced
by a dense subsite.
-/
noncomputable def equivCommuteConstant :
    constantSheaf J D ⋙ (sheafEquiv G J K D).functor ≅ constantSheaf K D :=
  ((constantSheafAdj J D hT).comp (sheafEquiv G J K D).toAdjunction).leftAdjointUniq
    (constantSheafAdj K D hT')

variable (D) in
/--
The constant sheaf functor commutes up to isomorphism the inverse equivalence of sheaf categories
induced by a dense subsite.
-/
noncomputable def equivCommuteConstant' :
    constantSheaf J D ≅ constantSheaf K D ⋙ (sheafEquiv G J K D).inverse :=
  isoWhiskerLeft (constantSheaf J D) (sheafEquiv G J K D).unitIso ≪≫
    isoWhiskerRight (equivCommuteConstant J D K G hT hT') (sheafEquiv G J K D).inverse

/- TODO: find suitable assumptions for proving generalizations of `equivCommuteConstant` and
`equivCommuteConstant'` above, to commute `constantSheaf` with pullback/pushforward of sheaves. -/

include hT hT' in
/--
The property of a sheaf of being constant is invariant under equivalence of sheaf
categories.
-/
lemma Sheaf.isConstant_iff_of_equivalence (F : Sheaf K D) :
    ((sheafEquiv G J K D).inverse.obj F).IsConstant J ↔ IsConstant K F := by
  constructor
  · exact fun ⟨Y, ⟨i⟩⟩ ↦ ⟨_, ⟨(equivCommuteConstant J D K G hT hT').symm.app _ ≪≫
      (sheafEquiv G J K D).functor.mapIso i ≪≫ (sheafEquiv G J K D).counitIso.app _⟩⟩
  · exact fun ⟨Y, ⟨i⟩⟩ ↦ ⟨_, ⟨(equivCommuteConstant' J D K G hT hT').app _ ≪≫
      (sheafEquiv G J K D).inverse.mapIso i⟩⟩

end Equivalence

section Forget

variable {B : Type*} [Category B] (U : D ⥤ B) [HasWeakSheafify J B]
  [J.PreservesSheafification U] [J.HasSheafCompose U] (F : Sheaf J D)

/--
The constant sheaf functor commutes with `sheafCompose J U` up to isomorphism, provided that `U`
preserves sheafification.
-/
noncomputable def constantCommuteCompose :
    constantSheaf J D ⋙ sheafCompose J U ≅ U ⋙ constantSheaf J B :=
  (isoWhiskerLeft (const Cᵒᵖ)
    (sheafComposeNatIso J U (sheafificationAdjunction J D) (sheafificationAdjunction J B)).symm) ≪≫
      isoWhiskerRight (compConstIso _ _).symm _

lemma constantCommuteCompose_hom_app_val (X : D) : ((constantCommuteCompose J U).hom.app X).val =
    (sheafifyComposeIso J U ((const Cᵒᵖ).obj X)).inv ≫ sheafifyMap J (constComp Cᵒᵖ X U).hom := rfl

/-- The counit of `constantSheafAdj` factors through the isomorphism `constantCommuteCompose`. -/
lemma constantSheafAdj_counit_w {T : C} (hT : IsTerminal T) :
    ((constantCommuteCompose J U).hom.app (F.val.obj ⟨T⟩)) ≫
      ((constantSheafAdj J B hT).counit.app ((sheafCompose J U).obj F)) =
        ((sheafCompose J U).map ((constantSheafAdj J D hT).counit.app F)) := by
  apply Sheaf.hom_ext
  rw [comp_val, constantCommuteCompose_hom_app_val, assoc, Iso.inv_comp_eq]
  apply sheafify_hom_ext _ _ _ ((sheafCompose J U).obj F).cond
  ext
  simp? says simp only [comp_obj, const_obj_obj, sheafCompose_obj_val, id_obj,
      constantSheafAdj_counit_app, comp_val,
      sheafificationAdjunction_counit_app_val, sheafifyMap_sheafifyLift, comp_id,
      toSheafify_sheafifyLift, NatTrans.comp_app, constComp_hom_app,
      constantPresheafAdj_counit_app_app, Functor.comp_map, id_comp, flip_obj_obj,
      sheafToPresheaf_obj, map_comp, sheafCompose_map_val, sheafComposeIso_hom_fac_assoc,
      whiskerRight_app]
  simp [← map_comp, ← NatTrans.comp_app]

lemma Sheaf.isConstant_of_forget [constantSheaf J D |>.Faithful] [constantSheaf J D |>.Full]
    [constantSheaf J B |>.Faithful] [constantSheaf J B |>.Full]
    [(sheafCompose J U).ReflectsIsomorphisms] [((sheafCompose J U).obj F).IsConstant J]
    {T : C} (hT : IsTerminal T) : F.IsConstant J := by
  have : IsIso ((sheafCompose J U).map ((constantSheafAdj J D hT).counit.app F)) := by
    rw [← constantSheafAdj_counit_w]
    infer_instance
  rw [F.isConstant_iff_isIso_counit_app (hT := hT)]
  exact isIso_of_reflects_iso _ (sheafCompose J U)

instance [h : F.IsConstant J] : ((sheafCompose J U).obj F).IsConstant J := by
  obtain ⟨Y, ⟨i⟩⟩ := h
  exact ⟨U.obj Y, ⟨(fullyFaithfulSheafToPresheaf _ _).preimageIso
    (((sheafifyComposeIso J U ((const Cᵒᵖ).obj Y)).symm ≪≫
      (presheafToSheaf J B ⋙ sheafToPresheaf J B).mapIso (constComp Cᵒᵖ Y U)).symm ≪≫
        (sheafToPresheaf _ _).mapIso ((sheafCompose J U).mapIso i))⟩⟩

lemma Sheaf.isConstant_iff_forget [constantSheaf J D |>.Faithful] [constantSheaf J D |>.Full]
    [constantSheaf J B |>.Faithful] [constantSheaf J B |>.Full]
      [(sheafCompose J U).ReflectsIsomorphisms] {T : C} (hT : IsTerminal T) :
        F.IsConstant J ↔ ((sheafCompose J U).obj F).IsConstant J :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ Sheaf.isConstant_of_forget _ U F hT⟩

end Forget

end CategoryTheory
