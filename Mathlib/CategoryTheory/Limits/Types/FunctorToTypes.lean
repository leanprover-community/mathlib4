/-
Copyright (c) 2025 Benoît Guillemet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benoît Guillemet
-/
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.IndYoneda
import Mathlib.CategoryTheory.Limits.Preserves.Ulift
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Natural transformations of presheaves as limits

Let `C` be a category and `F, G : Cᵒᵖ ⥤ Type w` two presheaves over `C`.
We give the natural isomorphism between natural transformations `F ⟶ G` and objects of the limit of
sections of `G` over sections of `F`.
-/

universe u v w

open CategoryTheory Limits

namespace Category

section sectionOver

variable {C : Type u} [Category.{v,u} C] (F : C ⥤ Type w)

def sectionOver : Type max u w :=  (X : C) × F.obj X

@[ext]
structure sectionOverMorphism (s s' : sectionOver F) where
  fst : s.fst ⟶ s'.fst
  w : F.map fst s.snd = s'.snd := by aesop_cat

attribute [simp] sectionOverMorphism.w

instance sectionOverCategory : Category (sectionOver F) where
  Hom := sectionOverMorphism F
  id s := {fst := 𝟙 s.fst}
  comp f g := {fst := f.fst ≫ g.fst}

namespace sectionOver

section

variable {s s' s'' : sectionOver F} (f : s ⟶ s') (g : s' ⟶ s'')

@[ext]
lemma hom_ext (f g : s ⟶ s') (h : f.fst = g.fst) : f = g :=
  sectionOverMorphism.ext h

@[simp]
lemma id_fst : (𝟙 s : sectionOverMorphism F s s).fst = 𝟙 (s.fst) := rfl

@[simp]
lemma comp_fst : (f ≫ g).fst = f.fst ≫ g.fst := rfl

@[simps]
def over : sectionOver F ⥤ C where
  obj s := s.fst
  map f := f.fst

end

end sectionOver

section homEquiv

open sectionOver

variable (G : C ⥤ Type w)

def homEquivOverCompSections :
    (F ⟶ G) ≃ (sectionOver.over F ⋙ G).sections where
  toFun α := ⟨
      fun s => α.app s.fst s.snd,
      fun {s s'} f => by
        show (α.app s.fst ≫ G.map f.fst) s.snd = α.app s'.fst s'.snd
        rw [← α.naturality]
        simp
    ⟩
  invFun σ := {
      app X x := σ.val (⟨X, x⟩ : sectionOver F),
      naturality {X Y} f := by
        ext x
        simp only [types_comp_apply,
          ← σ.prop ({fst := f} : sectionOverMorphism F ⟨X, x⟩ ⟨Y, F.map f x⟩)]
        rfl
    }
  left_inv _ := rfl
  right_inv _ := rfl

def homEquivOverCompSections' :
    (F ⟶ G) ≃ (sectionOver.over F ⋙ G ⋙ uliftFunctor.{u, w}).sections where
  toFun α := ⟨
      fun s => { down := α.app s.fst s.snd },
      fun {s s'} f => by
        simp only [Functor.comp_obj, over_obj, uliftFunctor_obj, Functor.comp_map, over_map,
          uliftFunctor_map, ULift.up.injEq]
        show (α.app s.fst ≫ G.map f.fst) s.snd = α.app s'.fst s'.snd
        rw [← α.naturality]
        simp
    ⟩
  invFun σ := {
      app X x := (σ.val (⟨X, x⟩ : sectionOver F)).down,
      naturality {X Y} f := by
        ext x
        simp only [types_comp_apply,
          ← σ.prop ({fst := f} : sectionOverMorphism F ⟨X, x⟩ ⟨Y, F.map f x⟩)]
        rfl
    }
  left_inv _ := rfl
  right_inv _ := rfl

abbrev whiskeringLeftOver := (whiskeringLeft _ _ (Type w)).obj (over F)

abbrev whiskeringRightUlift := (whiskeringRight (sectionOver F) _ _).obj uliftFunctor.{u, w}

def coyonedaOpNatIsoWhiskeringLeftOverCompSectionsFunctorSectionOver :
    coyoneda.obj (Opposite.op F) ≅ (whiskeringLeftOver F) ⋙
      (whiskeringRightUlift F) ⋙ Functor.sectionsFunctor (sectionOver F) where
  hom := {app G := (homEquivOverCompSections' F G).toFun}
  inv := {app G := (homEquivOverCompSections' F G).invFun}

-- inutile
noncomputable def homEquivLimitOverComp [UnivLE.{max w u, w}] :
    (F ⟶ G) ≃ limit (sectionOver.over F ⋙ G) :=
  (homEquivOverCompSections F G).trans
    (Types.limitEquivSections (sectionOver.over F ⋙ G)).symm

noncomputable def coyonedaOpNatIsoWhiskeringLeftOverCompLim [UnivLE.{max w u, w}] :
    coyoneda.obj (Opposite.op F) ≅
      (whiskeringLeftOver F) ⋙ (whiskeringRightUlift F) ⋙ lim :=
  (coyonedaOpNatIsoWhiskeringLeftOverCompSectionsFunctorSectionOver F).trans
    (isoWhiskerLeft (whiskeringLeftOver F) (isoWhiskerLeft (whiskeringRightUlift F)
    Types.limNatIsoSectionsFunctor.symm))

end homEquiv

end sectionOver


section presheaf

variable {C : Type u} [Category.{v, u} C] (F : Cᵒᵖ ⥤ Type v)

@[simps]
def overYoneda : (sectionOver F)ᵒᵖ ⥤ (Cᵒᵖ ⥤ Type v) where
  obj s := yoneda.obj s.unop.fst.unop
  map f := yoneda.map f.unop.fst.unop

-- inutile
lemma overYonedaRightOpIso : (overYoneda F).rightOp = sectionOver.over F ⋙ yoneda.op := by
  rfl

variable [UnivLE.{max v u, v}] {G : Cᵒᵖ ⥤ Type v} -- G inutile

-- inutole
noncomputable def colimitOverYonedaHomIsoLimitOverComp :
    (colimit (overYoneda F) ⟶ G) ≅ limit (sectionOver.over F ⋙ G ⋙ uliftFunctor) :=
  (colimitHomIsoLimitYoneda' (overYoneda F) G).trans
    (HasLimit.isoOfNatIso (isoWhiskerLeft (sectionOver.over F) (yonedaOpCompYonedaObj G)))

def overCompYonedaCompCoyonedaFlipNatIsoWhiskeringLeftOver :
    (sectionOver.over F ⋙ yoneda.op ⋙ coyoneda).flip
      ≅ (whiskeringLeftOver F) ⋙ (whiskeringRightUlift F) where
  hom := {
      app G := {
          app s := fun x => { down := yonedaEquiv.toFun x}
          naturality _ _ _ := by
            ext
            simp only [Functor.comp_obj, whiskeringLeft_obj_obj, whiskeringRight_obj_obj,
              sectionOver.over_obj, uliftFunctor_obj, Functor.flip_obj_obj, Functor.op_obj,
              coyoneda_obj_obj, Functor.flip_obj_map, Functor.comp_map, sectionOver.over_map,
              Functor.op_map, Opposite.op_unop, Equiv.toFun_as_coe, types_comp_apply,
              coyoneda_map_app, Quiver.Hom.unop_op, uliftFunctor_map, ULift.up.injEq]
            rw [← yonedaEquiv_naturality]
            rfl
        }
    }
  inv := {
      app G := {
          app s := fun x => yonedaEquiv.invFun x.down
          naturality _ _ _ := by
            ext
            apply NatTrans.ext
            ext
            simp only [sectionOver.over_obj, Functor.op_obj, Functor.comp_obj,
              whiskeringLeft_obj_obj, whiskeringRight_obj_obj, uliftFunctor_obj,
              Functor.flip_obj_obj, coyoneda_obj_obj, Functor.comp_map, sectionOver.over_map,
              Opposite.op_unop, Equiv.invFun_as_coe, types_comp_apply, uliftFunctor_map,
              Functor.flip_obj_map, Functor.op_map, coyoneda_map_app, Quiver.Hom.unop_op,
              FunctorToTypes.comp, yoneda_map_app]
            rw [yonedaEquiv_symm_app_apply]
            rw [yonedaEquiv_symm_app_apply]
            simp
        }
      naturality _ _ _ := by
        apply NatTrans.ext
        ext
        simp only [Functor.flip_obj_obj, Functor.comp_obj, sectionOver.over_obj, Functor.op_obj,
          coyoneda_obj_obj, whiskeringLeft_obj_obj, whiskeringRight_obj_obj, Functor.comp_map,
          whiskeringLeft_obj_map, whiskeringRight_obj_map, uliftFunctor_obj, Opposite.op_unop,
          Equiv.invFun_as_coe, FunctorToTypes.comp, whiskerRight_app, whiskerLeft_app,
          uliftFunctor_map, Functor.flip_map_app, coyoneda_obj_map]
        rw [yonedaEquiv_symm_naturality_right]
    }

noncomputable def coyonedaOpColimitOverYonedaNatIsoWhiskeringLeftOverLim :
    coyoneda.obj (Opposite.op (colimit (overYoneda F))) ≅
      (whiskeringLeftOver F) ⋙ (whiskeringRightUlift F) ⋙ lim :=
  (coyonedaOpColimitIsoLimitCoyoneda' (overYoneda F)).trans
    ((limitIsoFlipCompLim _).trans
    (isoWhiskerRight (overCompYonedaCompCoyonedaFlipNatIsoWhiskeringLeftOver F) _))

-- inutile
noncomputable def colimitOverYonedaHomIsoLimitOverComp' :
    (colimit (overYoneda F) ⟶ G) ≅ ULift.{u, v} (limit (sectionOver.over F ⋙ G)) :=
  (colimitOverYonedaHomIsoLimitOverComp F).trans
    (preservesLimitIso uliftFunctor (sectionOver.over F ⋙ G)).symm

-- inutile
noncomputable def colimitOverYonedaHomEquivLimitOverComp :
    (colimit (overYoneda F) ⟶ G) ≃ (limit (sectionOver.over F ⋙ G)) :=
  (colimitOverYonedaHomIsoLimitOverComp' F).toEquiv.trans Equiv.ulift

-- inutile
noncomputable def homEquivHomColimitOverYoneda :
    (F ⟶ G) ≃ (colimit (overYoneda F) ⟶ G) :=
  (homEquivLimitOverComp F G).trans (colimitOverYonedaHomEquivLimitOverComp F).symm

noncomputable def coyonedaOpNatIsoCoyonedaOpColimitOverYoneda :
    coyoneda.obj (Opposite.op F) ≅ coyoneda.obj (Opposite.op (colimit (overYoneda F))) :=
  (coyonedaOpNatIsoWhiskeringLeftOverCompLim F).trans
    (coyonedaOpColimitOverYonedaNatIsoWhiskeringLeftOverLim F).symm

noncomputable def isoColimitOverYoneda :
    F ≅ colimit (overYoneda F) :=
  (Coyoneda.fullyFaithful.preimageIso (coyonedaOpNatIsoCoyonedaOpColimitOverYoneda F).symm).unop

end presheaf

end Category
