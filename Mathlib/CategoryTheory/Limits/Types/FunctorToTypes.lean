/-
Copyright (c) 2025 Benoît Guillemet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benoît Guillemet
-/
import Mathlib.CategoryTheory.Limits.IndYoneda
import Mathlib.CategoryTheory.Limits.Preserves.Ulift

/-!
# Isomorphism with a colimit of representable

Let `C` be a category and `F, G : Cᵒᵖ ⥤ Type v` two presheaves over `C`.
We give the natural isomorphism between natural transformations `F ⟶ G` and objects of the limit of
sections of `G` over sections of `F`.
We deduce an isomorphism between any presheaf `F` and a colimit of representable presheaves.
-/

universe u v w

open CategoryTheory Limits

namespace CategoryTheory

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

/-- An equivalence between maps from `F` to `G` and a limit of sections of `G`. -/
noncomputable def homEquivLimitOverComp [UnivLE.{max w u, w}] :
    (F ⟶ G) ≃ limit (sectionOver.over F ⋙ G) :=
  (homEquivOverCompSections F G).trans
    (Types.limitEquivSections (sectionOver.over F ⋙ G)).symm

/-- A functorial version of `homEquivLimitOverComp` -/
noncomputable def coyonedaOpNatIsoWhiskeringLeftOverCompLim [UnivLE.{max w u, w}] :
    coyoneda.obj (Opposite.op F) ≅
      (whiskeringLeftOver F) ⋙ (whiskeringRightUlift F) ⋙ lim :=
  (coyonedaOpNatIsoWhiskeringLeftOverCompSectionsFunctorSectionOver F).trans
    (isoWhiskerLeft (whiskeringLeftOver F) (isoWhiskerLeft (whiskeringRightUlift F)
    Types.limNatIsoSectionsFunctor.symm))

end homEquiv

end sectionOver


section presheaf

variable {C : Type u} [Category.{v, u} C] (F : Cᵒᵖ ⥤ Type w)

@[simps]
def overYoneda : (sectionOver F)ᵒᵖ ⥤ (Cᵒᵖ ⥤ Type v) where
  obj s := yoneda.obj s.unop.fst.unop
  map f := yoneda.map f.unop.fst.unop

lemma overYonedaRightOpIso : (overYoneda F).rightOp = sectionOver.over F ⋙ yoneda.op := by
  rfl

def overYoneda' : (sectionOver F)ᵒᵖ ⥤ (Cᵒᵖ ⥤ Type (max v w)) :=
  overYoneda F ⋙ ((whiskeringRight _ _ _).obj uliftFunctor)

lemma overYonedaRightOpIso' : (overYoneda' F).rightOp =
    sectionOver.over F ⋙ yoneda.op ⋙ ((whiskeringRight _ _ _).obj uliftFunctor).op :=
  rfl

variable [UnivLE.{max u v, v}] (F : Cᵒᵖ ⥤ Type v)
variable [UnivLE.{max u v w, max v w}] (F' : Cᵒᵖ ⥤ Type (max v w))

def overCompYonedaCompCoyonedaFlipNatIsoWhiskeringLeftOver :
    (sectionOver.over F ⋙ yoneda.op ⋙ coyoneda).flip
      ≅ (whiskeringLeftOver F) ⋙ (whiskeringRightUlift F) :=
  (flipFunctor _ _ _).mapIso (isoWhiskerLeft (sectionOver.over F) largeCurriedYonedaLemma)

def overCompYonedaCompCoyonedaFlipNatIsoWhiskeringLeftOver' :
    (sectionOver.over F' ⋙ yoneda.op ⋙ ((whiskeringRight _ _ _).obj uliftFunctor).op
      ⋙ coyoneda).flip ≅ (whiskeringLeftOver F') ⋙ (whiskeringRightUlift F') :=
  (flipFunctor _ _ _).mapIso (isoWhiskerLeft (sectionOver.over F')
    largeCurriedYonedaCompUliftFunctorLemma)

noncomputable def coyonedaOpColimitOverYonedaNatIsoWhiskeringLeftOverLim :
    coyoneda.obj (Opposite.op (colimit (overYoneda F))) ≅
      (whiskeringLeftOver F) ⋙ (whiskeringRightUlift F) ⋙ lim :=
  (coyonedaOpColimitIsoLimitCoyoneda' (overYoneda F)).trans
    ((limitIsoFlipCompLim _).trans
    (isoWhiskerRight (overCompYonedaCompCoyonedaFlipNatIsoWhiskeringLeftOver F) _))

noncomputable def coyonedaOpColimitOverYonedaNatIsoWhiskeringLeftOverLim' :
    coyoneda.obj (Opposite.op (colimit (overYoneda' F'))) ≅
      (whiskeringLeftOver F') ⋙ (whiskeringRightUlift F') ⋙ lim :=
  (coyonedaOpColimitIsoLimitCoyoneda' (overYoneda' F')).trans
    ((limitIsoFlipCompLim _).trans
    (isoWhiskerRight (overCompYonedaCompCoyonedaFlipNatIsoWhiskeringLeftOver' F') _))

noncomputable def coyonedaOpNatIsoCoyonedaOpColimitOverYoneda :
    coyoneda.obj (Opposite.op F) ≅ coyoneda.obj (Opposite.op (colimit (overYoneda F))) :=
  (coyonedaOpNatIsoWhiskeringLeftOverCompLim F).trans
    (coyonedaOpColimitOverYonedaNatIsoWhiskeringLeftOverLim F).symm

noncomputable def coyonedaOpNatIsoCoyonedaOpColimitOverYoneda' :
    coyoneda.obj (Opposite.op F') ≅ coyoneda.obj (Opposite.op (colimit (overYoneda' F'))) :=
  (coyonedaOpNatIsoWhiskeringLeftOverCompLim F').trans
    (coyonedaOpColimitOverYonedaNatIsoWhiskeringLeftOverLim' F').symm

/-- A natural isomorphism between a presheaf a a colimit of representable presheaves. -/
noncomputable def natIsoColimitOverYoneda :
    F ≅ colimit (overYoneda F) :=
  (Coyoneda.fullyFaithful.preimageIso (coyonedaOpNatIsoCoyonedaOpColimitOverYoneda F).symm).unop

/-- A variant of `natIsoColimitOverYoneda` with heterogeneous universes. -/
noncomputable def natIsoColimitOverYoneda' :
    F' ≅ colimit (overYoneda' F') :=
  (Coyoneda.fullyFaithful.preimageIso (coyonedaOpNatIsoCoyonedaOpColimitOverYoneda' F').symm).unop

end presheaf

end CategoryTheory
