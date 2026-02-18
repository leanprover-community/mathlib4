/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Reid Barton
-/
module

public import Mathlib.CategoryTheory.Limits.Types.Limits

/-!
# Cones and limits

In this file, we give the natural isomorphism between cones on `F` with cone point `X` and the type
`lim Hom(X, F·)`, and similarly the natural isomorphism between cocones on `F` with cocone point `X`
and the type `lim Hom(F·, X)`.

-/

@[expose] public section

universe v u

namespace CategoryTheory.Limits

open Functor Opposite

section

variable {J C : Type*} [Category* J] [Category* C]

/-- Sections of `F ⋙ coyoneda.obj (op X)` identify to natural
transformations `(const J).obj X ⟶ F`. -/
@[simps!]
def compCoyonedaSectionsEquiv (F : J ⥤ C) (X : C) :
    (F ⋙ coyoneda.obj (op X)).sections ≃ ((const J).obj X ⟶ F) where
  toFun s :=
    { app := fun j => s.val j
      naturality := fun j j' f => by
        dsimp
        rw [Category.id_comp]
        exact (s.property f).symm }
  invFun τ := ⟨τ.app, fun {j j'} f => by simpa using (τ.naturality f).symm⟩

/-- Sections of `F.op ⋙ yoneda.obj X` identify to natural
transformations `F ⟶ (const J).obj X`. -/
@[simps]
def opCompYonedaSectionsEquiv (F : J ⥤ C) (X : C) :
    (F.op ⋙ yoneda.obj X).sections ≃ (F ⟶ (const J).obj X) where
  toFun s :=
    { app := fun j => s.val (op j)
      naturality := fun j j' f => by
        dsimp
        rw [Category.comp_id]
        exact (s.property f.op) }
  invFun τ := ⟨fun j => τ.app j.unop, fun {j j'} f => by simp [τ.naturality f.unop]⟩

/-- Sections of `F ⋙ yoneda.obj X` identify to natural
transformations `(const J).obj X ⟶ F`. -/
@[simps]
def compYonedaSectionsEquiv (F : J ⥤ Cᵒᵖ) (X : C) :
    (F ⋙ yoneda.obj X).sections ≃ ((const J).obj (op X) ⟶ F) where
  toFun s :=
    { app := fun j => (s.val j).op
      naturality := fun j j' f => by
        dsimp
        rw [Category.id_comp]
        exact Quiver.Hom.unop_inj (s.property f).symm }
  invFun τ := ⟨fun j => (τ.app j).unop,
    fun {j j'} f => Quiver.Hom.op_inj (by simpa using (τ.naturality f).symm)⟩

end

variable {J : Type v} [SmallCategory J] {C : Type u} [Category.{v} C]

/-- A cone on `F` with cone point `X` is the same as an element of `lim Hom(X, F·)`. -/
@[simps! inv]
noncomputable def limitCompCoyonedaIsoCone (F : J ⥤ C) (X : C) :
    limit (F ⋙ coyoneda.obj (op X)) ≅ TypeCat.of ((const J).obj X ⟶ F) :=
  ((Types.limitEquivSections _).trans (compCoyonedaSectionsEquiv F X)).toIso

@[simp]
lemma limitCompCoyonedaIsoCone_hom_app (F : J ⥤ C) (X : C)
    (a : ToType (limit (F ⋙ coyoneda.obj (op X)))) (j : J) :
    ((limitCompCoyonedaIsoCone F X).hom a : _ ⟶ _).app j =
      limit.π (F.comp (coyoneda.obj (Opposite.op X))) j a :=
  rfl

/-- A cone on `F` with cone point `X` is the same as an element of `lim Hom(X, F·)`,
    naturally in `X`. -/
@[simps! inv_app hom]
noncomputable def coyonedaCompLimIsoCones (F : J ⥤ C) :
    coyoneda ⋙ (whiskeringLeft _ _ _).obj F ⋙ lim ≅ F.cones := by
  refine NatIso.ofComponents (fun X => limitCompCoyonedaIsoCone F X.unop) ?_
  intros
  ext
  dsimp
  ext
  simp only [const_obj_obj, TypeCat.hom_as_apply, comp_apply, ConcreteCategory.hom_ofHom,
    TypeCat.Fun.as_apply, NatTrans.comp_app, const_map_app]
  rw [limitCompCoyonedaIsoCone_hom_app, limMap_π_apply] -- Why doesn't simp find these?
  rfl

variable (J) (C) in
/-- A cone on `F` with cone point `X` is the same as an element of `lim Hom(X, F·)`,
    naturally in `F` and `X`. -/
@[simps!]
noncomputable def whiskeringLimYonedaIsoCones : whiskeringLeft _ _ _ ⋙
    (whiskeringRight _ _ _).obj lim ⋙ (whiskeringLeft _ _ _).obj coyoneda ≅ cones J C := by
  refine NatIso.ofComponents coyonedaCompLimIsoCones ?_
  intros
  dsimp
  ext
  dsimp
  ext
  simp only [const_obj_obj, TypeCat.hom_as_apply, comp_apply, ConcreteCategory.hom_ofHom,
    TypeCat.Fun.as_apply, NatTrans.comp_app]
  rw [limitCompCoyonedaIsoCone_hom_app, limMap_π_apply] -- Why doesn't simp find these?
  rfl

/-- A cocone on `F` with cocone point `X` is the same as an element of `lim Hom(F·, X)`. -/
@[simps! inv]
noncomputable def limitCompYonedaIsoCocone (F : J ⥤ C) (X : C) :
    limit (F.op ⋙ yoneda.obj X) ≅ TypeCat.of (F ⟶ (const J).obj X) :=
  ((Types.limitEquivSections _).trans (opCompYonedaSectionsEquiv F X)).toIso

@[simp]
lemma limitCompYonedaIsoCocone_hom_app (F : J ⥤ C) (X : C)
    (a : (limit (F.op ⋙ yoneda.obj X) :)) (j : J) :
    ((limitCompYonedaIsoCocone F X).hom a).app j = limit.π (F.op ⋙ yoneda.obj X) (op j) a :=
  rfl

/-- A cocone on `F` with cocone point `X` is the same as an element of `lim Hom(F·, X)`,
    naturally in `X`. -/
@[simps! inv_app hom]
noncomputable def yonedaCompLimIsoCocones (F : J ⥤ C) :
    yoneda ⋙ (whiskeringLeft _ _ _).obj F.op ⋙ lim ≅ F.cocones := by
  refine NatIso.ofComponents (limitCompYonedaIsoCocone F) ?_
  intros
  ext
  dsimp
  ext
  simp only [const_obj_obj, TypeCat.hom_as_apply, comp_apply, ConcreteCategory.hom_ofHom,
    TypeCat.Fun.as_apply, NatTrans.comp_app, const_map_app]
  rw [limitCompYonedaIsoCocone_hom_app, limMap_π_apply]
  rfl

variable (J) (C) in
/-- A cocone on `F` with cocone point `X` is the same as an element of `lim Hom(F·, X)`,
    naturally in `F` and `X`. -/
@[simps!]
noncomputable def opHomCompWhiskeringLimYonedaIsoCocones : opHom _ _ ⋙ whiskeringLeft _ _ _ ⋙
      (whiskeringRight _ _ _).obj lim ⋙ (whiskeringLeft _ _ _).obj yoneda ≅ cocones J C := by
  refine NatIso.ofComponents (fun F => yonedaCompLimIsoCocones F.unop) ?_
  intros
  ext
  dsimp
  ext
  simp only [const_obj_obj, TypeCat.hom_as_apply, comp_apply, ConcreteCategory.hom_ofHom,
    TypeCat.Fun.as_apply, NatTrans.comp_app]
  rw [limitCompYonedaIsoCocone_hom_app, limMap_π_apply]
  rfl

end CategoryTheory.Limits
