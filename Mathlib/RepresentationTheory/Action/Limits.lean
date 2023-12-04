/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Abelian.Transfer
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Linear.FunctorCategory
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.RepresentationTheory.Action.Basic

/-!
# Categorical properties of `Action V G`

We show:

* When `V` has (co)limits so does `Action V G`.
* When `V` is preadditive, linear, or abelian so is `Action V G`.
-/

universe u v

open CategoryTheory Limits

variable {V : Type (u + 1)} [LargeCategory V] {G : MonCat.{u}}

namespace Action

section Limits

instance [HasFiniteProducts V] : HasFiniteProducts (Action V G) where
  out _ :=
    Adjunction.hasLimitsOfShape_of_equivalence (Action.functorCategoryEquivalence _ _).functor

instance [HasFiniteLimits V] : HasFiniteLimits (Action V G) where
  out _ _ _ :=
    Adjunction.hasLimitsOfShape_of_equivalence (Action.functorCategoryEquivalence _ _).functor

instance [HasLimits V] : HasLimits (Action V G) :=
  Adjunction.has_limits_of_equivalence (Action.functorCategoryEquivalence _ _).functor

instance [HasColimits V] : HasColimits (Action V G) :=
  Adjunction.has_colimits_of_equivalence (Action.functorCategoryEquivalence _ _).functor

end Limits

section HasZeroMorphisms

variable [HasZeroMorphisms V]

-- porting note: in order to ease automation, the `Zero` instance is introduced separately,
-- and the lemma `zero_hom` was moved just below
instance {X Y : Action V G} : Zero (X ⟶ Y) := ⟨0, by aesop_cat⟩

@[simp]
theorem zero_hom {X Y : Action V G} : (0 : X ⟶ Y).hom = 0 :=
  rfl
set_option linter.uppercaseLean3 false in
--#align Action.zero_hom Action.zero_hom

instance : HasZeroMorphisms (Action V G) where

instance forget_preservesZeroMorphisms : Functor.PreservesZeroMorphisms (forget V G) where
set_option linter.uppercaseLean3 false in
--#align Action.forget_preserves_zero_morphisms Action.forget_preservesZeroMorphisms

instance forget₂_preservesZeroMorphisms [ConcreteCategory V] :
    Functor.PreservesZeroMorphisms (forget₂ (Action V G) V) where
set_option linter.uppercaseLean3 false in
#align Action.forget₂_preserves_zero_morphisms Action.forget₂_preservesZeroMorphisms

instance functorCategoryEquivalence_preservesZeroMorphisms :
    Functor.PreservesZeroMorphisms (functorCategoryEquivalence V G).functor where
set_option linter.uppercaseLean3 false in
#align Action.functor_category_equivalence_preserves_zero_morphisms Action.functorCategoryEquivalence_preservesZeroMorphisms

end HasZeroMorphisms

section Preadditive

variable [Preadditive V]

instance : Preadditive (Action V G) where
  homGroup X Y :=
    { add := fun f g => ⟨f.hom + g.hom, by simp [f.comm, g.comm]⟩
      neg := fun f => ⟨-f.hom, by simp [f.comm]⟩
      zero_add := by intros; ext; exact zero_add _
      add_zero := by intros; ext; exact add_zero _
      add_assoc := by intros; ext; exact add_assoc _ _ _
      add_left_neg := by intros; ext; exact add_left_neg _
      add_comm := by intros; ext; exact add_comm _ _ }
  add_comp := by intros; ext; exact Preadditive.add_comp _ _ _ _ _ _
  comp_add := by intros; ext; exact Preadditive.comp_add _ _ _ _ _ _

instance forget_additive : Functor.Additive (forget V G) where
set_option linter.uppercaseLean3 false in
#align Action.forget_additive Action.forget_additive

instance forget₂_additive [ConcreteCategory V] : Functor.Additive (forget₂ (Action V G) V) where
set_option linter.uppercaseLean3 false in
#align Action.forget₂_additive Action.forget₂_additive

instance functorCategoryEquivalence_additive :
    Functor.Additive (functorCategoryEquivalence V G).functor where
set_option linter.uppercaseLean3 false in
#align Action.functor_category_equivalence_additive Action.functorCategoryEquivalence_additive

@[simp]
theorem neg_hom {X Y : Action V G} (f : X ⟶ Y) : (-f).hom = -f.hom :=
  rfl
set_option linter.uppercaseLean3 false in
#align Action.neg_hom Action.neg_hom

@[simp]
theorem add_hom {X Y : Action V G} (f g : X ⟶ Y) : (f + g).hom = f.hom + g.hom :=
  rfl
set_option linter.uppercaseLean3 false in
#align Action.add_hom Action.add_hom

@[simp]
theorem sum_hom {X Y : Action V G} {ι : Type*} (f : ι → (X ⟶ Y)) (s : Finset ι) :
    (s.sum f).hom = s.sum fun i => (f i).hom :=
  (forget V G).map_sum f s
set_option linter.uppercaseLean3 false in
#align Action.sum_hom Action.sum_hom

end Preadditive

section Linear

variable [Preadditive V] {R : Type*} [Semiring R] [Linear R V]

instance : Linear R (Action V G) where
  homModule X Y :=
    { smul := fun r f => ⟨r • f.hom, by simp [f.comm]⟩
      one_smul := by intros; ext; exact one_smul _ _
      smul_zero := by intros; ext; exact smul_zero _
      zero_smul := by intros; ext; exact zero_smul _ _
      add_smul := by intros; ext; exact add_smul _ _ _
      smul_add := by intros; ext; exact smul_add _ _ _
      mul_smul := by intros; ext; exact mul_smul _ _ _ }
  smul_comp := by intros; ext; exact Linear.smul_comp _ _ _ _ _ _
  comp_smul := by intros; ext; exact Linear.comp_smul _ _ _ _ _ _

instance forget_linear : Functor.Linear R (forget V G) where
set_option linter.uppercaseLean3 false in
#align Action.forget_linear Action.forget_linear

instance forget₂_linear [ConcreteCategory V] : Functor.Linear R (forget₂ (Action V G) V) where
set_option linter.uppercaseLean3 false in
#align Action.forget₂_linear Action.forget₂_linear

instance functorCategoryEquivalence_linear :
    Functor.Linear R (functorCategoryEquivalence V G).functor where
set_option linter.uppercaseLean3 false in
#align Action.functor_category_equivalence_linear Action.functorCategoryEquivalence_linear

@[simp]
theorem smul_hom {X Y : Action V G} (r : R) (f : X ⟶ Y) : (r • f).hom = r • f.hom :=
  rfl
set_option linter.uppercaseLean3 false in
#align Action.smul_hom Action.smul_hom

variable {H : MonCat.{u}} (f : G ⟶ H)

instance res_additive [Preadditive V] : (res V f).Additive where
set_option linter.uppercaseLean3 false in
#align Action.res_additive Action.res_additive

variable {R : Type*} [Semiring R]

instance res_linear [Preadditive V] [Linear R V] : (res V f).Linear R where
set_option linter.uppercaseLean3 false in
#align Action.res_linear Action.res_linear

end Linear

section Abelian

/-- Auxilliary construction for the `Abelian (Action V G)` instance. -/
def abelianAux : Action V G ≌ ULift.{u} (SingleObj G) ⥤ V :=
  (functorCategoryEquivalence V G).trans (Equivalence.congrLeft ULift.equivalence)
set_option linter.uppercaseLean3 false in
#align Action.abelian_aux Action.abelianAux

noncomputable instance [Abelian V] : Abelian (Action V G) :=
  abelianOfEquivalence abelianAux.functor

end Abelian

end Action

namespace CategoryTheory.Functor

variable {W : Type (u + 1)} [LargeCategory W] (F : V ⥤ W) (G : MonCat.{u}) [Preadditive V]
  [Preadditive W]

instance mapAction_preadditive [F.Additive] : (F.mapAction G).Additive where
set_option linter.uppercaseLean3 false in
#align category_theory.functor.map_Action_preadditive CategoryTheory.Functor.mapAction_preadditive

variable {R : Type*} [Semiring R] [CategoryTheory.Linear R V] [CategoryTheory.Linear R W]

instance mapAction_linear [F.Additive] [F.Linear R] : (F.mapAction G).Linear R where
set_option linter.uppercaseLean3 false in
#align category_theory.functor.map_Action_linear CategoryTheory.Functor.mapAction_linear

end CategoryTheory.Functor
