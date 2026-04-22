/-
Copyright (c) 2024 Alvaro Belmonte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alvaro Belmonte, Joël Riou
-/
module

public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.Data.ULift
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Codiscrete categories

We define `Codiscrete A` as a wrapper for the type `A`,
and use this wrapper to provide a `Category` instance
whose Hom types are `Unit`.

`Codiscrete.functor` promotes a function `f : C → A` (for any category `C`) to a functor
`f : C ⥤ Codiscrete A`.

Similarly, `Codiscrete.natTrans` and `Codiscrete.natIso` provide the unique natural
transformation or natural isomorphism between functors into a codiscrete category.

We define `functorToCat : Type u ⥤ Cat.{0,u}` which sends a type to the codiscrete category and show
it is right adjoint to `Cat.objects`.
-/

@[expose] public section
namespace CategoryTheory

universe u v w

-- This is intentionally a structure rather than a type synonym
-- to enforce using `CodiscreteEquiv` (or `Codiscrete.mk` and `Codiscrete.as`) to move between
-- `Codiscrete α` and `α`. Otherwise there is too much API leakage.
/-- A wrapper for promoting any type to a category,
with a unique morphism between any two objects of the category.
-/
@[ext, aesop safe cases (rule_sets := [CategoryTheory])]
structure Codiscrete (α : Type u) where
  /-- A wrapper for promoting any type to a category,
  with a unique morphism between any two objects of the category. -/
  as : α

@[simp]
theorem Codiscrete.mk_as {α : Type u} (X : Codiscrete α) : Codiscrete.mk X.as = X := rfl

/-- `Codiscrete α` is equivalent to the original type `α`. -/
@[simps]
def codiscreteEquiv {α : Type u} : Codiscrete α ≃ α where
  toFun := Codiscrete.as
  invFun := Codiscrete.mk
  left_inv := by cat_disch
  right_inv := by cat_disch

instance {α : Type u} [DecidableEq α] : DecidableEq (Codiscrete α) :=
  codiscreteEquiv.decidableEq

namespace Codiscrete

instance (A : Type*) : Category (Codiscrete A) where
  Hom _ _ := Unit
  id _ := ⟨⟩
  comp _ _ := ⟨⟩

section
variable {C : Type u} [Category.{v} C] {A : Type w}

/-- Any function `C → A` lifts to a functor `C ⥤ Codiscrete A`. -/
def functor (F : C → A) : C ⥤ Codiscrete A where
  obj := Codiscrete.mk ∘ F
  map _ := ⟨⟩

/-- The underlying function `C → A` of a functor `C ⥤ Codiscrete A`. -/
def invFunctor (F : C ⥤ Codiscrete A) : C → A := Codiscrete.as ∘ F.obj

/-- Given two functors to a codiscrete category, there is a trivial natural transformation. -/
def natTrans {F G : C ⥤ Codiscrete A} : F ⟶ G where
  app _ := ⟨⟩

/-- Given two functors into a codiscrete category, the trivial natural transformation is a
natural isomorphism. -/
def natIso {F G : C ⥤ Codiscrete A} : F ≅ G where
  hom := natTrans
  inv := natTrans

/-- Every functor `F` to a codiscrete category is naturally isomorphic {(actually, equal)} to
  `functor (Codiscrete.as ∘ F.obj)`. -/
@[simps!]
def natIsoFunctor {F : C ⥤ Codiscrete A} : F ≅ functor (Codiscrete.as ∘ F.obj) := Iso.refl _

end

/-- A function induces a functor between codiscrete categories. -/
def functorOfFun {A B : Type*} (f : A → B) : Codiscrete A ⥤ Codiscrete B :=
  functor (f ∘ Codiscrete.as)

open Opposite

/-- A codiscrete category is equivalent to its opposite category. -/
def oppositeEquivalence (A : Type*) : (Codiscrete A)ᵒᵖ ≌ Codiscrete A where
  functor := functor (fun x ↦ Codiscrete.as x.unop)
  inverse := (functor (fun x ↦ Codiscrete.as x.unop)).rightOp
  unitIso := NatIso.ofComponents (fun _ => by exact Iso.refl _)
  counitIso := natIso

/-- `Codiscrete.functorToCat` turns a type into a codiscrete category. -/
def functorToCat : Type u ⥤ Cat.{0, u} where
  obj A := Cat.of (Codiscrete A)
  map f := (functorOfFun f).toCatHom

open Adjunction Cat

/-- For a category `C` and type `A`, there is an equivalence between functions `objects.obj C ⟶ A`
and functors `C ⥤ Codiscrete A`. -/
def equivFunctorToCodiscrete {C : Type u} [Category.{v} C] {A : Type w} :
    (C → A) ≃ (C ⥤ Codiscrete A) where
  toFun := functor
  invFun := invFunctor

/-- The functor that turns a type into a codiscrete category is right adjoint to the objects
functor. -/
def adj : objects ⊣ functorToCat := mkOfHomEquiv {
  homEquiv _ _ := equivFunctorToCodiscrete.trans (Functor.equivCatHom _ _)
  homEquiv_naturality_left_symm _ _ := rfl
  homEquiv_naturality_right _ _ := rfl }

/-- Components of the unit of the adjunction `Cat.objects ⊣ Codiscrete.functorToCat`. -/
def unitApp (C : Type u) [Category.{v} C] : C ⥤ Codiscrete C := functor id

/-- Components of the counit of the adjunction `Cat.objects ⊣ Codiscrete.functorToCat` -/
def counitApp (A : Type u) : Codiscrete A → A := Codiscrete.as

lemma adj_unit_app (X : Cat.{0, u}) :
    adj.unit.app X = (unitApp X).toCatHom := rfl

lemma adj_counit_app (A : Type u) :
    adj.counit.app A = counitApp A := rfl

/-- Left triangle equality of the adjunction `Cat.objects ⊣ Codiscrete.functorToCat`,
as a universe polymorphic statement. -/
lemma left_triangle_components (C : Type u) [Category.{v} C] :
    (counitApp C).comp (unitApp C).obj = id :=
  rfl

/-- Right triangle equality of the adjunction `Cat.objects ⊣ Codiscrete.functorToCat`,
stated using a composition of functors. -/
lemma right_triangle_components (X : Type u) :
    unitApp (Codiscrete X) ⋙ functorOfFun (counitApp X) = 𝟭 (Codiscrete X) :=
  rfl

end Codiscrete

end CategoryTheory
