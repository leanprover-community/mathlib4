/-
Copyright (c) 2024 Alvaro Belmonte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alvaro Belmonte, Joël Riou
-/
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Pi.Basic
import Mathlib.Data.ULift
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Codiscrete categories

We define `Codiscrete A` as an alias for the type `A` ,
and use this type alias to provide a `Category` instance
whose Hom type are Unit types.

`Codiscrete.functor` promotes a function `f : C → A` (for any category `C`) to a functor
 `f : C ⥤ Codiscrete A`.

Similarly, `Codiscrete.natTrans` and `Codiscrete.natIso` promote `I`-indexed families of morphisms,
or `I`-indexed families of isomorphisms to natural transformations or natural isomorphism.

We define `functorToCat : Type u ⥤ Cat.{0,u}` which sends a type to the codiscrete category and show
it is right adjoint to `Cat.objects.`
-/
namespace CategoryTheory

universe u v w

-- This is intentionally a structure rather than a type synonym
-- to enforce using `CodiscreteEquiv` (or `Codiscrete.mk` and `Codiscrete.as`) to move between
-- `Codiscrete α` and `α`. Otherwise there is too much API leakage.
/-- A wrapper for promoting any type to a category,
with a unique morphisms between any two objects of the category.
-/
@[ext, aesop safe cases (rule_sets := [CategoryTheory])]
structure Codiscrete (α : Type u) where
  /-- A wrapper for promoting any type to a category,
  with a unique morphisms between any two objects of the category. -/
  as : α

@[simp]
theorem Codiscrete.mk_as {α : Type u} (X : Codiscrete α) : Codiscrete.mk X.as = X := rfl

/-- `Codiscrete α` is equivalent to the original type `α`. -/
@[simps]
def codiscreteEquiv {α : Type u} : Codiscrete α ≃ α where
  toFun := Codiscrete.as
  invFun := Codiscrete.mk
  left_inv := by aesop_cat
  right_inv := by aesop_cat

instance {α : Type u} [DecidableEq α] : DecidableEq (Codiscrete α) :=
  codiscreteEquiv.decidableEq

namespace Codiscrete

instance (A : Type*) : Category (Codiscrete A) where
  Hom _ _ := Unit
  id _ := ⟨⟩
  comp _ _ := ⟨⟩

section
variable {C : Type u} [Category.{v} C] {A : Type w}

/-- Any function `C → A` lifts to a functor `C ⥤ Codiscrete A`.-/
def functor (F : C → A) : C ⥤ Codiscrete A where
  obj := Codiscrete.mk ∘ F
  map _ := ⟨⟩

/-- The underlying function `C → A` of a functor `C ⥤ Codiscrete A`. -/
def invFunctor (F : C ⥤ Codiscrete A) : C → A := Codiscrete.as ∘ F.obj

/-- Given two functors to a codiscrete category, there is a trivial natural transformation.-/
def natTrans {F G : C ⥤ Codiscrete A} : F ⟶ G where
  app _ := ⟨⟩

/-- Given two functors into a codiscrete category, the trivial natural transformation is an
natural isomorphism.-/
def natIso {F G : C ⥤ Codiscrete A} : F ≅ G where
  hom := natTrans
  inv := natTrans

/-- Every functor `F` to a codiscrete category is naturally isomorphic {(actually, equal)} to
  `Codiscrete.as ∘ F.obj`. -/
@[simps!]
def natIsoFunctor {F : C ⥤ Codiscrete A} : F ≅ functor (Codiscrete.as ∘ F.obj) := Iso.refl _

end

/-- A function induces a functor between codiscrete categories.-/
def functorOfFun {A B : Type*} (f : A → B) : Codiscrete A ⥤ Codiscrete B :=
  functor (f ∘ Codiscrete.as)

open Opposite

/-- A codiscrete category is equivalent to its opposite category. -/
def oppositeEquivalence (A : Type*) : (Codiscrete A)ᵒᵖ ≌ Codiscrete A where
  functor := functor (fun x ↦ Codiscrete.as x.unop)
  inverse := (functor (fun x ↦ Codiscrete.as x.unop)).rightOp
  unitIso := NatIso.ofComponents (fun _ => by exact Iso.refl _)
  counitIso := natIso

/-- Codiscrete.Functor turns a type into a codiscrete category-/
def functorToCat : Type u ⥤ Cat.{0,u} where
  obj A := Cat.of (Codiscrete A)
  map := functorOfFun

open Adjunction Cat

/-- For a category `C` and type `A`, there is an equivalence between functions `objects.obj C ⟶ A`
and functors `C ⥤ Codiscrete A`.-/
def equivFunctorToCodiscrete {C : Type u} [Category.{v} C] {A : Type w} :
    (C → A) ≃ (C ⥤ Codiscrete A) where
  toFun := functor
  invFun := invFunctor
  left_inv _ := rfl
  right_inv _ := rfl

/-- The functor that turns a type into a codiscrete category is right adjoint to the objects
functor.-/
def adj : objects ⊣ functorToCat := mkOfHomEquiv {
  homEquiv := fun _ _ => equivFunctorToCodiscrete
  homEquiv_naturality_left_symm := fun _ _ => rfl
  homEquiv_naturality_right := fun _ _ => rfl }

/-- Components of the unit of the adjunction Cat.objects ⊣ Codiscrete.functorToCat -/
def unitApp (C : Type u) [Category.{v} C] : C ⥤ Codiscrete C := functor id

/-- Components of the counit of the adjunction `Cat.objects ⊣ Codiscrete.functorToCat` -/
def counitApp (A : Type u) : Codiscrete A → A := Codiscrete.as

lemma adj_unit_app (X : Cat.{0, u}) :
    adj.unit.app X = unitApp X := rfl

lemma adj_counit_app (A : Type u) :
    adj.counit.app A = counitApp A := rfl

/-- Left triangle equality of the adjunction Cat.objects ⊣ Codiscrete.functorToCat -/
lemma left_triangle_components {C : Cat.{0, u}} :
    objects.map (adj.unit.app C) ≫ adj.counit.app (objects.obj (C)) = 𝟙 (objects.obj C) := rfl

/-- Right triangle equality of the adjunction Cat.objects ⊣ Codiscrete.functorToCat -/
lemma right_triangle_components {X : Type u} :
    adj.unit.app (functorToCat.obj X) ≫ functorToCat.map (adj.counit.app X) =
      𝟙 (functorToCat.obj X) := rfl

end Codiscrete

end CategoryTheory
