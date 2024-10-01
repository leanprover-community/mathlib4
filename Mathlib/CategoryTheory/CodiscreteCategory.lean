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

`Codiscrete.lift` promotes a function `f : C → A` (for any category `C`) to a functor
`Discrete.functor f : C ⥤  Codiscrete A`.

Similarly, `Codiscrete.natTrans` and `Codiscrete.natIso` promote `I`-indexed families of morphisms,
or `I`-indexed families of isomorphisms to natural transformations or natural isomorphism.

We define `functor : Type u ⥤ Cat.{0,u}` which sends a type to the codiscrete category and show
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
  with the only morphisms being equalities. -/
  as : α

@[simp]
theorem Codiscrete.mk_as {α : Type u} (X : Codiscrete α) : Codiscrete.mk X.as = X := by
  rfl

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

/-- Any function `C → A` lifts to a functor `C ⥤  Codiscrete A`. For discrete categories this is
called `functor` but we use that name for something else. -/
def lift (F : C → A) : C ⥤ Codiscrete A where
  obj := Codiscrete.mk ∘ F
  map _ := ⟨⟩

/-- Any functor `C ⥤  Codiscrete A` has an underlying function.-/
def invlift (F : C ⥤ Codiscrete A) : C → A := Codiscrete.as ∘ F.obj

/-- Given two functors to a codiscrete category, there is a trivial natural transformation.-/
def natTrans {F G : C ⥤ Codiscrete A} :
    F ⟶ G where
  app _ := ⟨⟩

/-- Given two functors into a codiscrete category, the trivial natural transformation is an
natural isomorphism.-/
def natIso {F G : C ⥤ Codiscrete A} :
    F ≅ G where
  hom := natTrans
  inv := natTrans

/-- Every functor `F` to a codiscrete category is naturally isomorphic {(actually, equal)} to
  `Codiscrete.as ∘ F.obj`. -/
@[simps!]
def natIsoFunctor {F : C ⥤ Codiscrete A} : F ≅ lift (Codiscrete.as ∘ F.obj) := Iso.refl _

end

/-- A function induces a functor between codiscrete categories.-/
def functorOfFun {A B : Type*} (f : A → B) : Codiscrete A ⥤ Codiscrete B := lift (f ∘ Codiscrete.as)

open Opposite

/-- A codiscrete category is equivalent to its opposite category. -/
def oppositeEquivalence (A : Type*) : (Codiscrete A)ᵒᵖ ≌ Codiscrete A where
  functor := lift (fun x ↦ Codiscrete.as x.unop)
  inverse := (lift (fun x ↦ Codiscrete.as x.unop)).rightOp
  unitIso := NatIso.ofComponents (fun _ => by exact Iso.refl _)
  counitIso := natIso

/-- Codiscrete.Functor turns a type into a codiscrete category-/
def functor : Type u ⥤ Cat.{0,u} where
  obj A := Cat.of (Codiscrete A)
  map := functorOfFun

open Adjunction Cat

/-- For a category `C` and type `A`, there is an equivalence between functions `objects.obj C ⟶ A`
and functors `C ⥤ Codiscrete A`.-/
def equivFunctorToCodiscrete {C : Type u} [Category.{v} C] {A : Type w} :
    (C → A) ≃ (C ⥤ Codiscrete A) where
  toFun := lift
  invFun := invlift
  left_inv _ := rfl
  right_inv _ := rfl

/-- The functor that turns a type into a codiscrete category is right adjoint to the objects
functor.-/
def adj : objects ⊣ functor := mkOfHomEquiv
  {
    homEquiv := fun _ _ => equivFunctorToCodiscrete
    homEquiv_naturality_left_symm := fun _ _ => rfl
    homEquiv_naturality_right := fun _ _ => rfl
  }

/--Unit of the adjunction Cat.objects ⊣ Codiscrete.functor -/
def unit : 𝟭 Cat ⟶ objects ⋙ functor where
  app := by
    simp only [Functor.id_obj, Functor.comp_obj]
    intro C
    apply lift
    exact fun a ↦ a

/--Conit of the adjunction Cat.objects ⊣ Codiscrete.functor -/
def counit : functor ⋙ objects ⟶ 𝟭 (Type*) := {
    app := by
      intro A
      simp only [Functor.comp_obj, Functor.id_obj]
      apply invlift
      exact functor.map fun a ↦ a
  }

/--Left triangle equality of the adjunction Cat.objects ⊣ Codiscrete.functor -/
def leftTriangleComponents {X : Cat} :
    objects.map (unit.app X) ≫ counit.app (objects.obj X) = 𝟙 (objects.obj X) := rfl

/--Right triangle equality of the adjunction Cat.objects ⊣ Codiscrete.functor -/
def rightTriangleComponents {Y : Type u} :
    unit.app (functor.obj Y) ≫ functor.map (counit.app Y) = 𝟙 (functor.obj Y) := rfl

end Codiscrete

end CategoryTheory
