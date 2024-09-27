/-
Copyright (c) 2024 Alvaro Belmonte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alvaro Belmonte
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

/-- The type of objects in the category `Codiscrete A` is a type synonym for `A` and there is a unique
morphism between any two objects in this category. -/
def Codiscrete (A : Type u) : Type u := A

namespace Codiscrete

instance (A : Type*) : Category (Codiscrete A) where
  Hom _ _ := Unit -- The hom types in the Codiscrete A are the unit type.
  id _ := ⟨⟩ -- This is the unique element of the unit type.
  comp _ _ := ⟨⟩

/-- A function induces a functor between codiscrete categories.-/
def funToFunc {A B : Type*} (f : A → B) : Codiscrete A ⥤ Codiscrete B where
  obj a := f a
  map _ := ⟨⟩

section
variable {C : Type u} [Category.{v} C] {A : Type w}

/-- Any function `C → A` lifts to a functor `C ⥤  Codiscrete A`. For discrete categories this is
called `functor` but we use that name for something else. -/
def lift (F : C → A) : C ⥤ Codiscrete A where
  obj := F
  map _ := ⟨⟩

/-- Any functor `C ⥤  Codiscrete A` has an underlying function.-/
def invlift (F : C ⥤ Codiscrete A) : C → A := F.obj

/-- Given two functors to a codiscrete category, there is a trivial natural transformation.-/
def natTrans {F G : C ⥤ Codiscrete A} :
    F ⟶ G where
  app _ := ⟨⟩

/-- Given two functors into a codiscrete category, the trivial natural transformation is an
natural isomorphism.-/
def natIso {F G : C ⥤ Codiscrete A} :
    F ≅ G where
      hom := natTrans
      inv := {
        app := fun _ => ⟨⟩

      }

/-- Every functor `F` to a codiscrete category is naturally isomorphic {(actually, equal)?} to
  `Codiscrete.functor (F.obj)`. -/
def natIsoFunctor {F : C ⥤ Codiscrete A} : F ≅ lift (F.obj) where
  hom := {
    app := fun _ => ⟨⟩
  }
  inv := {
    app := fun _ => ⟨⟩
  }

end
open Opposite

/-- A codiscrete category is equivalent to its opposite category. -/
protected def opposite (A : Type*) : (Codiscrete A)ᵒᵖ ≌ Codiscrete A :=
 let F : (Codiscrete A)ᵒᵖ ⥤ Codiscrete A := lift fun (op (x)) => x
 {
  functor := F
  inverse := F.rightOp
  unitIso := NatIso.ofComponents fun ⟨x⟩ =>
   Iso.refl _
  counitIso := natIso
 }

/-- Codiscrete.Functor turns a type into a codiscrete category-/
def functor : Type u ⥤ Cat.{0,u} where
  obj A := Cat.of (Codiscrete A)
  map := funToFunc

open Adjunction Cat

/-- For a category `C` and type `A`, there is an equivalence between functions `objects.obj C ⟶ A`
and functors `C ⥤ Codiscrete A`.-/
def homEquiv (C : Cat) (A : Type*) : (objects.obj C ⟶ A) ≃ (C ⟶ functor.obj A) where
  toFun := lift
  invFun := invlift
  left_inv _ := rfl
  right_inv _ := rfl

/-- The functor that turns a type into a codiscrete category is right adjoint to the objects
functor.-/
def adj : objects ⊣ functor := mkOfHomEquiv
  {
    homEquiv := homEquiv
    homEquiv_naturality_left_symm := fun _ _ => Eq.refl _
    homEquiv_naturality_right := fun _ _ => Eq.refl _
  }

/-- A second proof of the same adjunction.  -/
def adj' : objects ⊣ functor where
  unit := {
    app := fun _ => {
      obj := fun _ => _
      map := fun _ => ⟨⟩
    }
  }
  counit := {
    app := fun _ => id
  }
  left_triangle_components := by aesop
  right_triangle_components := by aesop

end Codiscrete

end CategoryTheory
