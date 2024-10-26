/-
Copyright (c) 2024 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
import Mathlib.CategoryTheory.Grothendieck

/-!
# Structured Arrow Categories as strict functor to Cat

Forming a structured arrow category `StructuredArrow S T` with `S : D` and `T : C ⥤ D` is stictly
functorial in `S`, inducing a functor `Dᵒᵖ ⥤ Cat`. This file constructs said functor and proves
that we can precompose it with another functor `L : E ⥤ D` to obtain a category equivalent to
`Comma L T`.
-/

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace StructuredArrow

@[simps]
def functor (T : C ⥤ D) : Dᵒᵖ ⥤ Cat where
  obj d := .of <| StructuredArrow d.unop T
  map f := map f.unop
  map_id d := Functor.ext (fun ⟨_, _, _⟩ => by simp [CostructuredArrow.map, Comma.mapRight])
  map_comp f g := Functor.ext (fun _ => by simp [CostructuredArrow.map, Comma.mapRight])

end StructuredArrow

namespace CostructuredArrow

@[simps]
def functor (T : C ⥤ D) : D ⥤ Cat where
  obj d := .of <| CostructuredArrow T d
  map f := CostructuredArrow.map f
  map_id d := Functor.ext (fun ⟨_, _, _⟩ => by simp [CostructuredArrow.map, Comma.mapRight])
  map_comp f g := Functor.ext (fun _ => by simp [CostructuredArrow.map, Comma.mapRight])

variable {E : Type u₃} [Category.{v₃} E]
variable (L : C ⥤ D) (R : E ⥤ D)

@[simps]
def grothendieckPrecompFunctorToComma : Grothendieck (R ⋙ functor L) ⥤ Comma L R where
  obj := fun P => ⟨P.fiber.left, P.base, P.fiber.hom⟩
  map := fun f => ⟨f.fiber.left, f.base, by simp⟩

@[simps]
def commaToGrothendieckPrecompFunctor : Comma L R ⥤ Grothendieck (R ⋙ functor L) where
  obj := fun X => ⟨X.right, mk X.hom⟩
  map := fun f => ⟨f.right, homMk f.left⟩
  map_id X := Grothendieck.ext _ _ rfl (by simp)
  map_comp f g := Grothendieck.ext _ _ rfl (by simp)

@[simps]
def grothendieckPrecompFunctorEquivalence : Grothendieck (R ⋙ functor L) ≌ Comma L R where
  functor := grothendieckPrecompFunctorToComma _ _
  inverse := commaToGrothendieckPrecompFunctor _ _
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _)

end CostructuredArrow

end CategoryTheory
