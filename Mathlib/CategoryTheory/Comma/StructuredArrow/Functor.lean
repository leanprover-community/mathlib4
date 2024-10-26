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

namespace CostructuredArrow

@[simps]
def functor (T : C ⥤ D) : D ⥤ Cat where
  obj d := .of <| CostructuredArrow T d
  map f := CostructuredArrow.map f
  map_id d := Functor.ext (fun ⟨_, _, _⟩ => by simp [CostructuredArrow.map, Comma.mapRight])
  map_comp f g := Functor.ext (fun _ => by simp [CostructuredArrow.map, Comma.mapRight])

end CostructuredArrow

end CategoryTheory
