/-
Copyright (c) 2025 Joseph Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Hua
-/
import Mathlib.CategoryTheory.Category.Grpd
import Mathlib.CategoryTheory.Core
import Mathlib.CategoryTheory.Adjunction.Reflective

/-!
# The forgetful-core adjunction

Taking the core of a category defines a functor `Cat ⥤ Grpd`. This functor is left adjoint
to the forgetful functor from `Grpd ⥤ Cat`.

# Main definitions

* `CategoryTheory.Core.functor`: the functor `Cat ⥤ Grpd` that on objects takes
  the core of a category
* `CategoryTheory.Core.adjunction`: the adjunction with the forgetful functor
  `Grpd.forgetToCat` on the left, and the core functor `Core.functor` on the right.
* An instance that `Grpd.forgetToCat` is coreflective.

-/

universe w v u v₁ u₁ v₂ u₂ v₃ u₃

noncomputable section

namespace CategoryTheory
namespace Core

variable {C : Type u} [Category.{v} C] {D : Type u₁} [Category.{v₁} D]
  {G : Type u₂} [Groupoid.{v₂} G]

/-- The functor from `Cat` to `Grpd` that takes the core of a category, on objects. -/
def functor : Cat.{v,u} ⥤ Grpd.{v,u} where
  obj C := Grpd.of (Core C)
  map F := F.core

def functorEquiv : (G ⥤ C) ≃ (G ⥤ Core C) where
  toFun F := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

/-- The adjunction between the forgetful functor from `Grpd` to `Cat` and the core
functor from `Cat` to `Grpd`. -/
def adjunction : Grpd.forgetToCat ⊣ functor :=
  Adjunction.mkOfHomEquiv
    { homEquiv G C := by
        dsimp [Grpd.forgetToCat, functor]
        sorry
      homEquiv_naturality_left_symm := sorry
      homEquiv_naturality_right := sorry }
-- where
  -- unit := {
  --   app G := functorToCore (𝟭 _)
  --   naturality _ _ F := by
  --     simp [functor, Grpd.comp_eq_comp, ← functorToCore_comp_left, ← functorToCore_comp_right,
  --       Functor.id_comp, Functor.comp_id, Grpd.forgetToCat]}
  -- counit := {app C := inclusion C}

end Core

namespace Grpd

open Functor Core

instance : IsLeftAdjoint Grpd.forgetToCat :=
  IsLeftAdjoint.mk ⟨ functor , ⟨ adjunction ⟩ ⟩

instance : IsRightAdjoint functor :=
  IsRightAdjoint.mk ⟨ Grpd.forgetToCat , ⟨ adjunction ⟩ ⟩

instance : Coreflective Grpd.forgetToCat where
  R := functor
  adj := adjunction

end Grpd

end CategoryTheory
