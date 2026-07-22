/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward

/-!
# The pushforward functor is monoidal

If `F : C ⥤ D` is a functor and `R : Dᵒᵖ ⥤ CommRingCat` is a presheaf
of commutative rings, then the pushforward functor from the category
of presheaves of modules on `R` to the category of presheaves of
modules on `F.op ⋙ R` is monoidal.

-/

public section

universe v u

open CategoryTheory MonoidalCategory

namespace PresheafOfModules

variable {C D : Type*} [Category* C] [Category* D]
  (F : C ⥤ D) (R : Dᵒᵖ ⥤ CommRingCat.{u})

open ModuleCat.MonoidalCategory in
noncomputable instance : (pushforward₀OfCommRingCat F R).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      -- using `Iso.refl _` for `μIso` directly hurts kernel typechecking
      μIso _ _ := isoMk (fun _ ↦ Iso.refl _) (fun _ _ _ ↦ tensor_ext fun _ _ ↦ rfl)
      associativity _ _ _ := by
        ext1 x
        exact tensor_ext₃' fun m₁ m₂ m₃ ↦ rfl
      left_unitality _ := by
        ext1 x
        exact tensor_ext fun m₁ m₂ ↦ rfl
      right_unitality _ := by
        ext1 x
        exact tensor_ext fun m₁ m₂ ↦ rfl
    }

end PresheafOfModules
