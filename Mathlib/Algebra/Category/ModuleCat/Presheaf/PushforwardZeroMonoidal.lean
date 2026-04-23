/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.CategoryTheory.CategoryStar
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.SetLike

/-!
# The pushforward functor is monoidal

If `F : C ⥤ D` is a functor and `R : Dᵒᵖ ⥤ CommRingCat` is a presheaf
of commutative rings, then the pushforward functor from the category
of presheaves of modules on `R` to the category of presheaves of
modules on `F.op ⋙ R` is monoidal.

-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory

namespace PresheafOfModules

variable {C D : Type*} [Category* C] [Category* D]
  (F : C ⥤ D) (R : Dᵒᵖ ⥤ CommRingCat.{u})

set_option backward.isDefEq.respectTransparency false in
noncomputable instance : (pushforward₀OfCommRingCat F R).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso _ _ := Iso.refl _
      left_unitality _ := by rw [← cancel_epi (λ_ _).inv]; cat_disch
      right_unitality _ := by rw [← cancel_epi (ρ_ _).inv]; cat_disch }

end PresheafOfModules
