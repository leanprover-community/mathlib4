/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.CategoryTheory.Shift.CommShiftTwist
import Mathlib.CategoryTheory.Shift.Products
import Mathlib.CategoryTheory.Shift.Pullback

namespace CategoryTheory

namespace Functor

variable {C₁ C₂ D : Type*} [Category C₁] [Category C₂] [Category D]

/-structure CommShiftBifunctorData (A₁ A₂ B : Type*) [AddMonoid A₁] [AddMonoid A₂]
    [AddMonoid B] (D : Type*) [Category D] [HasShift D B] where
  p : A₁ × A₂ →+ B
  t : TwistCommShiftData (A₁ × A₂) (PullbackShift D p)

variable (F : C₁ ⥤ C₂ ⥤ D) (A₁ A₂ B : Type*) [AddMonoid A₁] [AddMonoid A₂]
  [AddMonoid B] (D : Type*) [Category D] [HasShift D B]
  (t : CommShiftBifunctorData A₁ A₂ B D)-/

end Functor

end CategoryTheory
