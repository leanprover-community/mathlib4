/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Presentable.Basic
import Mathlib.SetTheory.Cardinal.HasCardinalLT

/-!
# `κ`-cocontinuous functors
-/
universe w v v' u u'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (κ : Cardinal.{w}) [Fact κ.IsRegular]

namespace Functor

#check PreservesColimit
variable (C D) in
def isCardinalCocontinuous : ObjectProperty (C ⥤ D) :=
  ∀ (J : Type w) [Category J] (hJ : HasCardinalLT J κ), 0 = by
    have ip :=
    sorry


end CategoryTheory
