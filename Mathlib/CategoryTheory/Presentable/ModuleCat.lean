/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Presentable.LocallyPresentable

import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Generator.ModuleCat
import Mathlib.CategoryTheory.Presentable.StrongGenerator

/-!
# The category of modules over a ring is locally presentable

If `R : Type w` is a ring, we show that the category `ModuleCat.{w} R`
is `κ`-locally presentable for any regular cardinal `κ`.

-/

public section

open CategoryTheory

universe w

namespace ModuleCat

attribute [local instance] Cardinal.fact_isRegular_aleph0

variable (R : Type w) [Ring R] (κ : Cardinal.{w}) [Fact κ.IsRegular]

instance : (forget (ModuleCat.{w} R)).IsCardinalAccessible κ where
  preservesColimitOfShape J _ _ := by
    have := isFiltered_of_isCardinalFiltered J κ
    infer_instance

instance : (forget (ModuleCat.{w} R)).IsAccessible.{w} where
  exists_cardinal := ⟨.aleph0, inferInstance, inferInstance⟩

instance : IsCardinalPresentable (ModuleCat.of R R) κ :=
  Functor.isCardinalAccessible_of_natIso (coyonedaObjIsoForget R).symm κ

instance : IsCardinalLocallyPresentable (ModuleCat.{w} R) κ := by
  rw [IsCardinalLocallyPresentable.iff_exists_isStrongGenerator]
  exact ⟨_, inferInstance, isStrongGenerator_singleton R, by
    rw [ObjectProperty.singleton_le_iff]
    infer_instance⟩

instance : IsLocallyPresentable.{w} (ModuleCat.{w} R) where
  exists_cardinal := ⟨.aleph0, inferInstance, inferInstance⟩

end ModuleCat
