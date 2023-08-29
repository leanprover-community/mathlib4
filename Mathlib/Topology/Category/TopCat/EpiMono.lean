/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton
-/
import Mathlib.Topology.Category.TopCat.Adjunctions

#align_import topology.category.Top.epi_mono from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# Epi- and monomorphisms in `Top`

This file shows that a continuous function is an epimorphism in the category of topological spaces
if and only if it is surjective, and that a continuous function is a monomorphism in the category of
topological spaces if and only if it is injective.
-/


universe u

open CategoryTheory

open TopCat

namespace TopCat

theorem epi_iff_surjective {X Y : TopCat.{u}} (f : X ⟶ Y) : Epi f ↔ Function.Surjective f := by
  suffices Epi f ↔ Epi ((forget TopCat).map f) by
    rw [this, CategoryTheory.epi_iff_surjective]
    rfl
  constructor
  -- ⊢ Epi f → Epi ((forget TopCat).map f)
  · intro
    -- ⊢ Epi ((forget TopCat).map f)
    infer_instance
    -- 🎉 no goals
  · apply Functor.epi_of_epi_map
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.epi_iff_surjective TopCat.epi_iff_surjective

theorem mono_iff_injective {X Y : TopCat.{u}} (f : X ⟶ Y) : Mono f ↔ Function.Injective f := by
  suffices Mono f ↔ Mono ((forget TopCat).map f) by
    rw [this, CategoryTheory.mono_iff_injective]
    rfl
  constructor
  -- ⊢ Mono f → Mono ((forget TopCat).map f)
  · intro
    -- ⊢ Mono ((forget TopCat).map f)
    infer_instance
    -- 🎉 no goals
  · apply Functor.mono_of_mono_map
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Top.mono_iff_injective TopCat.mono_iff_injective

end TopCat
