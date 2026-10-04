/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Presentable.IsCardinalFiltered

/-!
# κ-Filtered colimits in the category of types.

In this file, we show that in a `κ`-filtered colimit of types (where κ is a regular cardinal),
any family of elements of size < κ in the colimit can be lifted to a common stage of the
diagram.
-/

@[expose] public section

open CategoryTheory Limits ConcreteCategory

universe v u w

namespace CategoryTheory.Limits.Types.FilteredColimit

variable {J : Type*} [Category* J] (κ : Cardinal.{w}) [Fact κ.IsRegular] [IsCardinalFiltered J κ]
  (F : J ⥤ Type u)

attribute [local instance] small_colimitType_of_hasColimit

open IsFiltered in
variable {F} in
lemma jointly_surjective_of_isColimit_of_hasCardinalLT
    {t : Cocone F} (ht : IsColimit t) {ι : Type*} (hι : HasCardinalLT ι κ) (x : ι → t.pt) :
    ∃ (j : J) (x' : ι → F.obj j), ∀ (i : ι), t.ι.app j (x' i) = x i := by
  have (i : ι) := Types.jointly_surjective_of_isColimit ht (x i)
  choose j₀ x₀ h₀ using this
  refine ⟨IsCardinalFiltered.max j₀ hι, fun i ↦ F.map (IsCardinalFiltered.toMax j₀ hι i) (x₀ i),
    by simpa⟩

end CategoryTheory.Limits.Types.FilteredColimit

