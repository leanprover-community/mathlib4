/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Subobject.Basic
public import Mathlib.SetTheory.Cardinal.HasCardinalLT

@[expose] public section

/-!
# Cardinality of Subobject

If `X ⟶ Y` is a monomorphism, and the cardinality of `Subobject Y`
is `< κ`, then the cardinality of `Subobject X` is also `< κ`.

-/

universe w v u

namespace CategoryTheory.Subobject

variable {C : Type u} [Category.{v} C]

lemma hasCardinalLT_of_mono {Y : C} {κ : Cardinal.{w}}
    (h : HasCardinalLT (Subobject Y) κ) {X : C} (f : X ⟶ Y) [Mono f] :
    HasCardinalLT (Subobject X) κ :=
  h.of_injective _ (map_obj_injective f)

end CategoryTheory.Subobject
