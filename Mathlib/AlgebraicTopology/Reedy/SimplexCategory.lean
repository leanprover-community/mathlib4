/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Julian Kuelshammer
-/
module

public import Mathlib.AlgebraicTopology.Reedy.Basic
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Order.SuccPred.Nat

/-!
# The Reedy structure on the simplex category

In this file, we show that for the simplex category equipped with the classes
of epimorphisms and monomorphisms, the length map `SimplexCategory → ℕ`
is the degree map of a Reedy structure.

## References
* [Emily Riehl and Dominic Verity, *Elements of ∞-Category Theory*, C.4][RiehlVerity2022]

-/

@[expose] public section

open CategoryTheory HomotopicalAlgebra MorphismProperty Limits

namespace SimplexCategory

instance {x y : SimplexCategory} (f : x ⟶ y) :
    Subsingleton ((epimorphisms _).MapFactorizationData (monomorphisms _) f) where
  allEq := by
    rintro ⟨z1, p1, i1, hfac1, _, _⟩ ⟨z2, p2, i2, hfac2, _, _⟩
    obtain rfl := image_eq hfac1
    obtain rfl := image_eq hfac2
    obtain rfl : i1 = i2 := by rw [← image_ι_eq hfac1, image_ι_eq hfac2]
    obtain rfl : p1 = p2 := by rw [← factorThruImage_eq hfac1, factorThruImage_eq hfac2]
    rfl

/-- The Reedy structure on the simplex category. -/
@[simps, implicit_reducible]
def reedyStructure : ReedyStructure (epimorphisms SimplexCategory) (monomorphisms _) ℕ where
  deg := len
  lt₁ {n m} f _ hf :=
    lt_of_le_of_ne (len_le_of_epi f) (fun h ↦ (by
      obtain rfl : m = n := by rwa [SimplexCategory.ext_iff]
      obtain rfl := eq_id_of_epi f
      exact hf ⟨_⟩))
  lt₂ {n m} f _ hf :=
    lt_of_le_of_ne (len_le_of_mono f) (fun h ↦ by
      obtain rfl : n = m := by rwa [SimplexCategory.ext_iff]
      obtain rfl := eq_id_of_mono f
      exact hf ⟨_⟩)
  nonempty_unique {x y} f := by
    refine ⟨?_, by subsingleton⟩
    obtain t := (HasStrongEpiMonoFactorisations.has_fac f).some
    exact ⟨t.I, t.e, t.m, t.fac, by infer_instance, by infer_instance⟩

end SimplexCategory
