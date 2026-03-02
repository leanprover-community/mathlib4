/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Dimension lemmas for homological complex differentials

This file proves basic dimension-related properties of the differentials `dFrom` and `dTo`
in homological complexes of modules over a division ring.

The core lemmas are stated for an arbitrary `HomologicalComplex (ModuleCat k) c` with
`c : ComplexShape ι`, making them applicable to ℕ-indexed, ℤ-indexed, or any other
complex shape.

## Main results

* `HomologicalComplex.dFrom_zero_range`: `dFrom` has zero range when `xNext` is zero.
* `HomologicalComplex.dTo_zero_range`: `dTo` has zero range when `xPrev` is zero.
* `HomologicalComplex.dFrom_range_finrank_eq_d`: The range of `dFrom` has the same dimension as
  the range of the underlying differential `d`.
* `HomologicalComplex.dTo_range_finrank_eq_d`: The range of `dTo` has the same dimension as the
  range of the underlying differential `d`.
* `HomologicalComplex.range_dTo_le_ker_dFrom`: The range of `dTo i` is contained in the kernel
  of `dFrom i`.
* `ChainComplex.dFrom_succ_range_finrank_eq_dTo`: The range of `dFrom (i+1)` has the same
  dimension as the range of `dTo i` (ℤ-indexed chain complexes).
-/

@[expose] public section

open CategoryTheory Limits HomologicalComplex

variable {k : Type*} [DivisionRing k]
variable {ι : Type*} {c : ComplexShape ι}

namespace HomologicalComplex

/-- If `xNext i` is zero, then `dFrom i` has zero range. -/
lemma dFrom_zero_range (C : HomologicalComplex (ModuleCat k) c) (i : ι)
    (h : IsZero (C.xNext i)) :
    LinearMap.range (C.dFrom i).hom = ⊥ := by
  rw [dFrom_eq_zero_of_isZero_xNext C i h, ModuleCat.hom_zero, LinearMap.range_zero]

/-- If `xPrev j` is zero, then `dTo j` has zero range. -/
lemma dTo_zero_range (C : HomologicalComplex (ModuleCat k) c) (j : ι)
    (h : IsZero (C.xPrev j)) :
    LinearMap.range (C.dTo j).hom = ⊥ := by
  rw [dTo_eq_zero_of_isZero_xPrev C j h, ModuleCat.hom_zero, LinearMap.range_zero]

/-- The range of `dFrom i` has the same dimension as the range of the underlying
differential `C.d i j`. -/
lemma dFrom_range_finrank_eq_d (C : HomologicalComplex (ModuleCat k) c) {i j : ι}
    (r : c.Rel i j) :
    Module.finrank k (LinearMap.range (C.dFrom i).hom) =
    Module.finrank k (LinearMap.range (C.d i j).hom) := by
  rw [C.dFrom_eq r, show ((C.d i j) ≫ (C.xNextIso r).inv).hom =
    (C.xNextIso r).toLinearEquiv.symm.toLinearMap ∘ₗ (C.d i j).hom from rfl,
    LinearMap.range_comp, ← LinearEquiv.finrank_map_eq (C.xNextIso r).toLinearEquiv.symm]

/-- The range of `dTo j` has the same dimension as the range of the underlying
differential `C.d i j`. -/
lemma dTo_range_finrank_eq_d (C : HomologicalComplex (ModuleCat k) c) {i j : ι}
    (r : c.Rel i j) :
    Module.finrank k (LinearMap.range (C.dTo j).hom) =
    Module.finrank k (LinearMap.range (C.d i j).hom) := by
  rw [C.dTo_eq r, show ((C.xPrevIso r).hom ≫ C.d i j).hom =
    (C.d i j).hom ∘ₗ (C.xPrevIso r).toLinearEquiv.toLinearMap from rfl,
    LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]

/-- The range of `dTo i` is contained in the kernel of `dFrom i`. -/
lemma range_dTo_le_ker_dFrom
    (C : HomologicalComplex (ModuleCat k) c) (i : ι) :
    LinearMap.range (C.dTo i).hom ≤
    LinearMap.ker (C.dFrom i).hom := by
  rw [LinearMap.range_le_ker_iff]
  exact congr_arg ModuleCat.Hom.hom (C.dTo_comp_dFrom i)

end HomologicalComplex

namespace ChainComplex

/-- The range of `dFrom (i + 1)` has the same dimension as the range of `dTo i`.
This is specific to ℤ-indexed chain complexes; the general versions
`HomologicalComplex.dFrom_range_finrank_eq_d` and `HomologicalComplex.dTo_range_finrank_eq_d`
apply to any complex shape. -/
lemma dFrom_succ_range_finrank_eq_dTo
    (C : ChainComplex (ModuleCat k) ℤ) (i : ℤ) :
    Module.finrank k (LinearMap.range (C.dFrom (i + 1)).hom) =
    Module.finrank k (LinearMap.range (C.dTo i).hom) := by
  have rel : (ComplexShape.down ℤ).Rel (i + 1) i := by
    simp [ComplexShape.down, ComplexShape.down']
  rw [HomologicalComplex.dFrom_range_finrank_eq_d C rel,
    HomologicalComplex.dTo_range_finrank_eq_d C rel]

end ChainComplex
