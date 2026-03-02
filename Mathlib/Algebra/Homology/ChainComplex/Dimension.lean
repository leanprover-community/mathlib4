/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.Dimension.RankNullity

/-!
# Dimension lemmas for chain complex differentials

This file proves basic dimension-related properties of the differentials `dFrom` and `dTo`
in ℤ-indexed chain complexes of modules over a division ring.

## Main results

* `ChainComplex.dFrom_eq_zero_of_isZero`: `dFrom` is zero when its target object is zero.
* `ChainComplex.dTo_eq_zero_of_isZero`: `dTo` is zero when its source object is zero.
* `ChainComplex.dFrom_zero_range`: `dFrom` has zero range when its target object is zero.
* `ChainComplex.dTo_zero_range`: `dTo` has zero range when its source object is zero.
* `ChainComplex.dFrom_range_finrank_eq_d`: The range of `dFrom` has the same dimension as the
  range of the underlying differential `d`.
* `ChainComplex.dTo_range_finrank_eq_d`: The range of `dTo` has the same dimension as the
  range of the underlying differential `d`.
* `ChainComplex.dFrom_succ_range_finrank_eq_dTo`: The range of `dFrom (i+1)` has the same
  dimension as the range of `dTo i`.
* `ChainComplex.range_dTo_le_ker_dFrom`: The range of `dTo i` is contained in the kernel
  of `dFrom i`.
-/

@[expose] public section

open CategoryTheory Limits HomologicalComplex

variable {k : Type*} [DivisionRing k]

namespace ChainComplex

/-- If the target object is zero, then dFrom is the zero map. -/
lemma dFrom_eq_zero_of_isZero (C : ChainComplex (ModuleCat k) ℤ) (i : ℤ)
    (h : IsZero (C.X (i - 1))) : C.dFrom i = 0 :=
  IsZero.eq_zero_of_tgt
    (by rwa [xNext, show (ComplexShape.down ℤ).next i = i - 1 from by simp]) _

/-- If the source object is zero, then dTo is the zero map. -/
lemma dTo_eq_zero_of_isZero (C : ChainComplex (ModuleCat k) ℤ) (i : ℤ)
    (h : IsZero (C.X (i + 1))) : C.dTo i = 0 :=
  IsZero.eq_zero_of_src
    (by rwa [xPrev, show (ComplexShape.down ℤ).prev i = i + 1 from by simp]) _

/-- If the target object is zero, then dFrom has zero range. -/
lemma dFrom_zero_range (C : ChainComplex (ModuleCat k) ℤ) (i : ℤ)
    (h : IsZero (C.X (i - 1))) :
    LinearMap.range (C.dFrom i).hom = ⊥ := by
  rw [dFrom_eq_zero_of_isZero C i h, ModuleCat.hom_zero, LinearMap.range_zero]

/-- If the source object is zero, then dTo has zero range. -/
lemma dTo_zero_range (C : ChainComplex (ModuleCat k) ℤ) (i : ℤ)
    (h : IsZero (C.X (i + 1))) :
    LinearMap.range (C.dTo i).hom = ⊥ := by
  rw [dTo_eq_zero_of_isZero C i h, ModuleCat.hom_zero, LinearMap.range_zero]

/-- The range of dFrom has the same dimension as the underlying differential. -/
lemma dFrom_range_finrank_eq_d (C : ChainComplex (ModuleCat k) ℤ) (i : ℤ) :
    Module.finrank k (LinearMap.range (C.dFrom (i + 1)).hom) =
    Module.finrank k (LinearMap.range (C.d (i + 1) i).hom) := by
  have rel : (ComplexShape.down ℤ).Rel (i + 1) i := by
    simp [ComplexShape.down, ComplexShape.down']
  rw [C.dFrom_eq rel, show ((C.d (i + 1) i) ≫ (C.xNextIso rel).inv).hom =
    (C.xNextIso rel).toLinearEquiv.symm.toLinearMap ∘ₗ (C.d (i + 1) i).hom from rfl,
    LinearMap.range_comp, ← LinearEquiv.finrank_map_eq (C.xNextIso rel).toLinearEquiv.symm]

/-- The range of dTo has the same dimension as the underlying differential. -/
lemma dTo_range_finrank_eq_d (C : ChainComplex (ModuleCat k) ℤ) (i : ℤ) :
    Module.finrank k (LinearMap.range (C.dTo i).hom) =
    Module.finrank k (LinearMap.range (C.d (i + 1) i).hom) := by
  have rel : (ComplexShape.down ℤ).Rel (i + 1) i := by
    simp [ComplexShape.down, ComplexShape.down']
  rw [C.dTo_eq rel, show ((C.xPrevIso rel).hom ≫ C.d (i + 1) i).hom =
    (C.d (i + 1) i).hom ∘ₗ (C.xPrevIso rel).toLinearEquiv.toLinearMap from rfl,
    LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]

/-- The range of `dFrom (i + 1)` has the same dimension as the range of `dTo i`. -/
lemma dFrom_succ_range_finrank_eq_dTo
    (C : ChainComplex (ModuleCat k) ℤ) (i : ℤ) :
    Module.finrank k (LinearMap.range (C.dFrom (i + 1)).hom) =
    Module.finrank k (LinearMap.range (C.dTo i).hom) := by
  rw [dFrom_range_finrank_eq_d, dTo_range_finrank_eq_d]

/-- The range of dTo i is contained in the kernel of dFrom i. -/
lemma range_dTo_le_ker_dFrom
    (C : ChainComplex (ModuleCat k) ℤ) (i : ℤ) :
    LinearMap.range (C.dTo i).hom ≤
    LinearMap.ker (C.dFrom i).hom := by
  rw [LinearMap.range_le_ker_iff]
  exact congr_arg ModuleCat.Hom.hom (C.dTo_comp_dFrom i)

end ChainComplex
