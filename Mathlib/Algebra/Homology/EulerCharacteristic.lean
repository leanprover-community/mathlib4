/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.GroupWithZero.Indicator
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Int.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
# Euler characteristic of homological complexes

The Euler characteristic is defined using the `ComplexShape.EulerCharSigns` typeclass,
which provides the alternating signs for each index. This allows the definition to work
uniformly for chain complexes, cochain complexes, and complexes with other index types.

The definitions work on graded objects, with the homological complex versions
defined as abbreviations that apply the graded object versions to `C.X` and `C.homology`.

## Junk values

These definitions may have junk values from `finsum` (0 for infinite support) and
`Module.finrank` (0 for modules not free of finite rank).

## Main definitions

* `ComplexShape.EulerCharSigns`: Typeclass providing alternating signs for Euler characteristic
* `GradedObject.eulerChar`: The Euler characteristic of a graded object using `finsum`
* `GradedObject.finrankSupport`: Indices where `Module.finrank` is nonzero
* `HomologicalComplex.eulerChar`: The Euler characteristic using `finsum`
* `HomologicalComplex.homologyEulerChar`: The homological Euler characteristic using `finsum`

## Main results

* `GradedObject.eulerChar_eq_sum_finSet_of_finrankSupport_subset`: The `finsum` equals the
  finite sum when the graded object has finite support contained in the given set
* `HomologicalComplex.eulerChar_eq_sum_finSet_of_finrankSupport_subset`: The `finsum` equals
  the finite sum when the complex has finite support contained in the given set
* `HomologicalComplex.homologyEulerChar_eq_sum_finSet_of_finrankSupport_subset`: The `finsum`
  homological Euler characteristic equals the finite sum when homology has finite support

-/

@[expose] public section

namespace ComplexShape

variable {ι : Type*} (c : ComplexShape ι)

/-- Signs for terms of Euler characteristic on complexes. -/
class EulerCharSigns where
  /-- The sign for each index -/
  χ : ι → ℤˣ
  /-- Signs alternate along relations in the complex shape -/
  χ_next {i j : ι} (h : c.Rel i j) : χ j = - χ i

variable [c.EulerCharSigns]

/-- The sign at index `i` for Euler characteristic computations. -/
abbrev χ : ι → ℤˣ := EulerCharSigns.χ c

/-- Signs alternate in the forward direction of the complex shape. -/
lemma χ_next {i j : ι} (h : c.Rel i j) : c.χ j = - c.χ i := EulerCharSigns.χ_next h

/-- Signs alternate in the backward direction of the complex shape. -/
lemma χ_prev {i j : ι} (h : c.Rel i j) : c.χ i = - c.χ j := by simp [c.χ_next h]

@[simps]
instance eulerCharSignsUpInt : (up ℤ).EulerCharSigns where
  χ := Int.negOnePow
  χ_next := by rintro _ _ rfl; rw [Int.negOnePow_succ]

@[simps]
instance eulerCharSignsDownInt : (down ℤ).EulerCharSigns where
  χ := Int.negOnePow
  χ_next := by rintro _ _ rfl; simp [Int.negOnePow_succ]

set_option backward.isDefEq.respectTransparency false in
@[simps]
instance eulerCharSignsUpNat : (up ℕ).EulerCharSigns where
  χ n := (-1) ^ n
  χ_next := by rintro _ _ rfl; simp [pow_add]

set_option backward.isDefEq.respectTransparency false in
@[simps]
instance eulerCharSignsDownNat : (down ℕ).EulerCharSigns where
  χ n := (-1) ^ n
  χ_next := by rintro _ _ rfl; simp [pow_add]

end ComplexShape

open ComplexShape CategoryTheory

variable {R : Type*} [Ring R] {ι : Type*}

namespace GradedObject

variable (c : ComplexShape ι) [c.EulerCharSigns]

/-- The support of a graded object with respect to finite rank:
the set of indices where the rank is nonzero. -/
def finrankSupport (X : CategoryTheory.GradedObject ι (ModuleCat R)) : Set ι :=
  Function.support (fun i => Module.finrank R (X i))

/-- The finite rank support is contained in a set if and only if
the rank vanishes outside that set. -/
lemma finrankSupport_subset_iff (X : CategoryTheory.GradedObject ι (ModuleCat R)) (s : Set ι) :
    finrankSupport X ⊆ s ↔ ∀ i ∉ s, Module.finrank R (X i) = 0 :=
  Function.support_subset_iff'

/-- The Euler characteristic of a graded object as a sum over all indices.
The sign at each index is determined by the `ComplexShape.EulerCharSigns` instance.
Defaults to 0 if the support of the ranks of the objects of `X` is infinite. -/
noncomputable def eulerChar (X : CategoryTheory.GradedObject ι (ModuleCat R)) : ℤ :=
  ∑ᶠ i : ι, (c.χ i : ℤ) * Module.finrank R (X i)

/-- The support of the Euler characteristic summand equals the finite rank support,
because the sign `c.χ i` is always nonzero (it's a unit). -/
private lemma support_eulerChar_summand (X : CategoryTheory.GradedObject ι (ModuleCat R)) :
    Function.support (fun i => (c.χ i : ℤ) * Module.finrank R (X i)) = finrankSupport X := by
  simp only [finrankSupport, Function.support_mul_of_ne_zero_left (fun i => Units.ne_zero (c.χ i))]
  ext i; simp [Function.mem_support]

/-- If a graded object has finite rank support contained in a finite set,
the `finsum` Euler characteristic equals the finite sum over that set. -/
theorem eulerChar_eq_sum_finSet_of_finrankSupport_subset
    (X : CategoryTheory.GradedObject ι (ModuleCat R)) (indices : Finset ι)
    (h_support : finrankSupport X ⊆ indices) :
    eulerChar c X = ∑ i ∈ indices, (c.χ i : ℤ) * Module.finrank R (X i) := by
  simp only [eulerChar]
  rw [finsum_eq_sum_of_support_subset]
  exact (support_eulerChar_summand c X).symm ▸ h_support

end GradedObject

namespace HomologicalComplex

variable {c : ComplexShape ι} [c.EulerCharSigns]

/-- The Euler characteristic of a homological complex as a sum over all indices using `finsum`.
The sign at each index is determined by the `ComplexShape.EulerCharSigns` instance.
Defaults to 0 if the support of the ranks is infinite. -/
noncomputable abbrev eulerChar (C : HomologicalComplex (ModuleCat R) c) : ℤ :=
  GradedObject.eulerChar c C.X

/-- The homological Euler characteristic as a sum over all indices using `finsum`.
This is the Euler characteristic computed from the homology groups rather than
the original complex. Defaults to 0 if the support of the ranks is infinite. -/
noncomputable abbrev homologyEulerChar (C : HomologicalComplex (ModuleCat R) c)
    [∀ i : ι, C.HasHomology i] : ℤ :=
  GradedObject.eulerChar c (fun i => C.homology i)

/-- If a complex has finite rank support contained in a finite set,
the `finsum` Euler characteristic equals the finite sum over that set. -/
theorem eulerChar_eq_sum_finSet_of_finrankSupport_subset (C : HomologicalComplex (ModuleCat R) c)
    (indices : Finset ι)
    (h_support : GradedObject.finrankSupport C.X ⊆ indices) :
    eulerChar C = ∑ i ∈ indices, (c.χ i : ℤ) * Module.finrank R (C.X i) :=
  GradedObject.eulerChar_eq_sum_finSet_of_finrankSupport_subset c C.X indices h_support

/-- If homology has finite rank support contained in a finite set,
the `finsum` homological Euler characteristic equals the finite sum over that set. -/
theorem homologyEulerChar_eq_sum_finSet_of_finrankSupport_subset
    (C : HomologicalComplex (ModuleCat R) c) [∀ i : ι, C.HasHomology i] (indices : Finset ι)
    (h_support : GradedObject.finrankSupport (fun i => C.homology i) ⊆ indices) :
    homologyEulerChar C = ∑ i ∈ indices, (c.χ i : ℤ) * Module.finrank R (C.homology i) :=
  GradedObject.eulerChar_eq_sum_finSet_of_finrankSupport_subset c
    (fun i => C.homology i) indices h_support

end HomologicalComplex
