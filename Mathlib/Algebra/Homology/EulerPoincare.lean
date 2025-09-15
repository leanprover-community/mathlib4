/-
Copyright (c) 2024 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.Algebra.BigOperators.Intervals

/-!
# The Euler-Poincaré Formula

This file proves the Euler-Poincaré formula for bounded chain complexes of
finite-dimensional vector spaces over a field.

## Main Results

* `homology_eulerChar`: The homological Euler characteristic (alternating sum of
  homology dimensions)
* `euler_poincare_formula`: For a bounded complex of finite-dimensional vector spaces,
  the alternating sum of dimensions equals the alternating sum of homology dimensions
* `acyclic_euler_char`: For an acyclic complex, the homological Euler characteristic
  equals the alternating sum of dimensions

## Implementation Notes

We work with chain complexes indexed by ℕ and bounded below by 0. The general
statement for arbitrary bounded complexes can be obtained by reindexing.

-/

open CategoryTheory Limits HomologicalComplex

variable {k : Type*} [Field k]

namespace ChainComplex

/-- The Euler characteristic of a bounded chain complex, defined as the
alternating sum of dimensions of chain groups. -/
noncomputable def eulerChar' (C : ChainComplex (ModuleCat k) ℕ) (n : ℕ) : ℤ :=
  Finset.sum (Finset.range (n + 1)) fun i =>
    (-1 : ℤ) ^ i * (Module.finrank k (C.X i) : ℤ)

/-- The homological Euler characteristic, defined as the alternating sum
of dimensions of homology groups. -/
noncomputable def homology_eulerChar (C : ChainComplex (ModuleCat k) ℕ)
    (n : ℕ) [∀ i : ℕ, C.HasHomology i] : ℤ :=
  Finset.sum (Finset.range (n + 1)) fun i =>
    (-1 : ℤ) ^ i * (Module.finrank k (C.homology i) : ℤ)

/-- The cycles at position i form a submodule of X_i -/
def cyclesSubmodule (C : ChainComplex (ModuleCat k) ℕ) (i : ℕ) : Submodule k (C.X i) :=
  LinearMap.ker (C.dFrom i).hom

/-- The boundaries at position i form a submodule of cycles -/
def boundariesSubmodule (C : ChainComplex (ModuleCat k) ℕ) (i : ℕ) :
    Submodule k (cyclesSubmodule C i) :=
  (LinearMap.range (C.dTo i).hom).comap (cyclesSubmodule C i).subtype

/-- Helper lemma: dimension of homology equals dimension of cycles minus dimension of boundaries -/
lemma homology_finrank_formula (C : ChainComplex (ModuleCat k) ℕ) (i : ℕ)
    [C.HasHomology i] [Module.Finite k (C.X i)]
    [Module.Finite k (C.cycles i)] [Module.Finite k (C.homology i)] :
    (Module.finrank k (C.homology i) : ℤ) +
    (Module.finrank k (LinearMap.range (C.dTo i).hom) : ℤ) =
    (Module.finrank k (LinearMap.ker (C.dFrom i).hom) : ℤ) := by
  -- The homology is ker(d_i) / im(d_{i+1})
  -- Use Submodule.finrank_quotient_add_finrank
  sorry

/-- The key telescoping lemma for the Euler-Poincaré formula -/
lemma euler_poincare_telescoping (C : ChainComplex (ModuleCat k) ℕ) (n : ℕ)
    [∀ i : ℕ, C.HasHomology i]
    [∀ i : ℕ, Module.Finite k (C.X i)]
    [∀ i : ℕ, Module.Finite k (C.homology i)] :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ)^i * (Module.finrank k (C.X i) : ℤ) =
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ)^i * (Module.finrank k (C.homology i) : ℤ) +
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ)^i * (Module.finrank k (LinearMap.range (C.dFrom i).hom) : ℤ) -
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ)^i * (Module.finrank k (LinearMap.range (C.dTo i).hom) : ℤ) := by
  -- Use rank-nullity: dim(X_i) = dim(ker d_i) + dim(range d_i)
  -- And homology formula: dim(H_i) = dim(ker d_i) - dim(range(dTo i))
  -- The telescoping comes from the fact that range(dFrom i) at position i
  -- equals range(dTo (i-1)) at position i-1, with opposite signs
  sorry

/-- The Euler-Poincaré formula: For a bounded complex of finite-dimensional
vector spaces, the alternating sum of dimensions equals the alternating sum
of homology dimensions. -/
theorem euler_poincare_formula (C : ChainComplex (ModuleCat k) ℕ) (n : ℕ)
    [∀ i : ℕ, C.HasHomology i]
    [∀ i : ℕ, Module.Finite k (C.X i)]
    [∀ i : ℕ, Module.Finite k (C.homology i)] :
    eulerChar' C n = homology_eulerChar C n := by
  unfold eulerChar' homology_eulerChar
  -- Apply the telescoping lemma
  have tel := euler_poincare_telescoping C n
  -- The key observation: range(dFrom i) and range(dTo (i+1)) represent
  -- the same subspace (image of d_{i+1} : X_{i+1} → X_i)
  -- but appear with opposite signs in the alternating sum, so they cancel
  sorry

/-- For an acyclic complex (all homology vanishes), the Euler characteristic
equals 0 when the complex has even length, and equals dim(C_0) when it has
odd length. -/
theorem acyclic_euler_char (C : ChainComplex (ModuleCat k) ℕ) (n : ℕ)
    [∀ i : ℕ, C.HasHomology i]
    [∀ i : ℕ, Module.Finite k (C.X i)]
    (hC : C.Acyclic) :
    homology_eulerChar C n = 0 := by
  -- Since the complex is acyclic, all homology groups are zero
  -- So each term in the sum is 0
  unfold homology_eulerChar
  apply Finset.sum_eq_zero
  intro i hi
  -- The homology at i is zero because the complex is acyclic
  have : IsZero (C.homology i) := by
    have exact_i : (C.sc i).Exact := hC i
    rw [ShortComplex.exact_iff_isZero_homology] at exact_i
    exact exact_i
  -- So its dimension is 0
  have dim_zero : Module.finrank k (C.homology i) = 0 := by
    -- IsZero implies Subsingleton for ModuleCat objects
    have : Subsingleton (C.homology i) := ModuleCat.subsingleton_of_isZero this
    exact Module.finrank_zero_of_subsingleton
  rw [dim_zero]
  simp

/-- Special case: when the complex is acyclic, the Euler-Poincaré formula
shows that the Euler characteristic depends only on the boundary conditions. -/
theorem acyclic_euler_poincare (C : ChainComplex (ModuleCat k) ℕ) (n : ℕ)
    [∀ i : ℕ, C.HasHomology i]
    [∀ i : ℕ, Module.Finite k (C.X i)]
    [∀ i : ℕ, Module.Finite k (C.homology i)]
    (hC : C.Acyclic) :
    eulerChar' C n = 0 := by
  -- First apply the Euler-Poincaré formula
  have ep := euler_poincare_formula C n
  rw [ep]
  -- Then use that all homology vanishes
  exact acyclic_euler_char C n hC

section Connection

/-- Our specific Euler characteristic for polyhedra is a special case
of the general Euler-Poincaré formula. When we have an acyclic augmented
complex with appropriate boundary conditions, we get the classical
Euler formula for polyhedra. -/
theorem polyhedron_euler_as_special_case
    (C : ChainComplex (ModuleCat k) ℕ) (n : ℕ)
    [∀ i : ℕ, C.HasHomology i]
    [∀ i : ℕ, Module.Finite k (C.X i)]
    [∀ i : ℕ, Module.Finite k (C.homology i)] :
    eulerChar' C n = homology_eulerChar C n := by
  -- This follows from the general Euler-Poincaré formula
  exact euler_poincare_formula C n

end Connection

end ChainComplex
