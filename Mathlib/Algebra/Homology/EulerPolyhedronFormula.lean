/-
Copyright (c) 2024 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
import Mathlib.Algebra.Homology.EulerPolyhedronFormula.Basic

/-!
# Euler Polyhedron Formula

This module proves Euler's polyhedron formula using homological algebra and chain complexes.

## Main Components

- `GeometricPolyhedron`: A polyhedron structure with the chain complex property (∂² = 0)
- `toChainComplex`: Constructs the chain complex from a geometric polyhedron
- `toAugmentedComplex`: Constructs the augmented chain complex
- `isAcyclic`: Defines acyclicity for the augmented complex

## Key Results

The main theorem `euler_polyhedron_formula` states that for an acyclic geometric polyhedron P
of dimension d, the Euler characteristic equals 1 + (-1)^d.

### Special Cases
- `euler_formula_2d`: For 2-dimensional polyhedra (surfaces), V - E + F = 2
- `euler_formula_1d`: For 1-dimensional polyhedra (polygons), V - E = 0

## Approach

The proof uses the augmented chain complex of the polyhedron. The key insight is that
for an acyclic complex, the Euler characteristic can be computed via a telescoping sum,
yielding the alternating sum of face counts.

## References

* [Grünbaum, *Convex Polytopes*][gruenbaum2003]
* [Lakatos, *Proofs and Refutations*][lakatos1976]
* [Richeson, *Euler's Gem*][richeson2008]
-/

open Polyhedron

variable {α : Type} [Fintype α]

/-- Version: For a acyclic d-dimensional geometric polyhedron,
    the Euler characteristic equals 1 + (-1)^d. -/
theorem euler_polyhedron_formula (GP : GeometricPolyhedron α) [DecidableEq α]
    (hacyclic : isAcyclic GP) :
    eulerCharacteristic GP.toPolyhedron = 1 + (-1 : ℤ)^GP.toPolyhedron.dim := by
  -- The strategy: use the relationship χ(A(P)) = 1 - χ(P) for complexes
  -- and the fact that hacyclic means the augmented complex is acyclic

  -- Step 1: Apply the augmented characteristic relation
  have augmented_relation := augmented_euler_characteristic_relation GP

  -- Step 2: Use the lemma for acyclic augmented complexes
  have acyclic_euler := acyclic_augmented_euler_char GP hacyclic

  -- Step 3: Combine the relations
  -- We have: χ(A(P)) = 1 - χ(P)
  -- With χ(A(P)) = (-1)^{d+1}, we get:
  -- (-1)^{d+1} = 1 - χ(P)
  -- Therefore: χ(P) = 1 - (-1)^{d+1} = 1 + (-1)^d
  rw [acyclic_euler] at augmented_relation
  -- augmented_relation : (-1)^{d+1} = 1 - χ(P)
  -- We need to show: χ(P) = 1 + (-1)^d
  have h : (1 : ℤ) - (-1)^(GP.toPolyhedron.dim + 1) = 1 + (-1)^GP.toPolyhedron.dim := by
    rw [pow_succ]
    ring
  linarith only [augmented_relation, h]

/-- Corollary: For 2-dimensional geometric polyhedra (surfaces in R³), we get V - E + F = 2
    This is the classical Euler formula. -/
theorem euler_formula_2d (GP : GeometricPolyhedron α) [DecidableEq α]
    (hacyclic : isAcyclic GP) (h_dim : GP.toPolyhedron.dim = 2) :
    (faceCount GP.toPolyhedron 0 : ℤ) - (faceCount GP.toPolyhedron 1 : ℤ) +
      (faceCount GP.toPolyhedron 2 : ℤ) = 2 := by
  have hformula := euler_polyhedron_formula GP hacyclic
  -- For a 2-dimensional polyhedron: χ(P) = 1 + (-1)^2 = 1 + 1 = 2
  rw [h_dim] at hformula
  simp [pow_two] at hformula
  unfold eulerCharacteristic at hformula
  rw [h_dim] at hformula
  -- Now hformula expands to the alternating sum with dim = 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hformula
  simp [pow_zero, pow_one, pow_two] at hformula
  linarith only [hformula]

/-- Special case: For 1-dimensional geometric polyhedra (cycles/polygons), V - E = 0 -/
theorem euler_formula_1d (GP : GeometricPolyhedron α) [DecidableEq α]
    (hacyclic : isAcyclic GP) (h_dim : GP.toPolyhedron.dim = 1) :
    (faceCount GP.toPolyhedron 0 : ℤ) = (faceCount GP.toPolyhedron 1 : ℤ) := by
  have hformula := euler_polyhedron_formula GP hacyclic
  -- For a 1-dimensional polyhedron: χ(P) = 1 + (-1)^1 = 1 - 1 = 0
  rw [h_dim] at hformula
  simp at hformula
  unfold eulerCharacteristic at hformula
  rw [h_dim] at hformula
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hformula
  simp [pow_zero, pow_one] at hformula
  have : (faceCount GP.toPolyhedron 0 : ℤ) - (faceCount GP.toPolyhedron 1 : ℤ) = 0 := by
    linarith only [hformula]
  linarith only [this]
