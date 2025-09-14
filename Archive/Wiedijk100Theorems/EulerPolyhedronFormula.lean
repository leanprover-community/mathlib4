/-
Copyright (c) 2024 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
import Mathlib.Algebra.Homology.EulerPolyhedronFormula

/-!
# Freek № 13: Euler's Polyhedron Formula

This file proves Theorem 13 from the [100 Theorems List](https://www.cs.ru.nl/~freek/100/),
Euler's polyhedron formula, which states that for a convex polyhedron with V vertices,
E edges, and F faces, we have V - E + F = 2.

We provide the classical 2-dimensional case for polyhedra.
The general n-dimensional case is proved using homological algebra in
`Mathlib.Algebra.Homology.EulerPolyhedronFormula`.

## Main Results

* `euler_formula_2d`: The classical formula V - E + F = 2 for 2-dimensional polyhedra

## References

* [Grünbaum, *Convex Polytopes*][gruenbaum2003]
* [Lakatos, *Proofs and Refutations*][lakatos1976]
* [Richeson, *Euler's Gem*][richeson2008]
-/

namespace Theorems100

open Polyhedron

variable {α : Type} [Fintype α]

/-- **Euler's Polyhedron Formula (2D case)**: For a 2-dimensional acyclic geometric polyhedron,
    V - E + F = 2, where V is the number of vertices, E is the number of edges,
    and F is the number of faces. -/
theorem euler_formula_2d (GP : GeometricPolyhedron α) [DecidableEq α]
    (hacyclic : isAcyclic GP) (hdim : GP.toPolyhedron.dim = 2) :
    (faceCount GP.toPolyhedron 0 : ℤ) - (faceCount GP.toPolyhedron 1 : ℤ)
      + (faceCount GP.toPolyhedron 2 : ℤ) = 2 := by
  have hformula := euler_polyhedron_formula GP hacyclic
  simp at hformula
  unfold eulerCharacteristic at hformula
  rw [hdim] at hformula
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hformula
  simp [pow_zero, pow_one, pow_two] at hformula
  linarith only [hformula]

end Theorems100
