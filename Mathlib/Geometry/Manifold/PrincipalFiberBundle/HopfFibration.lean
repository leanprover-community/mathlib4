/-
Copyright (c) 2025 Dominic Steinitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Steinitz
-/
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.FiberBundle.Basic
import Mathlib.Geometry.Manifold.PrincipalFiberBundle.PrincipalGBundle

/-!
# The Hopf Fibration

This file constructs the Hopf fibration as a fiber bundle, which is the canonical example
of a non-trivial principal S¹-bundle.

## Main definitions

* `xN`, `xS`: The north and south poles of S² ⊂ ℝ³
* `UN`, `US`: Stereographic coordinate charts for S² from the north and south poles
* `HopfFibration`: The fiber bundle core defining the Hopf fibration S³ → S²

## Mathematical background

The Hopf fibration is a continuous map π : S³ → S² where:
- The total space is the 3-sphere S³ ⊂ ℝ⁴
- The base space is the 2-sphere S² ⊂ ℝ³
- Each fiber π⁻¹(p) is a circle S¹
- The structure group is S¹ = U(1) acting freely and transitively on the fibers

This is historically significant as the first example of a non-trivial fiber bundle and
represents the non-trivial element of the homotopy group π₃(S²).

## Implementation notes

The construction uses stereographic projection charts at the north and south poles to cover
S². The coordinate change functions encode the non-trivial bundle structure. Many definitions
currently contain `sorry` and are work in progress.

## References

* H. Hopf, "Über die Abbildungen der dreidimensionalen Sphäre auf die Kugelfläche" (1931)
* Any standard text on fiber bundles or algebraic topology

-/

open Matrix Bundle Manifold
open Bundle Topology MulAction Set
open scoped Manifold
open Bundle Topology MulAction Set

def xN := (!₂[1, 0, 0] : EuclideanSpace ℝ (Fin 3))

theorem hN : xN ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  rw [EuclideanSpace.sphere_zero_eq 1 (le_of_lt Real.zero_lt_one), mem_setOf]
  simp [xN]
  rw [Fin.sum_univ_three]
  have h0 : ![(1 : ℝ), 0, 0] 0 ^ 2 = 1 := by simp
  have h1 : ![(1 : ℝ), 0, 0] 1 ^ 2 = 0 := by simp
  have h2 : ![(1 : ℝ), 0, 0] 2 ^ 2 = 0 := by simp
  have ha : ![(1 : ℝ), 0, 0] 0 ^ 2 +
            ![1, 0, 0] 1 ^ 2 +
            ![1, 0, 0] 2 ^ 2 = 1 := by rw [h0, h1, h2]; simp
  exact ha

noncomputable def UN := chartAt (EuclideanSpace ℝ (Fin 2))
  (⟨xN, hN⟩ : ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)))

def xS := (!₂[-1, 0, 0] : EuclideanSpace ℝ (Fin 3))

theorem hS : xS ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  rw [EuclideanSpace.sphere_zero_eq 1 (le_of_lt Real.zero_lt_one), mem_setOf]
  simp [xS]
  rw [Fin.sum_univ_three]
  have h0 : ![(-1 : ℝ), 0, 0] 0 ^ 2 = 1 := by simp
  have h1 : ![(1 : ℝ), 0, 0] 1 ^ 2 = 0 := by simp
  have h2 : ![(1 : ℝ), 0, 0] 2 ^ 2 = 0 := by simp
  have ha : ![(-1 : ℝ), 0, 0] 0 ^ 2 +
            ![1, 0, 0] 1 ^ 2 +
            ![1, 0, 0] 2 ^ 2 = 1 := by rw [h0, h1, h2]; simp
  exact ha

noncomputable def US := chartAt (EuclideanSpace ℝ (Fin 2))
  (⟨xS, hS⟩ : ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)))

def xhN := ((⟨xN, hN⟩ :  Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ))

noncomputable
def MyCoordChange : Fin 2 → Fin 2 →
                    (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) →
                    (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) →
                    (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) := by
  let f := Function.uncurry Complex.mk ∘
          (fun x => (x 0, x 1)) ∘
          (chartAt (EuclideanSpace ℝ (Fin 2)) xhN).toFun
  sorry

noncomputable
def HopfFibration : FiberBundleCore (Fin 2) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
                                            (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) where
  baseSet i := if i = 0 then UN.source
                        else US.source
  isOpen_baseSet i := by
    split
    · exact UN.open_source
    · exact US.open_source
  indexAt x := if (x.val 0) > 0 then 0 else 1
  mem_baseSet_at := sorry
  coordChange := MyCoordChange
  coordChange_self := sorry
  continuousOn_coordChange := sorry
  coordChange_comp := sorry

#min_imports
