/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Topology.Algebra.Module.LinearMap
import Mathlib.Analysis.LocallyConvex.Polar

/-!
# The topological StrongDual of a Module

## References

* [Conway, John B., A course in functional analysis][conway1990]

## Tags

StrongDual, polar
-/

/-
TODO Change the namespace
-/
namespace NormedSpace

section

variable (R : Type*) [CommSemiring R] [TopologicalSpace R]
  (M : Type*) [TopologicalSpace M] [AddCommMonoid M] [Module R M] [ContinuousAdd R]
  [ContinuousConstSMul R R]

/-- The StrongDual pairing as a bilinear form. -/
def dualPairing : StrongDual R M →ₗ[R] M →ₗ[R] R :=
  ContinuousLinearMap.coeLM R

@[simp]
theorem dualPairing_apply {v : StrongDual R M} {x : M} : dualPairing R M v x = v x :=
  rfl

end

section

variable (R : Type*) [SeminormedCommRing R]
variable (M : Type*) [TopologicalSpace M] [AddCommGroup M] [Module R M]

--instance : ContinuousMul R  := by exact ContinuousMul.to_continuousSMul

theorem dualPairing_separatingLeft : (dualPairing R M).SeparatingLeft := by
  rw [LinearMap.separatingLeft_iff_ker_eq_bot]
  unfold dualPairing
  rw [LinearMap.ker_eq_bot]
  exact ContinuousLinearMap.coe_injective

end


section

/-- Given a subset `s` in a normed space `E` (over a field `𝕜`), the polar
`polar 𝕜 s` is the subset of `StrongDual 𝕜 E` consisting of those functionals which
evaluate to something of norm at most one at all points `z ∈ s`. -/
def polar (𝕜 : Type*) [NormedCommRing 𝕜] {E : Type*} [AddCommGroup E]
  [TopologicalSpace E] [Module 𝕜 E] : Set E → Set (StrongDual 𝕜 E) :=
  (dualPairing 𝕜 E).flip.polar

/-- Given a subset `s` in a normed space `E` (over a field `𝕜`) closed under scalar multiplication,
the polar `polarSubmodule 𝕜 s` is the submodule of `StrongDual 𝕜 E` consisting of those functionals
which evaluate to zero at all points `z ∈ s`. -/
def polarSubmodule (𝕜 : Type*) [NontriviallyNormedField 𝕜] {E : Type*} [AddCommGroup E]
    [TopologicalSpace E] [Module 𝕜 E] {S : Type*} [SetLike S E] [SMulMemClass S 𝕜 E] (m : S) :
    Submodule 𝕜 (StrongDual 𝕜 E) := (dualPairing 𝕜 E).flip.polarSubmodule m

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]

lemma polarSubmodule_eq_polar (m : SubMulAction 𝕜 E) :
    (polarSubmodule 𝕜 m : Set (StrongDual 𝕜 E)) = polar 𝕜 m := rfl

theorem mem_polar_iff {x' : StrongDual 𝕜 E} (s : Set E) : x' ∈ polar 𝕜 s ↔ ∀ z ∈ s, ‖x' z‖ ≤ 1 :=
  Iff.rfl

lemma polarSubmodule_eq_setOf {S : Type*} [SetLike S E] [SMulMemClass S 𝕜 E] (m : S) :
    polarSubmodule 𝕜 m = { y : StrongDual 𝕜 E | ∀ x ∈ m, y x = 0 } :=
  (dualPairing 𝕜 E).flip.polar_subMulAction _

lemma mem_polarSubmodule {S : Type*} [SetLike S E] [SMulMemClass S 𝕜 E] (m : S)
    (y : StrongDual 𝕜 E) : y ∈ polarSubmodule 𝕜 m ↔ ∀ x ∈ m, y x = 0 := by
  have := polarSubmodule_eq_setOf 𝕜 m
  apply_fun (y ∈ ·) at this
  rwa [propext_iff] at this

@[simp]
theorem zero_mem_polar (s : Set E) : (0 : StrongDual 𝕜 E) ∈ polar 𝕜 s :=
  LinearMap.zero_mem_polar _ s

theorem polar_nonempty (s : Set E) : Set.Nonempty (polar 𝕜 s) :=
  LinearMap.polar_nonempty _ _

open Set

@[simp]
theorem polar_univ : polar 𝕜 (univ : Set E) = {(0 : StrongDual 𝕜 E)} :=
  (dualPairing 𝕜 E).flip.polar_univ
    (LinearMap.flip_separatingRight.mpr (dualPairing_separatingLeft 𝕜 E))

@[simp]
theorem polar_empty : polar 𝕜 (∅ : Set E) = Set.univ :=
  LinearMap.polar_empty _

@[simp]
theorem polar_singleton {a : E} : polar 𝕜 {a} = { x | ‖x a‖ ≤ 1 } := by
  simp only [polar, LinearMap.polar_singleton, LinearMap.flip_apply, dualPairing_apply]

theorem mem_polar_singleton {a : E} (y : StrongDual 𝕜 E) : y ∈ polar 𝕜 {a} ↔ ‖y a‖ ≤ 1 := by
  simp only [polar_singleton, mem_setOf_eq]

theorem polar_zero : polar 𝕜 ({0} : Set E) = Set.univ :=
  LinearMap.polar_zero _

end

end NormedSpace
