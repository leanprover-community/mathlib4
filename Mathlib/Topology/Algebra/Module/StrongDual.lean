/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Topology.Algebra.Module.LinearMap
import Mathlib.Analysis.LocallyConvex.Polar

/-!
# The topological strong dual of a module

## Main definitions

- `strongDualPairing`: The strong dual pairing as a bilinear form.
- `StrongDual.polar`: Given a subset `s` in a monoid `M` (over a commutative ring `R`), the polar
  `polar R s` is the subset of `StrongDual R M` consisting of those functionals which evaluate to
  something of norm at most one at all points `z ∈ s`.
- `StrongDual.polarSubmodule`: Given a subset `s` in a monoid `M` (over a field `𝕜`) closed under
  scalar multiplication, the polar `polarSubmodule 𝕜 s` is the submodule of `StrongDual 𝕜 M`
  consisting of those functionals which evaluate to zero at all points `z ∈ s`.

## References

* [Conway, John B., A course in functional analysis][conway1990]

## Tags

StrongDual, polar
-/

namespace StrongDual

section

variable (R : Type*) [CommSemiring R] [TopologicalSpace R]
  (M : Type*) [TopologicalSpace M] [AddCommMonoid M] [Module R M] [ContinuousAdd R]
  [ContinuousConstSMul R R]

/-- The StrongDual pairing as a bilinear form. -/
def _root_.strongDualPairing : StrongDual R M →ₗ[R] M →ₗ[R] R :=
  ContinuousLinearMap.coeLM R

@[deprecated (since := "2025-08-3")] alias NormedSpace.dualPairing := strongDualPairing

@[simp]
theorem dualPairing_apply {v : StrongDual R M} {x : M} : strongDualPairing R M v x = v x :=
  rfl

@[deprecated (since := "2025-08-3")] alias NormedSpace.dualPairing_apply := dualPairing_apply

end

section

variable (R M : Type*) [SeminormedCommRing R] [TopologicalSpace M] [AddCommGroup M] [Module R M]

theorem dualPairing_separatingLeft : (strongDualPairing R M).SeparatingLeft := by
  rw [LinearMap.separatingLeft_iff_ker_eq_bot, LinearMap.ker_eq_bot]
  exact ContinuousLinearMap.coe_injective

@[deprecated (since := "2025-08-3")] alias NormedSpace.dualPairing_separatingLeft :=
  dualPairing_separatingLeft

end

section

/-- Given a subset `s` in a monoid `M` (over a commutative ring `R`), the polar `polar R s` is the
subset of `StrongDual R M` consisting of those functionals which evaluate to something of norm at
most one at all points `z ∈ s`. -/
def polar (R : Type*) [NormedCommRing R] {M : Type*} [AddCommMonoid M]
    [TopologicalSpace M] [Module R M] : Set M → Set (StrongDual R M) :=
  (strongDualPairing R M).flip.polar

@[deprecated (since := "2025-08-3")] alias _root_.NormedSpace.polar := polar

/-- Given a subset `s` in a monoid `M` (over a field `𝕜`) closed under scalar multiplication,
the polar `polarSubmodule 𝕜 s` is the submodule of `StrongDual 𝕜 M` consisting of those functionals
which evaluate to zero at all points `z ∈ s`. -/
def polarSubmodule (𝕜 : Type*) [NontriviallyNormedField 𝕜] {M : Type*} [AddCommMonoid M]
    [TopologicalSpace M] [Module 𝕜 M] {S : Type*} [SetLike S M] [SMulMemClass S 𝕜 M] (m : S) :
    Submodule 𝕜 (StrongDual 𝕜 M) := (strongDualPairing 𝕜 M).flip.polarSubmodule m

@[deprecated (since := "2025-08-3")] alias _root_.NormedSpace.polarSubmodule := polarSubmodule

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
variable {E : Type*} [AddCommMonoid E] [TopologicalSpace E] [Module 𝕜 E]

lemma polarSubmodule_eq_polar (m : SubMulAction 𝕜 E) :
    (polarSubmodule 𝕜 m : Set (StrongDual 𝕜 E)) = polar 𝕜 m := rfl

@[deprecated (since := "2025-08-3")] alias _root_.NormedSpace.polarSubmodule_eq_polar :=
  polarSubmodule_eq_polar

theorem mem_polar_iff {x' : StrongDual 𝕜 E} (s : Set E) : x' ∈ polar 𝕜 s ↔ ∀ z ∈ s, ‖x' z‖ ≤ 1 :=
  Iff.rfl

@[deprecated (since := "2025-08-3")] alias _root_.NormedSpace.mem_polar_iff := mem_polar_iff

lemma polarSubmodule_eq_setOf {S : Type*} [SetLike S E] [SMulMemClass S 𝕜 E] (m : S) :
    polarSubmodule 𝕜 m = { y : StrongDual 𝕜 E | ∀ x ∈ m, y x = 0 } :=
  (strongDualPairing 𝕜 E).flip.polar_subMulAction _

@[deprecated (since := "2025-08-3")] alias _root_.NormedSpace.polarSubmodule_eq_setOf :=
  polarSubmodule_eq_setOf

lemma mem_polarSubmodule {S : Type*} [SetLike S E] [SMulMemClass S 𝕜 E] (m : S)
    (y : StrongDual 𝕜 E) : y ∈ polarSubmodule 𝕜 m ↔ ∀ x ∈ m, y x = 0 :=
  propext_iff.mp congr($(polarSubmodule_eq_setOf 𝕜 m) y)

@[deprecated (since := "2025-08-3")] alias _root_.NormedSpace.mem_polarSubmodule :=
  mem_polarSubmodule

@[simp]
theorem zero_mem_polar (s : Set E) : (0 : StrongDual 𝕜 E) ∈ polar 𝕜 s :=
  LinearMap.zero_mem_polar _ s

@[deprecated (since := "2025-08-3")] alias _root_.NormedSpace.zero_mem_polar := zero_mem_polar

theorem polar_nonempty (s : Set E) : Set.Nonempty (polar 𝕜 s) :=
  LinearMap.polar_nonempty _ _

@[deprecated (since := "2025-08-3")] alias _root_.NormedSpace.polar_nonempty := polar_nonempty

open Set

@[simp]
theorem polar_empty : polar 𝕜 (∅ : Set E) = Set.univ :=
  LinearMap.polar_empty _

@[deprecated (since := "2025-08-3")] alias _root_.NormedSpace.polar_empty := polar_empty

@[simp]
theorem polar_singleton {a : E} : polar 𝕜 {a} = { x | ‖x a‖ ≤ 1 } := by
  simp only [polar, LinearMap.polar_singleton, LinearMap.flip_apply, dualPairing_apply]

@[deprecated (since := "2025-08-3")] alias _root_.NormedSpace.polar_singleton := polar_singleton

theorem mem_polar_singleton {a : E} (y : StrongDual 𝕜 E) : y ∈ polar 𝕜 {a} ↔ ‖y a‖ ≤ 1 := by
  simp only [polar_singleton, mem_setOf_eq]

@[deprecated (since := "2025-08-3")] alias _root_.NormedSpace.mem_polar_singleton :=
  mem_polar_singleton

theorem polar_zero : polar 𝕜 ({0} : Set E) = Set.univ :=
  LinearMap.polar_zero _

@[deprecated (since := "2025-08-3")] alias _root_.NormedSpace.polar_zero := polar_zero

end

section

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]

open Set

@[simp]
theorem polar_univ : polar 𝕜 (univ : Set E) = {(0 : StrongDual 𝕜 E)} :=
  (strongDualPairing 𝕜 E).flip.polar_univ
    (LinearMap.flip_separatingRight.mpr (dualPairing_separatingLeft 𝕜 E))

@[deprecated (since := "2025-08-3")] alias _root_.NormedSpace.polar_univ := polar_univ

end

end StrongDual
