/-
Copyright (c) 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# Smooth structures

In this file we define smooth structures that build on Lie groups. We prefer using the term smooth
instead of Lie mainly because Lie ring has currently another use in mathematics.
-/

open scoped Manifold ContDiff

section SmoothRing

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

-- See note [Design choices about smooth algebraic structures]
/-- A smooth (semi)ring is a (semi)ring `R` where addition and multiplication are smooth.
If `R` is a ring, then negation is automatically smooth, as it is multiplication with `-1`. -/
class SmoothRing (I : ModelWithCorners 𝕜 E H) (R : Type*) [Semiring R] [TopologicalSpace R]
    [ChartedSpace H R] extends SmoothAdd I R : Prop where
  smooth_mul : ContMDiff (I.prod I) I ⊤ fun p : R × R => p.1 * p.2

-- see Note [lower instance priority]
instance (priority := 100) SmoothRing.toSmoothMul (I : ModelWithCorners 𝕜 E H) (R : Type*)
    [Semiring R] [TopologicalSpace R] [ChartedSpace H R] [h : SmoothRing I R] :
    SmoothMul I R :=
  { h with }

-- see Note [lower instance priority]
instance (priority := 100) SmoothRing.toLieAddGroup (I : ModelWithCorners 𝕜 E H) (R : Type*)
    [Ring R] [TopologicalSpace R] [ChartedSpace H R] [SmoothRing I R] : LieAddGroup I R where
  compatible := StructureGroupoid.compatible (contDiffGroupoid ∞ I)
  smooth_add := contMDiff_add I
  smooth_neg := by simpa only [neg_one_mul] using contMDiff_mul_left (G := R) (a := -1)

end SmoothRing

-- see Note [lower instance priority]
instance (priority := 100) fieldSmoothRing {𝕜 : Type*} [NontriviallyNormedField 𝕜] :
    SmoothRing 𝓘(𝕜) 𝕜 :=
  { normedSpaceLieAddGroup with
    smooth_mul := by
      rw [contMDiff_iff]
      refine ⟨continuous_mul, fun x y => ?_⟩
      simp only [mfld_simps]
      rw [contDiffOn_univ]
      exact contDiff_mul }

variable {𝕜 R E H : Type*} [TopologicalSpace R] [TopologicalSpace H] [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [ChartedSpace H R] (I : ModelWithCorners 𝕜 E H)

/-- A smooth (semi)ring is a topological (semi)ring. This is not an instance for technical reasons,
see note [Design choices about smooth algebraic structures]. -/
theorem topologicalSemiring_of_smooth [Semiring R] [SmoothRing I R] : TopologicalSemiring R :=
  { continuousMul_of_smooth I, continuousAdd_of_smooth I with }
