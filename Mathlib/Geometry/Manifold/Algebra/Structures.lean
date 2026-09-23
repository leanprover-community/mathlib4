/-
Copyright (c) 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.Notation

/-!
# `C^n` structures

In this file we define `C^n` structures that build on Lie groups. We prefer using the
term `ContMDiffRing` instead of Lie mainly because Lie ring has currently another use
in mathematics.
-/

public section

open scoped Manifold ContDiff

section ContMDiffRing

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ∞ω}

-- See note [Design choices about smooth algebraic structures]
/-- A `C^n` (semi)ring is a (semi)ring `R` where addition and multiplication are `C^n`.
If `R` is a ring, then negation is automatically `C^n`, as it is multiplication with `-1`. -/
class ContMDiffRing (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)
    (R : Type*) [Semiring R] [TopologicalSpace R] [ChartedSpace H R] : Prop
    extends ContMDiffAdd I n R where
  contMDiff_mul : CMDiff n fun p : R × R => p.1 * p.2

-- see Note [lower instance priority]
instance (priority := 100) ContMDiffRing.toContMDiffMul (I : ModelWithCorners 𝕜 E H) (R : Type*)
    [Semiring R] [TopologicalSpace R] [ChartedSpace H R] [h : ContMDiffRing I n R] :
    ContMDiffMul I n R :=
  { h with }

-- see Note [lower instance priority]
instance (priority := 100) ContMDiffRing.toLieAddGroup (I : ModelWithCorners 𝕜 E H) (R : Type*)
    [Ring R] [TopologicalSpace R] [ChartedSpace H R] [ContMDiffRing I n R] : LieAddGroup I n R where
  compatible := StructureGroupoid.compatible (contDiffGroupoid n I)
  contMDiff_add := contMDiff_add I n
  contMDiff_neg := by simpa only [neg_one_mul] using contMDiff_mul_left (G := R) (a := -1)

end ContMDiffRing

set_option backward.isDefEq.respectTransparency false in
-- see Note [lower instance priority]
instance (priority := 100) instFieldContMDiffRing
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ∞ω} :
    ContMDiffRing 𝓘(𝕜) n 𝕜 :=
  { instNormedSpaceLieAddGroup with
    contMDiff_mul := by
      rw [contMDiff_iff]
      refine ⟨continuous_mul, fun x y => ?_⟩
      simp only [mfld_simps]
      rw [contDiffOn_univ]
      exact contDiff_mul }

variable {𝕜 R E H : Type*} [TopologicalSpace R] [TopologicalSpace H] [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [ChartedSpace H R] (I : ModelWithCorners 𝕜 E H)
  (n : ℕ∞ω)

/-- A `C^n` (semi)ring is a topological (semi)ring. This is not an instance for technical reasons,
see note [Design choices about smooth algebraic structures]. -/
theorem topologicalSemiring_of_contMDiffRing [Semiring R] [ContMDiffRing I n R] :
    IsTopologicalSemiring R :=
  { continuousMul_of_contMDiffMul I n, continuousAdd_of_contMDiffAdd I n with }
