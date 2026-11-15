/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm

import Mathlib.Algebra.AlgebraicCard
import Mathlib.Analysis.Normed.Field.Approximation

/-!
# Separability of algebraic extensions of nonarchimedean fields

In this file, we prove that every algebraic normed field extension of a complete separable
nontrivially normed nonarchimedean field is a separable space. In particular, its algebraic closure,
equipped with the spectral norm, is a separable space.

Here separability refers to the topology, as expressed by `TopologicalSpace.SeparableSpace`.

## Main results

- `AlgebraicClosure.instSeparableSpace`: The algebraic closure of a complete separable nontrivially
  normed nonarchimedean field, equipped with the spectral norm, is a separable space.
- `Algebra.IsAlgebraic.separableSpace`: Every algebraic normed field extension of a complete
  separable nontrivially normed nonarchimedean field is a separable space.

## Implementation notes

We equip `AlgebraicClosure L` with the normed field and normed algebra structures induced by the
spectral norm using local instances `spectralNorm.normedField` and `spectralNorm.normedAlgebra`.

The proof first chooses a countable dense subfield `K` of `L`. The elements of `AlgebraicClosure L`
that are algebraic over `K` form a countable dense subset, with density following from polynomial
approximation and continuity of roots. For a general algebraic normed extension `F` of `L`, we
embed `F` into `AlgebraicClosure L`. Uniqueness of the extended norm makes this embedding an
isometry, so separability follows from that of the algebraic closure.

## Tags

normed field, nonarchimedean field, algebraic extension, algebraic closure, separable space,
spectral norm, dense subfield
-/

public section

noncomputable section

open Polynomial TopologicalSpace

variable (L : Type*) [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
  [SeparableSpace L]

/-- The normed field structure on `AlgebraicClosure L` induced by the spectral norm. -/
local instance : NormedField (AlgebraicClosure L) :=
  spectralNorm.normedField L (AlgebraicClosure L)

/-- The normed `L`-algebra structure on `AlgebraicClosure L` induced by the spectral norm. -/
local instance : NormedAlgebra L (AlgebraicClosure L) :=
  spectralNorm.normedAlgebra L (AlgebraicClosure L)

/-- The algebraic closure of a complete separable nontrivially normed nonarchimedean field,
equipped with the spectral norm, is a separable space. -/
instance AlgebraicClosure.instSeparableSpace : SeparableSpace (AlgebraicClosure L) := by
  let E := AlgebraicClosure L
  obtain ⟨K, hK_countable, hK_dense⟩ := exists_countable_dense_subfield L
  -- The elements algebraic over `K` form a countable subset of `E`.
  refine ⟨{z : E | IsAlgebraic K z}, Algebraic.countable K E,
    Metric.dense_iff.mpr <| fun α ε hε ↦ ?_⟩
  -- Approximate the minimal polynomial of `α` by a polynomial over `K` with a root near `α`.
  have hα : IsIntegral L α := Algebra.IsIntegral.isIntegral α
  let f := minpoly L α
  set δ := (ε / max ‖α‖ 1) ^ f.natDegree / (f.natDegree + 1) with hδ_def
  have hδ : 0 < δ := by positivity
  obtain ⟨g, hg_monic, hdegree, hcoeff⟩ :=
    exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt
      hK_dense.denseRange_val (minpoly.monic hα) hδ
  obtain ⟨β, hβ_root, hβ_dist⟩ := exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt
    hδ (minpoly.aeval L α) (minpoly.monic hα) (hg_monic.map _)
    (by simpa using hdegree.symm) hcoeff (IsAlgClosed.splits _)
  refine ⟨β, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_comm, dist_eq_norm]
    rwa [hδ_def, mul_div_cancel₀ _ (by positivity),
      Real.pow_rpow_inv_natCast (by positivity) (minpoly.natDegree_pos hα).ne',
      div_mul_cancel₀ _ (by positivity)] at hβ_dist
  · rw [mem_aroots, aeval_map_algebraMap] at hβ_root
    exact ⟨g, hg_monic.ne_zero, hβ_root.2⟩

/-- Every algebraic normed field extension of a complete separable nontrivially normed
nonarchimedean field is a separable space. -/
theorem Algebra.IsAlgebraic.separableSpace (F : Type*) [NormedField F] [NormedAlgebra L F]
    [Algebra.IsAlgebraic L F] : SeparableSpace F := by
  let E := AlgebraicClosure L
  let e : F →ₐ[L] E := IsAlgClosed.lift
  -- Uniqueness of the extended norm makes the embedding into `E` an isometry.
  have he : Isometry e := AddMonoidHomClass.isometry_of_norm e fun x ↦ by
    rw [NormedAlgebra.norm_eq_spectralNorm L, NormedAlgebra.norm_eq_spectralNorm L,
      spectralNorm, spectralNorm, minpoly.algHom_eq e (e : F →+* E).injective]
  have hsep := he.isEmbedding.isSeparable_preimage
    (IsSeparable.of_separableSpace (Set.univ : Set E))
  simpa [Set.preimage_univ] using isSeparable_univ_iff.mp hsep

end
