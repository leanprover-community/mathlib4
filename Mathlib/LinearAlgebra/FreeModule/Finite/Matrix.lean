/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import Mathlib.LinearAlgebra.Finrank
import Mathlib.LinearAlgebra.FreeModule.Finite.Rank
import Mathlib.LinearAlgebra.Matrix.ToLin

#align_import linear_algebra.free_module.finite.matrix from "leanprover-community/mathlib"@"b1c23399f01266afe392a0d8f71f599a0dad4f7b"

/-!
# Finite and free modules using matrices

We provide some instances for finite and free modules involving matrices.

## Main results

* `Module.Free.linearMap` : if `M` and `N` are finite and free, then `M →ₗ[R] N` is free.
* `Module.Finite.ofBasis` : A free module with a basis indexed by a `Fintype` is finite.
* `Module.Finite.linearMap` : if `M` and `N` are finite and free, then `M →ₗ[R] N`
  is finite.
-/


universe u v w

variable (R : Type u) (M : Type v) (N : Type w)

open Module.Free (chooseBasis)

open FiniteDimensional (finrank)

section CommRing

variable [CommRing R] [AddCommGroup M] [Module R M] [Module.Free R M]

variable [AddCommGroup N] [Module R N] [Module.Free R N]

instance Module.Free.linearMap [Module.Finite R M] [Module.Finite R N] :
    Module.Free R (M →ₗ[R] N) := by
  cases subsingleton_or_nontrivial R
  -- ⊢ Free R (M →ₗ[R] N)
  · apply Module.Free.of_subsingleton'
    -- 🎉 no goals
  classical exact
      Module.Free.of_equiv (LinearMap.toMatrix (chooseBasis R M) (chooseBasis R N)).symm
#align module.free.linear_map Module.Free.linearMap

variable {R}

instance Module.Finite.linearMap [Module.Finite R M] [Module.Finite R N] :
    Module.Finite R (M →ₗ[R] N) := by
  cases subsingleton_or_nontrivial R
  -- ⊢ Finite R (M →ₗ[R] N)
  · infer_instance
    -- 🎉 no goals
  classical
    have f := (LinearMap.toMatrix (chooseBasis R M) (chooseBasis R N)).symm
    exact Module.Finite.of_surjective f.toLinearMap (LinearEquiv.surjective f)
#align module.finite.linear_map Module.Finite.linearMap

end CommRing

section Integer

variable [AddCommGroup M] [Module.Finite ℤ M] [Module.Free ℤ M]

variable [AddCommGroup N] [Module.Finite ℤ N] [Module.Free ℤ N]

instance Module.Finite.addMonoidHom : Module.Finite ℤ (M →+ N) :=
  Module.Finite.equiv (addMonoidHomLequivInt ℤ).symm
#align module.finite.add_monoid_hom Module.Finite.addMonoidHom

instance Module.Free.addMonoidHom : Module.Free ℤ (M →+ N) :=
  letI : Module.Free ℤ (M →ₗ[ℤ] N) := Module.Free.linearMap _ _ _
  Module.Free.of_equiv (addMonoidHomLequivInt ℤ).symm
#align module.free.add_monoid_hom Module.Free.addMonoidHom

end Integer

section CommRing

variable [CommRing R] [StrongRankCondition R]

variable [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]

variable [AddCommGroup N] [Module R N] [Module.Free R N] [Module.Finite R N]

/-- The finrank of `M →ₗ[R] N` is `(finrank R M) * (finrank R N)`. -/
theorem FiniteDimensional.finrank_linearMap :
    finrank R (M →ₗ[R] N) = finrank R M * finrank R N := by
  classical
    letI := nontrivial_of_invariantBasisNumber R
    have h := LinearMap.toMatrix (chooseBasis R M) (chooseBasis R N)
    simp_rw [h.finrank_eq, FiniteDimensional.finrank_matrix,
      FiniteDimensional.finrank_eq_card_chooseBasisIndex, mul_comm]
#align finite_dimensional.finrank_linear_map FiniteDimensional.finrank_linearMap

end CommRing

theorem Matrix.rank_vecMulVec {K m n : Type u} [CommRing K] [StrongRankCondition K] [Fintype n]
    [DecidableEq n] (w : m → K) (v : n → K) : (Matrix.vecMulVec w v).toLin'.rank ≤ 1 := by
  rw [Matrix.vecMulVec_eq, Matrix.toLin'_mul]
  -- ⊢ LinearMap.rank (LinearMap.comp (↑toLin' (col w)) (↑toLin' (row v))) ≤ 1
  refine' le_trans (LinearMap.rank_comp_le_left _ _) _
  -- ⊢ LinearMap.rank (↑toLin' (col w)) ≤ 1
  refine' (LinearMap.rank_le_domain _).trans_eq _
  -- ⊢ Module.rank K (Unit → K) = 1
  rw [rank_fun', Fintype.card_unit, Nat.cast_one]
  -- 🎉 no goals
#align matrix.rank_vec_mul_vec Matrix.rank_vecMulVec
