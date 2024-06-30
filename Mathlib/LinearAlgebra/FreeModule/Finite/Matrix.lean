/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import Mathlib.LinearAlgebra.Dimension.LinearMap
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

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


universe u u' v w

variable (R : Type u) (S : Type u') (M : Type v) (N : Type w)

open Module.Free (chooseBasis ChooseBasisIndex)

open FiniteDimensional (finrank)

section Ring

variable [Ring R] [Ring S] [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
variable [AddCommGroup N] [Module R N] [Module S N] [SMulCommClass R S N]

private noncomputable def linearMapEquivFun : (M →ₗ[R] N) ≃ₗ[S] ChooseBasisIndex R M → N :=
  (chooseBasis R M).repr.congrLeft N S ≪≫ₗ (Finsupp.lsum S).symm ≪≫ₗ
    LinearEquiv.piCongrRight fun _ ↦ LinearMap.ringLmapEquivSelf R S N

instance Module.Free.linearMap [Module.Free S N] : Module.Free S (M →ₗ[R] N) :=
  Module.Free.of_equiv (linearMapEquivFun R S M N).symm
#align module.free.linear_map Module.Free.linearMap

instance Module.Finite.linearMap [Module.Finite S N] : Module.Finite S (M →ₗ[R] N) :=
  Module.Finite.equiv (linearMapEquivFun R S M N).symm
#align module.finite.linear_map Module.Finite.linearMap

variable [StrongRankCondition R] [StrongRankCondition S] [Module.Free S N]

open Cardinal
theorem FiniteDimensional.rank_linearMap :
    Module.rank S (M →ₗ[R] N) = lift.{w} (Module.rank R M) * lift.{v} (Module.rank S N) := by
  rw [(linearMapEquivFun R S M N).rank_eq, rank_fun_eq_lift_mul,
    ← finrank_eq_card_chooseBasisIndex, ← finrank_eq_rank R, lift_natCast]

/-- The finrank of `M →ₗ[R] N` as an `S`-module is `(finrank R M) * (finrank S N)`. -/
theorem FiniteDimensional.finrank_linearMap :
    finrank S (M →ₗ[R] N) = finrank R M * finrank S N := by
  simp_rw [finrank, rank_linearMap, toNat_mul, toNat_lift]
#align finite_dimensional.finrank_linear_map FiniteDimensional.finrank_linearMap

variable [Module R S] [SMulCommClass R S S]

theorem FiniteDimensional.rank_linearMap_self :
    Module.rank S (M →ₗ[R] S) = lift.{u'} (Module.rank R M) := by
  rw [rank_linearMap, rank_self, lift_one, mul_one]

theorem FiniteDimensional.finrank_linearMap_self : finrank S (M →ₗ[R] S) = finrank R M := by
  rw [finrank_linearMap, finrank_self, mul_one]

end Ring

section AlgHom

variable (K M : Type*) (L : Type v) [CommRing K] [Ring M] [Algebra K M]
  [Module.Free K M] [Module.Finite K M] [CommRing L] [IsDomain L] [Algebra K L]

instance Finite.algHom : Finite (M →ₐ[K] L) :=
  (linearIndependent_algHom_toLinearMap K M L).finite

open Cardinal

theorem cardinal_mk_algHom_le_rank : #(M →ₐ[K] L) ≤ lift.{v} (Module.rank K M) := by
  convert (linearIndependent_algHom_toLinearMap K M L).cardinal_lift_le_rank
  · rw [lift_id]
  · have := Module.nontrivial K L
    rw [lift_id, FiniteDimensional.rank_linearMap_self]

theorem card_algHom_le_finrank : Nat.card (M →ₐ[K] L) ≤ finrank K M := by
  convert toNat_le_toNat (cardinal_mk_algHom_le_rank K M L) ?_
  · rw [toNat_lift, finrank]
  · rw [lift_lt_aleph0]; have := Module.nontrivial K L; apply rank_lt_aleph0

end AlgHom

section Integer

variable [AddCommGroup M] [Module.Finite ℤ M] [Module.Free ℤ M] [AddCommGroup N]

instance Module.Finite.addMonoidHom [Module.Finite ℤ N] : Module.Finite ℤ (M →+ N) :=
  Module.Finite.equiv (addMonoidHomLequivInt ℤ).symm
#align module.finite.add_monoid_hom Module.Finite.addMonoidHom

instance Module.Free.addMonoidHom [Module.Free ℤ N] : Module.Free ℤ (M →+ N) :=
  letI : Module.Free ℤ (M →ₗ[ℤ] N) := Module.Free.linearMap _ _ _ _
  Module.Free.of_equiv (addMonoidHomLequivInt ℤ).symm
#align module.free.add_monoid_hom Module.Free.addMonoidHom

end Integer

theorem Matrix.rank_vecMulVec {K m n : Type u} [CommRing K] [Fintype n]
    [DecidableEq n] (w : m → K) (v : n → K) : (Matrix.vecMulVec w v).toLin'.rank ≤ 1 := by
  nontriviality K
  rw [Matrix.vecMulVec_eq (Fin 1), Matrix.toLin'_mul]
  refine le_trans (LinearMap.rank_comp_le_left _ _) ?_
  refine (LinearMap.rank_le_domain _).trans_eq ?_
  rw [rank_fun', Fintype.card_ofSubsingleton, Nat.cast_one]
#align matrix.rank_vec_mul_vec Matrix.rank_vecMulVec
