/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Data.Nat.Prime
import Mathlib.RingTheory.AlgebraTower
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

#align_import field_theory.tower from "leanprover-community/mathlib"@"c7bce2818663f456335892ddbdd1809f111a5b72"

/-!
# Tower of field extensions

In this file we prove the tower law for arbitrary extensions and finite extensions.
Suppose `L` is a field extension of `K` and `K` is a field extension of `F`.
Then `[L:F] = [L:K] [K:F]` where `[E₁:E₂]` means the `E₂`-dimension of `E₁`.

In fact we generalize it to rings and modules, where `L` is not necessarily a field,
but just a free module over `K`.

## Implementation notes

We prove two versions, since there are two notions of dimensions: `Module.rank` which gives
the dimension of an arbitrary vector space as a cardinal, and `FiniteDimensional.finrank` which
gives the dimension of a finite-dimensional vector space as a natural number.

## Tags

tower law

-/


universe u v w u₁ v₁ w₁

open BigOperators Cardinal Submodule

variable (F : Type u) (K : Type v) (A : Type w)

section Ring

variable [CommRing F] [Ring K] [AddCommGroup A]

variable [Algebra F K] [Module K A] [Module F A] [IsScalarTower F K A]

variable [StrongRankCondition F] [StrongRankCondition K]
  [Module.Free F K] [Module.Free K A]

/-- Tower law: if `A` is a `K`-module and `K` is an extension of `F` then
$\operatorname{rank}_F(A) = \operatorname{rank}_F(K) * \operatorname{rank}_K(A)$. -/
theorem lift_rank_mul_lift_rank :
    Cardinal.lift.{w} (Module.rank F K) * Cardinal.lift.{v} (Module.rank K A) =
      Cardinal.lift.{v} (Module.rank F A) := by
  -- porting note: `Module.Free.exists_basis` now has implicit arguments, but this is annoying
  -- to fix as it is a projection.
  obtain ⟨_, b⟩ := Module.Free.exists_basis (R := F) (M := K)
  -- ⊢ lift.{w, v} (Module.rank F K) * lift.{v, w} (Module.rank K A) = lift.{v, w}  …
  obtain ⟨_, c⟩ := Module.Free.exists_basis (R := K) (M := A)
  -- ⊢ lift.{w, v} (Module.rank F K) * lift.{v, w} (Module.rank K A) = lift.{v, w}  …
  rw [← (Module.rank F K).lift_id, ← b.mk_eq_rank, ← (Module.rank K A).lift_id, ← c.mk_eq_rank, ←
    lift_umax.{w, v}, ← (b.smul c).mk_eq_rank, mk_prod, lift_mul, lift_lift, lift_lift, lift_lift,
    lift_lift, lift_umax.{v, w}]
#align lift_rank_mul_lift_rank lift_rank_mul_lift_rank

/-- Tower law: if `A` is a `K`-module and `K` is an extension of `F` then
$\operatorname{rank}_F(A) = \operatorname{rank}_F(K) * \operatorname{rank}_K(A)$.

This is a simpler version of `lift_rank_mul_lift_rank` with `K` and `A` in the same universe. -/
theorem rank_mul_rank (F : Type u) (K A : Type v) [CommRing F] [Ring K] [AddCommGroup A]
    [Algebra F K] [Module K A] [Module F A] [IsScalarTower F K A] [StrongRankCondition F]
    [StrongRankCondition K] [Module.Free F K] [Module.Free K A] :
    Module.rank F K * Module.rank K A = Module.rank F A := by
  convert lift_rank_mul_lift_rank F K A <;> rw [lift_id]
                                            -- 🎉 no goals
                                            -- 🎉 no goals
                                            -- 🎉 no goals
#align rank_mul_rank rank_mul_rank

/-- Tower law: if `A` is a `K`-module and `K` is an extension of `F` then
$\operatorname{rank}_F(A) = \operatorname{rank}_F(K) * \operatorname{rank}_K(A)$. -/
theorem FiniteDimensional.finrank_mul_finrank' [Module.Finite F K]
    [Module.Finite K A] : finrank F K * finrank K A = finrank F A := by
  letI := nontrivial_of_invariantBasisNumber F
  -- ⊢ finrank F K * finrank K A = finrank F A
  let b := Module.Free.chooseBasis F K
  -- ⊢ finrank F K * finrank K A = finrank F A
  let c := Module.Free.chooseBasis K A
  -- ⊢ finrank F K * finrank K A = finrank F A
  rw [finrank_eq_card_basis b, finrank_eq_card_basis c, finrank_eq_card_basis (b.smul c),
    Fintype.card_prod]
#align finite_dimensional.finrank_mul_finrank' FiniteDimensional.finrank_mul_finrank'

end Ring

section Field

variable [Field F] [DivisionRing K] [AddCommGroup A]

variable [Algebra F K] [Module K A] [Module F A] [IsScalarTower F K A]

namespace FiniteDimensional

open IsNoetherian

theorem trans [FiniteDimensional F K] [FiniteDimensional K A] : FiniteDimensional F A :=
  Module.Finite.trans K A
#align finite_dimensional.trans FiniteDimensional.trans

/-- In a tower of field extensions `L / K / F`, if `L / F` is finite, so is `K / F`.

(In fact, it suffices that `L` is a nontrivial ring.)

Note this cannot be an instance as Lean cannot infer `L`.
-/
theorem left (K L : Type*) [Field K] [Algebra F K] [Ring L] [Nontrivial L] [Algebra F L]
    [Algebra K L] [IsScalarTower F K L] [FiniteDimensional F L] : FiniteDimensional F K :=
  FiniteDimensional.of_injective (IsScalarTower.toAlgHom F K L).toLinearMap (RingHom.injective _)
#align finite_dimensional.left FiniteDimensional.left

theorem right [hf : FiniteDimensional F A] : FiniteDimensional K A :=
  let ⟨⟨b, hb⟩⟩ := hf
  ⟨⟨b, Submodule.restrictScalars_injective F _ _ <| by
    rw [Submodule.restrictScalars_top, eq_top_iff, ← hb, Submodule.span_le]
    -- ⊢ ↑b ⊆ ↑(restrictScalars F (span K ↑b))
    exact Submodule.subset_span⟩⟩
    -- 🎉 no goals
#align finite_dimensional.right FiniteDimensional.right

/-- Tower law: if `A` is a `K`-vector space and `K` is a field extension of `F` then
`dim_F(A) = dim_F(K) * dim_K(A)`.

This is `FiniteDimensional.finrank_mul_finrank'` with one fewer finiteness assumption. -/
theorem finrank_mul_finrank [FiniteDimensional F K] : finrank F K * finrank K A = finrank F A := by
  by_cases hA : FiniteDimensional K A
  -- ⊢ finrank F K * finrank K A = finrank F A
  · replace hA : FiniteDimensional K A := hA -- porting note: broken instance cache
    -- ⊢ finrank F K * finrank K A = finrank F A
    rw [finrank_mul_finrank']
    -- 🎉 no goals
  · rw [finrank_of_infinite_dimensional hA, mul_zero, finrank_of_infinite_dimensional]
    -- ⊢ ¬FiniteDimensional F A
    exact mt (@right F K A _ _ _ _ _ _ _) hA
    -- 🎉 no goals
#align finite_dimensional.finrank_mul_finrank FiniteDimensional.finrank_mul_finrank

theorem Subalgebra.isSimpleOrder_of_finrank_prime (A) [Ring A] [IsDomain A] [Algebra F A]
    (hp : (finrank F A).Prime) : IsSimpleOrder (Subalgebra F A) :=
  { toNontrivial :=
      ⟨⟨⊥, ⊤, fun he =>
          Nat.not_prime_one ((Subalgebra.bot_eq_top_iff_finrank_eq_one.1 he).subst hp)⟩⟩
    eq_bot_or_eq_top := fun K => by
      haveI : FiniteDimensional _ _ := finiteDimensional_of_finrank hp.pos
      -- ⊢ K = ⊥ ∨ K = ⊤
      letI := divisionRingOfFiniteDimensional F K
      -- ⊢ K = ⊥ ∨ K = ⊤
      refine' (hp.eq_one_or_self_of_dvd _ ⟨_, (finrank_mul_finrank F K A).symm⟩).imp _ fun h => _
      -- ⊢ finrank F { x // x ∈ K } = 1 → K = ⊥
      · exact Subalgebra.eq_bot_of_finrank_one
        -- 🎉 no goals
      · exact
          Algebra.toSubmodule_eq_top.1 (eq_top_of_finrank_eq <| K.finrank_toSubmodule.trans h) }
#align finite_dimensional.subalgebra.is_simple_order_of_finrank_prime FiniteDimensional.Subalgebra.isSimpleOrder_of_finrank_prime
-- TODO: `IntermediateField` version

-- TODO: generalize by removing [FiniteDimensional F K]
-- V = ⊕F,
-- (V →ₗ[F] K) = ((⊕F) →ₗ[F] K) = (⊕ (F →ₗ[F] K)) = ⊕K
instance _root_.LinearMap.finite_dimensional'' (F : Type u) (K : Type v) (V : Type w) [Field F]
    [Field K] [Algebra F K] [FiniteDimensional F K] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] : FiniteDimensional K (V →ₗ[F] K) :=
  right F _ _
#align linear_map.finite_dimensional'' LinearMap.finite_dimensional''

theorem finrank_linear_map' (F : Type u) (K : Type v) (V : Type w) [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [AddCommGroup V] [Module F V] [FiniteDimensional F V] :
    finrank K (V →ₗ[F] K) = finrank F V :=
  mul_right_injective₀ finrank_pos.ne' <|
    calc
      finrank F K * finrank K (V →ₗ[F] K) = finrank F (V →ₗ[F] K) := finrank_mul_finrank _ _ _
      _ = finrank F V * finrank F K := (finrank_linearMap F V K)
      _ = finrank F K * finrank F V := mul_comm _ _
#align finite_dimensional.finrank_linear_map' FiniteDimensional.finrank_linear_map'

end FiniteDimensional

end Field
