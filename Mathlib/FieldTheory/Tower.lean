/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Data.Nat.Prime
import Mathlib.RingTheory.AlgebraTower
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.RingTheory.Ideal.LocalRing

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

open Cardinal Submodule

variable (F : Type u) (K : Type v) (A : Type w)

section Field

variable [DivisionRing F] [DivisionRing K] [AddCommGroup A]
variable [Module F K] [Module K A] [Module F A] [IsScalarTower F K A]

namespace FiniteDimensional

open IsNoetherian

/-- In a tower of field extensions `A / K / F`, if `A / F` is finite, so is `K / F`.

(In fact, it suffices that `A` is a nontrivial ring.)

Note this cannot be an instance as Lean cannot infer `A`.
-/
theorem left [Nontrivial A] [FiniteDimensional F A] : FiniteDimensional F K :=
  let ⟨x, hx⟩ := exists_ne (0 : A)
  FiniteDimensional.of_injective
    (LinearMap.ringLmapEquivSelf K ℕ A |>.symm x |>.restrictScalars F) (smul_left_injective K hx)
#align finite_dimensional.left FiniteDimensional.left

theorem right [hf : FiniteDimensional F A] : FiniteDimensional K A :=
  let ⟨⟨b, hb⟩⟩ := hf
  ⟨⟨b, Submodule.restrictScalars_injective F _ _ <| by
    rw [Submodule.restrictScalars_top, eq_top_iff, ← hb, Submodule.span_le]
    exact Submodule.subset_span⟩⟩
#align finite_dimensional.right FiniteDimensional.right

theorem Subalgebra.isSimpleOrder_of_finrank_prime (F A) [Field F] [Ring A] [IsDomain A]
    [Algebra F A] (hp : (finrank F A).Prime) : IsSimpleOrder (Subalgebra F A) :=
  { toNontrivial :=
      ⟨⟨⊥, ⊤, fun he =>
          Nat.not_prime_one ((Subalgebra.bot_eq_top_iff_finrank_eq_one.1 he).subst hp)⟩⟩
    eq_bot_or_eq_top := fun K => by
      haveI : FiniteDimensional _ _ := .of_finrank_pos hp.pos
      letI := divisionRingOfFiniteDimensional F K
      refine (hp.eq_one_or_self_of_dvd _ ⟨_, (finrank_mul_finrank F K A).symm⟩).imp ?_ fun h => ?_
      · exact fun h' => Subalgebra.eq_bot_of_finrank_one h'
      · exact
          Algebra.toSubmodule_eq_top.1 (eq_top_of_finrank_eq <| K.finrank_toSubmodule.trans h) }
#align finite_dimensional.subalgebra.is_simple_order_of_finrank_prime FiniteDimensional.Subalgebra.isSimpleOrder_of_finrank_prime
-- TODO: `IntermediateField` version

@[deprecated (since := "2024-01-12")]
alias finrank_linear_map' := FiniteDimensional.finrank_linearMap_self
#align finite_dimensional.finrank_linear_map' FiniteDimensional.finrank_linear_map'

end FiniteDimensional

end Field
