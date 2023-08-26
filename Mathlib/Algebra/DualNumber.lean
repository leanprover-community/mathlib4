/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.TrivSqZeroExt

#align_import algebra.dual_number from "leanprover-community/mathlib"@"b8d2eaa69d69ce8f03179a5cda774fc0cde984e4"

/-!
# Dual numbers

The dual numbers over `R` are of the form `a + bε`, where `a` and `b` are typically elements of a
commutative ring `R`, and `ε` is a symbol satisfying `ε^2 = 0`. They are a special case of
`TrivSqZeroExt R M` with `M = R`.

## Notation

In the `DualNumber` locale:

* `R[ε]` is a shorthand for `DualNumber R`
* `ε` is a shorthand for `DualNumber.eps`

## Main definitions

* `DualNumber`
* `DualNumber.eps`
* `DualNumber.lift`

## Implementation notes

Rather than duplicating the API of `TrivSqZeroExt`, this file reuses the functions there.

## References

* https://en.wikipedia.org/wiki/Dual_number
-/


variable {R : Type*}

/-- The type of dual numbers, numbers of the form $a + bε$ where $ε^2 = 0$.-/
abbrev DualNumber (R : Type*) : Type _ :=
  TrivSqZeroExt R R
#align dual_number DualNumber

/-- The unit element $ε$ that squares to zero. -/
def DualNumber.eps [Zero R] [One R] : DualNumber R :=
  TrivSqZeroExt.inr 1
#align dual_number.eps DualNumber.eps

-- mathport name: dual_number.eps
scoped[DualNumber] notation "ε" => DualNumber.eps

-- mathport name: dual_number
scoped[DualNumber] postfix:1024 "[ε]" => DualNumber

open DualNumber

namespace DualNumber

open TrivSqZeroExt

@[simp]
theorem fst_eps [Zero R] [One R] : fst ε = (0 : R) :=
  fst_inr _ _
#align dual_number.fst_eps DualNumber.fst_eps

@[simp]
theorem snd_eps [Zero R] [One R] : snd ε = (1 : R) :=
  snd_inr _ _
#align dual_number.snd_eps DualNumber.snd_eps

/-- A version of `TrivSqZeroExt.snd_mul` with `*` instead of `•`. -/
@[simp]
theorem snd_mul [Semiring R] (x y : R[ε]) : snd (x * y) = fst x * snd y + snd x * fst y :=
  TrivSqZeroExt.snd_mul _ _
#align dual_number.snd_mul DualNumber.snd_mul

@[simp]
theorem eps_mul_eps [Semiring R] : (ε * ε : R[ε]) = 0 :=
  inr_mul_inr _ _ _
#align dual_number.eps_mul_eps DualNumber.eps_mul_eps

@[simp]
theorem inr_eq_smul_eps [MulZeroOneClass R] (r : R) : inr r = (r • ε : R[ε]) :=
  ext (MulZeroClass.mul_zero r).symm (mul_one r).symm
#align dual_number.inr_eq_smul_eps DualNumber.inr_eq_smul_eps

/-- For two algebra morphisms out of `R[ε]` to agree, it suffices for them to agree on `ε`. -/
@[ext]
theorem algHom_ext {A} [CommSemiring R] [Semiring A] [Algebra R A] ⦃f g : R[ε] →ₐ[R] A⦄
    (h : f ε = g ε) : f = g :=
  algHom_ext' <| LinearMap.ext_ring <| h
#align dual_number.alg_hom_ext DualNumber.algHom_ext

variable {A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

/-- A universal property of the dual numbers, providing a unique `R[ε] →ₐ[R] A` for every element
of `A` which squares to `0`.

This isomorphism is named to match the very similar `Complex.lift`. -/
@[simps!]
def lift : { e : A // e * e = 0 } ≃ (R[ε] →ₐ[R] A) :=
  Equiv.trans
    (show { e : A // e * e = 0 } ≃ { f : R →ₗ[R] A // ∀ x y, f x * f y = 0 } from
      (LinearMap.ringLmapEquivSelf R ℕ A).symm.toEquiv.subtypeEquiv fun a => by
        dsimp
        simp_rw [smul_mul_smul]
        refine' ⟨fun h x y => h.symm ▸ smul_zero _, fun h => by simpa using h 1 1⟩)
    TrivSqZeroExt.lift
#align dual_number.lift DualNumber.lift

-- When applied to `ε`, `DualNumber.lift` produces the element of `A` that squares to 0.
-- @[simp] -- Porting note: simp can prove this
theorem lift_apply_eps (e : { e : A // e * e = 0 }) : @lift R _ _ _ _ e (ε : R[ε]) = e := by
  simp only [lift_apply_apply, fst_eps, map_zero, snd_eps, one_smul, zero_add]
#align dual_number.lift_apply_eps DualNumber.lift_apply_eps

-- Lifting `DualNumber.eps` itself gives the identity.
@[simp]
theorem lift_eps : lift ⟨ε, eps_mul_eps⟩ = AlgHom.id R R[ε] :=
  algHom_ext <| lift_apply_eps _
#align dual_number.lift_eps DualNumber.lift_eps

end DualNumber
