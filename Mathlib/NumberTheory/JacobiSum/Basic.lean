/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.NumberTheory.MulChar.Basic
import Mathlib.Algebra.Module.BigOperators

/-!
# Jacobi Sums

This file defines the *Jacobi sum* of two multiplicative characters `χ` and `ψ` on a finite
commutative ring `R` with values in another commutative ring `R'`:

`jacobiSum χ ψ = ∑ x : R, χ x * ψ (1 - x)`

(see `jacobiSum`) and provides some basic results and API lemmas on Jacobi sums.

## References

We essentially follow
* [K. Ireland, M. Rosen, *A classical introduction to modern number theory*
   (Section 8.3)][IrelandRosen1990]

but generalize where appropriate.

This is based on Lean code written as part of the bachelor's thesis of Alexander Spahl.
-/

open BigOperators Finset

/-!
### Jacobi sums: definition and first properties
-/

section Def

namespace Finset

-- Is this useful enough to be non-private?
private lemma sum_eq_sum_one_sub {R M : Type*} [Ring R] [Fintype R] [AddCommMonoid M] (f : R → M) :
    Finset.sum univ f = Finset.sum univ fun x ↦ f (1 - x) := by
  refine Fintype.sum_bijective (1 - ·) (Function.Involutive.bijective ?_) _ _ fun x ↦ ?_
  · simp only [Function.Involutive, sub_sub_cancel, implies_true]
  · simp only [sub_sub_cancel]

end Finset

-- need `Fintype` instead of `Finite` for `Finset.sum` etc.
variable {R R' : Type*} [CommRing R] [Fintype R] [CommRing R']

/- The *Jacobi sum* of two multiplicative characters on a finite commutative ring. -/
def jacobiSum (χ ψ : MulChar R R') : R' :=
  ∑ x : R, χ x * ψ (1 - x)

lemma jacobiSum_comm (χ ψ : MulChar R R') : jacobiSum χ ψ = jacobiSum ψ χ := by
  simp only [jacobiSum]
  convert sum_eq_sum_one_sub fun x ↦ χ x * ψ (1 - x) using 2 with x
  simp only [mul_comm, sub_sub_cancel]

/-- The Jacobi sum is compatible with ring homomorphisms. -/
lemma jacobiSum_ringHomComp {R'' : Type*} [CommRing R''] (χ ψ : MulChar R R') (f : R' →+* R'') :
    jacobiSum (χ.ringHomComp f) (ψ.ringHomComp f) = f (jacobiSum χ ψ) := by
  simp only [jacobiSum, MulChar.ringHomComp, MulChar.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    map_sum, map_mul]

end Def

/-!
### Jacobi sums over finite fields
-/

section FiniteField

variable {F R : Type*} [Field F] [Fintype F] [DecidableEq F] [CommRing R]

/-- The Jacobi sum of two multiplicative characters on a finite field `F` can be written
as a sum over `F \ {0,1}`. -/
lemma jacobiSum_eq_sum_sdiff (χ ψ : MulChar F R) :
    jacobiSum χ ψ = ∑ x ∈ univ \ {0,1}, χ x * ψ (1 - x) := by
  simp only [jacobiSum, subset_univ, sum_sdiff_eq_sub, mem_singleton, zero_ne_one,
    not_false_eq_true, sum_insert, isUnit_iff_ne_zero, ne_eq, not_true_eq_false,
    MulCharClass.map_nonunit, sub_zero, map_one, mul_one, sum_singleton, sub_self, mul_zero,
    add_zero]

private lemma jacobiSum_eq_aux (χ ψ : MulChar F R) :
    jacobiSum χ ψ = ∑ x : F, χ x + ∑ x : F, ψ x - Fintype.card F +
                      ∑ x ∈ univ \ {0, 1}, (χ x - 1) * (ψ (1 - x) - 1) := by
  rw [jacobiSum]
  conv =>
    enter [1, 2, x]
    rw [show ∀ x y : R, x * y = x + y - 1 + (x - 1) * (y - 1) by intros; ring]
  rw [sum_add_distrib, sum_sub_distrib, sum_add_distrib, ← sum_eq_sum_one_sub,
    Fintype.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, sum_sdiff_eq_sub (subset_univ _),
    ← sub_zero (_ - _ + _), add_sub_assoc]
  congr
  rw [sum_pair zero_ne_one, sub_zero, ψ.map_one, χ.map_one, sub_self, mul_zero, zero_mul, add_zero]

/-- If `1` is the trivial multiplicative character on a finite field `F`, then `J(1,1) = #F-2`. -/
theorem jacobiSum_triv_triv : jacobiSum (1 : MulChar F R) 1 = Fintype.card F - 2 := by
  rw [show 1 = MulChar.trivial F R from rfl, jacobiSum_eq_sum_sdiff]
  have : ∀ x ∈ univ \ {0, 1}, (MulChar.trivial F R) x * (MulChar.trivial F R) (1 - x) = 1 := by
    intros x hx
    have hx' : IsUnit (x * (1 - x)) := by
      simp only [mem_sdiff, mem_univ, mem_insert, mem_singleton, not_or, ← ne_eq, true_and] at hx
      simp only [isUnit_iff_ne_zero]
      exact mul_ne_zero hx.1 <| sub_ne_zero.mpr hx.2.symm
    rw [← map_mul, MulChar.trivial_apply, if_pos hx']
  calc ∑ x ∈ univ \ {0, 1}, (MulChar.trivial F R) x * (MulChar.trivial F R) (1 - x)
  _ = ∑ _ ∈ @univ F _ \ {0, 1}, (1 : R) := sum_congr rfl this
  _ = Finset.card (@univ F _ \ {0, 1}) := (cast_card _).symm
  _ = Fintype.card F - 2 := by
    rw [card_sdiff (subset_univ _), card_univ, card_pair zero_ne_one]
    obtain ⟨m, hm⟩ : ∃ m : ℕ, Fintype.card F = 1 + m + 1 :=
      Nat.exists_eq_add_of_lt Fintype.one_lt_card
    rw [show 1 + m + 1 = m + 2 by ring] at hm
    simp only [hm, add_tsub_cancel_right (α := ℕ), Nat.cast_add, Nat.cast_ofNat,
      add_sub_cancel_right]

end FiniteField
