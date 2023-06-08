/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module ring_theory.witt_vector.teichmuller
! leanprover-community/mathlib commit c0a51cf2de54089d69301befc4c73bbc2f5c7342
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.RingTheory.WittVector.Basic

/-!
# Teichmüller lifts

This file defines `witt_vector.teichmuller`, a monoid hom `R →* 𝕎 R`, which embeds `r : R` as the
`0`-th component of a Witt vector whose other coefficients are `0`.

## Main declarations

- `witt_vector.teichmuller`: the Teichmuller map.
- `witt_vector.map_teichmuller`: `witt_vector.teichmuller` is a natural transformation.
- `witt_vector.ghost_component_teichmuller`:
  the `n`-th ghost component of `witt_vector.teichmuller p r` is `r ^ p ^ n`.

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]
-/


namespace WittVector

open MvPolynomial

variable (p : ℕ) {R S : Type _} [hp : Fact p.Prime] [CommRing R] [CommRing S]

-- mathport name: expr𝕎
local notation "𝕎" => WittVector p

-- type as `\bbW`
/-- The underlying function of the monoid hom `witt_vector.teichmuller`.
The `0`-th coefficient of `teichmuller_fun p r` is `r`, and all others are `0`.
-/
def teichmullerFun (r : R) : 𝕎 R :=
  ⟨p, fun n => if n = 0 then r else 0⟩
#align witt_vector.teichmuller_fun WittVector.teichmullerFun

/-!
## `teichmuller` is a monoid homomorphism

On ghost components, it is clear that `teichmuller_fun` is a monoid homomorphism.
But in general the ghost map is not injective.
We follow the same strategy as for proving that the ring operations on `𝕎 R`
satisfy the ring axioms.

1. We first prove it for rings `R` where `p` is invertible,
   because then the ghost map is in fact an isomorphism.
2. After that, we derive the result for `mv_polynomial R ℤ`,
3. and from that we can prove the result for arbitrary `R`.
-/


include hp

private theorem ghost_component_teichmuller_fun (r : R) (n : ℕ) :
    ghostComponent n (teichmullerFun p r) = r ^ p ^ n := by
  rw [ghost_component_apply, aeval_wittPolynomial, Finset.sum_eq_single 0, pow_zero, one_mul,
    tsub_zero]
  · rfl
  · intro i hi h0
    convert MulZeroClass.mul_zero _; convert zero_pow _
    · cases i; · contradiction; · rfl
    · exact pow_pos hp.1.Pos _
  · rw [Finset.mem_range]; intro h; exact (h (Nat.succ_pos n)).elim

private theorem map_teichmuller_fun (f : R →+* S) (r : R) :
    map f (teichmullerFun p r) = teichmullerFun p (f r) := by ext n; cases n; · rfl;
  · exact f.map_zero

private theorem teichmuller_mul_aux₁ (x y : MvPolynomial R ℚ) :
    teichmullerFun p (x * y) = teichmullerFun p x * teichmullerFun p y := by
  apply (ghost_map.bijective_of_invertible p (MvPolynomial R ℚ)).1
  rw [RingHom.map_mul]
  ext1 n
  simp only [Pi.mul_apply, ghost_map_apply, ghost_component_teichmuller_fun, mul_pow]

private theorem teichmuller_mul_aux₂ (x y : MvPolynomial R ℤ) :
    teichmullerFun p (x * y) = teichmullerFun p x * teichmullerFun p y := by
  refine'
    map_injective (MvPolynomial.map (Int.castRingHom ℚ))
      (MvPolynomial.map_injective _ Int.cast_injective) _
  simp only [teichmuller_mul_aux₁, map_teichmuller_fun, RingHom.map_mul]

/-- The Teichmüller lift of an element of `R` to `𝕎 R`.
The `0`-th coefficient of `teichmuller p r` is `r`, and all others are `0`.
This is a monoid homomorphism. -/
def teichmuller : R →* 𝕎 R where
  toFun := teichmullerFun p
  map_one' := by
    ext ⟨⟩
    · rw [one_coeff_zero]; rfl
    · rw [one_coeff_eq_of_pos _ _ _ (Nat.succ_pos n)]; rfl
  map_mul' := by
    intro x y
    rcases counit_surjective R x with ⟨x, rfl⟩
    rcases counit_surjective R y with ⟨y, rfl⟩
    simp only [← map_teichmuller_fun, ← RingHom.map_mul, teichmuller_mul_aux₂]
#align witt_vector.teichmuller WittVector.teichmuller

@[simp]
theorem teichmuller_coeff_zero (r : R) : (teichmuller p r).coeff 0 = r :=
  rfl
#align witt_vector.teichmuller_coeff_zero WittVector.teichmuller_coeff_zero

@[simp]
theorem teichmuller_coeff_pos (r : R) : ∀ (n : ℕ) (hn : 0 < n), (teichmuller p r).coeff n = 0
  | n + 1, _ => rfl
#align witt_vector.teichmuller_coeff_pos WittVector.teichmuller_coeff_pos

@[simp]
theorem teichmuller_zero : teichmuller p (0 : R) = 0 := by ext ⟨⟩ <;> · rw [zero_coeff]; rfl
#align witt_vector.teichmuller_zero WittVector.teichmuller_zero

/-- `teichmuller` is a natural transformation. -/
@[simp]
theorem map_teichmuller (f : R →+* S) (r : R) : map f (teichmuller p r) = teichmuller p (f r) :=
  map_teichmullerFun _ _ _
#align witt_vector.map_teichmuller WittVector.map_teichmuller

/-- The `n`-th ghost component of `teichmuller p r` is `r ^ p ^ n`. -/
@[simp]
theorem ghostComponent_teichmuller (r : R) (n : ℕ) :
    ghostComponent n (teichmuller p r) = r ^ p ^ n :=
  ghostComponent_teichmullerFun _ _ _
#align witt_vector.ghost_component_teichmuller WittVector.ghostComponent_teichmuller

end WittVector

