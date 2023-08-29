/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.RingTheory.WittVector.Basic

#align_import ring_theory.witt_vector.teichmuller from "leanprover-community/mathlib"@"c0a51cf2de54089d69301befc4c73bbc2f5c7342"

/-!
# Teichmüller lifts

This file defines `WittVector.teichmuller`, a monoid hom `R →* 𝕎 R`, which embeds `r : R` as the
`0`-th component of a Witt vector whose other coefficients are `0`.

## Main declarations

- `WittVector.teichmuller`: the Teichmuller map.
- `WittVector.map_teichmuller`: `WittVector.teichmuller` is a natural transformation.
- `WittVector.ghostComponent_teichmuller`:
  the `n`-th ghost component of `WittVector.teichmuller p r` is `r ^ p ^ n`.

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]
-/


namespace WittVector

open MvPolynomial

variable (p : ℕ) {R S : Type*} [hp : Fact p.Prime] [CommRing R] [CommRing S]

local notation "𝕎" => WittVector p -- type as `\bbW`

/-- The underlying function of the monoid hom `WittVector.teichmuller`.
The `0`-th coefficient of `teichmullerFun p r` is `r`, and all others are `0`.
-/
def teichmullerFun (r : R) : 𝕎 R :=
  ⟨fun n => if n = 0 then r else 0⟩
#align witt_vector.teichmuller_fun WittVector.teichmullerFun

/-!
## `teichmuller` is a monoid homomorphism

On ghost components, it is clear that `teichmullerFun` is a monoid homomorphism.
But in general the ghost map is not injective.
We follow the same strategy as for proving that the ring operations on `𝕎 R`
satisfy the ring axioms.

1. We first prove it for rings `R` where `p` is invertible,
   because then the ghost map is in fact an isomorphism.
2. After that, we derive the result for `MvPolynomial R ℤ`,
3. and from that we can prove the result for arbitrary `R`.
-/


private theorem ghostComponent_teichmullerFun (r : R) (n : ℕ) :
    ghostComponent n (teichmullerFun p r) = r ^ p ^ n := by
  rw [ghostComponent_apply, aeval_wittPolynomial, Finset.sum_eq_single 0, pow_zero, one_mul,
    tsub_zero]
  · rfl
    -- 🎉 no goals
  · intro i hi h0
    -- ⊢ ↑p ^ i * coeff (teichmullerFun p r) i ^ p ^ (n - i) = 0
    convert mul_zero (M₀ := R) _
    -- ⊢ coeff (teichmullerFun p r) i ^ p ^ (n - i) = 0
    convert zero_pow (M := R) _
    -- ⊢ coeff (teichmullerFun p r) i = 0
    · cases i
      -- ⊢ coeff (teichmullerFun p r) Nat.zero = 0
      · contradiction
        -- 🎉 no goals
      · rfl
        -- 🎉 no goals
    · exact pow_pos hp.1.pos _
      -- 🎉 no goals
  · rw [Finset.mem_range]; intro h; exact (h (Nat.succ_pos n)).elim
    -- ⊢ ¬0 < n + 1 → ↑p ^ 0 * coeff (teichmullerFun p r) 0 ^ p ^ (n - 0) = 0
                           -- ⊢ ↑p ^ 0 * coeff (teichmullerFun p r) 0 ^ p ^ (n - 0) = 0
                                    -- 🎉 no goals

private theorem map_teichmullerFun (f : R →+* S) (r : R) :
    map f (teichmullerFun p r) = teichmullerFun p (f r) := by
  ext n; cases n
  -- ⊢ coeff (↑(map f) (teichmullerFun p r)) n = coeff (teichmullerFun p (↑f r)) n
         -- ⊢ coeff (↑(map f) (teichmullerFun p r)) Nat.zero = coeff (teichmullerFun p (↑f …
  · rfl
    -- 🎉 no goals
  · exact f.map_zero
    -- 🎉 no goals

private theorem teichmuller_mul_aux₁ (x y : MvPolynomial R ℚ) :
    teichmullerFun p (x * y) = teichmullerFun p x * teichmullerFun p y := by
  apply (ghostMap.bijective_of_invertible p (MvPolynomial R ℚ)).1
  -- ⊢ ↑ghostMap (teichmullerFun p (x * y)) = ↑ghostMap (teichmullerFun p x * teich …
  rw [RingHom.map_mul]
  -- ⊢ ↑ghostMap (teichmullerFun p (x * y)) = ↑ghostMap (teichmullerFun p x) * ↑gho …
  ext1 n
  -- ⊢ ↑ghostMap (teichmullerFun p (x * y)) n = (↑ghostMap (teichmullerFun p x) * ↑ …
  simp only [Pi.mul_apply, ghostMap_apply, ghostComponent_teichmullerFun, mul_pow]
  -- 🎉 no goals

private theorem teichmuller_mul_aux₂ (x y : MvPolynomial R ℤ) :
    teichmullerFun p (x * y) = teichmullerFun p x * teichmullerFun p y := by
  refine' map_injective (MvPolynomial.map (Int.castRingHom ℚ))
    (MvPolynomial.map_injective _ Int.cast_injective) _
  simp only [teichmuller_mul_aux₁, map_teichmullerFun, RingHom.map_mul]
  -- 🎉 no goals

/-- The Teichmüller lift of an element of `R` to `𝕎 R`.
The `0`-th coefficient of `teichmuller p r` is `r`, and all others are `0`.
This is a monoid homomorphism. -/
def teichmuller : R →* 𝕎 R where
  toFun := teichmullerFun p
  map_one' := by
    ext ⟨⟩
    -- ⊢ coeff (teichmullerFun p 1) Nat.zero = coeff 1 Nat.zero
    · rw [one_coeff_zero]; rfl
      -- ⊢ coeff (teichmullerFun p 1) Nat.zero = 1
                           -- 🎉 no goals
    · rw [one_coeff_eq_of_pos _ _ _ (Nat.succ_pos _)]; rfl
      -- ⊢ coeff (teichmullerFun p 1) (Nat.succ n✝) = 0
                                                       -- 🎉 no goals
  map_mul' := by
    intro x y
    -- ⊢ OneHom.toFun { toFun := teichmullerFun p, map_one' := (_ : teichmullerFun p  …
    rcases counit_surjective R x with ⟨x, rfl⟩
    -- ⊢ OneHom.toFun { toFun := teichmullerFun p, map_one' := (_ : teichmullerFun p  …
    rcases counit_surjective R y with ⟨y, rfl⟩
    -- ⊢ OneHom.toFun { toFun := teichmullerFun p, map_one' := (_ : teichmullerFun p  …
    simp only [← map_teichmullerFun, ← RingHom.map_mul, teichmuller_mul_aux₂]
    -- 🎉 no goals
#align witt_vector.teichmuller WittVector.teichmuller

@[simp]
theorem teichmuller_coeff_zero (r : R) : (teichmuller p r).coeff 0 = r :=
  rfl
#align witt_vector.teichmuller_coeff_zero WittVector.teichmuller_coeff_zero

@[simp]
theorem teichmuller_coeff_pos (r : R) : ∀ (n : ℕ) (_ : 0 < n), (teichmuller p r).coeff n = 0
  | _ + 1, _ => rfl
#align witt_vector.teichmuller_coeff_pos WittVector.teichmuller_coeff_pos

@[simp]
theorem teichmuller_zero : teichmuller p (0 : R) = 0 := by
  ext ⟨⟩ <;> · rw [zero_coeff]; rfl
  -- ⊢ coeff (↑(teichmuller p) 0) Nat.zero = coeff 0 Nat.zero
               -- ⊢ coeff (↑(teichmuller p) 0) Nat.zero = 0
                                -- 🎉 no goals
               -- ⊢ coeff (↑(teichmuller p) 0) (Nat.succ n✝) = 0
                                -- 🎉 no goals
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
