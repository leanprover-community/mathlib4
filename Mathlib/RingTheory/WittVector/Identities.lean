/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.RingTheory.WittVector.Frobenius
import Mathlib.RingTheory.WittVector.Verschiebung
import Mathlib.RingTheory.WittVector.MulP

#align_import ring_theory.witt_vector.identities from "leanprover-community/mathlib"@"0798037604b2d91748f9b43925fb7570a5f3256c"

/-!
## Identities between operations on the ring of Witt vectors

In this file we derive common identities between the Frobenius and Verschiebung operators.

## Main declarations

* `frobenius_verschiebung`: the composition of Frobenius and Verschiebung is multiplication by `p`
* `verschiebung_mul_frobenius`: the “projection formula”: `V(x * F y) = V x * y`
* `iterate_verschiebung_mul_coeff`: an identity from [Haze09] 6.2

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]
-/


namespace WittVector

variable {p : ℕ} {R : Type*} [hp : Fact p.Prime] [CommRing R]

-- type as `\bbW`
local notation "𝕎" => WittVector p

noncomputable section

-- Porting note: `ghost_calc` failure: `simp only []` and the manual instances had to be added.
/-- The composition of Frobenius and Verschiebung is multiplication by `p`. -/
theorem frobenius_verschiebung (x : 𝕎 R) : frobenius (verschiebung x) = x * p := by
  simp only []
  -- ⊢ ↑frobenius (↑verschiebung x) = x * ↑p
  have : IsPoly p fun {R} [CommRing R] x ↦ frobenius (verschiebung x) :=
    IsPoly.comp (hg := frobenius_isPoly p) (hf := verschiebung_isPoly)
  have : IsPoly p fun {R} [CommRing R] x ↦ x * p := mulN_isPoly p p
  -- ⊢ ↑frobenius (↑verschiebung x) = x * ↑p
  ghost_calc x
  -- ⊢ ∀ (n : ℕ), ↑(ghostComponent n) (↑frobenius (↑verschiebung x)) = ↑(ghostCompo …
  ghost_simp [mul_comm]
  -- 🎉 no goals
#align witt_vector.frobenius_verschiebung WittVector.frobenius_verschiebung

/-- Verschiebung is the same as multiplication by `p` on the ring of Witt vectors of `ZMod p`. -/
theorem verschiebung_zmod (x : 𝕎 (ZMod p)) : verschiebung x = x * p := by
  rw [← frobenius_verschiebung, frobenius_zmodp]
  -- 🎉 no goals
#align witt_vector.verschiebung_zmod WittVector.verschiebung_zmod

variable (p R)

theorem coeff_p_pow [CharP R p] (i : ℕ) : ((p : 𝕎 R) ^ i).coeff i = 1 := by
  induction' i with i h
  -- ⊢ coeff (↑p ^ Nat.zero) Nat.zero = 1
  · simp only [Nat.zero_eq, one_coeff_zero, Ne.def, pow_zero]
    -- 🎉 no goals
  · rw [pow_succ', ← frobenius_verschiebung, coeff_frobenius_charP,
      verschiebung_coeff_succ, h, one_pow]
#align witt_vector.coeff_p_pow WittVector.coeff_p_pow

theorem coeff_p_pow_eq_zero [CharP R p] {i j : ℕ} (hj : j ≠ i) : ((p : 𝕎 R) ^ i).coeff j = 0 := by
  induction' i with i hi generalizing j
  -- ⊢ coeff (↑p ^ Nat.zero) j = 0
  · rw [Nat.zero_eq, pow_zero, one_coeff_eq_of_pos]
    -- ⊢ 0 < j
    exact Nat.pos_of_ne_zero hj
    -- 🎉 no goals
  · rw [pow_succ', ← frobenius_verschiebung, coeff_frobenius_charP]
    -- ⊢ coeff (↑verschiebung (↑p ^ i)) j ^ p = 0
    cases j
    -- ⊢ coeff (↑verschiebung (↑p ^ i)) Nat.zero ^ p = 0
    · rw [verschiebung_coeff_zero, zero_pow]
      -- ⊢ 0 < p
      exact Nat.Prime.pos hp.out
      -- 🎉 no goals
    · rw [verschiebung_coeff_succ, hi, zero_pow]
      -- ⊢ 0 < p
      · exact Nat.Prime.pos hp.out
        -- 🎉 no goals
      · exact ne_of_apply_ne (fun j : ℕ => j.succ) hj
        -- 🎉 no goals
#align witt_vector.coeff_p_pow_eq_zero WittVector.coeff_p_pow_eq_zero

theorem coeff_p [CharP R p] (i : ℕ) : (p : 𝕎 R).coeff i = if i = 1 then 1 else 0 := by
  split_ifs with hi
  -- ⊢ coeff (↑p) i = 1
  · simpa only [hi, pow_one] using coeff_p_pow p R 1
    -- 🎉 no goals
  · simpa only [pow_one] using coeff_p_pow_eq_zero p R hi
    -- 🎉 no goals
#align witt_vector.coeff_p WittVector.coeff_p

@[simp]
theorem coeff_p_zero [CharP R p] : (p : 𝕎 R).coeff 0 = 0 := by
  rw [coeff_p, if_neg]
  -- ⊢ ¬0 = 1
  exact zero_ne_one
  -- 🎉 no goals
#align witt_vector.coeff_p_zero WittVector.coeff_p_zero

@[simp]
theorem coeff_p_one [CharP R p] : (p : 𝕎 R).coeff 1 = 1 := by rw [coeff_p, if_pos rfl]
                                                              -- 🎉 no goals
#align witt_vector.coeff_p_one WittVector.coeff_p_one

theorem p_nonzero [Nontrivial R] [CharP R p] : (p : 𝕎 R) ≠ 0 := by
  intro h
  -- ⊢ False
  simpa only [h, zero_coeff, zero_ne_one] using coeff_p_one p R
  -- 🎉 no goals
#align witt_vector.p_nonzero WittVector.p_nonzero

theorem FractionRing.p_nonzero [Nontrivial R] [CharP R p] : (p : FractionRing (𝕎 R)) ≠ 0 := by
  simpa using (IsFractionRing.injective (𝕎 R) (FractionRing (𝕎 R))).ne (WittVector.p_nonzero _ _)
  -- 🎉 no goals
#align witt_vector.fraction_ring.p_nonzero WittVector.FractionRing.p_nonzero

variable {p R}

-- Porting note: `ghost_calc` failure: `simp only []` and the manual instances had to be added.
/-- The “projection formula” for Frobenius and Verschiebung. -/
theorem verschiebung_mul_frobenius (x y : 𝕎 R) :
    verschiebung (x * frobenius y) = verschiebung x * y := by
  simp only []
  -- ⊢ ↑verschiebung (x * ↑frobenius y) = ↑verschiebung x * y
  have : IsPoly₂ p fun {R} [Rcr : CommRing R] x y ↦ verschiebung (x * frobenius y) :=
    IsPoly.comp₂ (hg := verschiebung_isPoly)
      (hf := IsPoly₂.comp (hh := mulIsPoly₂) (hf := idIsPolyI' p) (hg := frobenius_isPoly p))
  have : IsPoly₂ p fun {R} [CommRing R] x y ↦ verschiebung x * y :=
    IsPoly₂.comp (hh := mulIsPoly₂) (hf := verschiebung_isPoly) (hg := idIsPolyI' p)
  ghost_calc x y
  -- ⊢ ∀ (n : ℕ), ↑(ghostComponent n) (↑verschiebung (x * ↑frobenius y)) = ↑(ghostC …
  rintro ⟨⟩ <;> ghost_simp [mul_assoc]
  -- ⊢ ↑(ghostComponent Nat.zero) (↑verschiebung (x * ↑frobenius y)) = ↑(ghostCompo …
                -- 🎉 no goals
                -- 🎉 no goals
#align witt_vector.verschiebung_mul_frobenius WittVector.verschiebung_mul_frobenius

theorem mul_charP_coeff_zero [CharP R p] (x : 𝕎 R) : (x * p).coeff 0 = 0 := by
  rw [← frobenius_verschiebung, coeff_frobenius_charP, verschiebung_coeff_zero, zero_pow]
  -- ⊢ 0 < p
  exact Nat.Prime.pos hp.out
  -- 🎉 no goals
#align witt_vector.mul_char_p_coeff_zero WittVector.mul_charP_coeff_zero

theorem mul_charP_coeff_succ [CharP R p] (x : 𝕎 R) (i : ℕ) :
    (x * p).coeff (i + 1) = x.coeff i ^ p := by
  rw [← frobenius_verschiebung, coeff_frobenius_charP, verschiebung_coeff_succ]
  -- 🎉 no goals
#align witt_vector.mul_char_p_coeff_succ WittVector.mul_charP_coeff_succ

theorem verschiebung_frobenius [CharP R p] (x : 𝕎 R) : verschiebung (frobenius x) = x * p := by
  ext ⟨i⟩
  -- ⊢ coeff (↑verschiebung (↑frobenius x)) Nat.zero = coeff (x * ↑p) Nat.zero
  · rw [mul_charP_coeff_zero, verschiebung_coeff_zero]
    -- 🎉 no goals
  · rw [mul_charP_coeff_succ, verschiebung_coeff_succ, coeff_frobenius_charP]
    -- 🎉 no goals
#align witt_vector.verschiebung_frobenius WittVector.verschiebung_frobenius

theorem verschiebung_frobenius_comm [CharP R p] :
    Function.Commute (verschiebung : 𝕎 R → 𝕎 R) frobenius := fun x => by
  rw [verschiebung_frobenius, frobenius_verschiebung]
  -- 🎉 no goals
#align witt_vector.verschiebung_frobenius_comm WittVector.verschiebung_frobenius_comm

/-!
## Iteration lemmas
-/


open Function

theorem iterate_verschiebung_coeff (x : 𝕎 R) (n k : ℕ) :
    (verschiebung^[n] x).coeff (k + n) = x.coeff k := by
  induction' n with k ih
  -- ⊢ coeff ((↑verschiebung)^[Nat.zero] x) (k + Nat.zero) = coeff x k
  · simp
    -- 🎉 no goals
  · rw [iterate_succ_apply', Nat.add_succ, verschiebung_coeff_succ]
    -- ⊢ coeff ((↑verschiebung)^[k] x) (k✝ + k) = coeff x k✝
    exact ih
    -- 🎉 no goals
#align witt_vector.iterate_verschiebung_coeff WittVector.iterate_verschiebung_coeff

theorem iterate_verschiebung_mul_left (x y : 𝕎 R) (i : ℕ) :
    verschiebung^[i] x * y = verschiebung^[i] (x * frobenius^[i] y) := by
  induction' i with i ih generalizing y
  -- ⊢ (↑verschiebung)^[Nat.zero] x * y = (↑verschiebung)^[Nat.zero] (x * (↑frobeni …
  · simp
    -- 🎉 no goals
  · rw [iterate_succ_apply', ← verschiebung_mul_frobenius, ih, iterate_succ_apply']; rfl
    -- ⊢ ↑verschiebung ((↑verschiebung)^[i] (x * (↑frobenius)^[i] (↑frobenius y))) =  …
                                                                                     -- 🎉 no goals
#align witt_vector.iterate_verschiebung_mul_left WittVector.iterate_verschiebung_mul_left

section CharP

variable [CharP R p]

theorem iterate_verschiebung_mul (x y : 𝕎 R) (i j : ℕ) :
    verschiebung^[i] x * verschiebung^[j] y =
      verschiebung^[i + j] (frobenius^[j] x * frobenius^[i] y) := by
  calc
    _ = verschiebung^[i] (x * frobenius^[i] (verschiebung^[j] y)) := ?_
    _ = verschiebung^[i] (x * verschiebung^[j] (frobenius^[i] y)) := ?_
    _ = verschiebung^[i] (verschiebung^[j] (frobenius^[i] y) * x) := ?_
    _ = verschiebung^[i] (verschiebung^[j] (frobenius^[i] y * frobenius^[j] x)) := ?_
    _ = verschiebung^[i + j] (frobenius^[i] y * frobenius^[j] x) := ?_
    _ = _ := ?_
  · apply iterate_verschiebung_mul_left
    -- 🎉 no goals
  · rw [verschiebung_frobenius_comm.iterate_iterate]
    -- 🎉 no goals
  · rw [mul_comm]
    -- 🎉 no goals
  · rw [iterate_verschiebung_mul_left]
    -- 🎉 no goals
  · rw [iterate_add_apply]
    -- 🎉 no goals
  · rw [mul_comm]
    -- 🎉 no goals
#align witt_vector.iterate_verschiebung_mul WittVector.iterate_verschiebung_mul

-- Porting note: `ring_nf` doesn't handle powers yet; needed to add `Nat.pow_succ` rewrite
theorem iterate_frobenius_coeff (x : 𝕎 R) (i k : ℕ) :
    (frobenius^[i] x).coeff k = x.coeff k ^ p ^ i := by
  induction' i with i ih
  -- ⊢ coeff ((↑frobenius)^[Nat.zero] x) k = coeff x k ^ p ^ Nat.zero
  · simp
    -- 🎉 no goals
  · rw [iterate_succ_apply', coeff_frobenius_charP, ih, Nat.pow_succ]
    -- ⊢ (coeff x k ^ p ^ i) ^ p = coeff x k ^ (p ^ i * p)
    ring_nf
    -- 🎉 no goals
#align witt_vector.iterate_frobenius_coeff WittVector.iterate_frobenius_coeff

/-- This is a slightly specialized form of [Hazewinkel, *Witt Vectors*][Haze09] 6.2 equation 5. -/
theorem iterate_verschiebung_mul_coeff (x y : 𝕎 R) (i j : ℕ) :
    (verschiebung^[i] x * verschiebung^[j] y).coeff (i + j) =
      x.coeff 0 ^ p ^ j * y.coeff 0 ^ p ^ i := by
  calc
    _ = (verschiebung^[i + j] (frobenius^[j] x * frobenius^[i] y)).coeff (i + j) := ?_
    _ = (frobenius^[j] x * frobenius^[i] y).coeff 0 := ?_
    _ = (frobenius^[j] x).coeff 0 * (frobenius^[i] y).coeff 0 := ?_
    _ = _ := ?_
  · rw [iterate_verschiebung_mul]
    -- 🎉 no goals
  · convert iterate_verschiebung_coeff (p := p) (R := R) _ _ _ using 2
    -- ⊢ i + j = 0 + (i + j)
    rw [zero_add]
    -- 🎉 no goals
  · apply mul_coeff_zero
    -- 🎉 no goals
  · simp only [iterate_frobenius_coeff]
    -- 🎉 no goals
#align witt_vector.iterate_verschiebung_mul_coeff WittVector.iterate_verschiebung_mul_coeff

end CharP

end

end WittVector
