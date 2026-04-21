/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.RingTheory.WittVector.Frobenius
public import Mathlib.RingTheory.WittVector.Verschiebung
public import Mathlib.RingTheory.WittVector.MulP

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
set_option backward.defeqAttrib.useBackward true

public section


namespace WittVector

variable {p : ℕ} {R : Type*} [hp : Fact p.Prime] [CommRing R]

-- type as `\bbW`
local notation "𝕎" => WittVector p

noncomputable section

-- Porting note: `ghost_calc` failure: the manual instances had to be added.
/-- The composition of Frobenius and Verschiebung is multiplication by `p`. -/
theorem frobenius_verschiebung (x : 𝕎 R) : frobenius (verschiebung x) = x * p := by
  have : IsPoly p fun {R} [CommRing R] x ↦ frobenius (verschiebung x) :=
    IsPoly.comp (hg := frobenius_isPoly p) (hf := verschiebung_isPoly)
  have : IsPoly p fun {R} [CommRing R] x ↦ x * p := mulN_isPoly p p
  ghost_calc x
  ghost_simp [mul_comm]

/-- Verschiebung is the same as multiplication by `p` on the ring of Witt vectors of `ZMod p`. -/
theorem verschiebung_zmod (x : 𝕎 (ZMod p)) : verschiebung x = x * p := by
  rw [← frobenius_verschiebung, frobenius_zmodp]

variable (p R)

theorem coeff_p_pow [CharP R p] (i : ℕ) : ((p : 𝕎 R) ^ i).coeff i = 1 := by
  induction i with
  | zero => simp only [one_coeff_zero, pow_zero]
  | succ i h =>
    rw [pow_succ, ← frobenius_verschiebung, coeff_frobenius_charP,
      verschiebung_coeff_succ, h, one_pow]

theorem coeff_p_pow_eq_zero [CharP R p] {i j : ℕ} (hj : j ≠ i) : ((p : 𝕎 R) ^ i).coeff j = 0 := by
  induction i generalizing j with
  | zero =>
    rw [pow_zero, one_coeff_eq_of_pos]
    exact Nat.pos_of_ne_zero hj
  | succ i hi =>
    rw [pow_succ, ← frobenius_verschiebung, coeff_frobenius_charP]
    cases j
    · rw [verschiebung_coeff_zero, zero_pow hp.out.ne_zero]
    · rw [verschiebung_coeff_succ, hi (ne_of_apply_ne _ hj), zero_pow hp.out.ne_zero]

theorem coeff_p [CharP R p] (i : ℕ) : (p : 𝕎 R).coeff i = if i = 1 then 1 else 0 := by
  split_ifs with hi
  · simpa only [hi, pow_one] using coeff_p_pow p R 1
  · simpa only [pow_one] using coeff_p_pow_eq_zero p R hi

@[simp]
theorem coeff_p_zero [CharP R p] : (p : 𝕎 R).coeff 0 = 0 := by
  rw [coeff_p, if_neg]
  exact zero_ne_one

@[simp]
theorem coeff_p_one [CharP R p] : (p : 𝕎 R).coeff 1 = 1 := by rw [coeff_p, if_pos rfl]

theorem p_nonzero [Nontrivial R] [CharP R p] : (p : 𝕎 R) ≠ 0 := by
  intro h
  simpa only [h, zero_coeff, zero_ne_one] using coeff_p_one p R

theorem FractionRing.p_nonzero [Nontrivial R] [CharP R p] : (p : FractionRing (𝕎 R)) ≠ 0 := by
  simpa using (IsFractionRing.injective (𝕎 R) (FractionRing (𝕎 R))).ne (WittVector.p_nonzero _ _)

variable {p R}

-- Porting note: `ghost_calc` failure: the manual instances had to be added.
/-- The “projection formula” for Frobenius and Verschiebung. -/
theorem verschiebung_mul_frobenius (x y : 𝕎 R) :
    verschiebung (x * frobenius y) = verschiebung x * y := by
  have : IsPoly₂ p fun {R} [Rcr : CommRing R] x y ↦ verschiebung (x * frobenius y) :=
    IsPoly.comp₂ (hg := verschiebung_isPoly)
      (hf := IsPoly₂.comp (hh := mulIsPoly₂) (hf := idIsPolyI' p) (hg := frobenius_isPoly p))
  have : IsPoly₂ p fun {R} [CommRing R] x y ↦ verschiebung x * y :=
    IsPoly₂.comp (hh := mulIsPoly₂) (hf := verschiebung_isPoly) (hg := idIsPolyI' p)
  ghost_calc x y
  rintro ⟨⟩ <;> ghost_simp [mul_assoc]

theorem mul_charP_coeff_zero [CharP R p] (x : 𝕎 R) : (x * p).coeff 0 = 0 := by
  rw [← frobenius_verschiebung, coeff_frobenius_charP, verschiebung_coeff_zero,
    zero_pow hp.out.ne_zero]

theorem mul_charP_coeff_succ [CharP R p] (x : 𝕎 R) (i : ℕ) :
    (x * p).coeff (i + 1) = x.coeff i ^ p := by
  rw [← frobenius_verschiebung, coeff_frobenius_charP, verschiebung_coeff_succ]

theorem mul_pow_charP_coeff_zero [CharP R p] (x : 𝕎 R) {m n : ℕ} (h : m < n) :
    (x * p ^ n).coeff m = 0 := by
  induction n generalizing m with
  | zero => contradiction
  | succ n ih =>
    rw [pow_succ, ← mul_assoc]
    cases m with
    | zero => exact mul_charP_coeff_zero _
    | succ m' =>
      rw [mul_charP_coeff_succ, ih, zero_pow hp.out.ne_zero]
      simpa using h

theorem mul_pow_charP_coeff_succ [CharP R p] (x : 𝕎 R) {m n : ℕ} :
    (x * p ^ n).coeff (m + n) = x.coeff m ^ (p ^ n) := by
  induction n generalizing m with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← mul_assoc, ← add_assoc, mul_charP_coeff_succ, pow_succ, pow_mul]
    congr
    exact ih

theorem verschiebung_frobenius [CharP R p] (x : 𝕎 R) : verschiebung (frobenius x) = x * p := by
  ext ⟨i⟩
  · rw [mul_charP_coeff_zero, verschiebung_coeff_zero]
  · rw [mul_charP_coeff_succ, verschiebung_coeff_succ, coeff_frobenius_charP]

theorem verschiebung_frobenius_comm [CharP R p] :
    Function.Commute (verschiebung : 𝕎 R → 𝕎 R) frobenius := fun x => by
  rw [verschiebung_frobenius, frobenius_verschiebung]

/-!
## Iteration lemmas
-/


open Function

theorem iterate_verschiebung_coeff_eq_zero (x : 𝕎 R) {n : ℕ} {m : ℕ} (h : m < n) :
    (verschiebung^[n] x).coeff m = 0 := by
  induction n generalizing m with
  | zero => contradiction
  | succ n ih =>
    rw [iterate_succ_apply']
    cases m with
    | zero => exact verschiebung_coeff_zero _
    | succ m' =>
      rw [verschiebung_coeff_succ, ih]
      simpa using h

theorem iterate_verschiebung_coeff (x : 𝕎 R) (n k : ℕ) :
    (verschiebung^[n] x).coeff (k + n) = x.coeff k := by
  induction n with
  | zero => simp
  | succ k ih => rw [iterate_succ_apply', Nat.add_succ, verschiebung_coeff_succ]; exact ih

theorem iterate_verschiebung_mul_left (x y : 𝕎 R) (i : ℕ) :
    verschiebung^[i] x * y = verschiebung^[i] (x * frobenius^[i] y) := by
  induction i generalizing y with
  | zero => simp
  | succ i ih =>
    rw [iterate_succ_apply', ← verschiebung_mul_frobenius, ih, iterate_succ_apply',
      iterate_succ_apply]

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
  · rw [verschiebung_frobenius_comm.iterate_iterate]
  · rw [mul_comm]
  · rw [iterate_verschiebung_mul_left]
  · rw [iterate_add_apply]
  · rw [mul_comm]

theorem iterate_frobenius_coeff (x : 𝕎 R) (i k : ℕ) :
    (frobenius^[i] x).coeff k = x.coeff k ^ p ^ i := by
  induction i with
  | zero => simp
  | succ i ih => rw [iterate_succ_apply', coeff_frobenius_charP, ih]; ring_nf

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
  · convert iterate_verschiebung_coeff (p := p) (R := R) _ _ _ using 2
    rw [zero_add]
  · apply mul_coeff_zero
  · simp only [iterate_frobenius_coeff]

theorem iterate_verschiebung_iterate_frobenius (x : 𝕎 R) (n : ℕ) :
    verschiebung^[n] (frobenius^[n] x) = x * (p ^ n) := by
  rw [← comp_apply (f := verschiebung^[n]),
      ← Function.Commute.comp_iterate verschiebung_frobenius_comm]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ_apply', ih, pow_succ, comp_apply, verschiebung_frobenius, mul_assoc]

end CharP

end

end WittVector
