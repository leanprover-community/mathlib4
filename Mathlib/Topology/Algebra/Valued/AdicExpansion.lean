/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/

import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.PowerSeries.Evaluation
import Mathlib.RingTheory.PowerSeries.Trunc


/-!

# Adic expansions of elements of rings of integers of nonarchimedean fields.

We show that every element of a ring of integers of a nonarchimedean field can be uniquely
determined as an expansion in terms of a fixed uniformizer.

## Main definitions

* `AdicExpansion.Digits`: a preimage of the residue field which is used in the expansion.
* `AdicExpansion`: the expansion itself, implemented as a power series with `Digits` coefficients.

## TODO
* `AdicExpansion.evalAt`: the evaluation of the expansion at a given point.
* Show that the induced metric space has the same topology regardless of uniformizer chosen.
* `AdicExpansion.appr`: the expansion for a given element of the ring of integers, when over a
  complete discrete valuation ring.

-/

variable {R : Type*} [CommRing R]

namespace AdicExpansion

variable [IsLocalRing R]

section Digits

variable (R) in
/-- The digits used in an adic expansion, requiring that they are in bijection with the
residue field. Zero is required to be a digit to ensure uniqueness of the expansion. -/
structure Digits where
  /-- The underlying preimage of the residue field. -/
  (carrier : Set R)
  (zero : 0 ∈ carrier)
  (bij : Set.BijOn (IsLocalRing.residue R) carrier (Set.univ))

instance : SetLike (Digits R) R := ⟨Digits.carrier, by rintro ⟨⟩ ⟨⟩; simp⟩

noncomputable
instance (digits : Digits R) : Zero digits := ⟨0, digits.zero⟩

instance (digits : Digits R) : Nonempty digits := ⟨0⟩

@[simp, norm_cast]
lemma Digits.coe_zero (digits : Digits R) : ((0 : digits) : R) = 0 := rfl

lemma Digits.ext_iff {digits : Digits R} {x y : digits} : x = y ↔ (x : R) = y := by
  simp

@[simp]
lemma Digits.isUnit_iff {digits : Digits R} {x : digits} :
    IsUnit (x : R) ↔ x ≠ 0 := by
  rw [iff_not_comm]
  constructor <;> intro h
  · simp [h]
  rw [Digits.ext_iff, Digits.coe_zero]
  exact digits.bij.injOn x.prop digits.zero (by simpa using h)

lemma Digits.not_isUnit_dvd_iff {digits : Digits R} {ϖ : R} (hϖ : ¬ IsUnit ϖ) {x : digits} :
    ϖ ∣ x ↔ x = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  rw [← not_not (a := x = 0), ← ne_eq, ← isUnit_iff]
  exact not_isUnit_of_not_isUnit_dvd hϖ h

lemma Digits.coe_sub_eq_iff {digits : Digits R} {x y : digits} :
    (x : R) - y = 0 ↔ x = y := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  rw [Digits.ext_iff, ← sub_eq_zero, h]

lemma Digits.not_isUnit_dvd_sub_iff {digits : Digits R} {ϖ : R} (hϖ : ¬ IsUnit ϖ)
    {x y : digits} :
    ϖ ∣ x - y ↔ x = y := by
  constructor
  · rintro ⟨c, hc⟩
    apply_fun IsLocalRing.residue R at hc
    ext
    refine digits.bij.injOn x.prop y.prop ?_
    rw [← sub_eq_zero, ← map_sub, hc, (IsLocalRing.residue_eq_zero_iff _).mpr]
    simp [hϖ]
  · intro h
    simp [h]

end Digits

end AdicExpansion

open AdicExpansion

/-- A formal expansion of an element in the local ring, at the digits specified. Meant to
be evaluated using `AdicExpansion.evalAtUpto` and related definitions. -/
structure AdicExpansion [IsLocalRing R] (d : Digits R) where
  carrier : PowerSeries R
  isDigits i : carrier.coeff R i ∈ d

namespace AdicExpansion

variable [IsLocalRing R] {D : Digits R}

noncomputable
instance : FunLike (AdicExpansion D) ℕ D where
  coe f n := ⟨f.carrier.coeff R n, f.isDigits n⟩
  coe_injective' := by
    rintro ⟨⟩ ⟨⟩
    simp [funext_iff, PowerSeries.ext_iff]

protected lemma ext_iff {f g : AdicExpansion D} :
    f = g ↔ ∀ n, f n = g n :=
  DFunLike.ext_iff

@[ext]
protected lemma ext {f g : AdicExpansion D} (h : ∀ n, f n = g n) : f = g :=
  DFunLike.ext _ _ h

@[simp]
lemma coeff_carrier_eq_apply (f : AdicExpansion D) (n : ℕ) :
    f.carrier.coeff R n = f n := rfl

@[simp]
lemma apply_mk_eq_apply (f) (hf) (n : ℕ) :
    (⟨f, hf⟩ : AdicExpansion D) n = f.coeff _ n := rfl

noncomputable
instance : Zero (AdicExpansion D) := ⟨⟨0, fun _ ↦ D.zero⟩⟩

@[simp]
lemma carrier_zero : (0 : AdicExpansion D).carrier = 0 := rfl
@[simp]
lemma zero_apply (n : ℕ) : (0 : AdicExpansion D) n = 0 := rfl

/-- Evaluation of an `AdicExpansion` up to the indicated power, using the provided "base". -/
noncomputable
def evalAtUpto (ϖ : R) (f : AdicExpansion D) (n : ℕ) : R :=
  (PowerSeries.trunc n f.carrier).eval ϖ

@[simp]
lemma evalAtUpto_zero (ϖ : R) (f : AdicExpansion D) :
    evalAtUpto ϖ f 0 = 0 := by
  simp [evalAtUpto]

@[simp]
lemma evalAtUpto_one (ϖ : R) (f : AdicExpansion D) :
    evalAtUpto ϖ f 1 = f 0 := by
  simp [evalAtUpto]

lemma evalAtUpto_add_one (ϖ : R) (f : AdicExpansion D) (n : ℕ) :
    evalAtUpto ϖ f (n + 1) = evalAtUpto ϖ f n + f n * ϖ ^ n := by
  simp [evalAtUpto, PowerSeries.trunc_succ]

@[simp]
lemma zero_evalAtUpto (ϖ : R) (n : ℕ) :
    evalAtUpto ϖ (0 : AdicExpansion D) n = 0 := by
  simp [evalAtUpto]

@[simp]
lemma evalAtUpto_at_zero (f : AdicExpansion D) (n : ℕ) :
    evalAtUpto 0 f (n + 1) = f 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [evalAtUpto_add_one, ih]
    simp

lemma congr_of_eqOn (ϖ : R) {f g : AdicExpansion D} {n : ℕ}
    (h : ∀ i < n, f i = g i) :
    evalAtUpto ϖ f n = evalAtUpto ϖ g n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [evalAtUpto_add_one]
    rw [ih (fun i hi ↦ h i (Nat.lt_succ_of_lt hi)), h _ (by simp)]

noncomputable
def shiftLeft (f : AdicExpansion D) : AdicExpansion D :=
  ⟨.mk fun n ↦ f (n + 1), fun _ ↦ by simp⟩

@[simp]
lemma shiftLeft_apply (f : AdicExpansion D) (n : ℕ) :
    f.shiftLeft n = f (n + 1) := by
  dsimp only [shiftLeft]
  ext
  simp

lemma mul_evalAtUpto_shiftLeft (ϖ : R) (f : AdicExpansion D) (n : ℕ) :
    ϖ * evalAtUpto ϖ f.shiftLeft n = evalAtUpto ϖ f (n + 1) - f 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [evalAtUpto_add_one, shiftLeft_apply, mul_add, ih]
    ring

lemma evalAtUpto_add_one' (ϖ : R) (f : AdicExpansion D) (n : ℕ) :
    evalAtUpto ϖ f (n + 1) = f 0 + ϖ * evalAtUpto ϖ f.shiftLeft n := by
  rw [mul_evalAtUpto_shiftLeft]
  ring

lemma dvd_evalAtUpto_iff_apply_zero {ϖ : R} (hϖ : ¬ IsUnit ϖ)
    {f : AdicExpansion D} {n : ℕ} :
    ϖ ∣ evalAtUpto ϖ f (n + 1) ↔ f 0 = 0 := by
  constructor
  · intro h
    induction n with
    | zero => simpa using not_isUnit_of_not_isUnit_dvd hϖ h
    | succ n ih =>
      obtain ⟨c, h⟩ := h
      rw [evalAtUpto_add_one, eq_comm, ← sub_eq_iff_eq_add, pow_succ', mul_left_comm,
        ← mul_sub] at h
      exact ih ⟨_, h.symm⟩
  · intro h
    refine ⟨evalAtUpto ϖ f.shiftLeft n, ?_⟩
    simp [mul_evalAtUpto_shiftLeft, h]

lemma evalAtUpto_eq_zero_iff [IsDomain R] {ϖ : R} (hϖ : ¬ IsUnit ϖ) (hn : ϖ ≠ 0)
    {f : AdicExpansion D} {n : ℕ} :
    evalAtUpto ϖ f (n + 1) = 0 ↔ ∀ i < n + 1, f i = 0 := by
  constructor
  · intro h
    induction n generalizing f with
    | zero => simpa [Digits.ext_iff] using h
    | succ n ih =>
      have h' := h
      rw [evalAtUpto_add_one, add_eq_zero_iff_eq_neg, ← neg_mul, mul_comm] at h'
      replace h' : ϖ ^ (n + 1) ∣ evalAtUpto ϖ f (n + 1) := by
        rw [h']
        exact ⟨_, rfl⟩
      replace h' : ϖ ∣ evalAtUpto ϖ f (n + 1) := dvd_trans (dvd_pow_self _ (by simp)) h'
      rw [dvd_evalAtUpto_iff_apply_zero hϖ, Digits.ext_iff, Digits.coe_zero] at h'
      rw [← sub_zero (evalAtUpto _ _ _), ← h', ← mul_evalAtUpto_shiftLeft, h'] at h
      simp only [mul_eq_zero, hn, false_or] at h
      specialize ih h
      simp only [Function.comp_apply, Digits.ext_iff, Digits.coe_zero] at ih
      rintro (_|i) hi
      · simp [Digits.ext_iff, h']
      · simpa [Digits.ext_iff] using ih i (by linarith)
  · intro h
    rw [← zero_evalAtUpto (D := D) ϖ (n + 1)]
    refine congr_of_eqOn ϖ ?_
    simpa using h

lemma pow_not_dvd_evalAtUpto [IsDomain R] {ϖ : R} (hϖ : ¬ IsUnit ϖ) (hn : ϖ ≠ 0)
    (f : AdicExpansion D)
    (n : ℕ) (h : ∃ i < n + 1, f i ≠ 0) :
    ¬ϖ ^ (n + 1) ∣ evalAtUpto ϖ f (n + 1) := by
  contrapose! h
  rw [← evalAtUpto_eq_zero_iff hϖ hn]
  induction n generalizing f with
  | zero =>
    simp only [zero_add, pow_one, evalAtUpto_one] at h
    simpa [Digits.ext_iff] using not_isUnit_of_not_isUnit_dvd hϖ h
  | succ n ih =>
    rw [evalAtUpto_add_one, pow_succ] at h
    obtain ⟨c, h⟩ := h
    rw [mul_comm, eq_comm, ← sub_eq_iff_eq_add, mul_assoc, ← mul_sub] at h
    specialize ih _ ⟨_, h.symm⟩
    simp only [ih, mul_eq_zero, ne_eq, AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false,
      not_false_eq_true, pow_eq_zero_iff, hn, false_or, sub_eq_zero] at h
    replace h : f (n + 1) = 0 := by simpa using not_isUnit_of_not_isUnit_dvd hϖ ⟨_, h.symm⟩
    rw [evalAtUpto_add_one, ih, h, Digits.coe_zero]
    simp [hn]

lemma evalAtUpto_injOn [IsDomain R]
    {ϖ : R} (hϖ : ¬ IsUnit ϖ) (hϖ0 : ϖ ≠ 0) (n : ℕ) (z : D) :
    Set.InjOn (evalAtUpto ϖ · n) {f : AdicExpansion D | ∀ i ≥ n, f i = z} := by
  induction n generalizing z with
  | zero =>
    intro f hf g hg _
    simp only [ge_iff_le, zero_le, forall_const, Set.mem_setOf_eq] at hf hg
    ext
    simp [hf, hg]
  | succ n ih =>
    intro f hf g hg h
    simp only [ge_iff_le, Set.mem_setOf_eq] at hf hg h
    apply_fun (· - (f 0 : R)) at h
    apply_fun (· - (g 0 : R)) at h
    rw [← mul_evalAtUpto_shiftLeft, sub_sub, add_comm (f 0 : R), ← sub_sub,
      ← mul_evalAtUpto_shiftLeft, sub_eq_sub_iff_sub_eq_sub, ← mul_sub] at h
    have h0 : g 0 = f 0 := by simp [← Digits.not_isUnit_dvd_sub_iff hϖ, ← h]
    simp only [h0, sub_self, mul_eq_zero, hϖ0, false_or, sub_eq_zero] at h
    specialize ih z (fun i hi ↦ by simpa using hf (i + 1) (by simpa using hi))
      (fun i hi ↦ by simpa using hg (i + 1) (by simpa using hi)) h
    ext (_|n)
    · simp [h0]
    · simpa using congr_fun (congr_arg (⇑) ih) n

end AdicExpansion
