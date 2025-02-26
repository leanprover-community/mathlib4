/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Topology.Algebra.Valued.LocallyCompact


/-!

# Adic expansions of elements of rings of integers of nonarchimedean fields.

We show that every element of a ring of integers of a nonarchimedean field can be uniquely
determined as an expansion in terms of a fixed uniformizer.

## Main definitions

* `AdicExpansion.Digits`: a preimage of the residue field which is used in the expansion.
* `AdicExpansion`: the expansion itself, implemented as a type synonym of functions from `ℕ`.

## TODO
* `AdicExpansion.evalAt`: the evaluation of the expansion at a given point.
* Show that the induced metric space has the same topology regardless of uniformizer chosen.
* `AdicExpansion.appr`: the expansion for a given element of the ring of integers, when over a
  complete discrete valuation ring.

-/

variable {K R : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CommRing R]

open scoped Valued NormedField

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
def AdicExpansion [IsLocalRing R] (d : Digits R) := ℕ → d

namespace AdicExpansion

variable [IsLocalRing R] {D : Digits R}

protected lemma ext_iff {f g : AdicExpansion D} :
    f = g ↔ ∀ n, f n = g n :=
  funext_iff

@[ext]
protected lemma ext {f g : AdicExpansion D} (h : ∀ n, f n = g n) : f = g :=
  funext h

noncomputable
instance : Zero (AdicExpansion D) := inferInstanceAs (Zero (ℕ → D))

@[simp]
lemma zero_apply (n : ℕ) : (0 : AdicExpansion D) n = 0 := rfl

/-- Evaluation of an `AdicExpansion` up to the indicated power, using the provided "base". -/
noncomputable
def evalAtUpto (ϖ : R) (f : AdicExpansion D) (n : ℕ) : R :=
  ∑ i ∈ Finset.range n, f i * ϖ ^ i

@[simp]
lemma evalAtUpto_zero (ϖ : R) (f : AdicExpansion D) :
    evalAtUpto ϖ f 0 = 0 := by
  simp only [evalAtUpto, Finset.sum_range_zero, zero_mul]

@[simp]
lemma evalAtUpto_one (ϖ : R) (f : AdicExpansion D) :
    evalAtUpto ϖ f 1 = f 0 := by
  simp [evalAtUpto]

lemma evalAtUpto_add_one (ϖ : R) (f : AdicExpansion D) (n : ℕ) :
    evalAtUpto ϖ f (n + 1) = evalAtUpto ϖ f n + f n * ϖ ^ n := by
  simp only [evalAtUpto, Finset.sum_range_succ]

@[simp]
lemma zero_evalAtUpto (ϖ : R) (n : ℕ) :
    evalAtUpto ϖ (0 : ℕ → D) n = 0 := by
  induction n with
  | zero => simp
  | succ n ih => simp [evalAtUpto_add_one, ih]

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

lemma mul_evalAtUpto_of_add_one (ϖ : R) (f : AdicExpansion D) (n : ℕ) :
    ϖ * evalAtUpto ϖ (f ∘ (· + 1)) n = evalAtUpto ϖ f (n + 1) - f 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [evalAtUpto_add_one, Function.comp_apply, mul_add, ih]
    ring

lemma evalAtUpto_add_one' (ϖ : R) (f : AdicExpansion D) (n : ℕ) :
    evalAtUpto ϖ f (n + 1) = f 0 + ϖ * evalAtUpto ϖ (f ∘ (· + 1)) n := by
  rw [mul_evalAtUpto_of_add_one]
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
    refine ⟨evalAtUpto ϖ (f ∘ (· + 1)) n, ?_⟩
    simp [mul_evalAtUpto_of_add_one, h]

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
      rw [← sub_zero (evalAtUpto _ _ _), ← h', ← mul_evalAtUpto_of_add_one, h'] at h
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
    rw [← mul_evalAtUpto_of_add_one, sub_sub, add_comm (f 0 : R), ← sub_sub,
      ← mul_evalAtUpto_of_add_one, sub_eq_sub_iff_sub_eq_sub, ← mul_sub] at h
    have h0 : g 0 = f 0 := by simp [← Digits.not_isUnit_dvd_sub_iff hϖ, ← h]
    simp only [h0, sub_self, mul_eq_zero, hϖ0, false_or, sub_eq_zero] at h
    specialize ih z (fun i hi ↦ hf (i + 1) (by simpa using hi))
      (fun i hi ↦ hg (i + 1) (by simpa using hi)) h
    ext (_|n)
    · simp [h0]
    · simp [congr_fun ih n]

section appr

/-- The trailing digit in an adic expansion -- the digit when mod-ding by the base. -/
noncomputable
abbrev trailingDigit (x : R) : D :=
  Function.invFun (IsLocalRing.residue R ∘ (↑)) (IsLocalRing.residue R x)

@[simp]
lemma trailingDigit_zero : (trailingDigit 0 : D) = 0 := by
  apply Subtype.val_injective
  apply D.bij.injOn (Subtype.prop _) (Subtype.prop _)
  change (IsLocalRing.residue R ∘ Subtype.val) _ = _
  apply Function.invFun_eq
  refine ⟨0, ?_⟩
  simp

lemma residue_sub_trailingDigit_eq_zero (x : R) :
    IsLocalRing.residue R (x - (trailingDigit x : D)) = 0 := by
  rw [trailingDigit, RingHom.map_sub, sub_eq_zero, eq_comm]
  change (IsLocalRing.residue R ∘ Subtype.val) _ = _
  apply Function.invFun_eq
  simpa using D.bij.surjOn (Set.mem_univ (IsLocalRing.residue R x))

lemma sub_trailingDigit_mem_maximalIdeal (x : R) :
    x - (trailingDigit x : D) ∈ IsLocalRing.maximalIdeal R := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← IsLocalRing.residue]
  exact residue_sub_trailingDigit_eq_zero x

variable [IsDiscreteValuationRing 𝒪[K]] (D : Digits 𝒪[K]) {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ)
include hϖ

/-- The quotient when dividing through by the base after subtracting out the trailing digit.
In an adic expansion, this corresponds to the sequence of digits that come after the trailing digit.
-/
noncomputable
abbrev tail (x : 𝒪[K]) : 𝒪[K] :=
  ⟨(x - (trailingDigit x : D)) / ϖ, by
    suffices ϖ ∣ x - (trailingDigit x : D) by
      obtain ⟨c, hc⟩ := this
      simp only [← AddSubgroupClass.coe_sub, hc, Subring.coe_mul]
      rw [mul_div_cancel_left₀]
      · simp
      · simp [hϖ.ne_zero]
    rw [← Ideal.Quotient.eq_zero_iff_dvd, ← hϖ.maximalIdeal_eq, ← IsLocalRing.residue]
    exact residue_sub_trailingDigit_eq_zero x⟩

@[simp]
lemma tail_zero : tail D hϖ 0 = 0 := by
  ext
  simp [tail]

lemma trailingDigit_mul (x : 𝒪[K]) :
    trailingDigit (ϖ * x) = (0 : D) := by
  rw [trailingDigit, RingHom.map_mul]
  have : IsLocalRing.residue 𝒪[K] ϖ = 0 := by
    simp [hϖ.not_unit]
  simp only [this, zero_mul]
  rw [← (IsLocalRing.residue 𝒪[K]).map_zero, ← trailingDigit]
  simp

@[simp]
lemma tail_mul (x : 𝒪[K]) :
    tail D hϖ (ϖ * x) = x := by
  ext
  simp only [Subring.coe_mul, trailingDigit_mul D hϖ, Digits.coe_zero, ZeroMemClass.coe_zero,
    sub_zero]
  rw [mul_div_cancel_left₀]
  simp [hϖ.ne_zero]

lemma mul_tail (x : 𝒪[K]) :
    ϖ * tail D hϖ x = x - (trailingDigit x : D) := by
  ext
  simp only [tail, Subring.coe_mul, AddSubgroupClass.coe_sub]
  rw [mul_div_cancel₀]
  simp [hϖ.ne_zero]

/-- Recursively construct a partial adic expansion at a base, up to `n` digits. This construction
uses an explicit fuel of target of `n` digits to ensure it terminates. -/
noncomputable
def apprUpto : ℕ → 𝒪[K] → AdicExpansion D
  | 0, _ => 0
  | n + 1, x =>
    let d : D := trailingDigit x
    Function.update (apprUpto n (tail D hϖ x) ∘ (· - 1)) 0 d

@[simp]
lemma apprUpto_at_zero (x : 𝒪[K]) :
    apprUpto D hϖ 0 x = 0 := by
  simp [apprUpto]

lemma apprUpto_eval_zero_eq_invFun (n : ℕ) (x : 𝒪[K]) :
    apprUpto D hϖ (n + 1) x 0 = trailingDigit x := by
  simp [apprUpto]

@[simp]
lemma apprUpto_zero (n : ℕ) :
    apprUpto D hϖ n 0 = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [apprUpto]
    ext
    simp [ih]

lemma residue_apprUpto_eval_zero (n : ℕ) (x : 𝒪[K]) :
    IsLocalRing.residue 𝒪[K] (apprUpto D hϖ (n + 1) x 0) = IsLocalRing.residue 𝒪[K] x := by
  rw [apprUpto]
  change (IsLocalRing.residue 𝒪[K] ∘ Subtype.val) _ = _
  apply Function.invFun_eq
  simpa using D.bij.surjOn (Set.mem_univ (IsLocalRing.residue 𝒪[K] x))

lemma pow_dvd_sub_evalAtUpto_apprUpto (n : ℕ) (x : 𝒪[K]) :
    ϖ ^ n ∣ x - evalAtUpto ϖ (apprUpto D hϖ n x) n := by
  rcases n with (_|n)
  · simp
  induction n generalizing x with
  | zero =>
    simp only [zero_add, pow_one, evalAtUpto_one]
    rw [← Ideal.Quotient.eq_zero_iff_dvd, ← hϖ.maximalIdeal_eq, RingHom.map_sub, sub_eq_zero,
      eq_comm]
    exact residue_apprUpto_eval_zero D _ _ _
  | succ n ih =>
    rw [apprUpto, evalAtUpto_add_one', Function.update_self, ← sub_sub, ← mul_tail D hϖ,
      ← mul_sub, pow_succ']
    exact mul_dvd_mul_left ϖ (ih (tail D hϖ x))

end appr

end AdicExpansion
