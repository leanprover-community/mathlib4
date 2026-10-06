/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Mathlib.RingTheory.Ideal.Int

/-!
# The additive character attached to the trace

Let `A` be a commutative algebra over `ℤ ⧸ pℤ` with `p` a natural number, and let `ζ` be a
primitive `p`-th root of unity in a ring `R`. Composing the trace of `A` over `ℤ ⧸ pℤ` with the
character of `ℤ ⧸ pℤ` attached to `ζ` gives an additive character of `A` with values in `R`.
Throughout, the ideal `pℤ = Ideal.span {(p : ℤ)}` of `ℤ` is written `𝒑`.

This file defines that character and establishes its basic properties.

Over a finite field this is the construction behind `FiniteField.primitiveChar`, with one
difference: there the root of unity is chosen as part of the construction, whereas here it is
supplied by the user, which is what one needs when working inside a fixed cyclotomic field.

## Main definitions

* `AddChar.traceChar`: the additive character of `A` sending `x` to
  `ζ ^ Algebra.trace (ℤ ⧸ pℤ) A x`.

## Main results

* `AddChar.exists_nat_traceChar_eq_pow`: the value of `traceChar` at `x` is `ζ ^ a` for any
  natural number `a` representing the trace of `x`; this is how the character is computed in
  practice.

* `AddChar.mk_traceChar_apply_eq_one`: the values of `traceChar` are congruent to `1` modulo any
  ideal containing `ζ - 1`.

* `AddChar.mk_traceChar_apply_eq_one_add_smul`: first-order expansion of `traceChar` modulo the
  square of an ideal containing `ζ - 1`.

* `AddChar.isPrimitive_traceChar`: over a finite field, the character `traceChar` is primitive.

* `AddChar.traceChar_apply_pow`: over a finite field, the character `traceChar` is invariant
  under the Frobenius `x ↦ x ^ p`.

* `AddChar.compAddChar_traceChar`: pushing `traceChar` along an algebra homomorphism `R → S`
  gives the character attached to the image of `ζ`.

* `AddChar.map_traceChar_apply_eq_mulShift`: applying a homomorphism of `R` that sends `ζ` to
  `ζ ^ n` to a value of `traceChar` gives the corresponding value of the shift of `traceChar`
  by `n`.

## Tags

additive character, trace

-/

public section

open Ideal

namespace AddChar

variable {p : ℕ} [NeZero p] (A : Type*) [CommRing A] [Algebra (ℤ ⧸ Ideal.span {(p : ℤ)}) A]
  {R : Type*} [CommRing R] {ζ : R} (hζ : IsPrimitiveRoot ζ p)

local notation3 "𝒑" => Ideal.span {(p : ℤ)}

attribute [local instance] Ideal.Quotient.field

/-- The additive character of `A` sending `x` to `ζ ^ Algebra.trace (ℤ ⧸ 𝒑) A x`, where `ζ` is a
primitive `p`-th root of unity. -/
noncomputable def traceChar : AddChar A R :=
  (zmodChar p hζ.pow_eq_one).compAddMonoidHom <|
    AddMonoidHom.comp (Int.quotientSpanNatEquivZMod p) (Algebra.trace (ℤ ⧸ 𝒑) A).toAddMonoidHom

variable {A}

/-- The value of `traceChar` at `x`, as a power of `ζ` with exponent the canonical natural
number representing the trace of `x`. -/
theorem traceChar_apply (x : A) :
    traceChar A hζ x =
      ζ ^ (Int.quotientSpanNatEquivZMod p (Algebra.trace (ℤ ⧸ 𝒑) A x)).val := by rfl

/-- The value of `traceChar` at `x` is `ζ ^ a` for any natural number `a` representing the
trace of `x`. This is easier to work with than `traceChar_apply` in most cases. -/
theorem exists_nat_traceChar_eq_pow (x : A) :
    ∃ a : ℕ, traceChar A hζ x = ζ ^ a ∧ Algebra.trace (ℤ ⧸ 𝒑) A x = a := by
  refine ⟨(Int.quotientSpanNatEquivZMod p (Algebra.trace (ℤ ⧸ 𝒑) A x)).val, rfl, ?_⟩
  have := RingHom.congr_fun (Int.quotientSpanNatEquivZMod_comp_castRingHom p)
    (Int.quotientSpanNatEquivZMod p (Algebra.trace (ℤ ⧸ 𝒑) A x)).val
  rwa [RingHom.comp_apply, eq_intCast, Int.cast_natCast, ZMod.natCast_val, ZMod.cast_id,
    RingHom.coe_coe, RingEquiv.symm_apply_apply] at this

/-- The character `traceChar` is trivial at `x` if and only if the trace of `x` vanishes. -/
@[simp]
theorem traceChar_apply_eq_one_iff {x : A} :
    traceChar A hζ x = 1 ↔ Algebra.trace (ℤ ⧸ 𝒑) A x = 0 := by
  rw [traceChar_apply, ← orderOf_dvd_iff_pow_eq_one, ← hζ.eq_orderOf, ← ZMod.natCast_eq_zero_iff,
    ZMod.natCast_zmod_val, RingEquiv.map_eq_zero_iff]

/-- The values of `traceChar` are congruent to `1` modulo any ideal containing `ζ - 1`. -/
theorem mk_traceChar_apply_eq_one {𝓟 : Ideal R} (h : ζ - 1 ∈ 𝓟) (x : A) :
    Ideal.Quotient.mk 𝓟 (traceChar A hζ x) = 1 := by
  rw [traceChar_apply, show ζ = (ζ - 1) + 1 by ring, add_pow]
  simp only [one_pow, mul_one, Finset.sum_range_succ', pow_zero, Nat.choose_zero_right,
    Nat.cast_one, map_add, map_sum, map_mul, map_pow, map_one, map_natCast, add_eq_right]
  exact Finset.sum_eq_zero fun i _ ↦ by
    rw [Quotient.eq_zero_iff_mem.mpr h, zero_pow i.succ_ne_zero, zero_mul]

/-- First-order expansion of `traceChar` modulo the square of an ideal containing `ζ - 1`. -/
theorem mk_traceChar_apply_eq_one_add_smul {𝓟 : Ideal R} [(𝓟 ^ 2).LiesOver 𝒑] (h : ζ - 1 ∈ 𝓟)
    (x : A) :
    Ideal.Quotient.mk (𝓟 ^ 2) (traceChar A hζ x) =
      1 + Algebra.trace (ℤ ⧸ 𝒑) A x • (Ideal.Quotient.mk (𝓟 ^ 2) (ζ - 1)) := by
  obtain ⟨a, ha, ha'⟩ := exists_nat_traceChar_eq_pow hζ x
  rw [ha, ha', show ζ = (ζ - 1) + 1 by ring, add_pow]
  simp only [one_pow, mul_one, map_sum, map_mul, map_natCast, sub_add_cancel, Algebra.smul_def]
  cases a
  · simp
  · have {k} : Ideal.Quotient.mk (𝓟 ^ 2) ((ζ - 1) ^ (k + 2)) = 0 :=
      Quotient.eq_zero_iff_mem.mpr <| pow_le_pow_right le_add_self <| pow_mem_pow h _
    simp only [Finset.sum_range_succ', zero_add, pow_one, Nat.choose_one_right, Nat.cast_add,
      Nat.cast_one, pow_zero, Nat.choose_zero_right, mul_one, this, zero_mul, Finset.sum_const_zero,
      map_sub, map_one, zero_add]
    ring

/-- Pushing `traceChar` along an algebra homomorphism `R → S` gives the character attached to
the image of `ζ`. -/
theorem compAddChar_traceChar {S : Type*} [CommRing S] [Algebra R S] [FaithfulSMul R S] :
    (algebraMap R S).compAddChar (traceChar A hζ) =
        traceChar A (hζ.map_of_injective (FaithfulSMul.algebraMap_injective R S)) := by
  ext x
  have hζ' := hζ.map_of_injective (FaithfulSMul.algebraMap_injective R S)
  obtain ⟨a, ha, ha'⟩ := exists_nat_traceChar_eq_pow hζ x
  obtain ⟨b, hb, hb'⟩ := exists_nat_traceChar_eq_pow hζ' x
  rw [MonoidHom.coe_compAddChar, Function.comp_apply, ha, hb, map_pow, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_ofClass, (hζ'.isOfFinOrder (NeZero.ne _)).pow_eq_pow_iff_modEq]
  rwa [hb', CharP.natCast_eq_natCast, Int.ringChar_idealQuot, hζ'.eq_orderOf, Nat.ModEq.comm] at ha'

/-- If an homomorphism of `R` sends `ζ` to `ζ ^ n`, then it sends the value of `traceChar` at `x`
to the value at `x` of the shift of `traceChar` by `n`. -/
theorem map_traceChar_apply_eq_mulShift {G : Type*} [FunLike G R R] [MonoidHomClass G R R] (f : G)
    (n : ℕ) (h : f ζ = ζ ^ n) (x : A) :
    f (traceChar A hζ x) = (traceChar A hζ).mulShift (n : A) x := by
  obtain ⟨a, ha, ha'⟩ := exists_nat_traceChar_eq_pow hζ x
  obtain ⟨b, hb, hb'⟩ := exists_nat_traceChar_eq_pow hζ (n * x)
  rw [mulShift_apply, ha, hb, map_pow, h, ← pow_mul,
    (hζ.isOfFinOrder (NeZero.ne _)).pow_eq_pow_iff_modEq, ← hζ.eq_orderOf]
  rwa [← nsmul_eq_mul, map_nsmul, ha', nsmul_eq_mul, ← Nat.cast_mul, CharP.natCast_eq_natCast,
    Int.ringChar_idealQuot] at hb'

section Field

variable [Fact (p.Prime)] {F : Type*} [Field F] [Finite F]
  [Algebra (ℤ ⧸ Ideal.span {(p : ℤ)}) F]

/-- Over a finite field, the character `traceChar` is nontrivial, since the trace is. -/
theorem traceChar_ne_one : traceChar F hζ ≠ 1 := by
  obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp <| Algebra.trace_ne_zero (ℤ ⧸ 𝒑) F
  exact ne_one_iff.mpr ⟨x, by rwa [ne_eq, traceChar_apply_eq_one_iff]⟩

/-- Over a finite field, the character `traceChar` is primitive. -/
theorem isPrimitive_traceChar : IsPrimitive (traceChar F hζ) :=
  IsPrimitive.of_ne_one (traceChar_ne_one hζ)

/-- Over a finite field, the character `traceChar` is invariant under the Frobenius
`x ↦ x ^ p`. -/
theorem traceChar_apply_pow (x : F) : traceChar F hζ (x ^ p) = traceChar F hζ x := by
  have : CharP F p :=
    (Algebra.charP_iff (ℤ ⧸ 𝒑) _ _).mp <| ringChar.of_eq <| Int.ringChar_idealQuot p
  have : Fintype (ℤ ⧸ 𝒑) := Fintype.ofFinite (ℤ ⧸ 𝒑)
  have : x ^ p = FiniteField.frobeniusAlgEquiv (ℤ ⧸ 𝒑) F p x := by
    rw [FiniteField.frobeniusAlgEquiv_apply, ← Nat.card_eq_fintype_card, Int.card_ideal_quot]
  rw [this, traceChar_apply, Algebra.trace_eq_of_algEquiv, traceChar_apply]

end Field

end AddChar
