/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-!
# The additive character attached to the trace

Let `A` be a commutative algebra over `ZMod p` and let `ζ` be a primitive `p`-th root of unity in
a ring `R`. Composing the trace of `A` over `ZMod p` with the character of `ZMod p` attached to
`ζ` gives an additive character of `A` with values in `R`.

This file defines that character and establishes its basic properties.

Over a finite field this is the construction behind `FiniteField.primitiveChar`, with one main
difference: there the root of unity is chosen as part of the construction, whereas here it is a
parameter, thus one can work with a given root of unity in a given ring.

## Main definitions

* `AddChar.traceChar`: the additive character of `A` sending `x` to
  `ζ ^ Algebra.trace (ZMod p) A x`.

## Main results

* `AddChar.isPrimitive_traceChar`: over a finite field, the character `traceChar` is primitive.
* `AddChar.mk_traceChar_apply_eq_one_add_smul`: first-order expansion of `traceChar` modulo the
  square of an ideal containing `ζ - 1`.
* `AddChar.map_traceChar_apply_eq_mulShift`: applying a homomorphism of `R` that sends `ζ` to
  `ζ ^ n` to a value of `traceChar` gives the corresponding value of the shift of `traceChar`
  by `n`.

## Tags

additive character, trace

-/

public section

namespace AddChar

variable {p : ℕ} [NeZero p] (A : Type*) [CommRing A] [Algebra (ZMod p) A] {R : Type*} [CommRing R]
  {ζ : R} (hζ : IsPrimitiveRoot ζ p)

/-- The additive character of `A` sending `x` to `ζ ^ Algebra.trace (ZMod p) A x`, where `ζ` is a
primitive `p`-th root of unity. -/
noncomputable def traceChar : AddChar A R :=
  (zmodChar p hζ.pow_eq_one).compAddMonoidHom (Algebra.trace (ZMod p) A).toAddMonoidHom

variable {A}

/-- The value of `traceChar` at `x`, as a power of `ζ` with exponent the canonical natural
number representing the trace of `x`. -/
theorem traceChar_apply (x : A) :
    traceChar A hζ x = ζ ^ (Algebra.trace (ZMod p) A x).val := by rfl

/-- The character `traceChar` is trivial at `x` if and only if the trace of `x` vanishes. -/
@[simp]
theorem traceChar_apply_eq_one_iff {x : A} :
    traceChar A hζ x = 1 ↔ Algebra.trace (ZMod p) A x = 0 := by
  rw [traceChar_apply, ← orderOf_dvd_iff_pow_eq_one, ← hζ.eq_orderOf, ← ZMod.natCast_eq_zero_iff,
    ZMod.natCast_zmod_val]

/-- The character `traceChar` is trivial if and only if the trace vanishes. -/
theorem traceChar_eq_one_iff : traceChar A hζ = 1 ↔ Algebra.trace (ZMod p) A = 0 := by
  simp [AddChar.ext_iff, LinearMap.ext_iff]

/-- The values of `traceChar` are congruent to `1` modulo any ideal containing `ζ - 1`. -/
theorem mk_traceChar_apply_eq_one {𝓟 : Ideal R} (h : ζ - 1 ∈ 𝓟) (x : A) :
    Ideal.Quotient.mk 𝓟 (traceChar A hζ x) = 1 := by
  rw [traceChar_apply, map_pow, Ideal.Quotient.eq.mpr h, map_one, one_pow]

/-- First-order expansion of `traceChar` modulo the square of an ideal containing `ζ - 1`. -/
theorem mk_traceChar_apply_eq_one_add_smul {𝓟 : Ideal R} (h : ζ - 1 ∈ 𝓟) (x : A) :
    Ideal.Quotient.mk (𝓟 ^ 2) (traceChar A hζ x) =
      1 + (Algebra.trace (ZMod p) A x).val • Ideal.Quotient.mk (𝓟 ^ 2) (ζ - 1) := by
  have := Polynomial.eval_add_of_sq_eq_zero (Polynomial.X ^ (Algebra.trace (ZMod p) A x).val) 1
    (Ideal.Quotient.mk (𝓟 ^ 2) (ζ - 1))
    (by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.pow_mem_pow h 2)
  simpa [traceChar_apply, add_comm, Polynomial.derivative_X_pow] using this

/-- Pushing `traceChar` along an injective ring homomorphism `f : R → S` gives the character
attached to `f ζ`. -/
theorem compAddChar_traceChar {S : Type*} [CommRing S] {f : R →+* S} (hf : Function.Injective f) :
    f.compAddChar (traceChar A hζ) = traceChar A (hζ.map_of_injective hf) := by
  ext x
  rw [MonoidHom.coe_compAddChar, Function.comp_apply, traceChar_apply, traceChar_apply, map_pow,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]

/-- If a homomorphism of `R` sends `ζ` to `ζ ^ n`, then it sends the value of `traceChar` at `x`
to the value at `x` of the shift of `traceChar` by `n`. -/
theorem map_traceChar_apply_eq_mulShift {G : Type*} [FunLike G R R] [MonoidHomClass G R R] (f : G)
    (n : ℕ) (h : f ζ = ζ ^ n) (x : A) :
    f (traceChar A hζ x) = (traceChar A hζ).mulShift (n : A) x := by
  rw [mulShift_apply, traceChar_apply, traceChar_apply, map_pow, h, ← pow_mul,
    (hζ.isOfFinOrder (NeZero.ne _)).pow_eq_pow_iff_modEq, ← hζ.eq_orderOf,
    ← ZMod.natCast_eq_natCast_iff]
  simp [← nsmul_eq_mul]

/-- The character `traceChar` is invariant under isomorphisms of `ZMod p`-algebras. -/
theorem traceChar_apply_algEquiv {B : Type*} [CommRing B] [Algebra (ZMod p) B]
    (e : A ≃ₐ[ZMod p] B) (x : A) : traceChar B hζ (e x) = traceChar A hζ x := by
  rw [traceChar_apply, Algebra.trace_eq_of_algEquiv, traceChar_apply]

section Field

variable [Fact (p.Prime)] {F : Type*} [Field F] [Finite F] [Algebra (ZMod p) F]

/-- Over a finite field, the character `traceChar` is nontrivial. -/
theorem traceChar_ne_one : traceChar F hζ ≠ 1 :=
  (traceChar_eq_one_iff hζ).not.mpr (Algebra.trace_ne_zero _ _)

/-- Over a finite field, the character `traceChar` is primitive. -/
theorem isPrimitive_traceChar : IsPrimitive (traceChar F hζ) :=
  IsPrimitive.of_ne_one (traceChar_ne_one hζ)

/-- Over a finite field, the character `traceChar` is invariant under the Frobenius
`x ↦ x ^ p`. -/
theorem traceChar_apply_pow (x : F) : traceChar F hζ (x ^ p) = traceChar F hζ x := by
  have : CharP F p := (Algebra.charP_iff (ZMod p) F p).mp (ZMod.charP p)
  rw [← traceChar_apply_algEquiv hζ (FiniteField.frobeniusAlgEquiv (ZMod p) F p) x,
    FiniteField.frobeniusAlgEquiv_apply, ZMod.card]

end Field

end AddChar
