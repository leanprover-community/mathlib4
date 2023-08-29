/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.Algebra.CharP.CharAndCard

#align_import number_theory.legendre_symbol.gauss_sum from "leanprover-community/mathlib"@"e3f4be1fcb5376c4948d7f095bec45350bfb9d1a"

/-!
# Gauss sums

We define the Gauss sum associated to a multiplicative and an additive
character of a finite field and prove some results about them.

## Main definition

Let `R` be a finite commutative ring and let `R'` be another commutative ring.
If `χ` is a multiplicative character `R → R'` (type `MulChar R R'`) and `ψ`
is an additive character `R → R'` (type `AddChar R R'`, which abbreviates
`(Multiplicative R) →* R'`), then the *Gauss sum* of `χ` and `ψ` is `∑ a, χ a * ψ a`.

## Main results

Some important results are as follows.

* `gaussSum_mul_gaussSum_eq_card`: The product of the Gauss
  sums of `χ` and `ψ` and that of `χ⁻¹` and `ψ⁻¹` is the cardinality
  of the source ring `R` (if `χ` is nontrivial, `ψ` is primitive and `R` is a field).
* `gaussSum_sq`: The square of the Gauss sum is `χ(-1)` times
  the cardinality of `R` if in addition `χ` is a quadratic character.
* `MulChar.IsQuadratic.gaussSum_frob`: For a quadratic character `χ`, raising
  the Gauss sum to the `p`th power (where `p` is the characteristic of
  the target ring `R'`) multiplies it by `χ p`.
* `Char.card_pow_card`: When `F` and `F'` are finite fields and `χ : F → F'`
  is a nontrivial quadratic character, then `(χ (-1) * #F)^(#F'/2) = χ #F'`.
* `FiniteField.two_pow_card`: For every finite field `F` of odd characteristic,
  we have `2^(#F/2) = χ₈#F` in `F`.

This machinery can be used to derive (a generalization of) the Law of
Quadratic Reciprocity.

## Tags

additive character, multiplicative character, Gauss sum
-/


universe u v

open scoped BigOperators

open AddChar MulChar

section GaussSumDef

-- `R` is the domain of the characters
variable {R : Type u} [CommRing R] [Fintype R]

-- `R'` is the target of the characters
variable {R' : Type v} [CommRing R']

/-!
### Definition and first properties
-/


/-- Definition of the Gauss sum associated to a multiplicative and an additive character. -/
def gaussSum (χ : MulChar R R') (ψ : AddChar R R') : R' :=
  ∑ a, χ a * ψ a
#align gauss_sum gaussSum

/-- Replacing `ψ` by `mulShift ψ a` and multiplying the Gauss sum by `χ a` does not change it. -/
theorem gaussSum_mulShift (χ : MulChar R R') (ψ : AddChar R R') (a : Rˣ) :
    χ a * gaussSum χ (mulShift ψ a) = gaussSum χ ψ := by
  simp only [gaussSum, mulShift_apply, Finset.mul_sum]
  -- ⊢ ∑ x : R, ↑χ ↑a * (↑χ x * ↑ψ (↑a * x)) = ∑ x : R, ↑χ x * ↑ψ x
  simp_rw [← mul_assoc, ← map_mul]
  -- ⊢ ∑ x : R, ↑χ (↑a * x) * ↑ψ (↑a * x) = ∑ x : R, ↑χ x * ↑ψ x
  exact Fintype.sum_bijective _ a.mulLeft_bijective _ _ fun x => rfl
  -- 🎉 no goals
#align gauss_sum_mul_shift gaussSum_mulShift

end GaussSumDef

/-!
### The product of two Gauss sums
-/


section GaussSumProd

-- In the following, we need `R` to be a finite field and `R'` to be a domain.
variable {R : Type u} [Field R] [Fintype R] {R' : Type v} [CommRing R'] [IsDomain R']

-- A helper lemma for `gaussSum_mul_gaussSum_eq_card` below
-- Is this useful enough in other contexts to be public?
private theorem gaussSum_mul_aux {χ : MulChar R R'} (hχ : IsNontrivial χ) (ψ : AddChar R R')
    (b : R) : ∑ a, χ (a * b⁻¹) * ψ (a - b) = ∑ c, χ c * ψ (b * (c - 1)) := by
  cases' eq_or_ne b 0 with hb hb
  -- ⊢ ∑ a : R, ↑χ (a * b⁻¹) * ↑ψ (a - b) = ∑ c : R, ↑χ c * ↑ψ (b * (c - 1))
  · -- case `b = 0`
    simp only [hb, inv_zero, mul_zero, MulChar.map_zero, zero_mul,
      Finset.sum_const_zero, map_zero_one, mul_one]
    exact (hχ.sum_eq_zero).symm
    -- 🎉 no goals
  · -- case `b ≠ 0`
    refine' (Fintype.sum_bijective _ (mulLeft_bijective₀ b hb) _ _ fun x => _).symm
    -- ⊢ ↑χ x * ↑ψ (b * (x - 1)) = ↑χ ((fun x x_1 => x * x_1) b x * b⁻¹) * ↑ψ ((fun x …
    rw [mul_assoc, mul_comm x, ← mul_assoc, mul_inv_cancel hb, one_mul, mul_sub, mul_one]
    -- 🎉 no goals

/-- We have `gaussSum χ ψ * gaussSum χ⁻¹ ψ⁻¹ = Fintype.card R`
when `χ` is nontrivial and `ψ` is primitive (and `R` is a field). -/
theorem gaussSum_mul_gaussSum_eq_card {χ : MulChar R R'} (hχ : IsNontrivial χ) {ψ : AddChar R R'}
    (hψ : IsPrimitive ψ) : gaussSum χ ψ * gaussSum χ⁻¹ ψ⁻¹ = Fintype.card R := by
  simp only [gaussSum, AddChar.inv_apply, Finset.sum_mul, Finset.mul_sum, MulChar.inv_apply']
  -- ⊢ ∑ x : R, ∑ x_1 : R, ↑χ x_1 * ↑ψ x_1 * (↑χ x⁻¹ * ↑ψ (-x)) = ↑(Fintype.card R)
  conv =>
    lhs; congr; next => skip
    ext; congr; next => skip
    ext
    rw [mul_mul_mul_comm, ← map_mul, ← map_add_mul, ← sub_eq_add_neg]
--  conv in _ * _ * (_ * _) => rw [mul_mul_mul_comm, ← map_mul, ← map_add_mul, ← sub_eq_add_neg]
  simp_rw [gaussSum_mul_aux hχ ψ]
  -- ⊢ ∑ x : R, ∑ x_1 : R, ↑χ x_1 * ↑ψ (x * (x_1 - 1)) = ↑(Fintype.card R)
  rw [Finset.sum_comm]
  -- ⊢ ∑ y : R, ∑ x : R, ↑χ y * ↑ψ (x * (y - 1)) = ↑(Fintype.card R)
  classical -- to get `[DecidableEq R]` for `sum_mulShift`
  simp_rw [← Finset.mul_sum, sum_mulShift _ hψ, sub_eq_zero, apply_ite, Nat.cast_zero, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ (1 : R)]
  simp only [Finset.mem_univ, map_one, one_mul, if_true]
#align gauss_sum_mul_gauss_sum_eq_card gaussSum_mul_gaussSum_eq_card

/-- When `χ` is a nontrivial quadratic character, then the square of `gaussSum χ ψ`
is `χ(-1)` times the cardinality of `R`. -/
theorem gaussSum_sq {χ : MulChar R R'} (hχ₁ : IsNontrivial χ) (hχ₂ : IsQuadratic χ)
    {ψ : AddChar R R'} (hψ : IsPrimitive ψ) : gaussSum χ ψ ^ 2 = χ (-1) * Fintype.card R := by
  rw [pow_two, ← gaussSum_mul_gaussSum_eq_card hχ₁ hψ, hχ₂.inv, mul_rotate']
  -- ⊢ gaussSum χ ψ * gaussSum χ ψ = gaussSum χ ψ * (gaussSum χ ψ⁻¹ * ↑χ (-1))
  congr
  -- ⊢ gaussSum χ ψ = gaussSum χ ψ⁻¹ * ↑χ (-1)
  rw [mul_comm, ← gaussSum_mulShift _ _ (-1 : Rˣ), inv_mulShift]
  -- ⊢ ↑χ ↑(-1) * gaussSum χ (mulShift ψ ↑(-1)) = ↑χ (-1) * gaussSum χ (mulShift ψ  …
  rfl
  -- 🎉 no goals
#align gauss_sum_sq gaussSum_sq

end GaussSumProd

/-!
### Gauss sums and Frobenius
-/


section gaussSum_frob

variable {R : Type u} [CommRing R] [Fintype R] {R' : Type v} [CommRing R']

-- We assume that the target ring `R'` has prime characteristic `p`.
variable (p : ℕ) [fp : Fact p.Prime] [hch : CharP R' p]

/-- When `R'` has prime characteristic `p`, then the `p`th power of the Gauss sum
of `χ` and `ψ` is the Gauss sum of `χ^p` and `ψ^p`. -/
theorem gaussSum_frob (χ : MulChar R R') (ψ : AddChar R R') :
    gaussSum χ ψ ^ p = gaussSum (χ ^ p) (ψ ^ p) := by
  rw [← frobenius_def, gaussSum, gaussSum, map_sum]
  -- ⊢ ∑ x : R, ↑(frobenius R' p) (↑χ x * ↑ψ x) = ∑ a : R, ↑(χ ^ p) a * ↑(ψ ^ p) a
  simp_rw [pow_apply' χ fp.1.pos, map_mul, frobenius_def]
  -- ⊢ ∑ x : R, ↑χ x ^ p * ↑ψ x ^ p = ∑ x : R, ↑χ x ^ p * ↑(ψ ^ p) x
  rfl
  -- 🎉 no goals
#align gauss_sum_frob gaussSum_frob

/-- For a quadratic character `χ` and when the characteristic `p` of the target ring
is a unit in the source ring, the `p`th power of the Gauss sum of`χ` and `ψ` is
`χ p` times the original Gauss sum. -/
-- Porting note: Added `nonrec` to avoid error `failed to prove termination`
nonrec theorem MulChar.IsQuadratic.gaussSum_frob (hp : IsUnit (p : R)) {χ : MulChar R R'}
    (hχ : IsQuadratic χ) (ψ : AddChar R R') : gaussSum χ ψ ^ p = χ p * gaussSum χ ψ := by
  rw [gaussSum_frob, pow_mulShift, hχ.pow_char p, ← gaussSum_mulShift χ ψ hp.unit, ← mul_assoc,
    hp.unit_spec, ← pow_two, ← pow_apply' _ (by norm_num : 0 < 2), hχ.sq_eq_one, ← hp.unit_spec,
    one_apply_coe, one_mul]
#align mul_char.is_quadratic.gauss_sum_frob MulChar.IsQuadratic.gaussSum_frob

/-- For a quadratic character `χ` and when the characteristic `p` of the target ring
is a unit in the source ring and `n` is a natural number, the `p^n`th power of the Gauss
sum of`χ` and `ψ` is `χ (p^n)` times the original Gauss sum. -/
theorem MulChar.IsQuadratic.gaussSum_frob_iter (n : ℕ) (hp : IsUnit (p : R)) {χ : MulChar R R'}
    (hχ : IsQuadratic χ) (ψ : AddChar R R') :
    gaussSum χ ψ ^ p ^ n = χ ((p : R) ^ n) * gaussSum χ ψ := by
  induction' n with n ih
  -- ⊢ gaussSum χ ψ ^ p ^ Nat.zero = ↑χ (↑p ^ Nat.zero) * gaussSum χ ψ
  · rw [pow_zero, pow_one, pow_zero, MulChar.map_one, one_mul]
    -- 🎉 no goals
  · rw [pow_succ, mul_comm p, pow_mul, ih, mul_pow, hχ.gaussSum_frob _ hp, ← mul_assoc, pow_succ,
      mul_comm (p : R), map_mul, ← pow_apply' χ fp.1.pos ((p : R) ^ n), hχ.pow_char p]
#align mul_char.is_quadratic.gauss_sum_frob_iter MulChar.IsQuadratic.gaussSum_frob_iter

end gaussSum_frob

/-!
### Values of quadratic characters
-/


section GaussSumValues

variable {R : Type u} [CommRing R] [Fintype R] {R' : Type v} [CommRing R'] [IsDomain R']

/-- If the square of the Gauss sum of a quadratic character is `χ(-1) * #R`,
then we get, for all `n : ℕ`, the relation `(χ(-1) * #R) ^ (p^n/2) = χ(p^n)`,
where `p` is the (odd) characteristic of the target ring `R'`.
This version can be used when `R` is not a field, e.g., `ℤ/8ℤ`. -/
theorem Char.card_pow_char_pow {χ : MulChar R R'} (hχ : IsQuadratic χ) (ψ : AddChar R R') (p n : ℕ)
    [fp : Fact p.Prime] [hch : CharP R' p] (hp : IsUnit (p : R)) (hp' : p ≠ 2)
    (hg : gaussSum χ ψ ^ 2 = χ (-1) * Fintype.card R) :
    (χ (-1) * Fintype.card R) ^ (p ^ n / 2) = χ ((p : R) ^ n) := by
  have : gaussSum χ ψ ≠ 0 := by
    intro hf; rw [hf, zero_pow (by norm_num : 0 < 2), eq_comm, mul_eq_zero] at hg
    exact not_isUnit_prime_of_dvd_card p
        ((CharP.cast_eq_zero_iff R' p _).mp <| hg.resolve_left (isUnit_one.neg.map χ).ne_zero) hp
  rw [← hg]; apply mul_right_cancel₀ this
  -- ⊢ (gaussSum χ ψ ^ 2) ^ (p ^ n / 2) = ↑χ (↑p ^ n)
             -- ⊢ (gaussSum χ ψ ^ 2) ^ (p ^ n / 2) * gaussSum χ ψ = ↑χ (↑p ^ n) * gaussSum χ ψ
  rw [← hχ.gaussSum_frob_iter p n hp ψ, ← pow_mul, mul_comm, ← pow_succ,
    Nat.two_mul_div_two_add_one_of_odd (fp.1.eq_two_or_odd'.resolve_left hp').pow]
#align char.card_pow_char_pow Char.card_pow_char_pow

/-- When `F` and `F'` are finite fields and `χ : F → F'` is a nontrivial quadratic character,
then `(χ(-1) * #F)^(#F'/2) = χ(#F')`. -/
theorem Char.card_pow_card {F : Type*} [Field F] [Fintype F] {F' : Type*} [Field F'] [Fintype F']
    {χ : MulChar F F'} (hχ₁ : IsNontrivial χ) (hχ₂ : IsQuadratic χ)
    (hch₁ : ringChar F' ≠ ringChar F) (hch₂ : ringChar F' ≠ 2) :
    (χ (-1) * Fintype.card F) ^ (Fintype.card F' / 2) = χ (Fintype.card F') := by
  obtain ⟨n, hp, hc⟩ := FiniteField.card F (ringChar F)
  -- ⊢ (↑χ (-1) * ↑(Fintype.card F)) ^ (Fintype.card F' / 2) = ↑χ ↑(Fintype.card F')
  obtain ⟨n', hp', hc'⟩ := FiniteField.card F' (ringChar F')
  -- ⊢ (↑χ (-1) * ↑(Fintype.card F)) ^ (Fintype.card F' / 2) = ↑χ ↑(Fintype.card F')
  let ψ := primitiveCharFiniteField F F' hch₁
  -- ⊢ (↑χ (-1) * ↑(Fintype.card F)) ^ (Fintype.card F' / 2) = ↑χ ↑(Fintype.card F')
  -- Porting note: this was a `let` but then Lean would time out at
  -- unification so it is changed to as `set` and `FF'` is replaced by its
  -- definition before unification
  set FF' := CyclotomicField ψ.n F' with FF'_def
  -- ⊢ (↑χ (-1) * ↑(Fintype.card F)) ^ (Fintype.card F' / 2) = ↑χ ↑(Fintype.card F')
  have hchar := Algebra.ringChar_eq F' FF'
  -- ⊢ (↑χ (-1) * ↑(Fintype.card F)) ^ (Fintype.card F' / 2) = ↑χ ↑(Fintype.card F')
  apply (algebraMap F' FF').injective
  -- ⊢ ↑(algebraMap F' FF') ((↑χ (-1) * ↑(Fintype.card F)) ^ (Fintype.card F' / 2)) …
  rw [map_pow, map_mul, map_natCast, hc', hchar, Nat.cast_pow]
  -- ⊢ (↑(algebraMap F' FF') (↑χ (-1)) * ↑(Fintype.card F)) ^ (ringChar FF' ^ ↑n' / …
  simp only [← MulChar.ringHomComp_apply]
  -- ⊢ (↑(ringHomComp χ (algebraMap F' (CyclotomicField (PrimitiveAddChar.n (primit …
  haveI := Fact.mk hp'
  -- ⊢ (↑(ringHomComp χ (algebraMap F' (CyclotomicField (PrimitiveAddChar.n (primit …
  haveI := Fact.mk (hchar.subst hp')
  -- ⊢ (↑(ringHomComp χ (algebraMap F' (CyclotomicField (PrimitiveAddChar.n (primit …
  rw [Ne, ← Nat.prime_dvd_prime_iff_eq hp' hp, ← isUnit_iff_not_dvd_char, hchar] at hch₁
  -- ⊢ (↑(ringHomComp χ (algebraMap F' (CyclotomicField (PrimitiveAddChar.n (primit …
  -- Porting note: original proof is below and, as noted above, `FF'` needs to
  -- be replaced by its definition before unification to avoid time out
  -- exact Char.card_pow_char_pow (hχ₂.comp _) ψ.char (ringChar FF') n' hch₁ (hchar ▸ hch₂)
  --      (gaussSum_sq (hχ₁.comp <| RingHom.injective _) (hχ₂.comp _) ψ.prim)
  have := Char.card_pow_char_pow (hχ₂.comp (algebraMap F' FF')) ψ.char
    (ringChar FF') n' hch₁ (hchar ▸ hch₂)
    (gaussSum_sq (hχ₁.comp <| RingHom.injective _) (hχ₂.comp _) ψ.prim)
  simp_rw [FF'_def] at this
  -- ⊢ (↑(ringHomComp χ (algebraMap F' (CyclotomicField (PrimitiveAddChar.n (primit …
  exact this
  -- 🎉 no goals
#align char.card_pow_card Char.card_pow_card

end GaussSumValues

section GaussSumTwo

/-!
### The quadratic character of 2

This section proves the following result.

For every finite field `F` of odd characteristic, we have `2^(#F/2) = χ₈#F` in `F`.
This can be used to show that the quadratic character of `F` takes the value
`χ₈#F` at `2`.

The proof uses the Gauss sum of `χ₈` and a primitive additive character on `ℤ/8ℤ`;
in this way, the result is reduced to `card_pow_char_pow`.
-/


open ZMod

-- Porting note: This proof is _really_ slow, maybe it should be broken into several lemmas
-- See https://github.com/leanprover-community/mathlib4/issues/5028
set_option maxHeartbeats 800000 in
/-- For every finite field `F` of odd characteristic, we have `2^(#F/2) = χ₈#F` in `F`. -/
theorem FiniteField.two_pow_card {F : Type*} [Fintype F] [Field F] (hF : ringChar F ≠ 2) :
    (2 : F) ^ (Fintype.card F / 2) = χ₈ (Fintype.card F) := by
  have hp2 : ∀ n : ℕ, (2 ^ n : F) ≠ 0 := fun n => pow_ne_zero n (Ring.two_ne_zero hF)
  -- ⊢ 2 ^ (Fintype.card F / 2) = ↑(↑χ₈ ↑(Fintype.card F))
  obtain ⟨n, hp, hc⟩ := FiniteField.card F (ringChar F)
  -- ⊢ 2 ^ (Fintype.card F / 2) = ↑(↑χ₈ ↑(Fintype.card F))

  -- we work in `FF`, the eighth cyclotomic field extension of `F`
  -- Porting note: was
  -- let FF := (Polynomial.cyclotomic 8 F).SplittingField
  -- but we want to unify with `CyclotomicField` below.
  let FF := CyclotomicField 8 F
  -- ⊢ 2 ^ (Fintype.card F / 2) = ↑(↑χ₈ ↑(Fintype.card F))
  haveI : Polynomial.IsSplittingField F FF (Polynomial.cyclotomic 8 F) :=
    Polynomial.IsSplittingField.splittingField _
  haveI : FiniteDimensional F FF :=
    Polynomial.IsSplittingField.finiteDimensional FF (Polynomial.cyclotomic 8 F)
  haveI : Fintype FF := FiniteDimensional.fintypeOfFintype F FF
  -- ⊢ 2 ^ (Fintype.card F / 2) = ↑(↑χ₈ ↑(Fintype.card F))
  have hchar := Algebra.ringChar_eq F FF
  -- ⊢ 2 ^ (Fintype.card F / 2) = ↑(↑χ₈ ↑(Fintype.card F))
  have FFp := hchar.subst hp
  -- ⊢ 2 ^ (Fintype.card F / 2) = ↑(↑χ₈ ↑(Fintype.card F))
  haveI := Fact.mk FFp
  -- ⊢ 2 ^ (Fintype.card F / 2) = ↑(↑χ₈ ↑(Fintype.card F))
  have hFF := ne_of_eq_of_ne hchar.symm hF
  -- ⊢ 2 ^ (Fintype.card F / 2) = ↑(↑χ₈ ↑(Fintype.card F))
  -- `ringChar FF ≠ 2`
  have hu : IsUnit (ringChar FF : ZMod 8) := by
    rw [isUnit_iff_not_dvd_char, ringChar_zmod_n]
    rw [Ne, ← Nat.prime_dvd_prime_iff_eq FFp Nat.prime_two] at hFF
    change ¬_ ∣ 2 ^ 3
    exact mt FFp.dvd_of_dvd_pow hFF

  -- there is a primitive additive character `ℤ/8ℤ → FF`, sending `a + 8ℤ ↦ τ^a`
  -- with a primitive eighth root of unity `τ`
  -- Porting note: The type is actually `PrimitiveAddChar (ZMod (8 : ℕ+)) F`, but this seems faster.
  let ψ₈ : PrimitiveAddChar (ZMod 8) F :=
    primitiveZModChar 8 F (by convert hp2 3 using 1; norm_cast)
  -- Porting note: unifying this is very slow, so only do it once.
  let ψ₈char : AddChar (ZMod 8) FF := ψ₈.char
  -- ⊢ 2 ^ (Fintype.card F / 2) = ↑(↑χ₈ ↑(Fintype.card F))
  let τ : FF := ψ₈char 1
  -- ⊢ 2 ^ (Fintype.card F / 2) = ↑(↑χ₈ ↑(Fintype.card F))
  have τ_spec : τ ^ 4 = -1 := by
    refine (sq_eq_one_iff.1 ?_).resolve_left ?_
    · rw [← pow_mul, ← map_nsmul_pow ψ₈char, AddChar.IsPrimitive.zmod_char_eq_one_iff 8 ψ₈.prim]
      decide
    · rw [← map_nsmul_pow ψ₈char, AddChar.IsPrimitive.zmod_char_eq_one_iff 8 ψ₈.prim]
      decide

  -- we consider `χ₈` as a multiplicative character `ℤ/8ℤ → FF`
  let χ := χ₈.ringHomComp (Int.castRingHom FF)
  -- ⊢ 2 ^ (Fintype.card F / 2) = ↑(↑χ₈ ↑(Fintype.card F))
  have hχ : χ (-1) = 1 := Int.cast_one
  -- ⊢ 2 ^ (Fintype.card F / 2) = ↑(↑χ₈ ↑(Fintype.card F))
  have hq : IsQuadratic χ := isQuadratic_χ₈.comp _
  -- ⊢ 2 ^ (Fintype.card F / 2) = ↑(↑χ₈ ↑(Fintype.card F))

  -- we now show that the Gauss sum of `χ` and `ψ₈` has the relevant property
  have hg : gaussSum χ ψ₈char ^ 2 = χ (-1) * Fintype.card (ZMod 8) := by
    have _ := congr_arg (· ^ 2) (Fin.sum_univ_eight fun x => (χ₈ x : FF) * τ ^ x.1)
    have h₁ : (fun i : Fin 8 => ↑(χ₈ i) * τ ^ i.val) = (fun a : ZMod 8 => χ a * ↑(ψ₈char a)) := by
      -- Porting note: original proof
      -- ext; congr; apply pow_one
      ext (x : Fin 8); rw [← map_nsmul_pow ψ₈char]; congr 2;
      rw [Nat.smul_one_eq_coe, Fin.cast_val_eq_self x]
    have h₂ : (0 + 1 * τ ^ 1 + 0 + -1 * τ ^ 3 + 0 + -1 * τ ^ 5 + 0 + 1 * τ ^ 7) ^ 2 =
        8 + (τ ^ 4 + 1) * (τ ^ 10 - 2 * τ ^ 8 - 2 * τ ^ 6 + 6 * τ ^ 4 + τ ^ 2 - 8) := by ring
    have h₃ : 8 + (τ ^ 4 + 1) * (τ ^ 10 - 2 * τ ^ 8 - 2 * τ ^ 6 + 6 * τ ^ 4 + τ ^ 2 - 8) = ↑8 := by
      rw [τ_spec]; norm_num
    have h₄ : (0 + 1 * τ ^ 1 + 0 + -1 * τ ^ 3 + 0 + -1 * τ ^ 5 + 0 + 1 * τ ^ 7) ^ 2 = ↑8 := by
      rw [← h₃, ← h₂]
    have h₅ :
        (↑(χ₈ 0) * τ ^ 0 + ↑(χ₈ 1) * τ ^ 1 + ↑(χ₈ 2) * τ ^ 2 + ↑(χ₈ 3) * τ ^ 3 + ↑(χ₈ 4) * τ ^ 4 +
        ↑(χ₈ 5) * τ ^ 5 + ↑(χ₈ 6) * τ ^ 6 + ↑(χ₈ 7) * τ ^ 7) ^ 2 = 8 := by
      -- Porting note: original proof
      --  simp [← h₄, χ₈_apply, Matrix.cons_val_zero, algebraMap.coe_zero, zero_mul,
      -- Matrix.cons_val_one, Matrix.head_cons, algebraMap.coe_one, Matrix.cons_vec_bit0_eq_alt0,
      -- Matrix.cons_vecAppend, Matrix.cons_vecAlt0, Matrix.cons_vec_bit1_eq_alt1,
      -- Matrix.cons_vecAlt1, Int.cast_neg]
      simp_rw [χ₈_apply]
      rw [← h₄]
      dsimp only
      congr
      · rw [Matrix.cons_val_zero]; simp
      · simp only [Matrix.vecCons, ne_eq, Nat.cast_ofNat, id_eq, eq_mpr_eq_cast, mul_eq_zero,
          zero_lt_two, pow_eq_zero_iff]
        left
        rw [← Int.cast_zero (R := FF)]
        exact congr_arg Int.cast rfl
      · simp only [Matrix.vecCons]
        rw [show (-1 : FF) = ↑(- 1 : ℤ) by simp only [Int.cast_neg, Int.cast_one]]
        exact congr_arg Int.cast rfl
      · simp only [Matrix.vecCons, ne_eq, Nat.cast_ofNat, id_eq, eq_mpr_eq_cast, mul_eq_zero,
          zero_lt_two, pow_eq_zero_iff]
        left
        rw [← Int.cast_zero (R := FF)]
        exact congr_arg Int.cast rfl
      · simp only [Matrix.vecCons]
        rw [show (-1 : FF) = ↑(- 1 : ℤ) by simp only [Int.cast_neg, Int.cast_one]]
        exact congr_arg Int.cast rfl
      · simp only [Matrix.vecCons, ne_eq, Nat.cast_ofNat, id_eq, eq_mpr_eq_cast, mul_eq_zero,
          zero_lt_two, pow_eq_zero_iff]
        left
        rw [← Int.cast_zero (R := FF)]
        exact congr_arg Int.cast rfl
    -- Porting note: original proof
    -- simpa only [hχ, one_mul, card, gaussSum, ← h₅, h₁] using h
    rw [gaussSum, hχ, one_mul, ZMod.card, Nat.cast_ofNat, ← h₅]
    simp_rw [← h₁]
    rw [Fin.sum_univ_eight]
    rfl

  -- this allows us to apply `card_pow_char_pow` to our situation
  have h := Char.card_pow_char_pow (R := ZMod 8) hq ψ₈char (ringChar FF) n hu hFF hg
  -- ⊢ 2 ^ (Fintype.card F / 2) = ↑(↑χ₈ ↑(Fintype.card F))
  rw [ZMod.card, ← hchar, hχ, one_mul, ← hc, ← Nat.cast_pow (ringChar F), ← hc] at h
  -- ⊢ 2 ^ (Fintype.card F / 2) = ↑(↑χ₈ ↑(Fintype.card F))

  -- finally, we change `2` to `8` on the left hand side
  convert_to (8 : F) ^ (Fintype.card F / 2) = _
  -- ⊢ 2 ^ (Fintype.card F / 2) = 8 ^ (Fintype.card F / 2)
  · rw [(by norm_num : (8 : F) = 2 ^ 2 * 2), mul_pow,
      (FiniteField.isSquare_iff hF <| hp2 2).mp ⟨2, pow_two 2⟩, one_mul]
  apply (algebraMap F FF).injective
  -- ⊢ ↑(algebraMap F FF) (8 ^ (Fintype.card F / 2)) = ↑(algebraMap F FF) ↑(↑χ₈ ↑(F …
  simp only [map_pow, map_ofNat, map_intCast]
  -- ⊢ 8 ^ (Fintype.card F / 2) = ↑(↑χ₈ ↑(Fintype.card F))
  simp only [Nat.cast_ofNat, ringHomComp_apply, eq_intCast] at h
  -- ⊢ 8 ^ (Fintype.card F / 2) = ↑(↑χ₈ ↑(Fintype.card F))
  exact h
  -- 🎉 no goals
#align finite_field.two_pow_card FiniteField.two_pow_card

end GaussSumTwo
