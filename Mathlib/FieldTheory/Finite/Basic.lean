/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Joey van Langen, Casper Putz
-/
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.IntegralDomain
import Mathlib.Tactic.ApplyFun

#align_import field_theory.finite.basic from "leanprover-community/mathlib"@"12a85fac627bea918960da036049d611b1a3ee43"

/-!
# Finite fields

This file contains basic results about finite fields.
Throughout most of this file, `K` denotes a finite field
and `q` is notation for the cardinality of `K`.

See `RingTheory.IntegralDomain` for the fact that the unit group of a finite field is a
cyclic group, as well as the fact that every finite integral domain is a field
(`Fintype.fieldOfDomain`).

## Main results

1. `Fintype.card_units`: The unit group of a finite field has cardinality `q - 1`.
2. `sum_pow_units`: The sum of `x^i`, where `x` ranges over the units of `K`, is
   - `q-1` if `q-1 ∣ i`
   - `0`   otherwise
3. `FiniteField.card`: The cardinality `q` is a power of the characteristic of `K`.
   See `FiniteField.card'` for a variant.

## Notation

Throughout most of this file, `K` denotes a finite field
and `q` is notation for the cardinality of `K`.

## Implementation notes

While `Fintype Kˣ` can be inferred from `Fintype K` in the presence of `DecidableEq K`,
in this file we take the `Fintype Kˣ` argument directly to reduce the chance of typeclass
diamonds, as `Fintype` carries data.

-/


variable {K : Type*} {R : Type*}

-- mathport name: exprq
local notation "q" => Fintype.card K

open Finset

open scoped BigOperators Polynomial

namespace FiniteField

section Polynomial

-- 6. Needs refactoring
-- Next step: check that every lemma looks the same binder-wise!


variable [CommRing R] [IsDomain R]

open Polynomial

/-- The cardinality of a field is at most `n` times the cardinality of the image of a degree `n`
  polynomial -/
theorem card_image_polynomial_eval [DecidableEq R] [Fintype R] {p : R[X]} (hp : 0 < p.degree) :
    Fintype.card R ≤ natDegree p * (univ.image fun x => eval x p).card := sorry

/-- If `f` and `g` are quadratic polynomials, then the `f.eval a + g.eval b = 0` has a solution. -/
theorem exists_root_sum_quadratic {R} [CommRing R] [IsDomain R] [Fintype R] {f g : R[X]} (hf2 : degree f = 2) (hg2 : degree g = 2)
    (hR : Fintype.card R % 2 = 1) : ∃ a b, f.eval a + g.eval b = 0 :=
sorry
#align finite_field.exists_root_sum_quadratic FiniteField.exists_root_sum_quadratic

end Polynomial

theorem prod_univ_units_id_eq_neg_one [CommRing K] [NoZeroDivisors K] [Fintype Kˣ] :
    ∏ x : Kˣ, x = (-1 : Kˣ) := by sorry
#align finite_field.prod_univ_units_id_eq_neg_one FiniteField.prod_univ_units_id_eq_neg_one

theorem card_cast_subgroup_card_ne_zero [Ring K] [IsDomain K]
    (G : Subgroup Kˣ) [Fintype G] : (Fintype.card G : K) ≠ 0 := sorry

/-- The sum of a nontrivial subgroup of the units of a field is zero. -/
theorem sum_subgroup_units_eq_zero [Ring K] [NoZeroDivisors K]
    {G : Subgroup Kˣ} [Fintype G] (hg : G ≠ ⊥) :
    ∑ x : G, (x.val : K) = 0 := sorry

/-- The sum of a subgroup of the units of a field is 1 if the subgroup is trivial and 1 otherwise -/
@[simp]
theorem sum_subgroup_units [Ring K] [NoZeroDivisors K]
    {G : Subgroup Kˣ} [Fintype G] [Decidable (G = ⊥)] :
    ∑ x : G, (x.val : K) = if G = ⊥ then 1 else 0 := by
sorry

@[simp]
theorem sum_subgroup_pow_eq_zero [CommRing K] [NoZeroDivisors K]
    {G : Subgroup Kˣ} [Fintype G] {k : ℕ} (k_pos : k ≠ 0) (k_lt_card_G : k < Fintype.card G) :
    ∑ x : G, ((x : Kˣ) : K) ^ k = 0 := sorry

section

variable [GroupWithZero K] [Fintype K]

theorem pow_card_sub_one_eq_one (a : K) (ha : a ≠ 0) : a ^ (q - 1) = 1 := sorry

theorem pow_card (a : K) : a ^ q = a := sorry

theorem pow_card_pow (n : ℕ) (a : K) : a ^ q ^ n = a := sorry

end

section

variable (K) [Ring K] [NoZeroDivisors K] [Fintype K]

-- this lemma is stated weird!
theorem card (p : ℕ) [CharP K p] [Nontrivial K] : ∃ n : ℕ+, Nat.Prime p ∧ q = p ^ (n : ℕ) := by
sorry

-- this statement doesn't use `q` because we want `K` to be an explicit parameter
theorem card' [Nontrivial K] : ∃ (p : ℕ) (n : ℕ+), Nat.Prime p ∧ Fintype.card K = p ^ (n : ℕ) :=
sorry

end

section

variable [Fintype K]


theorem forall_pow_eq_one_iff [Field K] (i : ℕ) : (∀ x : Kˣ, x ^ i = 1) ↔ q - 1 ∣ i := sorry

/-- The sum of `x ^ i` as `x` ranges over the units of a finite field of cardinality `q`
is equal to `0` unless `(q - 1) ∣ i`, in which case the sum is `q - 1`. -/
-- 6.
theorem sum_pow_units [Field K] [DecidableEq K] (i : ℕ) :
    (∑ x : Kˣ, (x ^ i : K)) = if q - 1 ∣ i then -1 else 0 := by
  let φ : Kˣ →* K :=
    { toFun := fun x => x ^ i
      map_one' := by simp
      map_mul' := by intros; simp [mul_pow] }
  have : Decidable (φ = 1) := by classical infer_instance
  calc (∑ x : Kˣ, φ x) = if φ = 1 then Fintype.card Kˣ else 0 := sum_hom_units φ
      _ = if q - 1 ∣ i then -1 else 0 := by
        suffices q - 1 ∣ i ↔ φ = 1 by
          simp only [this]
          split_ifs; swap
          · exact Nat.cast_zero
          · rw [Fintype.card_units, Nat.cast_sub,
              CharP.cast_card_eq_zero, Nat.cast_one, zero_sub]
            show 1 ≤ q; exact Fintype.card_pos_iff.mpr ⟨0⟩
        rw [← forall_pow_eq_one_iff, FunLike.ext_iff]
        apply forall_congr'; intro x; simp [Units.ext_iff]
#align finite_field.sum_pow_units FiniteField.sum_pow_units

end

section

variable [Fintype K] [Field K]

/-- The sum of `x ^ i` as `x` ranges over a finite field of cardinality `q`
is equal to `0` if `i < q - 1`. -/
theorem sum_pow_lt_card_sub_one (i : ℕ) (h : i < q - 1) : ∑ x : K, x ^ i = 0 := by sorry

end

#align finite_field.sum_pow_lt_card_sub_one FiniteField.sum_pow_lt_card_sub_one

open Polynomial

section

variable (K' : Type*) [Field K'] {p n : ℕ}

theorem X_pow_card_sub_X_natDegree_eq (hp : 1 < p) : (X ^ p - X : K'[X]).natDegree = p := by
sorry

theorem X_pow_card_pow_sub_X_natDegree_eq (hn : n ≠ 0) (hp : 1 < p) :
    (X ^ p ^ n - X : K'[X]).natDegree = p ^ n := sorry

theorem X_pow_card_sub_X_ne_zero (hp : 1 < p) : (X ^ p - X : K'[X]) ≠ 0 := sorry

theorem X_pow_card_pow_sub_X_ne_zero (hn : n ≠ 0) (hp : 1 < p) : (X ^ p ^ n - X : K'[X]) ≠ 0 := sorry

end

variable (p : ℕ) [Field K] [Fintype K] [Fact p.Prime] [Algebra (ZMod p) K]

theorem roots_X_pow_card_sub_X : roots (X ^ q - X : K[X]) = Finset.univ.val := by
sorry

theorem frobenius_pow {p : ℕ} [Fact p.Prime] [CharP K p] {n : ℕ} (hcard : q = p ^ n) :
    frobenius K p ^ n = 1 := by
sorry

theorem expand_card (f : K[X]) : expand K q f = f ^ q := by
sorry

end FiniteField

namespace ZMod

open FiniteField Polynomial

-- this holds for all finite fields actually, so I will generalise; the proof goes by every element
-- being a square in char2. (`isSquareOfChar2`)
theorem sq_add_sq (p : ℕ) [hp : Fact p.Prime] (x : ZMod p) : ∃ a b : ZMod p, a ^ 2 + b ^ 2 = x := by
  cases' hp.1.eq_two_or_odd with hp2 hp_odd
  · subst p
    change Fin 2 at x
    fin_cases x
    · use 0; simp
    · use 0, 1; simp
  let f : (ZMod p)[X] := X ^ 2
  let g : (ZMod p)[X] := X ^ 2 - C x
  obtain ⟨a, b, hab⟩ : ∃ a b, f.eval a + g.eval b = 0 :=
    @exists_root_sum_quadratic _ _ _ _ f g (degree_X_pow 2) (degree_X_pow_sub_C (by decide) _)
      (by rw [ZMod.card, hp_odd])
  refine' ⟨a, b, _⟩
  rw [← sub_eq_zero]
  simpa only [eval_C, eval_X, eval_pow, eval_sub, ← add_sub_assoc] using hab
#align zmod.sq_add_sq ZMod.sq_add_sq

end ZMod

/-- If `p` is a prime natural number and `x` is an integer number, then there exist natural numbers
`a ≤ p / 2` and `b ≤ p / 2` such that `a ^ 2 + b ^ 2 ≡ x [ZMOD p]`. This is a version of
`ZMod.sq_add_sq` with estimates on `a` and `b`. -/
theorem Nat.sq_add_sq_zmodEq (p : ℕ) [Fact p.Prime] (x : ℤ) :
    ∃ a b : ℕ, a ≤ p / 2 ∧ b ≤ p / 2 ∧ (a : ℤ) ^ 2 + (b : ℤ) ^ 2 ≡ x [ZMOD p] := by
  rcases ZMod.sq_add_sq p x with ⟨a, b, hx⟩
  refine ⟨a.valMinAbs.natAbs, b.valMinAbs.natAbs, ZMod.natAbs_valMinAbs_le _,
    ZMod.natAbs_valMinAbs_le _, ?_⟩
  rw [← a.coe_valMinAbs, ← b.coe_valMinAbs] at hx
  push_cast
  rw [sq_abs, sq_abs, ← ZMod.int_cast_eq_int_cast_iff]
  exact_mod_cast hx

/-- If `p` is a prime natural number and `x` is a natural number, then there exist natural numbers
`a ≤ p / 2` and `b ≤ p / 2` such that `a ^ 2 + b ^ 2 ≡ x [MOD p]`. This is a version of
`ZMod.sq_add_sq` with estimates on `a` and `b`. -/
theorem Nat.sq_add_sq_modEq (p : ℕ) [Fact p.Prime] (x : ℕ) :
    ∃ a b : ℕ, a ≤ p / 2 ∧ b ≤ p / 2 ∧ a ^ 2 + b ^ 2 ≡ x [MOD p] := by
  simpa only [← Int.coe_nat_modEq_iff] using Nat.sq_add_sq_zmodEq p x

namespace CharP

theorem sq_add_sq (R : Type*) [CommRing R] [IsDomain R] (p : ℕ) [NeZero p] [CharP R p] (x : ℤ) :
    ∃ a b : ℕ, ((a : R) ^ 2 + (b : R) ^ 2) = x := by
  haveI := char_is_prime_of_pos R p
  obtain ⟨a, b, hab⟩ := ZMod.sq_add_sq p x
  refine' ⟨a.val, b.val, _⟩
  simpa using congr_arg (ZMod.castHom dvd_rfl R) hab
#align char_p.sq_add_sq CharP.sq_add_sq

end CharP

open scoped Nat

open ZMod

/-- The **Fermat-Euler totient theorem**. `Nat.ModEq.pow_totient` is an alternative statement
  of the same theorem. -/
@[simp]
theorem ZMod.pow_totient {n : ℕ} (x : (ZMod n)ˣ) : x ^ φ n = 1 := by
  cases n
  · rw [Nat.totient_zero, pow_zero]
  · rw [← card_units_eq_totient, pow_card_eq_one]
#align zmod.pow_totient ZMod.pow_totient

/-- The **Fermat-Euler totient theorem**. `ZMod.pow_totient` is an alternative statement
  of the same theorem. -/
theorem Nat.ModEq.pow_totient {x n : ℕ} (h : Nat.Coprime x n) : x ^ φ n ≡ 1 [MOD n] := by
  rw [← ZMod.eq_iff_modEq_nat]
  let x' : Units (ZMod n) := ZMod.unitOfCoprime _ h
  have := ZMod.pow_totient x'
  apply_fun ((fun (x : Units (ZMod n)) => (x : ZMod n)) : Units (ZMod n) → ZMod n) at this
  simpa only [Nat.succ_eq_add_one, Nat.cast_pow, Units.val_one, Nat.cast_one,
    coe_unitOfCoprime, Units.val_pow_eq_pow_val]
#align nat.modeq.pow_totient Nat.ModEq.pow_totient

section

variable {V : Type*} [Fintype K] [DivisionRing K] [AddCommGroup V] [Module K V]

-- should this go in a namespace?
-- finite_dimensional would be natural,
-- but we don't assume it...
theorem card_eq_pow_finrank [Fintype V] : Fintype.card V = q ^ FiniteDimensional.finrank K V := by
  let b := IsNoetherian.finsetBasis K V
  rw [Module.card_fintype b, ← FiniteDimensional.finrank_eq_card_basis b]
#align card_eq_pow_finrank card_eq_pow_finrank

end

open FiniteField

namespace ZMod

/-- A variation on Fermat's little theorem. See `ZMod.pow_card_sub_one_eq_one` -/
@[simp]
theorem pow_card {p : ℕ} [Fact p.Prime] (x : ZMod p) : x ^ p = x := by
  have h := FiniteField.pow_card x; rwa [ZMod.card p] at h
#align zmod.pow_card ZMod.pow_card

@[simp]
theorem pow_card_pow {n p : ℕ} [Fact p.Prime] (x : ZMod p) : x ^ p ^ n = x := by
  induction' n with n ih
  · simp
  · simp [pow_succ, pow_mul, ih, pow_card]
#align zmod.pow_card_pow ZMod.pow_card_pow

@[simp]
theorem frobenius_zmod (p : ℕ) [Fact p.Prime] : frobenius (ZMod p) p = RingHom.id _ := by
  ext a
  rw [frobenius_def, ZMod.pow_card, RingHom.id_apply]
#align zmod.frobenius_zmod ZMod.frobenius_zmod

--Porting note: this was a `simp` lemma, but now the LHS simplify to `φ p`.
theorem card_units (p : ℕ) [Fact p.Prime] : Fintype.card (ZMod p)ˣ = p - 1 := by
  rw [Fintype.card_units, card]
#align zmod.card_units ZMod.card_units

/-- **Fermat's Little Theorem**: for every unit `a` of `ZMod p`, we have `a ^ (p - 1) = 1`. -/
theorem units_pow_card_sub_one_eq_one (p : ℕ) [Fact p.Prime] (a : (ZMod p)ˣ) : a ^ (p - 1) = 1 := by
  rw [← card_units p, pow_card_eq_one]
#align zmod.units_pow_card_sub_one_eq_one ZMod.units_pow_card_sub_one_eq_one

/-- **Fermat's Little Theorem**: for all nonzero `a : ZMod p`, we have `a ^ (p - 1) = 1`. -/
theorem pow_card_sub_one_eq_one {p : ℕ} [Fact p.Prime] {a : ZMod p} (ha : a ≠ 0) :
    a ^ (p - 1) = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one a ha
    rwa [ZMod.card p] at h
#align zmod.pow_card_sub_one_eq_one ZMod.pow_card_sub_one_eq_one

theorem orderOf_units_dvd_card_sub_one {p : ℕ} [Fact p.Prime] (u : (ZMod p)ˣ) : orderOf u ∣ p - 1 :=
  orderOf_dvd_of_pow_eq_one <| units_pow_card_sub_one_eq_one _ _
#align zmod.order_of_units_dvd_card_sub_one ZMod.orderOf_units_dvd_card_sub_one

theorem orderOf_dvd_card_sub_one {p : ℕ} [Fact p.Prime] {a : ZMod p} (ha : a ≠ 0) :
    orderOf a ∣ p - 1 :=
  orderOf_dvd_of_pow_eq_one <| pow_card_sub_one_eq_one ha
#align zmod.order_of_dvd_card_sub_one ZMod.orderOf_dvd_card_sub_one

open Polynomial

theorem expand_card {p : ℕ} [Fact p.Prime] (f : Polynomial (ZMod p)) :
    expand (ZMod p) p f = f ^ p := by have h := FiniteField.expand_card f; rwa [ZMod.card p] at h
#align zmod.expand_card ZMod.expand_card

end ZMod

/-- **Fermat's Little Theorem**: for all `a : ℤ` coprime to `p`, we have
`a ^ (p - 1) ≡ 1 [ZMOD p]`. -/
theorem Int.ModEq.pow_card_sub_one_eq_one {p : ℕ} (hp : Nat.Prime p) {n : ℤ} (hpn : IsCoprime n p) :
    n ^ (p - 1) ≡ 1 [ZMOD p] := by
  haveI : Fact p.Prime := ⟨hp⟩
  have : ¬(n : ZMod p) = 0 := by
    rw [CharP.int_cast_eq_zero_iff _ p, ← (Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd]
    · exact hpn.symm
  simpa [← ZMod.int_cast_eq_int_cast_iff] using ZMod.pow_card_sub_one_eq_one this
#align int.modeq.pow_card_sub_one_eq_one Int.ModEq.pow_card_sub_one_eq_one

section

namespace FiniteField

variable {F : Type*} [Field F]

section Finite

variable [Finite F]

/-- In a finite field of characteristic `2`, all elements are squares. -/
theorem isSquare_of_char_two (hF : ringChar F = 2) (a : F) : IsSquare a :=
  haveI hF' : CharP F 2 := ringChar.of_eq hF
  isSquare_of_charTwo' a
#align finite_field.is_square_of_char_two FiniteField.isSquare_of_char_two

/-- In a finite field of odd characteristic, not every element is a square. -/
theorem exists_nonsquare (hF : ringChar F ≠ 2) : ∃ a : F, ¬IsSquare a := by
  -- Idea: the squaring map on `F` is not injective, hence not surjective
  let sq : F → F := fun x => x ^ 2
  have h : ¬Function.Injective sq := by
    simp only [Function.Injective, not_forall, exists_prop]
    refine' ⟨-1, 1, _, Ring.neg_one_ne_one_of_char_ne_two hF⟩
    simp only [one_pow, neg_one_sq]
  rw [Finite.injective_iff_surjective] at h
  -- sq not surjective
  simp_rw [IsSquare, ← pow_two, @eq_comm _ _ (_ ^ 2)]
  unfold Function.Surjective at h
  push_neg at h ⊢
  exact h
#align finite_field.exists_nonsquare FiniteField.exists_nonsquare

end Finite

variable [Fintype F]

/-- The finite field `F` has even cardinality iff it has characteristic `2`. -/
theorem even_card_iff_char_two : ringChar F = 2 ↔ Fintype.card F % 2 = 0 := by
  rcases FiniteField.card F (ringChar F) with ⟨n, hp, h⟩
  rw [h, Nat.pow_mod]
  constructor
  · intro hF
    simp [hF]
  · rw [← Nat.even_iff, Nat.even_pow]
    rintro ⟨hev, hnz⟩
    rw [Nat.even_iff, Nat.mod_mod] at hev
    exact (Nat.Prime.eq_two_or_odd hp).resolve_right (ne_of_eq_of_ne hev zero_ne_one)
#align finite_field.even_card_iff_char_two FiniteField.even_card_iff_char_two

theorem even_card_of_char_two (hF : ringChar F = 2) : Fintype.card F % 2 = 0 :=
  even_card_iff_char_two.mp hF
#align finite_field.even_card_of_char_two FiniteField.even_card_of_char_two

theorem odd_card_of_char_ne_two (hF : ringChar F ≠ 2) : Fintype.card F % 2 = 1 :=
  Nat.mod_two_ne_zero.mp (mt even_card_iff_char_two.mpr hF)
#align finite_field.odd_card_of_char_ne_two FiniteField.odd_card_of_char_ne_two

/-- If `F` has odd characteristic, then for nonzero `a : F`, we have that `a ^ (#F / 2) = ±1`. -/
theorem pow_dichotomy (hF : ringChar F ≠ 2) {a : F} (ha : a ≠ 0) :
    a ^ (Fintype.card F / 2) = 1 ∨ a ^ (Fintype.card F / 2) = -1 := by
  have h₁ := FiniteField.pow_card_sub_one_eq_one a ha
  rw [← Nat.two_mul_odd_div_two (FiniteField.odd_card_of_char_ne_two hF), mul_comm, pow_mul,
    pow_two] at h₁
  exact mul_self_eq_one_iff.mp h₁
#align finite_field.pow_dichotomy FiniteField.pow_dichotomy

/-- A unit `a` of a finite field `F` of odd characteristic is a square
if and only if `a ^ (#F / 2) = 1`. -/
theorem unit_isSquare_iff (hF : ringChar F ≠ 2) (a : Fˣ) :
    IsSquare a ↔ a ^ (Fintype.card F / 2) = 1 := by
  classical
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
    obtain ⟨n, hn⟩ : a ∈ Submonoid.powers g := by rw [mem_powers_iff_mem_zpowers]; apply hg
    have hodd := Nat.two_mul_odd_div_two (FiniteField.odd_card_of_char_ne_two hF)
    constructor
    · rintro ⟨y, rfl⟩
      rw [← pow_two, ← pow_mul, hodd]
      apply_fun Units.val using Units.ext
      · push_cast
        exact FiniteField.pow_card_sub_one_eq_one (y : F) (Units.ne_zero y)
    · subst a; intro h
      have key : 2 * (Fintype.card F / 2) ∣ n * (Fintype.card F / 2) := by
        rw [← pow_mul] at h
        rw [hodd, ← Fintype.card_units, ← orderOf_eq_card_of_forall_mem_zpowers hg]
        apply orderOf_dvd_of_pow_eq_one h
      have : 0 < Fintype.card F / 2 := Nat.div_pos Fintype.one_lt_card (by norm_num)
      obtain ⟨m, rfl⟩ := Nat.dvd_of_mul_dvd_mul_right this key
      refine' ⟨g ^ m, _⟩
      dsimp
      rw [mul_comm, pow_mul, pow_two]
#align finite_field.unit_is_square_iff FiniteField.unit_isSquare_iff

/-- A non-zero `a : F` is a square if and only if `a ^ (#F / 2) = 1`. -/
theorem isSquare_iff (hF : ringChar F ≠ 2) {a : F} (ha : a ≠ 0) :
    IsSquare a ↔ a ^ (Fintype.card F / 2) = 1 := by
  apply
    (iff_congr _ (by simp [Units.ext_iff])).mp (FiniteField.unit_isSquare_iff hF (Units.mk0 a ha))
  simp only [IsSquare, Units.ext_iff, Units.val_mk0, Units.val_mul]
  constructor
  · rintro ⟨y, hy⟩; exact ⟨y, hy⟩
  · rintro ⟨y, rfl⟩
    have hy : y ≠ 0 := by rintro rfl; simp at ha
    refine' ⟨Units.mk0 y hy, _⟩; simp
#align finite_field.is_square_iff FiniteField.isSquare_iff

end FiniteField

end
