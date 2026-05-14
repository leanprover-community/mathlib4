/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, Thomas Zhu, Mario Carneiro
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.Basic
public meta import Mathlib.Tactic.Basic
public meta import Mathlib.Tactic.ToAdditive
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Algebra.Order.Ring.Canonical
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sign.Basic
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Init
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic.ArithMult.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.SetLike

/-!
# The Jacobi Symbol

We define the Jacobi symbol and prove its main properties.

## Main definitions

We define the Jacobi symbol, `jacobiSym a b`, for integers `a` and natural numbers `b`
as the product over the prime factors `p` of `b` of the Legendre symbols `legendreSym p a`.
This agrees with the mathematical definition when `b` is odd.

The prime factors are obtained via `Nat.factors`. Since `Nat.factors 0 = []`,
this implies in particular that `jacobiSym a 0 = 1` for all `a`.

## Main statements

We prove the main properties of the Jacobi symbol, including the following.

* Multiplicativity in both arguments (`jacobiSym.mul_left`, `jacobiSym.mul_right`)

* The value of the symbol is `1` or `-1` when the arguments are coprime
  (`jacobiSym.eq_one_or_neg_one`)

* The symbol vanishes if and only if `b ≠ 0` and the arguments are not coprime
  (`jacobiSym.eq_zero_iff_not_coprime`)

* If the symbol has the value `-1`, then `a : ZMod b` is not a square
  (`ZMod.nonsquare_of_jacobiSym_eq_neg_one`); the converse holds when `b = p` is a prime
  (`ZMod.nonsquare_iff_jacobiSym_eq_neg_one`); in particular, in this case `a` is a
  square mod `p` when the symbol has the value `1` (`ZMod.isSquare_of_jacobiSym_eq_one`).

* Quadratic reciprocity (`jacobiSym.quadratic_reciprocity`,
  `jacobiSym.quadratic_reciprocity_one_mod_four`,
  `jacobiSym.quadratic_reciprocity_three_mod_four`)

* The supplementary laws for `a = -1`, `a = 2`, `a = -2` (`jacobiSym.at_neg_one`,
  `jacobiSym.at_two`, `jacobiSym.at_neg_two`)

* The symbol depends on `a` only via its residue class mod `b` (`jacobiSym.mod_left`)
  and on `b` only via its residue class mod `4*a` (`jacobiSym.mod_right`)

* A `csimp` rule for `jacobiSym` and `legendreSym` that evaluates `J(a | b)` efficiently by
  reducing to the case `0 ≤ a < b` and `a`, `b` odd, and then swaps `a`, `b` and recurses using
  quadratic reciprocity.

## Notation

We define the notation `J(a | b)` for `jacobiSym a b`, localized to `NumberTheorySymbols`.

## Tags
Jacobi symbol, quadratic reciprocity
-/

@[expose] public section


section Jacobi

/-!
### Definition of the Jacobi symbol

We define the Jacobi symbol $\Bigl(\frac{a}{b}\Bigr)$ for integers `a` and natural numbers `b`
as the product of the Legendre symbols $\Bigl(\frac{a}{p}\Bigr)$, where `p` runs through the
prime divisors (with multiplicity) of `b`, as provided by `b.factors`. This agrees with the
Jacobi symbol when `b` is odd and gives less meaningful values when it is not (e.g., the symbol
is `1` when `b = 0`). This is called `jacobiSym a b`.

We define localized notation (scope `NumberTheorySymbols`) `J(a | b)` for the Jacobi
symbol `jacobiSym a b`.
-/


open Nat ZMod

-- Since we need the fact that the factors are prime, we use `List.pmap`.
/-- The Jacobi symbol of `a` and `b` -/
def jacobiSym (a : ℤ) (b : ℕ) : ℤ :=
  (b.primeFactorsList.pmap (fun p pp => @legendreSym p ⟨pp⟩ a) fun _ pf =>
    prime_of_mem_primeFactorsList pf).prod

-- Notation for the Jacobi symbol.
@[inherit_doc]
scoped[NumberTheorySymbols] notation "J(" a " | " b ")" => jacobiSym a b

open NumberTheorySymbols

/-!
### Properties of the Jacobi symbol
-/


namespace jacobiSym

/-- The symbol `J(a | 0)` has the value `1`. -/
@[simp]
theorem zero_right (a : ℤ) : J(a | 0) = 1 := by
  simp only [jacobiSym, primeFactorsList_zero, List.prod_nil, List.pmap]

/-- The symbol `J(a | 1)` has the value `1`. -/
@[simp]
theorem one_right (a : ℤ) : J(a | 1) = 1 := by
  simp only [jacobiSym, primeFactorsList_one, List.prod_nil, List.pmap]

/-- The Legendre symbol `legendreSym p a` with an integer `a` and a prime number `p`
is the same as the Jacobi symbol `J(a | p)`. -/
theorem legendreSym.to_jacobiSym (p : ℕ) [fp : Fact p.Prime] (a : ℤ) :
    legendreSym p a = J(a | p) := by
  simp only [jacobiSym, primeFactorsList_prime fp.1, List.prod_cons, List.prod_nil, mul_one,
    List.pmap]

/-- The Jacobi symbol is multiplicative in its second argument. -/
theorem mul_right' (a : ℤ) {b₁ b₂ : ℕ} (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) :
    J(a | b₁ * b₂) = J(a | b₁) * J(a | b₂) := by
  rw [jacobiSym, ((perm_primeFactorsList_mul hb₁ hb₂).pmap _).prod_eq, List.pmap_append,
    List.prod_append]
  pick_goal 2
  · exact fun p hp =>
      (List.mem_append.mp hp).elim prime_of_mem_primeFactorsList prime_of_mem_primeFactorsList
  · rfl

/-- The Jacobi symbol is multiplicative in its second argument. -/
theorem mul_right (a : ℤ) (b₁ b₂ : ℕ) [NeZero b₁] [NeZero b₂] :
    J(a | b₁ * b₂) = J(a | b₁) * J(a | b₂) :=
  mul_right' a (NeZero.ne b₁) (NeZero.ne b₂)

/-- The Jacobi symbol takes only the values `0`, `1` and `-1`. -/
theorem trichotomy (a : ℤ) (b : ℕ) : J(a | b) = 0 ∨ J(a | b) = 1 ∨ J(a | b) = -1 :=
  ((MonoidHom.mrange (@SignType.castHom ℤ _ _).toMonoidHom).copy {0, 1, -1} <| by
    rw [Set.pair_comm]
    exact (SignType.range_eq SignType.castHom).symm).list_prod_mem
      (by
        intro _ ha'
        rcases List.mem_pmap.mp ha' with ⟨p, hp, rfl⟩
        haveI : Fact p.Prime := ⟨prime_of_mem_primeFactorsList hp⟩
        exact quadraticChar_isQuadratic (ZMod p) a)

/-- The symbol `J(1 | b)` has the value `1`. -/
@[simp]
theorem one_left (b : ℕ) : J(1 | b) = 1 :=
  List.prod_eq_one fun z hz => by
    let ⟨p, hp, he⟩ := List.mem_pmap.1 hz
    rw [← he, legendreSym.at_one]

/-- The Jacobi symbol is multiplicative in its first argument. -/
theorem mul_left (a₁ a₂ : ℤ) (b : ℕ) : J(a₁ * a₂ | b) = J(a₁ | b) * J(a₂ | b) := by
  simp_rw [jacobiSym, List.pmap_eq_map_attach, legendreSym.mul _ _ _]
  exact List.prod_map_mul (l := (primeFactorsList b).attach)
    (f := fun x ↦ @legendreSym x { out := prime_of_mem_primeFactorsList x.2 } a₁)
    (g := fun x ↦ @legendreSym x { out := prime_of_mem_primeFactorsList x.2 } a₂)

/-- The symbol `J(a | b)` vanishes iff `a` and `b` are not coprime (assuming `b ≠ 0`). -/
theorem eq_zero_iff_not_coprime {a : ℤ} {b : ℕ} [NeZero b] : J(a | b) = 0 ↔ a.gcd b ≠ 1 :=
  List.prod_eq_zero_iff.trans
    (by
      rw [List.mem_pmap, Int.gcd_eq_natAbs, Ne, Prime.not_coprime_iff_dvd]
      simp_rw [legendreSym.eq_zero_iff _ _, intCast_zmod_eq_zero_iff_dvd,
        mem_primeFactorsList (NeZero.ne b), ← Int.natCast_dvd, Int.natCast_dvd_natCast, exists_prop,
        and_assoc, _root_.and_comm])

/-- The symbol `J(a | b)` is nonzero when `a` and `b` are coprime. -/
protected theorem ne_zero {a : ℤ} {b : ℕ} (h : a.gcd b = 1) : J(a | b) ≠ 0 := by
  rcases eq_zero_or_neZero b with hb | _
  · rw [hb, zero_right]
    exact one_ne_zero
  · contrapose! h; exact eq_zero_iff_not_coprime.1 h

/-- The symbol `J(a | b)` vanishes if and only if `b ≠ 0` and `a` and `b` are not coprime. -/
theorem eq_zero_iff {a : ℤ} {b : ℕ} : J(a | b) = 0 ↔ b ≠ 0 ∧ a.gcd b ≠ 1 :=
  ⟨fun h => by
    rcases eq_or_ne b 0 with hb | hb
    · rw [hb, zero_right] at h; cases h
    exact ⟨hb, mt jacobiSym.ne_zero <| Classical.not_not.2 h⟩, fun ⟨hb, h⟩ => by
    rw [← neZero_iff] at hb; exact eq_zero_iff_not_coprime.2 h⟩

/-- The symbol `J(0 | b)` vanishes when `b > 1`. -/
theorem zero_left {b : ℕ} (hb : 1 < b) : J(0 | b) = 0 :=
  (@eq_zero_iff_not_coprime 0 b ⟨ne_zero_of_lt hb⟩).mpr <| by
    rw [Int.gcd_zero_left, Int.natAbs_natCast]; exact hb.ne'

/-- The symbol `J(a | b)` takes the value `1` or `-1` if `a` and `b` are coprime. -/
theorem eq_one_or_neg_one {a : ℤ} {b : ℕ} (h : a.gcd b = 1) : J(a | b) = 1 ∨ J(a | b) = -1 :=
  (trichotomy a b).resolve_left <| jacobiSym.ne_zero h

/-- We have that `J(a^e | b) = J(a | b)^e`. -/
theorem pow_left (a : ℤ) (e b : ℕ) : J(a ^ e | b) = J(a | b) ^ e :=
  Nat.recOn e (by rw [_root_.pow_zero, _root_.pow_zero, one_left]) fun _ ih => by
    rw [_root_.pow_succ, _root_.pow_succ, mul_left, ih]

/-- We have that `J(a | b^e) = J(a | b)^e`. -/
theorem pow_right (a : ℤ) (b e : ℕ) : J(a | b ^ e) = J(a | b) ^ e := by
  induction e with
  | zero => rw [Nat.pow_zero, _root_.pow_zero, one_right]
  | succ e ih =>
    rcases eq_zero_or_neZero b with hb | _
    · rw [hb, zero_pow e.succ_ne_zero, zero_right, one_pow]
    · rw [_root_.pow_succ, _root_.pow_succ, mul_right, ih]

/-- The square of `J(a | b)` is `1` when `a` and `b` are coprime. -/
theorem sq_one {a : ℤ} {b : ℕ} (h : a.gcd b = 1) : J(a | b) ^ 2 = 1 := by
  rcases eq_one_or_neg_one h with h₁ | h₁ <;> rw [h₁] <;> rfl

/-- The symbol `J(a^2 | b)` is `1` when `a` and `b` are coprime. -/
theorem sq_one' {a : ℤ} {b : ℕ} (h : a.gcd b = 1) : J(a ^ 2 | b) = 1 := by rw [pow_left, sq_one h]

/-- The symbol `J(a | b)` depends only on `a` mod `b`. -/
theorem mod_left (a : ℤ) (b : ℕ) : J(a | b) = J(a % b | b) :=
  congr_arg List.prod <|
    List.pmap_congr_left _
      (by
        rintro p hp _ h₂
        conv_rhs =>
          rw [legendreSym.mod, Int.emod_emod_of_dvd _ (Int.natCast_dvd_natCast.2 <|
            dvd_of_mem_primeFactorsList hp), ← legendreSym.mod])

/-- The symbol `J(a | b)` depends only on `a` mod `b`. -/
theorem mod_left' {a₁ a₂ : ℤ} {b : ℕ} (h : a₁ % b = a₂ % b) : J(a₁ | b) = J(a₂ | b) := by
  rw [mod_left, h, ← mod_left]

/-- If `p` is prime, `J(a | p) = -1` and `p` divides `x^2 - a*y^2`, then `p` must divide
`x` and `y`. -/
theorem prime_dvd_of_eq_neg_one {p : ℕ} [Fact p.Prime] {a : ℤ} (h : J(a | p) = -1) {x y : ℤ}
    (hxy : ↑p ∣ (x ^ 2 - a * y ^ 2 : ℤ)) : ↑p ∣ x ∧ ↑p ∣ y := by
  rw [← legendreSym.to_jacobiSym] at h
  exact legendreSym.prime_dvd_of_eq_neg_one h hxy

/-- We can pull out a product over a list in the first argument of the Jacobi symbol. -/
theorem list_prod_left {l : List ℤ} {n : ℕ} : J(l.prod | n) = (l.map fun a => J(a | n)).prod := by
  induction l with
  | nil => simp only [List.prod_nil, List.map_nil, one_left]
  | cons n l' ih => rw [List.map, List.prod_cons, List.prod_cons, mul_left, ih]

/-- We can pull out a product over a list in the second argument of the Jacobi symbol. -/
theorem list_prod_right {a : ℤ} {l : List ℕ} (hl : ∀ n ∈ l, n ≠ 0) :
    J(a | l.prod) = (l.map fun n => J(a | n)).prod := by
  induction l with
  | nil => simp only [List.prod_nil, one_right, List.map_nil]
  | cons n l' ih =>
    have hn := hl n List.mem_cons_self
    -- `n ≠ 0`
    have hl' := List.prod_ne_zero fun hf => hl 0 (List.mem_cons_of_mem _ hf) rfl
    -- `l'.prod ≠ 0`
    have h := fun m hm => hl m (List.mem_cons_of_mem _ hm)
    -- `∀ (m : ℕ), m ∈ l' → m ≠ 0`
    rw [List.map, List.prod_cons, List.prod_cons, mul_right' a hn hl', ih h]

/-- If `J(a | n) = -1`, then `n` has a prime divisor `p` such that `J(a | p) = -1`. -/
theorem eq_neg_one_at_prime_divisor_of_eq_neg_one {a : ℤ} {n : ℕ} (h : J(a | n) = -1) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ J(a | p) = -1 := by
  have hn₀ : n ≠ 0 := by
    rintro rfl
    rw [zero_right, CharZero.eq_neg_self_iff] at h
    exact one_ne_zero h
  have hf₀ (p) (hp : p ∈ n.primeFactorsList) : p ≠ 0 := (Nat.pos_of_mem_primeFactorsList hp).ne.symm
  rw [← Nat.prod_primeFactorsList hn₀, list_prod_right hf₀] at h
  obtain ⟨p, hmem, hj⟩ := List.mem_map.mp (List.neg_one_mem_of_prod_eq_neg_one h)
  exact ⟨p, Nat.prime_of_mem_primeFactorsList hmem, Nat.dvd_of_mem_primeFactorsList hmem, hj⟩

end jacobiSym

namespace ZMod

open jacobiSym

/-- If `J(a | b)` is `-1`, then `a` is not a square modulo `b`. -/
theorem nonsquare_of_jacobiSym_eq_neg_one {a : ℤ} {b : ℕ} (h : J(a | b) = -1) :
    ¬IsSquare (a : ZMod b) := fun ⟨r, ha⟩ => by
  rw [← r.coe_valMinAbs, ← Int.cast_mul, intCast_eq_intCast_iff', ← sq] at ha
  apply (by simp : ¬(0 : ℤ) ≤ -1)
  rw [← h, mod_left, ha, ← mod_left, pow_left]
  apply sq_nonneg

/-- If `p` is prime, then `J(a | p)` is `-1` iff `a` is not a square modulo `p`. -/
theorem nonsquare_iff_jacobiSym_eq_neg_one {a : ℤ} {p : ℕ} [Fact p.Prime] :
    J(a | p) = -1 ↔ ¬IsSquare (a : ZMod p) := by
  rw [← legendreSym.to_jacobiSym]
  exact legendreSym.eq_neg_one_iff p

/-- If `p` is prime and `J(a | p) = 1`, then `a` is a square mod `p`. -/
theorem isSquare_of_jacobiSym_eq_one {a : ℤ} {p : ℕ} [Fact p.Prime] (h : J(a | p) = 1) :
    IsSquare (a : ZMod p) :=
  Classical.not_not.mp <| by rw [← nonsquare_iff_jacobiSym_eq_neg_one, h]; decide

end ZMod

/-!
### Values at `-1`, `2` and `-2`
-/


namespace jacobiSym

/-- If `χ` is a multiplicative function such that `J(a | p) = χ p` for all odd primes `p`,
then `J(a | b)` equals `χ b` for all odd natural numbers `b`. -/
theorem value_at (a : ℤ) {R : Type*} [Semiring R] (χ : R →* ℤ)
    (hp : ∀ (p : ℕ) (pp : p.Prime), p ≠ 2 → @legendreSym p ⟨pp⟩ a = χ p) {b : ℕ} (hb : Odd b) :
    J(a | b) = χ b := by
  conv_rhs => rw [← prod_primeFactorsList hb.pos.ne', cast_list_prod, map_list_prod χ]
  rw [jacobiSym, List.map_map, ← List.pmap_eq_map
    fun _ => prime_of_mem_primeFactorsList]
  congr 1; apply List.pmap_congr_left
  exact fun p h pp _ => hp p pp (hb.ne_two_of_dvd_nat <| dvd_of_mem_primeFactorsList h)

/-- If `b` is odd, then `J(-1 | b)` is given by `χ₄ b`. -/
theorem at_neg_one {b : ℕ} (hb : Odd b) : J(-1 | b) = χ₄ b :=
  -- Porting note: In mathlib3, it was written `χ₄` and Lean could guess that it had to use
  -- `χ₄.to_monoid_hom`. This is not the case with Lean 4.
  value_at (-1) χ₄.toMonoidHom (fun p pp => @legendreSym.at_neg_one p ⟨pp⟩) hb

/-- If `b` is odd, then `J(-a | b) = χ₄ b * J(a | b)`. -/
protected theorem neg (a : ℤ) {b : ℕ} (hb : Odd b) : J(-a | b) = χ₄ b * J(a | b) := by
  rw [neg_eq_neg_one_mul, mul_left, at_neg_one hb]

/-- If `b` is odd, then `J(2 | b)` is given by `χ₈ b`. -/
theorem at_two {b : ℕ} (hb : Odd b) : J(2 | b) = χ₈ b :=
  value_at 2 χ₈.toMonoidHom (fun p pp => @legendreSym.at_two p ⟨pp⟩) hb

/-- If `b` is odd, then `J(-2 | b)` is given by `χ₈' b`. -/
theorem at_neg_two {b : ℕ} (hb : Odd b) : J(-2 | b) = χ₈' b :=
  value_at (-2) χ₈'.toMonoidHom (fun p pp => @legendreSym.at_neg_two p ⟨pp⟩) hb

theorem div_four_left {a : ℤ} {b : ℕ} (ha4 : a % 4 = 0) (hb2 : b % 2 = 1) :
    J(a / 4 | b) = J(a | b) := by
  obtain ⟨a, rfl⟩ := Int.dvd_of_emod_eq_zero ha4
  have : Int.gcd (2 : ℕ) b = 1 := by
    rw [Int.gcd_natCast_natCast, ← b.mod_add_div 2, hb2, Nat.gcd_add_mul_left_right,
      Nat.gcd_one_right]
  rw [Int.mul_ediv_cancel_left _ (by decide), jacobiSym.mul_left,
    (by decide : (4 : ℤ) = (2 : ℕ) ^ 2), jacobiSym.sq_one' this, one_mul]

/-- If `b` is odd, then `J(4 | b) = 1`. -/
theorem at_four {b : ℕ} (hb : Odd b) : J(4 | b) = 1 := by
  have : J((4 : ℤ) | b) = J((4 : ℤ) / 4 | b) :=
    (div_four_left (by decide) (Nat.odd_iff.mp hb)).symm
  simpa [one_left]

theorem even_odd {a : ℤ} {b : ℕ} (ha2 : a % 2 = 0) (hb2 : b % 2 = 1) :
    (if b % 8 = 3 ∨ b % 8 = 5 then -J(a / 2 | b) else J(a / 2 | b)) = J(a | b) := by
  obtain ⟨a, rfl⟩ := Int.dvd_of_emod_eq_zero ha2
  rw [Int.mul_ediv_cancel_left _ (by decide), jacobiSym.mul_left,
    jacobiSym.at_two (Nat.odd_iff.mpr hb2), ZMod.χ₈_nat_eq_if_mod_eight,
    if_neg (Nat.mod_two_ne_zero.mpr hb2)]
  grind

end jacobiSym

/-!
### Quadratic Reciprocity
-/


/-- The bi-multiplicative map giving the sign in the Law of Quadratic Reciprocity -/
def qrSign (m n : ℕ) : ℤ :=
  J(χ₄ m | n)

namespace qrSign

/-- We can express `qrSign m n` as a power of `-1` when `m` and `n` are odd. -/
theorem neg_one_pow {m n : ℕ} (hm : Odd m) (hn : Odd n) :
    qrSign m n = (-1) ^ (m / 2 * (n / 2)) := by
  rw [qrSign, pow_mul, ← χ₄_eq_neg_one_pow (odd_iff.mp hm)]
  rcases odd_mod_four_iff.mp (odd_iff.mp hm) with h | h
  · rw [χ₄_nat_one_mod_four h, jacobiSym.one_left, one_pow]
  · rw [χ₄_nat_three_mod_four h, ← χ₄_eq_neg_one_pow (odd_iff.mp hn), jacobiSym.at_neg_one hn]

/-- When `m` and `n` are odd, then the square of `qrSign m n` is `1`. -/
theorem sq_eq_one {m n : ℕ} (hm : Odd m) (hn : Odd n) : qrSign m n ^ 2 = 1 := by
  rw [neg_one_pow hm hn, ← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]

/-- `qrSign` is multiplicative in the first argument. -/
theorem mul_left (m₁ m₂ n : ℕ) : qrSign (m₁ * m₂) n = qrSign m₁ n * qrSign m₂ n := by
  simp_rw [qrSign, Nat.cast_mul, map_mul, jacobiSym.mul_left]

/-- `qrSign` is multiplicative in the second argument. -/
theorem mul_right (m n₁ n₂ : ℕ) [NeZero n₁] [NeZero n₂] :
    qrSign m (n₁ * n₂) = qrSign m n₁ * qrSign m n₂ :=
  jacobiSym.mul_right (χ₄ m) n₁ n₂

/-- `qrSign` is symmetric when both arguments are odd. -/
protected theorem symm {m n : ℕ} (hm : Odd m) (hn : Odd n) : qrSign m n = qrSign n m := by
  rw [neg_one_pow hm hn, neg_one_pow hn hm, mul_comm (m / 2)]

/-- We can move `qrSign m n` from one side of an equality to the other when `m` and `n` are odd. -/
theorem eq_iff_eq {m n : ℕ} (hm : Odd m) (hn : Odd n) (x y : ℤ) :
    qrSign m n * x = y ↔ x = qrSign m n * y := by
  refine
      ⟨fun h' =>
        let h := h'.symm
        ?_,
        fun h => ?_⟩ <;>
    rw [h, ← mul_assoc, ← pow_two, sq_eq_one hm hn, one_mul]

end qrSign

namespace jacobiSym

/-- The **Law of Quadratic Reciprocity for the Jacobi symbol**, version with `qrSign` -/
theorem quadratic_reciprocity' {a b : ℕ} (ha : Odd a) (hb : Odd b) :
    J(a | b) = qrSign b a * J(b | a) := by
  -- define the right-hand side for fixed `a` as a `ℕ →* ℤ`
  let rhs : ℕ → ℕ →* ℤ := fun a =>
    { toFun := fun x => qrSign x a * J(x | a)
      map_one' := by convert ← mul_one (M := ℤ) _; (on_goal 1 => symm); all_goals apply one_left
      map_mul' := fun x y => by
        simp_rw [qrSign.mul_left x y a, Nat.cast_mul, mul_left, mul_mul_mul_comm] }
  have rhs_apply : ∀ a b : ℕ, rhs a b = qrSign b a * J(b | a) := fun a b => rfl
  refine value_at a (rhs a) (fun p pp hp => Eq.symm ?_) hb
  have hpo := pp.eq_two_or_odd'.resolve_left hp
  rw [@legendreSym.to_jacobiSym p ⟨pp⟩, rhs_apply, Nat.cast_id, qrSign.eq_iff_eq hpo ha,
    qrSign.symm hpo ha]
  refine value_at p (rhs p) (fun q pq hq => ?_) ha
  have hqo := pq.eq_two_or_odd'.resolve_left hq
  rw [rhs_apply, Nat.cast_id, ← @legendreSym.to_jacobiSym p ⟨pp⟩, qrSign.symm hqo hpo,
    qrSign.neg_one_pow hpo hqo, @legendreSym.quadratic_reciprocity' p q ⟨pp⟩ ⟨pq⟩ hp hq]

/-- The Law of Quadratic Reciprocity for the Jacobi symbol -/
theorem quadratic_reciprocity {a b : ℕ} (ha : Odd a) (hb : Odd b) :
    J(a | b) = (-1) ^ (a / 2 * (b / 2)) * J(b | a) := by
  rw [← qrSign.neg_one_pow ha hb, qrSign.symm ha hb, quadratic_reciprocity' ha hb]

/-- The Law of Quadratic Reciprocity for the Jacobi symbol: if `a` and `b` are natural numbers
with `a % 4 = 1` and `b` odd, then `J(a | b) = J(b | a)`. -/
theorem quadratic_reciprocity_one_mod_four {a b : ℕ} (ha : a % 4 = 1) (hb : Odd b) :
    J(a | b) = J(b | a) := by
  rw [quadratic_reciprocity (odd_iff.mpr (odd_of_mod_four_eq_one ha)) hb, pow_mul,
    neg_one_pow_div_two_of_one_mod_four ha, one_pow, one_mul]

/-- The Law of Quadratic Reciprocity for the Jacobi symbol: if `a` and `b` are natural numbers
with `a` odd and `b % 4 = 1`, then `J(a | b) = J(b | a)`. -/
theorem quadratic_reciprocity_one_mod_four' {a b : ℕ} (ha : Odd a) (hb : b % 4 = 1) :
    J(a | b) = J(b | a) :=
  (quadratic_reciprocity_one_mod_four hb ha).symm

/-- The Law of Quadratic Reciprocity for the Jacobi symbol: if `a` and `b` are natural numbers
both congruent to `3` mod `4`, then `J(a | b) = -J(b | a)`. -/
theorem quadratic_reciprocity_three_mod_four {a b : ℕ} (ha : a % 4 = 3) (hb : b % 4 = 3) :
    J(a | b) = -J(b | a) := by
  let nop := @neg_one_pow_div_two_of_three_mod_four
  rw [quadratic_reciprocity, pow_mul, nop ha, nop hb, neg_one_mul] <;>
    rwa [odd_iff, odd_of_mod_four_eq_three]

theorem quadratic_reciprocity_if {a b : ℕ} (ha2 : a % 2 = 1) (hb2 : b % 2 = 1) :
    (if a % 4 = 3 ∧ b % 4 = 3 then -J(b | a) else J(b | a)) = J(a | b) := by
  rcases Nat.odd_mod_four_iff.mp ha2 with ha1 | ha3
  · simpa [ha1] using jacobiSym.quadratic_reciprocity_one_mod_four' (Nat.odd_iff.mpr hb2) ha1
  rcases Nat.odd_mod_four_iff.mp hb2 with hb1 | hb3
  · simpa [hb1] using jacobiSym.quadratic_reciprocity_one_mod_four hb1 (Nat.odd_iff.mpr ha2)
  simpa [ha3, hb3] using (jacobiSym.quadratic_reciprocity_three_mod_four ha3 hb3).symm

/-- The Jacobi symbol `J(a | b)` depends only on `b` mod `4*a` (version for `a : ℕ`). -/
theorem mod_right' (a : ℕ) {b : ℕ} (hb : Odd b) : J(a | b) = J(a | b % (4 * a)) := by
  rcases eq_or_ne a 0 with (rfl | ha₀)
  · rw [mul_zero, mod_zero]
  have hb' : Odd (b % (4 * a)) := hb.mod_even (Even.mul_right (by decide) _)
  rcases exists_eq_pow_mul_and_not_dvd ha₀ 2 (by simp) with ⟨e, a', ha₁', ha₂⟩
  have ha₁ := odd_iff.mpr (two_dvd_ne_zero.mp ha₁')
  nth_rw 2 [ha₂]; nth_rw 1 [ha₂]
  rw [Nat.cast_mul, mul_left, mul_left, quadratic_reciprocity' ha₁ hb,
    quadratic_reciprocity' ha₁ hb', Nat.cast_pow, pow_left, pow_left, Nat.cast_two, at_two hb,
    at_two hb']
  congr 1; swap
  · congr 1
    · simp_rw [qrSign]
      rw [χ₄_nat_mod_four, χ₄_nat_mod_four (b % (4 * a)), mod_mod_of_dvd b (dvd_mul_right 4 a)]
    · rw [mod_left ↑(b % _), mod_left b, Int.natCast_mod, Int.emod_emod_of_dvd b]
      simp only [ha₂, Nat.cast_mul, ← mul_assoc]
      apply dvd_mul_left
  rcases e with - | e; · simp
  · rw [χ₈_nat_mod_eight, χ₈_nat_mod_eight (b % (4 * a)), mod_mod_of_dvd b]
    use 2 ^ e * a'; rw [ha₂, Nat.pow_succ]; ring

/-- The Jacobi symbol `J(a | b)` depends only on `b` mod `4*a`. -/
theorem mod_right (a : ℤ) {b : ℕ} (hb : Odd b) : J(a | b) = J(a | b % (4 * a.natAbs)) := by
  rcases Int.natAbs_eq a with ha | ha <;> nth_rw 2 [ha] <;> nth_rw 1 [ha]
  · exact mod_right' a.natAbs hb
  · have hb' : Odd (b % (4 * a.natAbs)) := hb.mod_even (Even.mul_right (by decide) _)
    rw [jacobiSym.neg _ hb, jacobiSym.neg _ hb', mod_right' _ hb, χ₄_nat_mod_four,
      χ₄_nat_mod_four (b % (4 * _)), mod_mod_of_dvd b (dvd_mul_right 4 _)]

end jacobiSym

end Jacobi


section FastJacobi

/-!
### Fast computation of the Jacobi symbol
We follow the implementation as in `Mathlib/Tactic/NormNum/LegendreSymbol.lean`.
-/

set_option backward.privateInPublic true

open NumberTheorySymbols jacobiSym

/-- Computes `J(a | b)` (or `-J(a | b)` if `flip` is set to `true`) given assumptions, by reducing
`a` to odd by repeated division and then using quadratic reciprocity to swap `a`, `b`. -/
private def fastJacobiSymAux (a b : ℕ) (flip : Bool) (ha0 : a > 0) : ℤ :=
  if ha4 : a % 4 = 0 then
    fastJacobiSymAux (a / 4) b flip
      (Nat.div_pos (Nat.le_of_dvd ha0 (Nat.dvd_of_mod_eq_zero ha4)) (by decide))
  else if ha2 : a % 2 = 0 then
    fastJacobiSymAux (a / 2) b (xor (b % 8 = 3 ∨ b % 8 = 5) flip)
      (Nat.div_pos (Nat.le_of_dvd ha0 (Nat.dvd_of_mod_eq_zero ha2)) (by decide))
  else if ha1 : a = 1 then
    if flip then -1 else 1
  else if hba : b % a = 0 then
    0
  else
    fastJacobiSymAux (b % a) a (xor (a % 4 = 3 ∧ b % 4 = 3) flip) (Nat.pos_of_ne_zero hba)
termination_by a
decreasing_by
  · exact a.div_lt_self ha0 (by decide)
  · exact a.div_lt_self ha0 (by decide)
  · exact b.mod_lt ha0

private theorem fastJacobiSymAux.eq_jacobiSym {a b : ℕ} {flip : Bool} {ha0 : a > 0}
    (hb2 : b % 2 = 1) (hb1 : b > 1) :
    fastJacobiSymAux a b flip ha0 = if flip then -J(a | b) else J(a | b) := by
  induction a using Nat.strongRecOn generalizing b flip with | ind a IH =>
  unfold fastJacobiSymAux
  split <;> rename_i ha4
  · rw [IH (a / 4) (a.div_lt_self ha0 (by decide)) hb2 hb1]
    simp only [Int.natCast_ediv, Nat.cast_ofNat, div_four_left (a := a) (mod_cast ha4) hb2]
  split <;> rename_i ha2
  · rw [IH (a / 2) (a.div_lt_self ha0 (by decide)) hb2 hb1]
    simp only [Int.natCast_ediv, Nat.cast_ofNat, ← even_odd (a := a) (mod_cast ha2) hb2]
    by_cases h : b % 8 = 3 ∨ b % 8 = 5 <;> simp [h]; cases flip <;> simp
  split <;> rename_i ha1
  · subst ha1; simp
  split <;> rename_i hba
  · suffices J(a | b) = 0 by simp [this]
    refine eq_zero_iff.mpr ⟨fun h ↦ absurd (h ▸ hb1) (by decide), ?_⟩
    rwa [Int.gcd_natCast_natCast, Nat.gcd_eq_left (Nat.dvd_of_mod_eq_zero hba)]
  rw [IH (b % a) (b.mod_lt ha0) (Nat.mod_two_ne_zero.mp ha2) (lt_of_le_of_ne ha0 (Ne.symm ha1))]
  simp only [Int.natCast_mod, ← mod_left]
  rw [← quadratic_reciprocity_if (Nat.mod_two_ne_zero.mp ha2) hb2]
  by_cases h : a % 4 = 3 ∧ b % 4 = 3 <;> simp [h]; cases flip <;> simp

/-- Computes `J(a | b)` by reducing `b` to odd by repeated division and then using
`fastJacobiSymAux`. -/
private def fastJacobiSym (a : ℤ) (b : ℕ) : ℤ :=
  if hb0 : b = 0 then
    1
  else if _ : b % 2 = 0 then
    if a % 2 = 0 then
      0
    else
      have : b / 2 < b := b.div_lt_self (Nat.pos_of_ne_zero hb0) one_lt_two
      fastJacobiSym a (b / 2)
  else if b = 1 then
    1
  else if hab : a % b = 0 then
    0
  else
    fastJacobiSymAux (a % b).natAbs b false (Int.natAbs_pos.mpr hab)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[csimp] private theorem fastJacobiSym.eq : jacobiSym = fastJacobiSym := by
  ext a b
  induction b using Nat.strongRecOn with | ind b IH =>
  unfold fastJacobiSym
  split_ifs with hb0 hb2 ha2 hb1 hab
  · rw [hb0, zero_right]
  · refine eq_zero_iff.mpr ⟨hb0, ne_of_gt ?_⟩
    refine Nat.le_of_dvd (Int.gcd_pos_iff.mpr (mod_cast .inr hb0)) ?_
    refine Nat.dvd_gcd (Int.ofNat_dvd_left.mp (Int.dvd_of_emod_eq_zero ha2)) ?_
    exact Int.ofNat_dvd_left.mp (Int.dvd_of_emod_eq_zero (mod_cast hb2))
  · dsimp only
    rw [← IH (b / 2) (b.div_lt_self (Nat.pos_of_ne_zero hb0) one_lt_two)]
    obtain ⟨b, rfl⟩ := Nat.dvd_of_mod_eq_zero hb2
    rw [mul_right' a (by decide) fun h ↦ hb0 (mul_eq_zero_of_right 2 h),
      b.mul_div_cancel_left (by decide), mod_left a 2, Nat.cast_ofNat,
      Int.emod_two_ne_zero.mp ha2, one_left, one_mul]
  · rw [hb1, one_right]
  · rw [mod_left, hab, zero_left (lt_of_le_of_ne (Nat.pos_of_ne_zero hb0) (Ne.symm hb1))]
  · rw [fastJacobiSymAux.eq_jacobiSym, if_neg Bool.false_ne_true, mod_left a b,
      Int.natAbs_of_nonneg (a.emod_nonneg (mod_cast hb0))]
    · exact Nat.mod_two_ne_zero.mp hb2
    · exact lt_of_le_of_ne (Nat.one_le_iff_ne_zero.mpr hb0) (Ne.symm hb1)

/-- Computes `legendreSym p a` using `fastJacobiSym`. -/
@[inline, nolint unusedArguments]
private def fastLegendreSym (p : ℕ) [Fact p.Prime] (a : ℤ) : ℤ := J(a | p)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[csimp] private theorem fastLegendreSym.eq : legendreSym = fastLegendreSym := by
  ext p _ a; rw [legendreSym.to_jacobiSym, fastLegendreSym]

end FastJacobi
