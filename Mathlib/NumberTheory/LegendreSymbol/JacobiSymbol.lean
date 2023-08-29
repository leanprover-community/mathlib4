/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

#align_import number_theory.legendre_symbol.jacobi_symbol from "leanprover-community/mathlib"@"74a27133cf29446a0983779e37c8f829a85368f3"

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

## Notations

We define the notation `J(a | b)` for `jacobiSym a b`, localized to `NumberTheorySymbols`.

## Tags
Jacobi symbol, quadratic reciprocity
-/


section Jacobi

/-!
### Definition of the Jacobi symbol

We define the Jacobi symbol $\Bigl(\frac{a}{b}\Bigr)$ for integers `a` and natural numbers `b`
as the product of the Legendre symbols $\Bigl(\frac{a}{p}\Bigr)$, where `p` runs through the
prime divisors (with multiplicity) of `b`, as provided by `b.factors`. This agrees with the
Jacobi symbol when `b` is odd and gives less meaningful values when it is not (e.g., the symbol
is `1` when `b = 0`). This is called `jacobiSym a b`.

We define localized notation (locale `NumberTheorySymbols`) `J(a | b)` for the Jacobi
symbol `jacobiSym a b`.
-/


open Nat ZMod

-- Since we need the fact that the factors are prime, we use `List.pmap`.
/-- The Jacobi symbol of `a` and `b` -/
def jacobiSym (a : ℤ) (b : ℕ) : ℤ :=
  (b.factors.pmap (fun p pp => @legendreSym p ⟨pp⟩ a) fun _ pf => prime_of_mem_factors pf).prod
#align jacobi_sym jacobiSym

-- Notation for the Jacobi symbol.
scoped[NumberTheorySymbols] notation "J(" a " | " b ")" => jacobiSym a b

-- porting note: Without the following line, Lean expected `|` on several lines, e.g. line 102.
open NumberTheorySymbols

/-!
### Properties of the Jacobi symbol
-/


namespace jacobiSym

/-- The symbol `J(a | 0)` has the value `1`. -/
@[simp]
theorem zero_right (a : ℤ) : J(a | 0) = 1 := by
  simp only [jacobiSym, factors_zero, List.prod_nil, List.pmap]
  -- 🎉 no goals
#align jacobi_sym.zero_right jacobiSym.zero_right

/-- The symbol `J(a | 1)` has the value `1`. -/
@[simp]
theorem one_right (a : ℤ) : J(a | 1) = 1 := by
  simp only [jacobiSym, factors_one, List.prod_nil, List.pmap]
  -- 🎉 no goals
#align jacobi_sym.one_right jacobiSym.one_right

/-- The Legendre symbol `legendreSym p a` with an integer `a` and a prime number `p`
is the same as the Jacobi symbol `J(a | p)`. -/
theorem legendreSym.to_jacobiSym (p : ℕ) [fp : Fact p.Prime] (a : ℤ) : legendreSym p a = J(a | p) :=
  by simp only [jacobiSym, factors_prime fp.1, List.prod_cons, List.prod_nil, mul_one, List.pmap]
     -- 🎉 no goals
#align legendre_sym.to_jacobi_sym jacobiSym.legendreSym.to_jacobiSym

/-- The Jacobi symbol is multiplicative in its second argument. -/
theorem mul_right' (a : ℤ) {b₁ b₂ : ℕ} (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) :
    J(a | b₁ * b₂) = J(a | b₁) * J(a | b₂) := by
  rw [jacobiSym, ((perm_factors_mul hb₁ hb₂).pmap _).prod_eq, List.pmap_append, List.prod_append]
  case h => exact fun p hp => (List.mem_append.mp hp).elim prime_of_mem_factors prime_of_mem_factors
  -- ⊢ List.prod (List.pmap (fun p pp => legendreSym p a) (factors b₁) (_ : ∀ (a :  …
  -- 🎉 no goals
  case _ => rfl
  -- 🎉 no goals
  -- 🎉 no goals
#align jacobi_sym.mul_right' jacobiSym.mul_right'

/-- The Jacobi symbol is multiplicative in its second argument. -/
theorem mul_right (a : ℤ) (b₁ b₂ : ℕ) [NeZero b₁] [NeZero b₂] :
    J(a | b₁ * b₂) = J(a | b₁) * J(a | b₂) :=
  mul_right' a (NeZero.ne b₁) (NeZero.ne b₂)
#align jacobi_sym.mul_right jacobiSym.mul_right

/-- The Jacobi symbol takes only the values `0`, `1` and `-1`. -/
theorem trichotomy (a : ℤ) (b : ℕ) : J(a | b) = 0 ∨ J(a | b) = 1 ∨ J(a | b) = -1 :=
  ((@SignType.castHom ℤ _ _).toMonoidHom.mrange.copy {0, 1, -1} <| by
    rw [Set.pair_comm];
    -- ⊢ {0, -1, 1} = ↑(MonoidHom.mrange ↑SignType.castHom)
    exact (SignType.range_eq SignType.castHom).symm).list_prod_mem
    -- 🎉 no goals
      (by
        intro _ ha'
        -- ⊢ x✝ ∈ Submonoid.copy (MonoidHom.mrange ↑SignType.castHom) {0, 1, -1} (_ : {0, …
        rcases List.mem_pmap.mp ha' with ⟨p, hp, rfl⟩
        -- ⊢ legendreSym p a ∈ Submonoid.copy (MonoidHom.mrange ↑SignType.castHom) {0, 1, …
        haveI : Fact p.Prime := ⟨prime_of_mem_factors hp⟩
        -- ⊢ legendreSym p a ∈ Submonoid.copy (MonoidHom.mrange ↑SignType.castHom) {0, 1, …
        exact quadraticChar_isQuadratic (ZMod p) a)
        -- 🎉 no goals
#align jacobi_sym.trichotomy jacobiSym.trichotomy

/-- The symbol `J(1 | b)` has the value `1`. -/
@[simp]
theorem one_left (b : ℕ) : J(1 | b) = 1 :=
  List.prod_eq_one fun z hz => by
    let ⟨p, hp, he⟩ := List.mem_pmap.1 hz
    -- ⊢ z = 1
    -- porting note: The line 150 was added because Lean does not synthesize the instance
    -- `[Fact (Nat.Prime p)]` automatically (it is needed for `legendreSym.at_one`)
    letI : Fact p.Prime := ⟨prime_of_mem_factors hp⟩
    -- ⊢ z = 1
    rw [← he, legendreSym.at_one]
    -- 🎉 no goals
#align jacobi_sym.one_left jacobiSym.one_left

/-- The Jacobi symbol is multiplicative in its first argument. -/
theorem mul_left (a₁ a₂ : ℤ) (b : ℕ) : J(a₁ * a₂ | b) = J(a₁ | b) * J(a₂ | b) := by
  simp_rw [jacobiSym, List.pmap_eq_map_attach, legendreSym.mul _ _ _];
  -- ⊢ List.prod (List.map (fun x => legendreSym (↑x) a₁ * legendreSym (↑x) a₂) (Li …
  exact List.prod_map_mul (α := ℤ) (l := (factors b).attach)
    (f := fun x ↦ @legendreSym x {out := prime_of_mem_factors x.2} a₁)
    (g := fun x ↦ @legendreSym x {out := prime_of_mem_factors x.2} a₂)
#align jacobi_sym.mul_left jacobiSym.mul_left

/-- The symbol `J(a | b)` vanishes iff `a` and `b` are not coprime (assuming `b ≠ 0`). -/
theorem eq_zero_iff_not_coprime {a : ℤ} {b : ℕ} [NeZero b] : J(a | b) = 0 ↔ a.gcd b ≠ 1 :=
  List.prod_eq_zero_iff.trans
    (by
      rw [List.mem_pmap, Int.gcd_eq_natAbs, Ne, Prime.not_coprime_iff_dvd]
      -- ⊢ (∃ a_1 h, legendreSym a_1 a = 0) ↔ ∃ p, Nat.Prime p ∧ p ∣ Int.natAbs a ∧ p ∣ …
      -- porting note: Initially, `and_assoc'` and `and_comm'` were used on line 164 but they have
      -- been deprecated so we replace them with `and_assoc` and `and_comm`
      simp_rw [legendreSym.eq_zero_iff _ _, int_cast_zmod_eq_zero_iff_dvd,
        mem_factors (NeZero.ne b), ← Int.coe_nat_dvd_left, Int.coe_nat_dvd, exists_prop, and_assoc,
        and_comm])
#align jacobi_sym.eq_zero_iff_not_coprime jacobiSym.eq_zero_iff_not_coprime

/-- The symbol `J(a | b)` is nonzero when `a` and `b` are coprime. -/
protected theorem ne_zero {a : ℤ} {b : ℕ} (h : a.gcd b = 1) : J(a | b) ≠ 0 := by
  cases' eq_zero_or_neZero b with hb
  -- ⊢ J(a | b) ≠ 0
  · rw [hb, zero_right]
    -- ⊢ 1 ≠ 0
    exact one_ne_zero
    -- 🎉 no goals
  · contrapose! h; exact eq_zero_iff_not_coprime.1 h
    -- ⊢ Int.gcd a ↑b ≠ 1
                   -- 🎉 no goals
#align jacobi_sym.ne_zero jacobiSym.ne_zero

/-- The symbol `J(a | b)` vanishes if and only if `b ≠ 0` and `a` and `b` are not coprime. -/
theorem eq_zero_iff {a : ℤ} {b : ℕ} : J(a | b) = 0 ↔ b ≠ 0 ∧ a.gcd b ≠ 1 :=
  ⟨fun h => by
    cases' eq_or_ne b 0 with hb hb
    -- ⊢ b ≠ 0 ∧ Int.gcd a ↑b ≠ 1
    · rw [hb, zero_right] at h; cases h
      -- ⊢ b ≠ 0 ∧ Int.gcd a ↑b ≠ 1
                                -- 🎉 no goals
    exact ⟨hb, mt jacobiSym.ne_zero <| Classical.not_not.2 h⟩, fun ⟨hb, h⟩ => by
    -- 🎉 no goals
    rw [← neZero_iff] at hb; exact eq_zero_iff_not_coprime.2 h⟩
    -- ⊢ J(a | b) = 0
                             -- 🎉 no goals
#align jacobi_sym.eq_zero_iff jacobiSym.eq_zero_iff

/-- The symbol `J(0 | b)` vanishes when `b > 1`. -/
theorem zero_left {b : ℕ} (hb : 1 < b) : J(0 | b) = 0 :=
  (@eq_zero_iff_not_coprime 0 b ⟨ne_zero_of_lt hb⟩).mpr <| by
    rw [Int.gcd_zero_left, Int.natAbs_ofNat]; exact hb.ne'
    -- ⊢ b ≠ 1
                                              -- 🎉 no goals
#align jacobi_sym.zero_left jacobiSym.zero_left

/-- The symbol `J(a | b)` takes the value `1` or `-1` if `a` and `b` are coprime. -/
theorem eq_one_or_neg_one {a : ℤ} {b : ℕ} (h : a.gcd b = 1) : J(a | b) = 1 ∨ J(a | b) = -1 :=
  (trichotomy a b).resolve_left <| jacobiSym.ne_zero h
#align jacobi_sym.eq_one_or_neg_one jacobiSym.eq_one_or_neg_one

/-- We have that `J(a^e | b) = J(a | b)^e`. -/
theorem pow_left (a : ℤ) (e b : ℕ) : J(a ^ e | b) = J(a | b) ^ e :=
  Nat.recOn e (by rw [_root_.pow_zero, _root_.pow_zero, one_left]) fun _ ih => by
                  -- 🎉 no goals
    rw [_root_.pow_succ, _root_.pow_succ, mul_left, ih]
    -- 🎉 no goals
#align jacobi_sym.pow_left jacobiSym.pow_left

/-- We have that `J(a | b^e) = J(a | b)^e`. -/
theorem pow_right (a : ℤ) (b e : ℕ) : J(a | b ^ e) = J(a | b) ^ e := by
  induction' e with e ih
  -- ⊢ J(a | b ^ zero) = J(a | b) ^ zero
  · rw [Nat.pow_zero, _root_.pow_zero, one_right]
    -- 🎉 no goals
  · cases' eq_zero_or_neZero b with hb
    -- ⊢ J(a | b ^ succ e) = J(a | b) ^ succ e
    · rw [hb, zero_pow (succ_pos e), zero_right, one_pow]
      -- 🎉 no goals
    · rw [_root_.pow_succ, _root_.pow_succ, mul_right, ih]
      -- 🎉 no goals
#align jacobi_sym.pow_right jacobiSym.pow_right

/-- The square of `J(a | b)` is `1` when `a` and `b` are coprime. -/
theorem sq_one {a : ℤ} {b : ℕ} (h : a.gcd b = 1) : J(a | b) ^ 2 = 1 := by
  cases' eq_one_or_neg_one h with h₁ h₁ <;> rw [h₁] <;> rfl
  -- ⊢ J(a | b) ^ 2 = 1
                                            -- ⊢ 1 ^ 2 = 1
                                            -- ⊢ (-1) ^ 2 = 1
                                                        -- 🎉 no goals
                                                        -- 🎉 no goals
#align jacobi_sym.sq_one jacobiSym.sq_one

/-- The symbol `J(a^2 | b)` is `1` when `a` and `b` are coprime. -/
theorem sq_one' {a : ℤ} {b : ℕ} (h : a.gcd b = 1) : J(a ^ 2 | b) = 1 := by rw [pow_left, sq_one h]
                                                                           -- 🎉 no goals
#align jacobi_sym.sq_one' jacobiSym.sq_one'

/-- The symbol `J(a | b)` depends only on `a` mod `b`. -/
theorem mod_left (a : ℤ) (b : ℕ) : J(a | b) = J(a % b | b) :=
  congr_arg List.prod <|
    List.pmap_congr _
      (by
        -- porting note: Lean does not synthesize the instance [Fact (Nat.Prime p)] automatically
        -- (it is needed for `legendreSym.mod` on line 227). Thus, we name the hypothesis
        -- `Nat.Prime p` explicitly on line 224 and prove `Fact (Nat.Prime p)` on line 225.
        rintro p hp _ h₂
        -- ⊢ legendreSym p a = legendreSym p (a % ↑b)
        letI : Fact p.Prime := ⟨h₂⟩
        -- ⊢ legendreSym p a = legendreSym p (a % ↑b)
        conv_rhs =>
          rw [legendreSym.mod, Int.emod_emod_of_dvd _ (Int.coe_nat_dvd.2 <| dvd_of_mem_factors hp),
            ← legendreSym.mod])
#align jacobi_sym.mod_left jacobiSym.mod_left

/-- The symbol `J(a | b)` depends only on `a` mod `b`. -/
theorem mod_left' {a₁ a₂ : ℤ} {b : ℕ} (h : a₁ % b = a₂ % b) : J(a₁ | b) = J(a₂ | b) := by
  rw [mod_left, h, ← mod_left]
  -- 🎉 no goals
#align jacobi_sym.mod_left' jacobiSym.mod_left'

/-- If `p` is prime, `J(a | p) = -1` and `p` divides `x^2 - a*y^2`, then `p` must divide
`x` and `y`. -/
theorem prime_dvd_of_eq_neg_one {p : ℕ} [Fact p.Prime] {a : ℤ} (h : J(a | p) = -1) {x y : ℤ}
    (hxy : ↑p ∣ (x ^ 2 - a * y ^ 2 : ℤ)) : ↑p ∣ x ∧ ↑p ∣ y := by
  rw [← legendreSym.to_jacobiSym] at h
  -- ⊢ ↑p ∣ x ∧ ↑p ∣ y
  exact legendreSym.prime_dvd_of_eq_neg_one h hxy
  -- 🎉 no goals
#align jacobi_sym.prime_dvd_of_eq_neg_one jacobiSym.prime_dvd_of_eq_neg_one

/-- We can pull out a product over a list in the first argument of the Jacobi symbol. -/
theorem list_prod_left {l : List ℤ} {n : ℕ} : J(l.prod | n) = (l.map fun a => J(a | n)).prod := by
  induction' l with n l' ih
  -- ⊢ J(List.prod [] | n) = List.prod (List.map (fun a => J(a | n)) [])
  · simp only [List.prod_nil, List.map_nil, one_left]
    -- 🎉 no goals
  · rw [List.map, List.prod_cons, List.prod_cons, mul_left, ih]
    -- 🎉 no goals
#align jacobi_sym.list_prod_left jacobiSym.list_prod_left

/-- We can pull out a product over a list in the second argument of the Jacobi symbol. -/
theorem list_prod_right {a : ℤ} {l : List ℕ} (hl : ∀ n ∈ l, n ≠ 0) :
    J(a | l.prod) = (l.map fun n => J(a | n)).prod := by
  induction' l with n l' ih
  -- ⊢ J(a | List.prod []) = List.prod (List.map (fun n => J(a | n)) [])
  · simp only [List.prod_nil, one_right, List.map_nil]
    -- 🎉 no goals
  · have hn := hl n (List.mem_cons_self n l')
    -- ⊢ J(a | List.prod (n :: l')) = List.prod (List.map (fun n => J(a | n)) (n :: l …
    -- `n ≠ 0`
    have hl' := List.prod_ne_zero fun hf => hl 0 (List.mem_cons_of_mem _ hf) rfl
    -- ⊢ J(a | List.prod (n :: l')) = List.prod (List.map (fun n => J(a | n)) (n :: l …
    -- `l'.prod ≠ 0`
    have h := fun m hm => hl m (List.mem_cons_of_mem _ hm)
    -- ⊢ J(a | List.prod (n :: l')) = List.prod (List.map (fun n => J(a | n)) (n :: l …
    -- `∀ (m : ℕ), m ∈ l' → m ≠ 0`
    rw [List.map, List.prod_cons, List.prod_cons, mul_right' a hn hl', ih h]
    -- 🎉 no goals
#align jacobi_sym.list_prod_right jacobiSym.list_prod_right

/-- If `J(a | n) = -1`, then `n` has a prime divisor `p` such that `J(a | p) = -1`. -/
theorem eq_neg_one_at_prime_divisor_of_eq_neg_one {a : ℤ} {n : ℕ} (h : J(a | n) = -1) :
    ∃ (p : ℕ) (_ : p.Prime), p ∣ n ∧ J(a | p) = -1 := by
  have hn₀ : n ≠ 0 := by
    rintro rfl
    rw [zero_right, eq_neg_self_iff] at h
    exact one_ne_zero h
  have hf₀ : ∀ p ∈ n.factors, p ≠ 0 := fun p hp => (Nat.pos_of_mem_factors hp).ne.symm
  -- ⊢ ∃ p x, p ∣ n ∧ J(a | p) = -1
  rw [← Nat.prod_factors hn₀, list_prod_right hf₀] at h
  -- ⊢ ∃ p x, p ∣ n ∧ J(a | p) = -1
  obtain ⟨p, hmem, hj⟩ := List.mem_map.mp (List.neg_one_mem_of_prod_eq_neg_one h)
  -- ⊢ ∃ p x, p ∣ n ∧ J(a | p) = -1
  exact ⟨p, Nat.prime_of_mem_factors hmem, Nat.dvd_of_mem_factors hmem, hj⟩
  -- 🎉 no goals
#align jacobi_sym.eq_neg_one_at_prime_divisor_of_eq_neg_one jacobiSym.eq_neg_one_at_prime_divisor_of_eq_neg_one

end jacobiSym

namespace ZMod

open jacobiSym

/-- If `J(a | b)` is `-1`, then `a` is not a square modulo `b`. -/
theorem nonsquare_of_jacobiSym_eq_neg_one {a : ℤ} {b : ℕ} (h : J(a | b) = -1) :
    ¬IsSquare (a : ZMod b) := fun ⟨r, ha⟩ => by
  rw [← r.coe_valMinAbs, ← Int.cast_mul, int_cast_eq_int_cast_iff', ← sq] at ha
  -- ⊢ False
  apply (by norm_num : ¬(0 : ℤ) ≤ -1)
  -- ⊢ 0 ≤ -1
  rw [← h, mod_left, ha, ← mod_left, pow_left]
  -- ⊢ 0 ≤ J(valMinAbs r | b) ^ 2
  apply sq_nonneg
  -- 🎉 no goals
#align zmod.nonsquare_of_jacobi_sym_eq_neg_one ZMod.nonsquare_of_jacobiSym_eq_neg_one

/-- If `p` is prime, then `J(a | p)` is `-1` iff `a` is not a square modulo `p`. -/
theorem nonsquare_iff_jacobiSym_eq_neg_one {a : ℤ} {p : ℕ} [Fact p.Prime] :
    J(a | p) = -1 ↔ ¬IsSquare (a : ZMod p) := by
  rw [← legendreSym.to_jacobiSym];
  -- ⊢ legendreSym p a = -1 ↔ ¬IsSquare ↑a
  exact legendreSym.eq_neg_one_iff p
  -- 🎉 no goals
#align zmod.nonsquare_iff_jacobi_sym_eq_neg_one ZMod.nonsquare_iff_jacobiSym_eq_neg_one

/-- If `p` is prime and `J(a | p) = 1`, then `a` is a square mod `p`. -/
theorem isSquare_of_jacobiSym_eq_one {a : ℤ} {p : ℕ} [Fact p.Prime] (h : J(a | p) = 1) :
    IsSquare (a : ZMod p) :=
  Classical.not_not.mp <| by rw [← nonsquare_iff_jacobiSym_eq_neg_one, h]; decide
                             -- ⊢ ¬1 = -1
                                                                           -- 🎉 no goals
#align zmod.is_square_of_jacobi_sym_eq_one ZMod.isSquare_of_jacobiSym_eq_one

end ZMod

/-!
### Values at `-1`, `2` and `-2`
-/


namespace jacobiSym

/-- If `χ` is a multiplicative function such that `J(a | p) = χ p` for all odd primes `p`,
then `J(a | b)` equals `χ b` for all odd natural numbers `b`. -/
theorem value_at (a : ℤ) {R : Type*} [CommSemiring R] (χ : R →* ℤ)
    (hp : ∀ (p : ℕ) (pp : p.Prime) (_ : p ≠ 2), @legendreSym p ⟨pp⟩ a = χ p) {b : ℕ} (hb : Odd b) :
    J(a | b) = χ b := by
  conv_rhs => rw [← prod_factors hb.pos.ne', cast_list_prod, χ.map_list_prod]
  -- ⊢ J(a | b) = List.prod (List.map (↑χ) (List.map Nat.cast (factors b)))
  rw [jacobiSym, List.map_map, ← List.pmap_eq_map Nat.Prime _ _ fun _ => prime_of_mem_factors]
  -- ⊢ List.prod (List.pmap (fun p pp => legendreSym p a) (factors b) (_ : ∀ (x : ℕ …
  congr 1; apply List.pmap_congr
  -- ⊢ List.pmap (fun p pp => legendreSym p a) (factors b) (_ : ∀ (x : ℕ), x ∈ fact …
           -- ⊢ ∀ (a_1 : ℕ), a_1 ∈ factors b → ∀ (h₁ : Nat.Prime a_1), Nat.Prime a_1 → legen …
  exact fun p h pp _ => hp p pp (hb.ne_two_of_dvd_nat <| dvd_of_mem_factors h)
  -- 🎉 no goals
#align jacobi_sym.value_at jacobiSym.value_at

/-- If `b` is odd, then `J(-1 | b)` is given by `χ₄ b`. -/
theorem at_neg_one {b : ℕ} (hb : Odd b) : J(-1 | b) = χ₄ b :=
  -- porting note: In mathlib3, it was written `χ₄` and Lean could guess that it had to use
  -- `χ₄.to_monoid_hom`. This is not the case with Lean 4.
  value_at (-1) χ₄.toMonoidHom (fun p pp => @legendreSym.at_neg_one p ⟨pp⟩) hb
#align jacobi_sym.at_neg_one jacobiSym.at_neg_one

/-- If `b` is odd, then `J(-a | b) = χ₄ b * J(a | b)`. -/
protected theorem neg (a : ℤ) {b : ℕ} (hb : Odd b) : J(-a | b) = χ₄ b * J(a | b) := by
  rw [neg_eq_neg_one_mul, mul_left, at_neg_one hb]
  -- 🎉 no goals
#align jacobi_sym.neg jacobiSym.neg

/-- If `b` is odd, then `J(2 | b)` is given by `χ₈ b`. -/
theorem at_two {b : ℕ} (hb : Odd b) : J(2 | b) = χ₈ b :=
  value_at 2 χ₈.toMonoidHom (fun p pp => @legendreSym.at_two p ⟨pp⟩) hb
#align jacobi_sym.at_two jacobiSym.at_two

/-- If `b` is odd, then `J(-2 | b)` is given by `χ₈' b`. -/
theorem at_neg_two {b : ℕ} (hb : Odd b) : J(-2 | b) = χ₈' b :=
  value_at (-2) χ₈'.toMonoidHom (fun p pp => @legendreSym.at_neg_two p ⟨pp⟩) hb
#align jacobi_sym.at_neg_two jacobiSym.at_neg_two

end jacobiSym

/-!
### Quadratic Reciprocity
-/


/-- The bi-multiplicative map giving the sign in the Law of Quadratic Reciprocity -/
def qrSign (m n : ℕ) : ℤ :=
  J(χ₄ m | n)
#align qr_sign qrSign

namespace qrSign

/-- We can express `qrSign m n` as a power of `-1` when `m` and `n` are odd. -/
theorem neg_one_pow {m n : ℕ} (hm : Odd m) (hn : Odd n) :
    qrSign m n = (-1) ^ (m / 2 * (n / 2)) := by
  rw [qrSign, pow_mul, ← χ₄_eq_neg_one_pow (odd_iff.mp hm)]
  -- ⊢ J(↑χ₄ ↑m | n) = ↑χ₄ ↑m ^ (n / 2)
  cases' odd_mod_four_iff.mp (odd_iff.mp hm) with h h
  -- ⊢ J(↑χ₄ ↑m | n) = ↑χ₄ ↑m ^ (n / 2)
  · rw [χ₄_nat_one_mod_four h, jacobiSym.one_left, one_pow]
    -- 🎉 no goals
  · rw [χ₄_nat_three_mod_four h, ← χ₄_eq_neg_one_pow (odd_iff.mp hn), jacobiSym.at_neg_one hn]
    -- 🎉 no goals
#align qr_sign.neg_one_pow qrSign.neg_one_pow

/-- When `m` and `n` are odd, then the square of `qrSign m n` is `1`. -/
theorem sq_eq_one {m n : ℕ} (hm : Odd m) (hn : Odd n) : qrSign m n ^ 2 = 1 := by
  rw [neg_one_pow hm hn, ← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  -- 🎉 no goals
#align qr_sign.sq_eq_one qrSign.sq_eq_one

/-- `qrSign` is multiplicative in the first argument. -/
theorem mul_left (m₁ m₂ n : ℕ) : qrSign (m₁ * m₂) n = qrSign m₁ n * qrSign m₂ n := by
  simp_rw [qrSign, Nat.cast_mul, map_mul, jacobiSym.mul_left]
  -- 🎉 no goals
#align qr_sign.mul_left qrSign.mul_left

/-- `qrSign` is multiplicative in the second argument. -/
theorem mul_right (m n₁ n₂ : ℕ) [NeZero n₁] [NeZero n₂] :
    qrSign m (n₁ * n₂) = qrSign m n₁ * qrSign m n₂ :=
  jacobiSym.mul_right (χ₄ m) n₁ n₂
#align qr_sign.mul_right qrSign.mul_right

/-- `qrSign` is symmetric when both arguments are odd. -/
protected theorem symm {m n : ℕ} (hm : Odd m) (hn : Odd n) : qrSign m n = qrSign n m := by
  rw [neg_one_pow hm hn, neg_one_pow hn hm, mul_comm (m / 2)]
  -- 🎉 no goals
#align qr_sign.symm qrSign.symm

/-- We can move `qrSign m n` from one side of an equality to the other when `m` and `n` are odd. -/
theorem eq_iff_eq {m n : ℕ} (hm : Odd m) (hn : Odd n) (x y : ℤ) :
    qrSign m n * x = y ↔ x = qrSign m n * y := by
  refine'
      ⟨fun h' =>
        let h := h'.symm
        _,
        fun h => _⟩ <;>
    rw [h, ← mul_assoc, ← pow_two, sq_eq_one hm hn, one_mul]
    -- 🎉 no goals
    -- 🎉 no goals
#align qr_sign.eq_iff_eq qrSign.eq_iff_eq

end qrSign

namespace jacobiSym

/-- The Law of Quadratic Reciprocity for the Jacobi symbol, version with `qrSign` -/
theorem quadratic_reciprocity' {a b : ℕ} (ha : Odd a) (hb : Odd b) :
    J(a | b) = qrSign b a * J(b | a) := by
  -- define the right hand side for fixed `a` as a `ℕ →* ℤ`
  let rhs : ℕ → ℕ →* ℤ := fun a =>
    { toFun := fun x => qrSign x a * J(x | a)
      map_one' := by convert ← mul_one (M := ℤ) _; symm; all_goals apply one_left
      map_mul' := fun x y => by
        -- porting note: `simp_rw` on line 423 replaces `rw` to allow the rewrite rules to be
        -- applied under the binder `fun ↦ ...`
        simp_rw [qrSign.mul_left x y a, Nat.cast_mul, mul_left, mul_mul_mul_comm] }
  have rhs_apply : ∀ a b : ℕ, rhs a b = qrSign b a * J(b | a) := fun a b => rfl
  -- ⊢ J(↑a | b) = qrSign b a * J(↑b | a)
  refine' value_at a (rhs a) (fun p pp hp => Eq.symm _) hb
  -- ⊢ ↑(rhs a) ↑p = legendreSym p ↑a
  have hpo := pp.eq_two_or_odd'.resolve_left hp
  -- ⊢ ↑(rhs a) ↑p = legendreSym p ↑a
  rw [@legendreSym.to_jacobiSym p ⟨pp⟩, rhs_apply, Nat.cast_id, qrSign.eq_iff_eq hpo ha,
    qrSign.symm hpo ha]
  refine' value_at p (rhs p) (fun q pq hq => _) ha
  -- ⊢ legendreSym q ↑p = ↑(rhs p) ↑q
  have hqo := pq.eq_two_or_odd'.resolve_left hq
  -- ⊢ legendreSym q ↑p = ↑(rhs p) ↑q
  rw [rhs_apply, Nat.cast_id, ← @legendreSym.to_jacobiSym p ⟨pp⟩, qrSign.symm hqo hpo,
    qrSign.neg_one_pow hpo hqo, @legendreSym.quadratic_reciprocity' p q ⟨pp⟩ ⟨pq⟩ hp hq]
#align jacobi_sym.quadratic_reciprocity' jacobiSym.quadratic_reciprocity'

/-- The Law of Quadratic Reciprocity for the Jacobi symbol -/
theorem quadratic_reciprocity {a b : ℕ} (ha : Odd a) (hb : Odd b) :
    J(a | b) = (-1) ^ (a / 2 * (b / 2)) * J(b | a) := by
  rw [← qrSign.neg_one_pow ha hb, qrSign.symm ha hb, quadratic_reciprocity' ha hb]
  -- 🎉 no goals
#align jacobi_sym.quadratic_reciprocity jacobiSym.quadratic_reciprocity

/-- The Law of Quadratic Reciprocity for the Jacobi symbol: if `a` and `b` are natural numbers
with `a % 4 = 1` and `b` odd, then `J(a | b) = J(b | a)`. -/
theorem quadratic_reciprocity_one_mod_four {a b : ℕ} (ha : a % 4 = 1) (hb : Odd b) :
    J(a | b) = J(b | a) := by
  rw [quadratic_reciprocity (odd_iff.mpr (odd_of_mod_four_eq_one ha)) hb, pow_mul,
    neg_one_pow_div_two_of_one_mod_four ha, one_pow, one_mul]
#align jacobi_sym.quadratic_reciprocity_one_mod_four jacobiSym.quadratic_reciprocity_one_mod_four

/-- The Law of Quadratic Reciprocity for the Jacobi symbol: if `a` and `b` are natural numbers
with `a` odd and `b % 4 = 1`, then `J(a | b) = J(b | a)`. -/
theorem quadratic_reciprocity_one_mod_four' {a b : ℕ} (ha : Odd a) (hb : b % 4 = 1) :
    J(a | b) = J(b | a) :=
  (quadratic_reciprocity_one_mod_four hb ha).symm
#align jacobi_sym.quadratic_reciprocity_one_mod_four' jacobiSym.quadratic_reciprocity_one_mod_four'

/-- The Law of Quadratic Reciprocity for the Jacobi symbol: if `a` and `b` are natural numbers
both congruent to `3` mod `4`, then `J(a | b) = -J(b | a)`. -/
theorem quadratic_reciprocity_three_mod_four {a b : ℕ} (ha : a % 4 = 3) (hb : b % 4 = 3) :
    J(a | b) = -J(b | a) := by
  let nop := @neg_one_pow_div_two_of_three_mod_four
  -- ⊢ J(↑a | b) = -J(↑b | a)
  rw [quadratic_reciprocity, pow_mul, nop ha, nop hb, neg_one_mul] <;>
  -- ⊢ Odd a
    rwa [odd_iff, odd_of_mod_four_eq_three]
    -- 🎉 no goals
    -- 🎉 no goals
#align jacobi_sym.quadratic_reciprocity_three_mod_four jacobiSym.quadratic_reciprocity_three_mod_four

/-- The Jacobi symbol `J(a | b)` depends only on `b` mod `4*a` (version for `a : ℕ`). -/
theorem mod_right' (a : ℕ) {b : ℕ} (hb : Odd b) : J(a | b) = J(a | b % (4 * a)) := by
  rcases eq_or_ne a 0 with (rfl | ha₀)
  -- ⊢ J(↑0 | b) = J(↑0 | b % (4 * 0))
  · rw [mul_zero, mod_zero]
    -- 🎉 no goals
  have hb' : Odd (b % (4 * a)) := hb.mod_even (Even.mul_right (by norm_num) _)
  -- ⊢ J(↑a | b) = J(↑a | b % (4 * a))
  rcases exists_eq_pow_mul_and_not_dvd ha₀ 2 (by norm_num) with ⟨e, a', ha₁', ha₂⟩
  -- ⊢ J(↑a | b) = J(↑a | b % (4 * a))
  have ha₁ := odd_iff.mpr (two_dvd_ne_zero.mp ha₁')
  -- ⊢ J(↑a | b) = J(↑a | b % (4 * a))
  nth_rw 2 [ha₂]; nth_rw 1 [ha₂]
  -- ⊢ J(↑a | b) = J(↑(2 ^ e * a') | b % (4 * a))
                  -- ⊢ J(↑(2 ^ e * a') | b) = J(↑(2 ^ e * a') | b % (4 * a))
  rw [Nat.cast_mul, mul_left, mul_left, quadratic_reciprocity' ha₁ hb,
    quadratic_reciprocity' ha₁ hb', Nat.cast_pow, pow_left, pow_left, Nat.cast_two, at_two hb,
    at_two hb']
  congr 1; swap; congr 1
  -- ⊢ ↑χ₈ ↑b ^ e = ↑χ₈ ↑(b % (4 * a)) ^ e
           -- ⊢ qrSign b a' * J(↑b | a') = qrSign (b % (4 * a)) a' * J(↑(b % (4 * a)) | a')
  · simp_rw [qrSign]
    -- ⊢ J(↑χ₄ ↑b | a') = J(↑χ₄ ↑(b % (4 * a)) | a')
    rw [χ₄_nat_mod_four, χ₄_nat_mod_four (b % (4 * a)), mod_mod_of_dvd b (dvd_mul_right 4 a)]
    -- 🎉 no goals
  · rw [mod_left ↑(b % _), mod_left b, Int.coe_nat_mod, Int.emod_emod_of_dvd b]
    -- ⊢ ↑a' ∣ ↑(4 * a)
    simp only [ha₂, Nat.cast_mul, ← mul_assoc]
    -- ⊢ ↑a' ∣ ↑4 * ↑(2 ^ e) * ↑a'
    exact dvd_mul_left (a' : ℤ) (↑4 * ↑(2 ^ e))
    -- 🎉 no goals
  -- porting note: In mathlib3, it was written `cases' e`. In Lean 4, this resulted in the choice
  -- of a name other than e (for the case distinction of line 482) so we indicate the name
  -- to use explicitly.
  cases' e with e; · rfl
  -- ⊢ ↑χ₈ ↑b ^ zero = ↑χ₈ ↑(b % (4 * a)) ^ zero
                     -- 🎉 no goals
  · rw [χ₈_nat_mod_eight, χ₈_nat_mod_eight (b % (4 * a)), mod_mod_of_dvd b]
    -- ⊢ 8 ∣ 4 * a
    use 2 ^ e * a'; rw [ha₂, Nat.pow_succ]; ring
    -- ⊢ 4 * a = 8 * (2 ^ e * a')
                    -- ⊢ 4 * (2 ^ e * 2 * a') = 8 * (2 ^ e * a')
                                            -- 🎉 no goals
#align jacobi_sym.mod_right' jacobiSym.mod_right'

/-- The Jacobi symbol `J(a | b)` depends only on `b` mod `4*a`. -/
theorem mod_right (a : ℤ) {b : ℕ} (hb : Odd b) : J(a | b) = J(a | b % (4 * a.natAbs)) := by
  cases' Int.natAbs_eq a with ha ha <;> nth_rw 2 [ha] <;> nth_rw 1 [ha]
  -- ⊢ J(a | b) = J(a | b % (4 * Int.natAbs a))
                                        -- ⊢ J(a | b) = J(↑(Int.natAbs a) | b % (4 * Int.natAbs a))
                                        -- ⊢ J(a | b) = J(-↑(Int.natAbs a) | b % (4 * Int.natAbs a))
                                                          -- ⊢ J(↑(Int.natAbs a) | b) = J(↑(Int.natAbs a) | b % (4 * Int.natAbs a))
                                                          -- ⊢ J(-↑(Int.natAbs a) | b) = J(-↑(Int.natAbs a) | b % (4 * Int.natAbs a))
  · exact mod_right' a.natAbs hb
    -- 🎉 no goals
  · have hb' : Odd (b % (4 * a.natAbs)) := hb.mod_even (Even.mul_right (by norm_num) _)
    -- ⊢ J(-↑(Int.natAbs a) | b) = J(-↑(Int.natAbs a) | b % (4 * Int.natAbs a))
    rw [jacobiSym.neg _ hb, jacobiSym.neg _ hb', mod_right' _ hb, χ₄_nat_mod_four,
      χ₄_nat_mod_four (b % (4 * _)), mod_mod_of_dvd b (dvd_mul_right 4 _)]
#align jacobi_sym.mod_right jacobiSym.mod_right

end jacobiSym

end Jacobi
