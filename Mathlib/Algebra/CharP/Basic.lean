/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Joey van Langen, Casper Putz
-/
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Multiplicity
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Cast.Prod
import Mathlib.Algebra.Group.ULift
import Mathlib.GroupTheory.OrderOfElement

#align_import algebra.char_p.basic from "leanprover-community/mathlib"@"47a1a73351de8dd6c8d3d32b569c8e434b03ca47"

/-!
# Characteristic of semirings
-/


universe u v

open Finset

open BigOperators

variable {R : Type*}

namespace Commute

variable [Semiring R] {p : ℕ} {x y : R}

protected theorem add_pow_prime_pow_eq (hp : p.Prime) (h : Commute x y) (n : ℕ) :
    (x + y) ^ p ^ n =
      x ^ p ^ n + y ^ p ^ n +
        p * ∑ k in Ioo 0 (p ^ n), x ^ k * y ^ (p ^ n - k) * ↑((p ^ n).choose k / p) := by
  trans x ^ p ^ n + y ^ p ^ n + ∑ k in Ioo 0 (p ^ n), x ^ k * y ^ (p ^ n - k) * (p ^ n).choose k
  · simp_rw [h.add_pow, ← Nat.Ico_zero_eq_range, Nat.Ico_succ_right, Icc_eq_cons_Ico (zero_le _),
      Finset.sum_cons, Ico_eq_cons_Ioo (pow_pos hp.pos _), Finset.sum_cons, tsub_self, tsub_zero,
      pow_zero, Nat.choose_zero_right, Nat.choose_self, Nat.cast_one, mul_one, one_mul, ← add_assoc]
  · congr 1
    simp_rw [Finset.mul_sum, Nat.cast_comm, mul_assoc _ _ (p : R), ← Nat.cast_mul]
    refine' Finset.sum_congr rfl fun i hi => _
    rw [mem_Ioo] at hi
    rw [Nat.div_mul_cancel (hp.dvd_choose_pow hi.1.ne' hi.2.ne)]
#align commute.add_pow_prime_pow_eq Commute.add_pow_prime_pow_eq

protected theorem add_pow_prime_eq (hp : p.Prime) (h : Commute x y) :
    (x + y) ^ p =
      x ^ p + y ^ p + p * ∑ k in Finset.Ioo 0 p, x ^ k * y ^ (p - k) * ↑(p.choose k / p) :=
  by simpa using h.add_pow_prime_pow_eq hp 1
#align commute.add_pow_prime_eq Commute.add_pow_prime_eq

protected theorem exists_add_pow_prime_pow_eq (hp : p.Prime) (h : Commute x y) (n : ℕ) :
    ∃ r, (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n + p * r :=
  ⟨_, h.add_pow_prime_pow_eq hp n⟩
#align commute.exists_add_pow_prime_pow_eq Commute.exists_add_pow_prime_pow_eq

protected theorem exists_add_pow_prime_eq (hp : p.Prime) (h : Commute x y) :
    ∃ r, (x + y) ^ p = x ^ p + y ^ p + p * r :=
  ⟨_, h.add_pow_prime_eq hp⟩
#align commute.exists_add_pow_prime_eq Commute.exists_add_pow_prime_eq

end Commute

section CommSemiring

variable [CommSemiring R] {p : ℕ} {x y : R}

theorem add_pow_prime_pow_eq (hp : p.Prime) (x y : R) (n : ℕ) :
    (x + y) ^ p ^ n =
      x ^ p ^ n + y ^ p ^ n +
        p * ∑ k in Finset.Ioo 0 (p ^ n), x ^ k * y ^ (p ^ n - k) * ↑((p ^ n).choose k / p) :=
  (Commute.all x y).add_pow_prime_pow_eq hp n
#align add_pow_prime_pow_eq add_pow_prime_pow_eq

theorem add_pow_prime_eq (hp : p.Prime) (x y : R) :
    (x + y) ^ p =
      x ^ p + y ^ p + p * ∑ k in Finset.Ioo 0 p, x ^ k * y ^ (p - k) * ↑(p.choose k / p) :=
  (Commute.all x y).add_pow_prime_eq hp
#align add_pow_prime_eq add_pow_prime_eq

theorem exists_add_pow_prime_pow_eq (hp : p.Prime) (x y : R) (n : ℕ) :
    ∃ r, (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n + p * r :=
  (Commute.all x y).exists_add_pow_prime_pow_eq hp n
#align exists_add_pow_prime_pow_eq exists_add_pow_prime_pow_eq

theorem exists_add_pow_prime_eq (hp : p.Prime) (x y : R) :
    ∃ r, (x + y) ^ p = x ^ p + y ^ p + p * r :=
  (Commute.all x y).exists_add_pow_prime_eq hp
#align exists_add_pow_prime_eq exists_add_pow_prime_eq

end CommSemiring

variable (R)

/-- The generator of the kernel of the unique homomorphism ℕ → R for a semiring R.

*Warning*: for a semiring `R`, `CharP R 0` and `CharZero R` need not coincide.
* `CharP R 0` asks that only `0 : ℕ` maps to `0 : R` under the map `ℕ → R`;
* `CharZero R` requires an injection `ℕ ↪ R`.

For instance, endowing `{0, 1}` with addition given by `max` (i.e. `1` is absorbing), shows that
`CharZero {0, 1}` does not hold and yet `CharP {0, 1} 0` does.
This example is formalized in `Counterexamples/CharPZeroNeCharZero.lean`.
-/
@[mk_iff]
class CharP [AddMonoidWithOne R] (p : ℕ) : Prop where
  cast_eq_zero_iff' : ∀ x : ℕ, (x : R) = 0 ↔ p ∣ x
#align char_p CharP
#align char_p_iff charP_iff

-- porting note: the field of the structure had implicit arguments where they were
-- explicit in Lean 3
theorem CharP.cast_eq_zero_iff (R : Type u) [AddMonoidWithOne R] (p : ℕ) [CharP R p] (x : ℕ) :
    (x : R) = 0 ↔ p ∣ x :=
CharP.cast_eq_zero_iff' (R := R) (p := p) x

@[simp]
theorem CharP.cast_eq_zero [AddMonoidWithOne R] (p : ℕ) [CharP R p] : (p : R) = 0 :=
  (CharP.cast_eq_zero_iff R p p).2 (dvd_refl p)
#align char_p.cast_eq_zero CharP.cast_eq_zero

@[simp]
theorem CharP.cast_card_eq_zero [AddGroupWithOne R] [Fintype R] : (Fintype.card R : R) = 0 := by
  rw [← nsmul_one, card_nsmul_eq_zero]
#align char_p.cast_card_eq_zero CharP.cast_card_eq_zero

theorem CharP.addOrderOf_one (R) [Semiring R] : CharP R (addOrderOf (1 : R)) :=
  ⟨fun n => by rw [← Nat.smul_one_eq_coe, addOrderOf_dvd_iff_nsmul_eq_zero]⟩
#align char_p.add_order_of_one CharP.addOrderOf_one

theorem CharP.int_cast_eq_zero_iff [AddGroupWithOne R] (p : ℕ) [CharP R p] (a : ℤ) :
    (a : R) = 0 ↔ (p : ℤ) ∣ a := by
  rcases lt_trichotomy a 0 with (h | rfl | h)
  · rw [← neg_eq_zero, ← Int.cast_neg, ← dvd_neg]
    lift -a to ℕ using neg_nonneg.mpr (le_of_lt h) with b
    rw [Int.cast_ofNat, CharP.cast_eq_zero_iff R p, Int.coe_nat_dvd]
  · simp only [Int.cast_zero, eq_self_iff_true, dvd_zero]
  · lift a to ℕ using le_of_lt h with b
    rw [Int.cast_ofNat, CharP.cast_eq_zero_iff R p, Int.coe_nat_dvd]
#align char_p.int_cast_eq_zero_iff CharP.int_cast_eq_zero_iff

theorem CharP.intCast_eq_intCast [AddGroupWithOne R] (p : ℕ) [CharP R p] {a b : ℤ} :
    (a : R) = b ↔ a ≡ b [ZMOD p] := by
  rw [eq_comm, ← sub_eq_zero, ← Int.cast_sub, CharP.int_cast_eq_zero_iff R p, Int.modEq_iff_dvd]
#align char_p.int_cast_eq_int_cast CharP.intCast_eq_intCast

theorem CharP.natCast_eq_natCast' [AddMonoidWithOne R] (p : ℕ) [CharP R p] {a b : ℕ}
    (h : a ≡ b [MOD p]) : (a : R) = b := by
  wlog hle : a ≤ b
  · exact (this R p h.symm (le_of_not_le hle)).symm
  rw [Nat.modEq_iff_dvd' hle] at h
  rw [← Nat.sub_add_cancel hle, Nat.cast_add, (CharP.cast_eq_zero_iff R p _).mpr h, zero_add]

theorem CharP.natCast_eq_natCast [AddMonoidWithOne R] [IsRightCancelAdd R] (p : ℕ) [CharP R p]
    {a b : ℕ} : (a : R) = b ↔ a ≡ b [MOD p] := by
  wlog hle : a ≤ b
  · rw [eq_comm, this R p (le_of_not_le hle), Nat.ModEq.comm]
  rw [Nat.modEq_iff_dvd' hle, ← CharP.cast_eq_zero_iff R p (b - a),
    ← add_right_cancel_iff (G := R) (a := a) (b := b - a), zero_add, ← Nat.cast_add,
    Nat.sub_add_cancel hle, eq_comm]
#align char_p.nat_cast_eq_nat_cast CharP.natCast_eq_natCast

theorem CharP.intCast_eq_intCast_mod [AddGroupWithOne R] (p : ℕ) [CharP R p] {a : ℤ} :
    (a : R) = a % (p : ℤ) :=
  (CharP.intCast_eq_intCast R p).mpr (Int.mod_modEq a p).symm

theorem CharP.natCast_eq_natCast_mod [AddMonoidWithOne R] (p : ℕ) [CharP R p] {a : ℕ} :
    (a : R) = a % p :=
  CharP.natCast_eq_natCast' R p (Nat.mod_modEq a p).symm

theorem CharP.eq [AddMonoidWithOne R] {p q : ℕ} (_c1 : CharP R p) (_c2 : CharP R q) : p = q :=
  Nat.dvd_antisymm ((CharP.cast_eq_zero_iff R p q).1 (CharP.cast_eq_zero _ _))
    ((CharP.cast_eq_zero_iff R q p).1 (CharP.cast_eq_zero _ _))
#align char_p.eq CharP.eq

instance CharP.ofCharZero [AddMonoidWithOne R] [CharZero R] : CharP R 0 :=
  ⟨fun x => by rw [zero_dvd_iff, ← Nat.cast_zero, Nat.cast_inj]⟩
#align char_p.of_char_zero CharP.ofCharZero

theorem CharP.exists [NonAssocSemiring R] : ∃ p, CharP R p :=
  letI := Classical.decEq R
  by_cases
    (fun H : ∀ p : ℕ, (p : R) = 0 → p = 0 =>
      ⟨0, ⟨fun x => by rw [zero_dvd_iff]; exact ⟨H x, by rintro rfl; simp⟩⟩⟩)
    fun H =>
    ⟨Nat.find (not_forall.1 H),
      ⟨fun x =>
        ⟨fun H1 =>
          Nat.dvd_of_mod_eq_zero
            (by_contradiction fun H2 =>
              Nat.find_min (not_forall.1 H)
                (Nat.mod_lt x <|
                  Nat.pos_of_ne_zero <| not_of_not_imp <| Nat.find_spec (not_forall.1 H))
                (not_imp_of_and_not
                  ⟨by
                    rwa [← Nat.mod_add_div x (Nat.find (not_forall.1 H)), Nat.cast_add,
                      Nat.cast_mul,
                      of_not_not (not_not_of_not_imp <| Nat.find_spec (not_forall.1 H)),
                      zero_mul, add_zero] at H1,
                    H2⟩)),
          fun H1 => by
          rw [← Nat.mul_div_cancel' H1, Nat.cast_mul,
            of_not_not (not_not_of_not_imp <| Nat.find_spec (not_forall.1 H)),
            zero_mul]⟩⟩⟩
#align char_p.exists CharP.exists

theorem CharP.exists_unique [NonAssocSemiring R] : ∃! p, CharP R p :=
  let ⟨c, H⟩ := CharP.exists R
  ⟨c, H, fun _y H2 => CharP.eq R H2 H⟩
#align char_p.exists_unique CharP.exists_unique

theorem CharP.congr {R : Type u} [AddMonoidWithOne R] {p : ℕ} (q : ℕ) [hq : CharP R q] (h : q = p) :
    CharP R p :=
  h ▸ hq
#align char_p.congr CharP.congr

/-- Noncomputable function that outputs the unique characteristic of a semiring. -/
noncomputable def ringChar [NonAssocSemiring R] : ℕ :=
  Classical.choose (CharP.exists_unique R)
#align ring_char ringChar

namespace ringChar

variable [NonAssocSemiring R]

theorem spec : ∀ x : ℕ, (x : R) = 0 ↔ ringChar R ∣ x := by
  letI : CharP R (ringChar R) := (Classical.choose_spec (CharP.exists_unique R)).1
  exact CharP.cast_eq_zero_iff R (ringChar R)
#align ring_char.spec ringChar.spec

theorem eq (p : ℕ) [C : CharP R p] : ringChar R = p :=
  ((Classical.choose_spec (CharP.exists_unique R)).2 p C).symm
#align ring_char.eq ringChar.eq

instance charP : CharP R (ringChar R) :=
  ⟨spec R⟩
#align ring_char.char_p ringChar.charP

variable {R}

theorem of_eq {p : ℕ} (h : ringChar R = p) : CharP R p :=
  CharP.congr (ringChar R) h
#align ring_char.of_eq ringChar.of_eq

theorem eq_iff {p : ℕ} : ringChar R = p ↔ CharP R p :=
  ⟨of_eq, @eq R _ p⟩
#align ring_char.eq_iff ringChar.eq_iff

theorem dvd {x : ℕ} (hx : (x : R) = 0) : ringChar R ∣ x :=
  (spec R x).1 hx
#align ring_char.dvd ringChar.dvd

@[simp]
theorem eq_zero [CharZero R] : ringChar R = 0 :=
  eq R 0
#align ring_char.eq_zero ringChar.eq_zero

-- @[simp] -- Porting note: simp can prove this
theorem Nat.cast_ringChar : (ringChar R : R) = 0 := by rw [ringChar.spec]
#align ring_char.nat.cast_ring_char ringChar.Nat.cast_ringChar

end ringChar

theorem add_pow_char_of_commute [Semiring R] {p : ℕ} [hp : Fact p.Prime] [CharP R p] (x y : R)
    (h : Commute x y) : (x + y) ^ p = x ^ p + y ^ p := by
  let ⟨r, hr⟩ := h.exists_add_pow_prime_eq hp.out
  simp [hr]
#align add_pow_char_of_commute add_pow_char_of_commute

theorem add_pow_char_pow_of_commute [Semiring R] {p n : ℕ} [hp : Fact p.Prime] [CharP R p]
    (x y : R) (h : Commute x y) : (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n := by
  let ⟨r, hr⟩ := h.exists_add_pow_prime_pow_eq hp.out n
  simp [hr]
#align add_pow_char_pow_of_commute add_pow_char_pow_of_commute

theorem sub_pow_char_of_commute [Ring R] {p : ℕ} [Fact p.Prime] [CharP R p] (x y : R)
    (h : Commute x y) : (x - y) ^ p = x ^ p - y ^ p := by
  rw [eq_sub_iff_add_eq, ← add_pow_char_of_commute _ _ _ (Commute.sub_left h rfl)]
  simp
#align sub_pow_char_of_commute sub_pow_char_of_commute

theorem sub_pow_char_pow_of_commute [Ring R] {p : ℕ} [Fact p.Prime] [CharP R p] {n : ℕ} (x y : R)
    (h : Commute x y) : (x - y) ^ p ^ n = x ^ p ^ n - y ^ p ^ n := by
  induction n with
  | zero => simp
  | succ n n_ih =>
      rw [pow_succ', pow_mul, pow_mul, pow_mul, n_ih]
      apply sub_pow_char_of_commute; apply Commute.pow_pow h
#align sub_pow_char_pow_of_commute sub_pow_char_pow_of_commute

theorem add_pow_char [CommSemiring R] {p : ℕ} [Fact p.Prime] [CharP R p] (x y : R) :
    (x + y) ^ p = x ^ p + y ^ p :=
  add_pow_char_of_commute _ _ _ (Commute.all _ _)
#align add_pow_char add_pow_char

theorem add_pow_char_pow [CommSemiring R] {p : ℕ} [Fact p.Prime] [CharP R p] {n : ℕ} (x y : R) :
    (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n :=
  add_pow_char_pow_of_commute _ _ _ (Commute.all _ _)
#align add_pow_char_pow add_pow_char_pow

theorem sub_pow_char [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p] (x y : R) :
    (x - y) ^ p = x ^ p - y ^ p :=
  sub_pow_char_of_commute _ _ _ (Commute.all _ _)
#align sub_pow_char sub_pow_char

theorem sub_pow_char_pow [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p] {n : ℕ} (x y : R) :
    (x - y) ^ p ^ n = x ^ p ^ n - y ^ p ^ n :=
  sub_pow_char_pow_of_commute _ _ _ (Commute.all _ _)
#align sub_pow_char_pow sub_pow_char_pow

theorem CharP.neg_one_ne_one [Ring R] (p : ℕ) [CharP R p] [Fact (2 < p)] : (-1 : R) ≠ (1 : R) := by
  suffices (2 : R) ≠ 0 by
    intro h
    symm at h
    rw [← sub_eq_zero, sub_neg_eq_add] at h
    norm_num at h
    exact this h
    -- porting note: this could probably be golfed
  intro h
  rw [show (2 : R) = (2 : ℕ) by norm_cast] at h
  have := (CharP.cast_eq_zero_iff R p 2).mp h
  have := Nat.le_of_dvd (by decide) this
  rw [fact_iff] at *
  linarith
#align char_p.neg_one_ne_one CharP.neg_one_ne_one

theorem CharP.neg_one_pow_char [Ring R] (p : ℕ) [CharP R p] [Fact p.Prime] :
    (-1 : R) ^ p = -1 := by
  rw [eq_neg_iff_add_eq_zero]
  nth_rw 2 [← one_pow p]
  rw [← add_pow_char_of_commute R _ _ (Commute.one_right _), add_left_neg,
    zero_pow (Fact.out (p := Nat.Prime p)).pos]
#align char_p.neg_one_pow_char CharP.neg_one_pow_char

theorem CharP.neg_one_pow_char_pow [Ring R] (p n : ℕ) [CharP R p] [Fact p.Prime] :
    (-1 : R) ^ p ^ n = -1 := by
  rw [eq_neg_iff_add_eq_zero]
  nth_rw 2 [← one_pow (p ^ n)]
  rw [← add_pow_char_pow_of_commute R _ _ (Commute.one_right _), add_left_neg,
    zero_pow (pow_pos (Fact.out (p := Nat.Prime p)).pos _)]
#align char_p.neg_one_pow_char_pow CharP.neg_one_pow_char_pow

theorem RingHom.charP_iff_charP {K L : Type*} [DivisionRing K] [Semiring L] [Nontrivial L]
    (f : K →+* L) (p : ℕ) : CharP K p ↔ CharP L p := by
  simp only [charP_iff, ← f.injective.eq_iff, map_natCast f, f.map_zero]
#align ring_hom.char_p_iff_char_p RingHom.charP_iff_charP

section frobenius

section CommSemiring

variable [CommSemiring R] {S : Type v} [CommSemiring S] (f : R →* S) (g : R →+* S) (p : ℕ)
  [Fact p.Prime] [CharP R p] [CharP S p] (x y : R)

/-- The frobenius map that sends x to x^p -/
def frobenius : R →+* R where
  toFun x := x ^ p
  map_one' := one_pow p
  map_mul' x y := mul_pow x y p
  map_zero' := zero_pow (Fact.out (p := Nat.Prime p)).pos
  map_add' := add_pow_char R
#align frobenius frobenius

variable {R}

theorem frobenius_def : frobenius R p x = x ^ p :=
  rfl
#align frobenius_def frobenius_def

theorem iterate_frobenius (n : ℕ) : (frobenius R p)^[n] x = x ^ p ^ n := by
  induction n with
  | zero => simp
  | succ n n_ih =>
      rw [Function.iterate_succ', pow_succ', pow_mul, Function.comp_apply, frobenius_def, n_ih]
#align iterate_frobenius iterate_frobenius

theorem frobenius_mul : frobenius R p (x * y) = frobenius R p x * frobenius R p y :=
  (frobenius R p).map_mul x y
#align frobenius_mul frobenius_mul

theorem frobenius_one : frobenius R p 1 = 1 :=
  one_pow _
#align frobenius_one frobenius_one

theorem MonoidHom.map_frobenius : f (frobenius R p x) = frobenius S p (f x) :=
  f.map_pow x p
#align monoid_hom.map_frobenius MonoidHom.map_frobenius

theorem RingHom.map_frobenius : g (frobenius R p x) = frobenius S p (g x) :=
  g.map_pow x p
#align ring_hom.map_frobenius RingHom.map_frobenius

theorem MonoidHom.map_iterate_frobenius (n : ℕ) :
    f ((frobenius R p)^[n] x) = (frobenius S p)^[n] (f x) :=
  Function.Semiconj.iterate_right (f.map_frobenius p) n x
#align monoid_hom.map_iterate_frobenius MonoidHom.map_iterate_frobenius

theorem RingHom.map_iterate_frobenius (n : ℕ) :
    g ((frobenius R p)^[n] x) = (frobenius S p)^[n] (g x) :=
  g.toMonoidHom.map_iterate_frobenius p x n
#align ring_hom.map_iterate_frobenius RingHom.map_iterate_frobenius

theorem MonoidHom.iterate_map_frobenius (f : R →* R) (p : ℕ) [Fact p.Prime] [CharP R p] (n : ℕ) :
    f^[n] (frobenius R p x) = frobenius R p (f^[n] x) :=
  f.iterate_map_pow _ _ _
#align monoid_hom.iterate_map_frobenius MonoidHom.iterate_map_frobenius

theorem RingHom.iterate_map_frobenius (f : R →+* R) (p : ℕ) [Fact p.Prime] [CharP R p] (n : ℕ) :
    f^[n] (frobenius R p x) = frobenius R p (f^[n] x) :=
  f.iterate_map_pow _ _ _
#align ring_hom.iterate_map_frobenius RingHom.iterate_map_frobenius

variable (R)

theorem frobenius_zero : frobenius R p 0 = 0 :=
  (frobenius R p).map_zero
#align frobenius_zero frobenius_zero

theorem frobenius_add : frobenius R p (x + y) = frobenius R p x + frobenius R p y :=
  (frobenius R p).map_add x y
#align frobenius_add frobenius_add

theorem frobenius_nat_cast (n : ℕ) : frobenius R p n = n :=
  map_natCast (frobenius R p) n
#align frobenius_nat_cast frobenius_nat_cast

open BigOperators

variable {R}

theorem list_sum_pow_char (l : List R) : l.sum ^ p = (l.map (· ^ p : R → R)).sum :=
  (frobenius R p).map_list_sum _
#align list_sum_pow_char list_sum_pow_char

theorem multiset_sum_pow_char (s : Multiset R) : s.sum ^ p = (s.map (· ^ p : R → R)).sum :=
  (frobenius R p).map_multiset_sum _
#align multiset_sum_pow_char multiset_sum_pow_char

theorem sum_pow_char {ι : Type*} (s : Finset ι) (f : ι → R) :
    (∑ i in s, f i) ^ p = ∑ i in s, f i ^ p :=
  (frobenius R p).map_sum _ _
#align sum_pow_char sum_pow_char

variable (n : ℕ)

theorem list_sum_pow_char_pow (l : List R) : l.sum ^ p ^ n = (l.map (· ^ p ^ n : R → R)).sum := by
  induction' n with n ih
  · simp_rw [pow_zero, pow_one, List.map_id']
  simp_rw [pow_succ', pow_mul, ih, list_sum_pow_char, List.map_map]
  rfl

theorem multiset_sum_pow_char_pow (s : Multiset R) :
    s.sum ^ p ^ n = (s.map (· ^ p ^ n : R → R)).sum := by
  induction' n with n ih
  · simp_rw [pow_zero, pow_one, Multiset.map_id']
  simp_rw [pow_succ', pow_mul, ih, multiset_sum_pow_char, Multiset.map_map]
  rfl

theorem sum_pow_char_pow {ι : Type*} (s : Finset ι) (f : ι → R) :
    (∑ i in s, f i) ^ p ^ n = ∑ i in s, f i ^ p ^ n := by
  induction' n with n ih
  · simp_rw [pow_zero, pow_one]
  simp_rw [pow_succ', pow_mul, ih, sum_pow_char]

end CommSemiring

section CommRing

variable [CommRing R] {S : Type v} [CommRing S] (f : R →* S) (g : R →+* S) (p : ℕ) [Fact p.Prime]
  [CharP R p] [CharP S p] (x y : R)

theorem frobenius_neg : frobenius R p (-x) = -frobenius R p x :=
  (frobenius R p).map_neg x
#align frobenius_neg frobenius_neg

theorem frobenius_sub : frobenius R p (x - y) = frobenius R p x - frobenius R p y :=
  (frobenius R p).map_sub x y
#align frobenius_sub frobenius_sub

end CommRing

end frobenius

namespace CharP

section

variable [NonAssocRing R]

theorem charP_to_charZero (R : Type*) [AddGroupWithOne R] [CharP R 0] : CharZero R :=
  charZero_of_inj_zero fun n h0 => eq_zero_of_zero_dvd ((cast_eq_zero_iff R 0 n).mp h0)
#align char_p.char_p_to_char_zero CharP.charP_to_charZero

theorem charP_zero_iff_charZero (R : Type*) [AddGroupWithOne R] : CharP R 0 ↔ CharZero R :=
  ⟨fun _ ↦ charP_to_charZero R, fun _ ↦ ofCharZero R⟩

theorem cast_eq_mod (p : ℕ) [CharP R p] (k : ℕ) : (k : R) = (k % p : ℕ) :=
  calc
    (k : R) = ↑(k % p + p * (k / p)) := by rw [Nat.mod_add_div]
    _ = ↑(k % p) := by simp [cast_eq_zero]
#align char_p.cast_eq_mod CharP.cast_eq_mod

/-- The characteristic of a finite ring cannot be zero. -/
theorem char_ne_zero_of_finite (p : ℕ) [CharP R p] [Finite R] : p ≠ 0 := by
  rintro rfl
  haveI : CharZero R := charP_to_charZero R
  cases nonempty_fintype R
  exact absurd Nat.cast_injective (not_injective_infinite_finite ((↑) : ℕ → R))
#align char_p.char_ne_zero_of_finite CharP.char_ne_zero_of_finite

theorem ringChar_ne_zero_of_finite [Finite R] : ringChar R ≠ 0 :=
  char_ne_zero_of_finite R (ringChar R)
#align char_p.ring_char_ne_zero_of_finite CharP.ringChar_ne_zero_of_finite

theorem ringChar_zero_iff_CharZero [NonAssocRing R] : ringChar R = 0 ↔ CharZero R := by
  rw [ringChar.eq_iff, charP_zero_iff_charZero]

end

section Semiring

variable [NonAssocSemiring R]

theorem char_ne_one [Nontrivial R] (p : ℕ) [hc : CharP R p] : p ≠ 1 := fun hp : p = 1 =>
  have : (1 : R) = 0 := by simpa using (cast_eq_zero_iff R p 1).mpr (hp ▸ dvd_refl p)
  absurd this one_ne_zero
#align char_p.char_ne_one CharP.char_ne_one

section NoZeroDivisors

variable [NoZeroDivisors R]

theorem char_is_prime_of_two_le (p : ℕ) [hc : CharP R p] (hp : 2 ≤ p) : Nat.Prime p :=
  suffices ∀ (d) (_ : d ∣ p), d = 1 ∨ d = p from Nat.prime_def_lt''.mpr ⟨hp, this⟩
  fun (d : ℕ) (hdvd : ∃ e, p = d * e) =>
  let ⟨e, hmul⟩ := hdvd
  have : (p : R) = 0 := (cast_eq_zero_iff R p p).mpr (dvd_refl p)
  have : (d : R) * e = 0 := @Nat.cast_mul R _ d e ▸ hmul ▸ this
  Or.elim (eq_zero_or_eq_zero_of_mul_eq_zero this)
    (fun hd : (d : R) = 0 =>
      have : p ∣ d := (cast_eq_zero_iff R p d).mp hd
      show d = 1 ∨ d = p from Or.inr (this.antisymm' ⟨e, hmul⟩))
    fun he : (e : R) = 0 =>
    have : p ∣ e := (cast_eq_zero_iff R p e).mp he
    have : e ∣ p := dvd_of_mul_left_eq d (Eq.symm hmul)
    have : e = p := ‹e ∣ p›.antisymm ‹p ∣ e›
    have h₀ : 0 < p := two_pos.trans_le hp
    have : d * p = 1 * p := by rw [‹e = p›] at hmul; rw [one_mul]; exact Eq.symm hmul
    show d = 1 ∨ d = p from Or.inl (mul_right_cancel₀ h₀.ne' this)
#align char_p.char_is_prime_of_two_le CharP.char_is_prime_of_two_le

section Nontrivial

variable [Nontrivial R]

theorem char_is_prime_or_zero (p : ℕ) [hc : CharP R p] : Nat.Prime p ∨ p = 0 :=
  match p, hc with
  | 0, _ => Or.inr rfl
  | 1, hc => absurd (Eq.refl (1 : ℕ)) (@char_ne_one R _ _ (1 : ℕ) hc)
  | m + 2, hc => Or.inl (@char_is_prime_of_two_le R _ _ (m + 2) hc (Nat.le_add_left 2 m))
#align char_p.char_is_prime_or_zero CharP.char_is_prime_or_zero

theorem exists' (R : Type*) [NonAssocRing R] [NoZeroDivisors R] [Nontrivial R] :
    CharZero R ∨ ∃ p : ℕ, Fact p.Prime ∧ CharP R p := by
  obtain ⟨p, hchar⟩ := CharP.exists R
  rcases char_is_prime_or_zero R p with h | rfl
  exacts [Or.inr ⟨p, Fact.mk h, hchar⟩, Or.inl (charP_to_charZero R)]

theorem char_is_prime_of_pos (p : ℕ) [NeZero p] [CharP R p] : Fact p.Prime :=
  ⟨(CharP.char_is_prime_or_zero R _).resolve_right <| NeZero.ne p⟩
#align char_p.char_is_prime_of_pos CharP.char_is_prime_of_pos

end Nontrivial

end NoZeroDivisors

end Semiring

section Ring

variable [Ring R] [NoZeroDivisors R] [Nontrivial R] [Finite R]
-- porting note: removed redundant binder annotation update `(R)`

theorem char_is_prime (p : ℕ) [CharP R p] : p.Prime :=
  Or.resolve_right (char_is_prime_or_zero R p) (char_ne_zero_of_finite R p)
#align char_p.char_is_prime CharP.char_is_prime

end Ring

section NonAssocSemiring

variable {R} [NonAssocSemiring R]

-- see Note [lower instance priority]
instance (priority := 100) CharOne.subsingleton [CharP R 1] : Subsingleton R :=
  Subsingleton.intro <|
    suffices ∀ r : R, r = 0 from fun a b => show a = b by rw [this a, this b]
    fun r =>
    calc
      r = 1 * r := by rw [one_mul]
      _ = (1 : ℕ) * r := by rw [Nat.cast_one]
      _ = 0 * r := by rw [CharP.cast_eq_zero]
      _ = 0 := by rw [zero_mul]

theorem false_of_nontrivial_of_char_one [Nontrivial R] [CharP R 1] : False :=
  false_of_nontrivial_of_subsingleton R
#align char_p.false_of_nontrivial_of_char_one CharP.false_of_nontrivial_of_char_one

theorem ringChar_ne_one [Nontrivial R] : ringChar R ≠ 1 := by
  intro h
  apply zero_ne_one' R
  symm
  rw [← Nat.cast_one, ringChar.spec, h]
#align char_p.ring_char_ne_one CharP.ringChar_ne_one

theorem nontrivial_of_char_ne_one {v : ℕ} (hv : v ≠ 1) [hr : CharP R v] : Nontrivial R :=
  ⟨⟨(1 : ℕ), 0, fun h =>
      hv <| by rwa [CharP.cast_eq_zero_iff _ v, Nat.dvd_one] at h⟩⟩
#align char_p.nontrivial_of_char_ne_one CharP.nontrivial_of_char_ne_one

theorem ringChar_of_prime_eq_zero [Nontrivial R] {p : ℕ} (hprime : Nat.Prime p)
    (hp0 : (p : R) = 0) : ringChar R = p :=
  Or.resolve_left ((Nat.dvd_prime hprime).1 (ringChar.dvd hp0)) ringChar_ne_one
#align char_p.ring_char_of_prime_eq_zero CharP.ringChar_of_prime_eq_zero

theorem charP_iff_prime_eq_zero [Nontrivial R] {p : ℕ} (hp : p.Prime) :
    CharP R p ↔ (p : R) = 0 :=
  ⟨fun _ => cast_eq_zero R p,
   fun hp0 => (ringChar_of_prime_eq_zero hp hp0) ▸ inferInstance⟩

end NonAssocSemiring

end CharP

section

/-- We have `2 ≠ 0` in a nontrivial ring whose characteristic is not `2`. -/
protected theorem Ring.two_ne_zero {R : Type*} [NonAssocSemiring R] [Nontrivial R]
    (hR : ringChar R ≠ 2) : (2 : R) ≠ 0 := by
  rw [Ne.def, (by norm_cast : (2 : R) = (2 : ℕ)), ringChar.spec, Nat.dvd_prime Nat.prime_two]
  exact mt (or_iff_left hR).mp CharP.ringChar_ne_one
#align ring.two_ne_zero Ring.two_ne_zero

-- We have `CharP.neg_one_ne_one`, which assumes `[Ring R] (p : ℕ) [CharP R p] [Fact (2 < p)]`.
-- This is a version using `ringChar` instead.
/-- Characteristic `≠ 2` and nontrivial implies that `-1 ≠ 1`. -/
theorem Ring.neg_one_ne_one_of_char_ne_two {R : Type*} [NonAssocRing R] [Nontrivial R]
    (hR : ringChar R ≠ 2) : (-1 : R) ≠ 1 := fun h =>
  Ring.two_ne_zero hR (one_add_one_eq_two (α := R) ▸ neg_eq_iff_add_eq_zero.mp h)
#align ring.neg_one_ne_one_of_char_ne_two Ring.neg_one_ne_one_of_char_ne_two

/-- Characteristic `≠ 2` in a domain implies that `-a = a` iff `a = 0`. -/
theorem Ring.eq_self_iff_eq_zero_of_char_ne_two {R : Type*} [NonAssocRing R] [Nontrivial R]
    [NoZeroDivisors R] (hR : ringChar R ≠ 2) {a : R} : -a = a ↔ a = 0 :=
  ⟨fun h =>
    (mul_eq_zero.mp <| (two_mul a).trans <| neg_eq_iff_add_eq_zero.mp h).resolve_left
      (Ring.two_ne_zero hR),
    fun h => ((congr_arg (fun x => -x) h).trans neg_zero).trans h.symm⟩
#align ring.eq_self_iff_eq_zero_of_char_ne_two Ring.eq_self_iff_eq_zero_of_char_ne_two

end

section

variable [NonAssocRing R] [Fintype R] (n : ℕ)
-- porting note: removed redundant binder annotation update `(R)`

theorem charP_of_ne_zero (hn : Fintype.card R = n) (hR : ∀ i < n, (i : R) = 0 → i = 0) :
    CharP R n :=
  { cast_eq_zero_iff' := by
      have H : (n : R) = 0 := by rw [← hn, CharP.cast_card_eq_zero]
      intro k
      constructor
      · intro h
        rw [← Nat.mod_add_div k n, Nat.cast_add, Nat.cast_mul, H, zero_mul,
          add_zero] at h
        rw [Nat.dvd_iff_mod_eq_zero]
        apply hR _ (Nat.mod_lt _ _) h
        rw [← hn, gt_iff_lt, Fintype.card_pos_iff]
        exact ⟨0⟩
      · rintro ⟨k, rfl⟩
        rw [Nat.cast_mul, H, zero_mul] }
#align char_p_of_ne_zero charP_of_ne_zero

theorem charP_of_prime_pow_injective (R) [Ring R] [Fintype R] (p : ℕ) [hp : Fact p.Prime] (n : ℕ)
    (hn : Fintype.card R = p ^ n) (hR : ∀ i ≤ n, (p : R) ^ i = 0 → i = n) : CharP R (p ^ n) := by
  obtain ⟨c, hc⟩ := CharP.exists R
  have hcpn : c ∣ p ^ n := by rw [← CharP.cast_eq_zero_iff R c, ← hn, CharP.cast_card_eq_zero]
  obtain ⟨i, hi, hc⟩ : ∃ i ≤ n, c = p ^ i := by rwa [Nat.dvd_prime_pow hp.1] at hcpn
  obtain rfl : i = n := by
    apply hR i hi
    rw [← Nat.cast_pow, ← hc, CharP.cast_eq_zero]
  rwa [← hc]
#align char_p_of_prime_pow_injective charP_of_prime_pow_injective

end

section Prod

variable (S : Type v) [AddMonoidWithOne R] [AddMonoidWithOne S] (p q : ℕ) [CharP R p]

/-- The characteristic of the product of rings is the least common multiple of the
characteristics of the two rings. -/
instance Nat.lcm.charP [CharP S q] : CharP (R × S) (Nat.lcm p q) where
  cast_eq_zero_iff' := by
    simp [Prod.ext_iff, CharP.cast_eq_zero_iff R p, CharP.cast_eq_zero_iff S q, Nat.lcm_dvd_iff]

/-- The characteristic of the product of two rings of the same characteristic
  is the same as the characteristic of the rings -/
instance Prod.charP [CharP S p] : CharP (R × S) p := by
  convert Nat.lcm.charP R S p p; simp
#align prod.char_p Prod.charP

end Prod

instance ULift.charP [AddMonoidWithOne R] (p : ℕ) [CharP R p] : CharP (ULift.{v} R) p where
  cast_eq_zero_iff' n := Iff.trans (ULift.ext_iff _ _) <| CharP.cast_eq_zero_iff R p n
#align ulift.char_p ULift.charP

instance MulOpposite.charP [AddMonoidWithOne R] (p : ℕ) [CharP R p] : CharP Rᵐᵒᵖ p where
  cast_eq_zero_iff' n := MulOpposite.unop_inj.symm.trans <| CharP.cast_eq_zero_iff R p n
#align mul_opposite.char_p MulOpposite.charP

section

/-- If two integers from `{0, 1, -1}` result in equal elements in a ring `R`
that is nontrivial and of characteristic not `2`, then they are equal. -/
theorem Int.cast_injOn_of_ringChar_ne_two {R : Type*} [NonAssocRing R] [Nontrivial R]
    (hR : ringChar R ≠ 2) : ({0, 1, -1} : Set ℤ).InjOn ((↑) : ℤ → R) := by
  rintro _ (rfl | rfl | rfl) _ (rfl | rfl | rfl) h <;>
  simp only
    [cast_neg, cast_one, cast_zero, neg_eq_zero, one_ne_zero, zero_ne_one, zero_eq_neg] at h ⊢
  · exact ((Ring.neg_one_ne_one_of_char_ne_two hR).symm h).elim
  · exact ((Ring.neg_one_ne_one_of_char_ne_two hR) h).elim
#align int.cast_inj_on_of_ring_char_ne_two Int.cast_injOn_of_ringChar_ne_two

end

namespace NeZero

variable [AddMonoidWithOne R] {r : R} {n p : ℕ} {a : ℕ+}
-- porting note: removed redundant binder annotation update `(R)`

theorem of_not_dvd [CharP R p] (h : ¬p ∣ n) : NeZero (n : R) :=
  ⟨(CharP.cast_eq_zero_iff R p n).not.mpr h⟩
#align ne_zero.of_not_dvd NeZero.of_not_dvd

theorem not_char_dvd (p : ℕ) [CharP R p] (k : ℕ) [h : NeZero (k : R)] : ¬p ∣ k := by
  rwa [← CharP.cast_eq_zero_iff R p k, ← Ne.def, ← neZero_iff]
#align ne_zero.not_char_dvd NeZero.not_char_dvd

end NeZero

namespace CharZero

theorem charZero_iff_forall_prime_ne_zero
    [NonAssocRing R] [NoZeroDivisors R] [Nontrivial R] :
    CharZero R ↔ ∀ p : ℕ, p.Prime → (p : R) ≠ 0 := by
  refine ⟨fun h p hp => by simp [hp.ne_zero], fun h => ?_⟩
  let p := ringChar R
  cases CharP.char_is_prime_or_zero R p with
  | inl hp => simpa using h p hp
  | inr h =>
    haveI : CharP R 0 := h ▸ inferInstance
    exact CharP.charP_to_charZero R

end CharZero

namespace Fin

instance charP (n : ℕ) : CharP (Fin (n + 1)) (n + 1) where
    cast_eq_zero_iff' := by
      simp [Fin.eq_iff_veq, Nat.dvd_iff_mod_eq_zero]

end Fin
