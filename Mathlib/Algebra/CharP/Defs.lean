/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Joey van Langen, Casper Putz
-/
import Mathlib.Algebra.Group.Fin
import Mathlib.Algebra.Group.ULift
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Cast.Prod
import Mathlib.Data.Nat.Prime

#align_import algebra.char_p.basic from "leanprover-community/mathlib"@"47a1a73351de8dd6c8d3d32b569c8e434b03ca47"

/-!
# Characteristic of semirings
-/

assert_not_exists Finset

variable (R : Type*)

namespace CharP
section AddMonoidWithOne
variable [AddMonoidWithOne R] (p : ℕ)

/-- The generator of the kernel of the unique homomorphism ℕ → R for a semiring R.

*Warning*: for a semiring `R`, `CharP R 0` and `CharZero R` need not coincide.
* `CharP R 0` asks that only `0 : ℕ` maps to `0 : R` under the map `ℕ → R`;
* `CharZero R` requires an injection `ℕ ↪ R`.

For instance, endowing `{0, 1}` with addition given by `max` (i.e. `1` is absorbing), shows that
`CharZero {0, 1}` does not hold and yet `CharP {0, 1} 0` does.
This example is formalized in `Counterexamples/CharPZeroNeCharZero.lean`.
-/
@[mk_iff]
class _root_.CharP : Prop where
  cast_eq_zero_iff' : ∀ x : ℕ, (x : R) = 0 ↔ p ∣ x
#align char_p CharP
#align char_p_iff charP_iff

variable [CharP R p] {a b : ℕ}

-- Porting note: the field of the structure had implicit arguments where they were
-- explicit in Lean 3
lemma cast_eq_zero_iff (a : ℕ) : (a : R) = 0 ↔ p ∣ a := cast_eq_zero_iff' a

variable {R} in
lemma congr {q : ℕ} (h : p = q) : CharP R q := h ▸ ‹CharP R p›
#align char_p.congr CharP.congr

lemma natCast_eq_natCast' (h : a ≡ b [MOD p]) : (a : R) = b := by
  wlog hle : a ≤ b
  · exact (this R p h.symm (le_of_not_le hle)).symm
  rw [Nat.modEq_iff_dvd' hle] at h
  rw [← Nat.sub_add_cancel hle, Nat.cast_add, (cast_eq_zero_iff R p _).mpr h, zero_add]

@[simp] lemma cast_eq_zero : (p : R) = 0 := (cast_eq_zero_iff R p p).2 dvd_rfl
#align char_p.cast_eq_zero CharP.cast_eq_zero

-- See note [no_index around OfNat.ofNat]
--
-- TODO: This lemma needs to be `@[simp]` for confluence in the presence of `CharP.cast_eq_zero` and
-- `Nat.cast_ofNat`, but with `no_index` on its entire LHS, it matches literally every expression so
-- is too expensive. If lean4#2867 is fixed in a performant way, this can be made `@[simp]`.
--
-- @[simp]
lemma ofNat_eq_zero [p.AtLeastTwo] : no_index (OfNat.ofNat p : R) = 0 := cast_eq_zero R p

lemma natCast_eq_natCast_mod (a : ℕ) : (a : R) = a % p :=
  natCast_eq_natCast' R p (Nat.mod_modEq a p).symm

lemma eq {p q : ℕ} (_hp : CharP R p) (_hq : CharP R q) : p = q :=
  Nat.dvd_antisymm ((cast_eq_zero_iff R p q).1 (cast_eq_zero _ _))
    ((cast_eq_zero_iff R q p).1 (cast_eq_zero _ _))
#align char_p.eq CharP.eq

instance ofCharZero [CharZero R] : CharP R 0 where
  cast_eq_zero_iff' x := by rw [zero_dvd_iff, ← Nat.cast_zero, Nat.cast_inj]
#align char_p.of_char_zero CharP.ofCharZero

variable [IsRightCancelAdd R]

lemma natCast_eq_natCast : (a : R) = b ↔ a ≡ b [MOD p] := by
  wlog hle : a ≤ b
  · rw [eq_comm, this R p (le_of_not_le hle), Nat.ModEq.comm]
  rw [Nat.modEq_iff_dvd' hle, ← cast_eq_zero_iff R p (b - a),
    ← add_right_cancel_iff (G := R) (a := a) (b := b - a), zero_add, ← Nat.cast_add,
    Nat.sub_add_cancel hle, eq_comm]
#align char_p.nat_cast_eq_nat_cast CharP.natCast_eq_natCast

lemma natCast_injOn_Iio : (Set.Iio p).InjOn ((↑) : ℕ → R) :=
  fun _a ha _b hb hab ↦ ((natCast_eq_natCast _ _).1 hab).eq_of_lt_of_lt ha hb

end AddMonoidWithOne

section AddGroupWithOne
variable [AddGroupWithOne R] (p : ℕ) [CharP R p] {a b : ℤ}

lemma intCast_eq_zero_iff (a : ℤ) : (a : R) = 0 ↔ (p : ℤ) ∣ a := by
  rcases lt_trichotomy a 0 with (h | rfl | h)
  · rw [← neg_eq_zero, ← Int.cast_neg, ← dvd_neg]
    lift -a to ℕ using neg_nonneg.mpr (le_of_lt h) with b
    rw [Int.cast_natCast, CharP.cast_eq_zero_iff R p, Int.natCast_dvd_natCast]
  · simp only [Int.cast_zero, eq_self_iff_true, dvd_zero]
  · lift a to ℕ using le_of_lt h with b
    rw [Int.cast_natCast, CharP.cast_eq_zero_iff R p, Int.natCast_dvd_natCast]
#align char_p.int_cast_eq_zero_iff CharP.intCast_eq_zero_iff

lemma intCast_eq_intCast : (a : R) = b ↔ a ≡ b [ZMOD p] := by
  rw [eq_comm, ← sub_eq_zero, ← Int.cast_sub, CharP.intCast_eq_zero_iff R p, Int.modEq_iff_dvd]
#align char_p.int_cast_eq_int_cast CharP.intCast_eq_intCast

lemma intCast_eq_intCast_mod : (a : R) = a % (p : ℤ) :=
  (CharP.intCast_eq_intCast R p).mpr (Int.mod_modEq a p).symm

lemma charP_to_charZero [CharP R 0] : CharZero R :=
  charZero_of_inj_zero fun n h0 => eq_zero_of_zero_dvd ((cast_eq_zero_iff R 0 n).mp h0)
#align char_p.char_p_to_char_zero CharP.charP_to_charZero

lemma charP_zero_iff_charZero : CharP R 0 ↔ CharZero R :=
  ⟨fun _ ↦ charP_to_charZero R, fun _ ↦ ofCharZero R⟩

end AddGroupWithOne

section NonAssocSemiring
variable [NonAssocSemiring R]

lemma «exists» : ∃ p, CharP R p :=
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

lemma exists_unique : ∃! p, CharP R p :=
  let ⟨c, H⟩ := CharP.exists R
  ⟨c, H, fun _y H2 => CharP.eq R H2 H⟩
#align char_p.exists_unique CharP.exists_unique

end NonAssocSemiring
end CharP

/-- Noncomputable function that outputs the unique characteristic of a semiring. -/
noncomputable def ringChar [NonAssocSemiring R] : ℕ := Classical.choose (CharP.exists_unique R)
#align ring_char ringChar

namespace ringChar
variable [NonAssocSemiring R]

lemma spec : ∀ x : ℕ, (x : R) = 0 ↔ ringChar R ∣ x := by
  letI : CharP R (ringChar R) := (Classical.choose_spec (CharP.exists_unique R)).1
  exact CharP.cast_eq_zero_iff R (ringChar R)
#align ring_char.spec ringChar.spec

lemma eq (p : ℕ) [C : CharP R p] : ringChar R = p :=
  ((Classical.choose_spec (CharP.exists_unique R)).2 p C).symm
#align ring_char.eq ringChar.eq

instance charP : CharP R (ringChar R) :=
  ⟨spec R⟩
#align ring_char.char_p ringChar.charP

variable {R}

lemma of_eq {p : ℕ} (h : ringChar R = p) : CharP R p :=
  CharP.congr (ringChar R) h
#align ring_char.of_eq ringChar.of_eq

lemma eq_iff {p : ℕ} : ringChar R = p ↔ CharP R p :=
  ⟨of_eq, @eq R _ p⟩
#align ring_char.eq_iff ringChar.eq_iff

lemma dvd {x : ℕ} (hx : (x : R) = 0) : ringChar R ∣ x :=
  (spec R x).1 hx
#align ring_char.dvd ringChar.dvd

@[simp]
lemma eq_zero [CharZero R] : ringChar R = 0 :=
  eq R 0
#align ring_char.eq_zero ringChar.eq_zero

-- @[simp] -- Porting note (#10618): simp can prove this
lemma Nat.cast_ringChar : (ringChar R : R) = 0 := by rw [ringChar.spec]
#align ring_char.nat.cast_ring_char ringChar.Nat.cast_ringChar

end ringChar

lemma CharP.neg_one_ne_one [Ring R] (p : ℕ) [CharP R p] [Fact (2 < p)] : (-1 : R) ≠ (1 : R) := by
  suffices (2 : R) ≠ 0 by
    intro h
    symm at h
    rw [← sub_eq_zero, sub_neg_eq_add] at h
    norm_num at h
    exact this h
    -- Porting note: this could probably be golfed
  intro h
  rw [show (2 : R) = (2 : ℕ) by norm_cast] at h
  have := (CharP.cast_eq_zero_iff R p 2).mp h
  have := Nat.le_of_dvd (by decide) this
  rw [fact_iff] at *
  omega
#align char_p.neg_one_ne_one CharP.neg_one_ne_one

lemma RingHom.charP_iff_charP {K L : Type*} [DivisionRing K] [Semiring L] [Nontrivial L]
    (f : K →+* L) (p : ℕ) : CharP K p ↔ CharP L p := by
  simp only [charP_iff, ← f.injective.eq_iff, map_natCast f, map_zero f]
#align ring_hom.char_p_iff_char_p RingHom.charP_iff_charP

namespace CharP

section

variable [NonAssocRing R]

lemma cast_eq_mod (p : ℕ) [CharP R p] (k : ℕ) : (k : R) = (k % p : ℕ) :=
  calc
    (k : R) = ↑(k % p + p * (k / p)) := by rw [Nat.mod_add_div]
    _ = ↑(k % p) := by simp [cast_eq_zero]
#align char_p.cast_eq_mod CharP.cast_eq_mod

lemma ringChar_zero_iff_CharZero : ringChar R = 0 ↔ CharZero R := by
  rw [ringChar.eq_iff, charP_zero_iff_charZero]

end

section Semiring

variable [NonAssocSemiring R]

lemma char_ne_one [Nontrivial R] (p : ℕ) [hc : CharP R p] : p ≠ 1 := fun hp : p = 1 =>
  have : (1 : R) = 0 := by simpa using (cast_eq_zero_iff R p 1).mpr (hp ▸ dvd_refl p)
  absurd this one_ne_zero
#align char_p.char_ne_one CharP.char_ne_one

section NoZeroDivisors

variable [NoZeroDivisors R]

lemma char_is_prime_of_two_le (p : ℕ) [hc : CharP R p] (hp : 2 ≤ p) : Nat.Prime p :=
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
    have h₀ : 0 < p := by omega
    have : d * p = 1 * p := by rw [‹e = p›] at hmul; rw [one_mul]; exact Eq.symm hmul
    show d = 1 ∨ d = p from Or.inl (mul_right_cancel₀ h₀.ne' this)
#align char_p.char_is_prime_of_two_le CharP.char_is_prime_of_two_le

section Nontrivial

variable [Nontrivial R]

lemma char_is_prime_or_zero (p : ℕ) [hc : CharP R p] : Nat.Prime p ∨ p = 0 :=
  match p, hc with
  | 0, _ => Or.inr rfl
  | 1, hc => absurd (Eq.refl (1 : ℕ)) (@char_ne_one R _ _ (1 : ℕ) hc)
  | m + 2, hc => Or.inl (@char_is_prime_of_two_le R _ _ (m + 2) hc (Nat.le_add_left 2 m))
#align char_p.char_is_prime_or_zero CharP.char_is_prime_or_zero

lemma exists' (R : Type*) [NonAssocRing R] [NoZeroDivisors R] [Nontrivial R] :
    CharZero R ∨ ∃ p : ℕ, Fact p.Prime ∧ CharP R p := by
  obtain ⟨p, hchar⟩ := CharP.exists R
  rcases char_is_prime_or_zero R p with h | rfl
  exacts [Or.inr ⟨p, Fact.mk h, hchar⟩, Or.inl (charP_to_charZero R)]

lemma char_is_prime_of_pos (p : ℕ) [NeZero p] [CharP R p] : Fact p.Prime :=
  ⟨(CharP.char_is_prime_or_zero R _).resolve_right <| NeZero.ne p⟩
#align char_p.char_is_prime_of_pos CharP.char_is_prime_of_pos

end Nontrivial

end NoZeroDivisors

end Semiring

section NonAssocSemiring

variable {R} [NonAssocSemiring R]

-- This lemma is not an instance, to make sure that trying to prove `α` is a subsingleton does
-- not try to find a ring structure on `α`, which can be expensive.
lemma CharOne.subsingleton [CharP R 1] : Subsingleton R :=
  Subsingleton.intro <|
    suffices ∀ r : R, r = 0 from fun a b => show a = b by rw [this a, this b]
    fun r =>
    calc
      r = 1 * r := by rw [one_mul]
      _ = (1 : ℕ) * r := by rw [Nat.cast_one]
      _ = 0 * r := by rw [CharP.cast_eq_zero]
      _ = 0 := by rw [zero_mul]

lemma false_of_nontrivial_of_char_one [Nontrivial R] [CharP R 1] : False := by
  have : Subsingleton R := CharOne.subsingleton
  exact false_of_nontrivial_of_subsingleton R
#align char_p.false_of_nontrivial_of_char_one CharP.false_of_nontrivial_of_char_one

lemma ringChar_ne_one [Nontrivial R] : ringChar R ≠ 1 := by
  intro h
  apply zero_ne_one' R
  symm
  rw [← Nat.cast_one, ringChar.spec, h]
#align char_p.ring_char_ne_one CharP.ringChar_ne_one

lemma nontrivial_of_char_ne_one {v : ℕ} (hv : v ≠ 1) [hr : CharP R v] : Nontrivial R :=
  ⟨⟨(1 : ℕ), 0, fun h =>
      hv <| by rwa [CharP.cast_eq_zero_iff _ v, Nat.dvd_one] at h⟩⟩
#align char_p.nontrivial_of_char_ne_one CharP.nontrivial_of_char_ne_one

lemma ringChar_of_prime_eq_zero [Nontrivial R] {p : ℕ} (hprime : Nat.Prime p)
    (hp0 : (p : R) = 0) : ringChar R = p :=
  Or.resolve_left ((Nat.dvd_prime hprime).1 (ringChar.dvd hp0)) ringChar_ne_one
#align char_p.ring_char_of_prime_eq_zero CharP.ringChar_of_prime_eq_zero

lemma charP_iff_prime_eq_zero [Nontrivial R] {p : ℕ} (hp : p.Prime) :
    CharP R p ↔ (p : R) = 0 :=
  ⟨fun _ => cast_eq_zero R p,
   fun hp0 => (ringChar_of_prime_eq_zero hp hp0) ▸ inferInstance⟩

end NonAssocSemiring
end CharP

section

/-- We have `2 ≠ 0` in a nontrivial ring whose characteristic is not `2`. -/
protected lemma Ring.two_ne_zero {R : Type*} [NonAssocSemiring R] [Nontrivial R]
    (hR : ringChar R ≠ 2) : (2 : R) ≠ 0 := by
  rw [Ne, (by norm_cast : (2 : R) = (2 : ℕ)), ringChar.spec, Nat.dvd_prime Nat.prime_two]
  exact mt (or_iff_left hR).mp CharP.ringChar_ne_one
#align ring.two_ne_zero Ring.two_ne_zero

-- We have `CharP.neg_one_ne_one`, which assumes `[Ring R] (p : ℕ) [CharP R p] [Fact (2 < p)]`.
-- This is a version using `ringChar` instead.
/-- Characteristic `≠ 2` and nontrivial implies that `-1 ≠ 1`. -/
lemma Ring.neg_one_ne_one_of_char_ne_two {R : Type*} [NonAssocRing R] [Nontrivial R]
    (hR : ringChar R ≠ 2) : (-1 : R) ≠ 1 := fun h =>
  Ring.two_ne_zero hR (one_add_one_eq_two (R := R) ▸ neg_eq_iff_add_eq_zero.mp h)
#align ring.neg_one_ne_one_of_char_ne_two Ring.neg_one_ne_one_of_char_ne_two

/-- Characteristic `≠ 2` in a domain implies that `-a = a` iff `a = 0`. -/
lemma Ring.eq_self_iff_eq_zero_of_char_ne_two {R : Type*} [NonAssocRing R] [Nontrivial R]
    [NoZeroDivisors R] (hR : ringChar R ≠ 2) {a : R} : -a = a ↔ a = 0 :=
  ⟨fun h =>
    (mul_eq_zero.mp <| (two_mul a).trans <| neg_eq_iff_add_eq_zero.mp h).resolve_left
      (Ring.two_ne_zero hR),
    fun h => ((congr_arg (fun x => -x) h).trans neg_zero).trans h.symm⟩
#align ring.eq_self_iff_eq_zero_of_char_ne_two Ring.eq_self_iff_eq_zero_of_char_ne_two

end

section Prod
variable (S : Type*) [AddMonoidWithOne R] [AddMonoidWithOne S] (p q : ℕ) [CharP R p]

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

instance Prod.charZero_of_left [CharZero R] : CharZero (R × S) where
  cast_injective _ _ h := CharZero.cast_injective congr(Prod.fst $h)

instance Prod.charZero_of_right [CharZero S] : CharZero (R × S) where
  cast_injective _ _ h := CharZero.cast_injective congr(Prod.snd $h)

end Prod

instance ULift.charP [AddMonoidWithOne R] (p : ℕ) [CharP R p] : CharP (ULift R) p where
  cast_eq_zero_iff' n := Iff.trans (ULift.ext_iff _ _) <| CharP.cast_eq_zero_iff R p n
#align ulift.char_p ULift.charP

instance MulOpposite.charP [AddMonoidWithOne R] (p : ℕ) [CharP R p] : CharP Rᵐᵒᵖ p where
  cast_eq_zero_iff' n := MulOpposite.unop_inj.symm.trans <| CharP.cast_eq_zero_iff R p n
#align mul_opposite.char_p MulOpposite.charP

section

/-- If two integers from `{0, 1, -1}` result in equal elements in a ring `R`
that is nontrivial and of characteristic not `2`, then they are equal. -/
lemma Int.cast_injOn_of_ringChar_ne_two {R : Type*} [NonAssocRing R] [Nontrivial R]
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

lemma of_not_dvd [CharP R p] (h : ¬p ∣ n) : NeZero (n : R) :=
  ⟨(CharP.cast_eq_zero_iff R p n).not.mpr h⟩
#align ne_zero.of_not_dvd NeZero.of_not_dvd

lemma not_char_dvd (p : ℕ) [CharP R p] (k : ℕ) [h : NeZero (k : R)] : ¬p ∣ k := by
  rwa [← CharP.cast_eq_zero_iff R p k, ← Ne, ← neZero_iff]
#align ne_zero.not_char_dvd NeZero.not_char_dvd

end NeZero

namespace CharZero

lemma charZero_iff_forall_prime_ne_zero [NonAssocRing R] [NoZeroDivisors R] [Nontrivial R] :
    CharZero R ↔ ∀ p : ℕ, p.Prime → (p : R) ≠ 0 := by
  refine ⟨fun h p hp => by simp [hp.ne_zero], fun h => ?_⟩
  let p := ringChar R
  cases CharP.char_is_prime_or_zero R p with
  | inl hp => simpa using h p hp
  | inr h => have : CharP R 0 := h ▸ inferInstance; exact CharP.charP_to_charZero R

end CharZero

namespace Fin

instance charP (n : ℕ) : CharP (Fin (n + 1)) (n + 1) where
    cast_eq_zero_iff' := by simp [Fin.ext_iff, Nat.dvd_iff_mod_eq_zero]

end Fin
