/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Mathlib.Data.Nat.Order.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Ring.CharZero
import Mathlib.Algebra.Divisibility.Basic

#align_import data.int.order.basic from "leanprover-community/mathlib"@"e8638a0fcaf73e4500469f368ef9494e495099b3"

/-!
# Order instances on the integers

This file contains:
* instances on `ℤ`. The stronger one is `Int.linearOrderedCommRing`.
* basic lemmas about integers that involve order properties.

## Recursors

* `Int.rec`: Sign disjunction. Something is true/defined on `ℤ` if it's true/defined for nonnegative
  and for negative values. (Defined in core Lean 3)
* `Int.inductionOn`: Simple growing induction on positive numbers, plus simple decreasing induction
  on negative numbers. Note that this recursor is currently only `Prop`-valued.
* `Int.inductionOn'`: Simple growing induction for numbers greater than `b`, plus simple decreasing
  induction on numbers less than `b`.
-/

open Function Nat

namespace Int

instance linearOrderedCommRing : LinearOrderedCommRing ℤ :=
  { instCommRingInt, instLinearOrderInt, instNontrivialInt with
    add_le_add_left := @Int.add_le_add_left,
    mul_pos := @Int.mul_pos, zero_le_one := le_of_lt Int.zero_lt_one }

/-! ### Extra instances to short-circuit type class resolution
-/


instance orderedCommRing : OrderedCommRing ℤ :=
  StrictOrderedCommRing.toOrderedCommRing'

instance orderedRing : OrderedRing ℤ :=
  StrictOrderedRing.toOrderedRing'

instance linearOrderedAddCommGroup : LinearOrderedAddCommGroup ℤ := by infer_instance

end Int

namespace Int

theorem abs_eq_natAbs : ∀ a : ℤ, |a| = natAbs a
  | (n : ℕ) => abs_of_nonneg <| ofNat_zero_le _
  | -[_+1] => abs_of_nonpos <| le_of_lt <| negSucc_lt_zero _
#align int.abs_eq_nat_abs Int.abs_eq_natAbs

@[simp, norm_cast] lemma natCast_natAbs (n : ℤ) : (n.natAbs : ℤ) = |n| := n.abs_eq_natAbs.symm
#align int.coe_nat_abs Int.natCast_natAbs

lemma _root_.Nat.cast_natAbs {α : Type*} [AddGroupWithOne α] (n : ℤ) : (n.natAbs : α) = |n| := by
  rw [← natCast_natAbs, Int.cast_ofNat]
#align nat.cast_nat_abs Nat.cast_natAbs

theorem natAbs_abs (a : ℤ) : natAbs |a| = natAbs a := by rw [abs_eq_natAbs]; rfl
#align int.nat_abs_abs Int.natAbs_abs

theorem sign_mul_abs (a : ℤ) : sign a * |a| = a := by
  rw [abs_eq_natAbs, sign_mul_natAbs a]
#align int.sign_mul_abs Int.sign_mul_abs

lemma natAbs_sq (x : ℤ) : (x.natAbs : ℤ) ^ 2 = x ^ 2 := by rw [sq, Int.natAbs_mul_self', sq]
#align int.nat_abs_sq Int.natAbs_sq

alias natAbs_pow_two := natAbs_sq
#align int.nat_abs_pow_two Int.natAbs_pow_two

lemma natAbs_le_self_sq (a : ℤ) : (Int.natAbs a : ℤ) ≤ a ^ 2 := by
  rw [← Int.natAbs_sq a, sq]
  norm_cast
  apply Nat.le_mul_self
#align int.abs_le_self_sq Int.natAbs_le_self_sq

alias natAbs_le_self_pow_two := natAbs_le_self_sq

lemma le_self_sq (b : ℤ) : b ≤ b ^ 2 := le_trans le_natAbs (natAbs_le_self_sq _)
#align int.le_self_sq Int.le_self_sq

alias le_self_pow_two := le_self_sq
#align int.le_self_pow_two Int.le_self_pow_two

theorem natCast_eq_zero {n : ℕ} : (n : ℤ) = 0 ↔ n = 0 :=
  Nat.cast_eq_zero
#align int.coe_nat_eq_zero Int.natCast_eq_zero

theorem natCast_ne_zero {n : ℕ} : (n : ℤ) ≠ 0 ↔ n ≠ 0 := by simp
#align int.coe_nat_ne_zero Int.natCast_ne_zero

theorem natCast_ne_zero_iff_pos {n : ℕ} : (n : ℤ) ≠ 0 ↔ 0 < n :=
  ⟨fun h => Nat.pos_of_ne_zero (natCast_ne_zero.1 h),
   fun h => (_root_.ne_of_lt (ofNat_lt.2 h)).symm⟩
#align int.coe_nat_ne_zero_iff_pos Int.natCast_ne_zero_iff_pos

@[norm_cast] lemma abs_natCast (n : ℕ) : |(n : ℤ)| = n := abs_of_nonneg (natCast_nonneg n)
#align int.abs_coe_nat Int.abs_natCast

theorem sign_add_eq_of_sign_eq : ∀ {m n : ℤ}, m.sign = n.sign → (m + n).sign = n.sign := by
  have : (1 : ℤ) ≠ -1 := by decide
  rintro ((_ | m) | m) ((_ | n) | n) <;> simp [this, this.symm, Int.negSucc_add_negSucc]
  rw [Int.sign_eq_one_iff_pos]
  apply Int.add_pos <;> · exact zero_lt_one.trans_le (le_add_of_nonneg_left <| natCast_nonneg _)
#align int.sign_add_eq_of_sign_eq Int.sign_add_eq_of_sign_eq

/-- Note this holds in marginally more generality than `Int.cast_mul` -/
lemma cast_mul_eq_zsmul_cast {α : Type*} [AddCommGroupWithOne α] :
    ∀ m n : ℤ, ↑(m * n) = m • (n : α) :=
  fun m ↦ Int.induction_on m (by simp) (fun _ ih ↦ by simp [add_mul, add_zsmul, ih]) fun _ ih ↦ by
    simp only [sub_mul, one_mul, cast_sub, ih, sub_zsmul, one_zsmul, ← sub_eq_add_neg, forall_const]
#align int.cast_mul_eq_zsmul_cast Int.cast_mul_eq_zsmul_cast

theorem natAbs_sub_pos_iff {i j : ℤ} : 0 < natAbs (i - j) ↔ i ≠ j := by
  rw [natAbs_pos, ne_eq, sub_eq_zero]

theorem natAbs_sub_ne_zero_iff {i j : ℤ} : natAbs (i - j) ≠ 0 ↔ i ≠ j :=
  Nat.ne_zero_iff_zero_lt.trans natAbs_sub_pos_iff

/-! ### succ and pred -/


theorem lt_succ_self (a : ℤ) : a < succ a :=
  lt_add_of_pos_right _ zero_lt_one
#align int.lt_succ_self Int.lt_succ_self

theorem pred_self_lt (a : ℤ) : pred a < a :=
  sub_lt_self _ zero_lt_one
#align int.pred_self_lt Int.pred_self_lt

#align int.lt_add_one_iff Int.lt_add_one_iff
#align int.le_add_one Int.le_add_one

theorem le_add_one_iff {m n : ℤ} : m ≤ n + 1 ↔ m ≤ n ∨ m = n + 1 := by
  rw [le_iff_lt_or_eq, lt_add_one_iff]

theorem sub_one_lt_iff {a b : ℤ} : a - 1 < b ↔ a ≤ b :=
  sub_lt_iff_lt_add.trans lt_add_one_iff
#align int.sub_one_lt_iff Int.sub_one_lt_iff

theorem le_sub_one_iff {a b : ℤ} : a ≤ b - 1 ↔ a < b :=
  le_sub_iff_add_le
#align int.le_sub_one_iff Int.le_sub_one_iff

@[simp]
theorem abs_lt_one_iff {a : ℤ} : |a| < 1 ↔ a = 0 := by
  rw [← zero_add 1, lt_add_one_iff, abs_nonpos_iff]
#align int.abs_lt_one_iff Int.abs_lt_one_iff

theorem abs_le_one_iff {a : ℤ} : |a| ≤ 1 ↔ a = 0 ∨ a = 1 ∨ a = -1 := by
  rw [le_iff_lt_or_eq, abs_lt_one_iff, abs_eq (zero_le_one' ℤ)]
#align int.abs_le_one_iff Int.abs_le_one_iff

theorem one_le_abs {z : ℤ} (h₀ : z ≠ 0) : 1 ≤ |z| :=
  add_one_le_iff.mpr (abs_pos.mpr h₀)
#align int.one_le_abs Int.one_le_abs

/-- Inductively define a function on `ℤ` by defining it at `b`, for the `succ` of a number greater
than `b`, and the `pred` of a number less than `b`. -/
@[elab_as_elim] protected def inductionOn' {C : ℤ → Sort*}
    (z : ℤ) (b : ℤ) (H0 : C b) (Hs : ∀ k, b ≤ k → C k → C (k + 1))
    (Hp : ∀ k ≤ b, C k → C (k - 1)) : C z := by
  rw [← sub_add_cancel (G := ℤ) z b, add_comm]
  exact match z - b with
  | .ofNat n => pos n
  | .negSucc n => neg n
where
  /-- The positive case of `Int.inductionOn'`. -/
  pos : ∀ n : ℕ, C (b + n)
  | 0 => _root_.cast (by erw [add_zero]) H0
  | n+1 => _root_.cast (by rw [add_assoc]; rfl) <|
    Hs _ (Int.le_add_of_nonneg_right (ofNat_nonneg _)) (pos n)

  /-- The negative case of `Int.inductionOn'`. -/
  neg : ∀ n : ℕ, C (b + -[n+1])
  | 0 => Hp _ (Int.le_refl _) H0
  | n+1 => by
    refine _root_.cast (by rw [add_sub_assoc]; rfl) (Hp _ (Int.le_of_lt ?_) (neg n))
    conv => rhs; apply (add_zero b).symm
    rw [Int.add_lt_add_iff_left]; apply negSucc_lt_zero
#align int.induction_on' Int.inductionOn'

/-- See `Int.inductionOn'` for an induction in both directions. -/
protected theorem le_induction {P : ℤ → Prop} {m : ℤ} (h0 : P m)
    (h1 : ∀ n : ℤ, m ≤ n → P n → P (n + 1)) (n : ℤ) : m ≤ n → P n := by
  refine Int.inductionOn' n m ?_ ?_ ?_
  · intro
    exact h0
  · intro k hle hi _
    exact h1 k hle (hi hle)
  · intro k hle _ hle'
    exfalso
    exact lt_irrefl k (le_sub_one_iff.mp (hle.trans hle'))
#align int.le_induction Int.le_induction

/-- See `Int.inductionOn'` for an induction in both directions. -/
protected theorem le_induction_down {P : ℤ → Prop} {m : ℤ} (h0 : P m)
    (h1 : ∀ n : ℤ, n ≤ m → P n → P (n - 1)) (n : ℤ) : n ≤ m → P n := by
  refine Int.inductionOn' n m ?_ ?_ ?_
  · intro
    exact h0
  · intro k hle _ hle'
    exfalso
    exact lt_irrefl k (add_one_le_iff.mp (hle'.trans hle))
  · intro k hle hi _
    exact h1 k hle (hi hle)
#align int.le_induction_down Int.le_induction_down

/-! ### nat abs -/


variable {a b : ℤ} {n : ℕ}

attribute [simp] natAbs_ofNat natAbs_zero natAbs_one

#align int.nat_abs_dvd_iff_dvd Int.natAbs_dvd_natAbs

/-! ### `/`  -/

#align int.div_nonpos Int.ediv_nonpos

theorem ediv_eq_zero_of_lt_abs {a b : ℤ} (H1 : 0 ≤ a) (H2 : a < |b|) : a / b = 0 :=
  match b, |b|, abs_eq_natAbs b, H2 with
  | (n : ℕ), _, rfl, H2 => ediv_eq_zero_of_lt H1 H2
  | -[n+1], _, rfl, H2 => neg_injective <| by rw [← Int.ediv_neg]; exact ediv_eq_zero_of_lt H1 H2
#align int.div_eq_zero_of_lt_abs Int.ediv_eq_zero_of_lt_abs

#align int.add_mul_div_right Int.add_mul_ediv_right

#align int.add_mul_div_left Int.add_mul_ediv_left

#align int.mul_div_cancel Int.mul_ediv_cancel

#align int.mul_div_cancel_left Int.mul_ediv_cancel_left

#align int.div_self Int.ediv_self

attribute [local simp] Int.zero_ediv Int.ediv_zero

#align int.add_div_of_dvd_right Int.add_ediv_of_dvd_right

#align int.add_div_of_dvd_left Int.add_ediv_of_dvd_left

/-! ### mod -/


@[simp]
theorem emod_abs (a b : ℤ) : a % |b| = a % b :=
  abs_by_cases (fun i => a % i = a % b) rfl (emod_neg _ _)
#align int.mod_abs Int.emod_abs

#align int.mod_nonneg Int.emod_nonneg

#align int.mod_lt_of_pos Int.emod_lt_of_pos

theorem emod_lt (a : ℤ) {b : ℤ} (H : b ≠ 0) : a % b < |b| := by
  rw [← emod_abs]; exact emod_lt_of_pos _ (abs_pos.2 H)
#align int.mod_lt Int.emod_lt

#align int.add_mul_mod_self Int.add_mul_emod_self

#align int.add_mul_mod_self_left Int.add_mul_emod_self_left

#align int.add_mod_self Int.add_emod_self

#align int.add_mod_self_left Int.add_emod_self_left

#align int.mod_add_mod Int.emod_add_emod

#align int.add_mod_mod Int.add_emod_emod

#align int.add_mod Int.add_emod

theorem add_emod_eq_add_mod_right {m n k : ℤ} (i : ℤ) (H : m % n = k % n) :
    (m + i) % n = (k + i) % n := by rw [← emod_add_emod, ← emod_add_emod k, H]
#align int.add_mod_eq_add_mod_right Int.add_emod_eq_add_emod_right

#align int.add_mod_eq_add_mod_left Int.add_emod_eq_add_emod_left

#align int.mod_add_cancel_right Int.emod_add_cancel_right

#align int.mod_add_cancel_left Int.emod_add_cancel_left

#align int.mod_sub_cancel_right Int.emod_sub_cancel_right

#align int.mul_mod_left Int.mul_emod_left

#align int.mul_mod_right Int.mul_emod_right

#align int.mul_mod Int.mul_emod

#align int.mod_self Int.emod_self

#align int.mod_mod_of_dvd Int.emod_emod_of_dvd

#align int.mod_mod Int.emod_emod

#align int.sub_mod Int.sub_emod

-- Porting note: this should be a doc comment, but the lemma isn't here any more!
/- See also `Int.divModEquiv` for a similar statement as an `Equiv`. -/
#align int.div_mod_unique Int.ediv_emod_unique

attribute [local simp] Int.zero_emod

#align int.mod_eq_mod_iff_mod_sub_eq_zero Int.emod_eq_emod_iff_emod_sub_eq_zero

@[simp]
theorem neg_emod_two (i : ℤ) : -i % 2 = i % 2 := by
  apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
  convert Int.mul_emod_right 2 (-i) using 2
  rw [two_mul, sub_eq_add_neg]
#align int.neg_mod_two Int.neg_emod_two

/-! ### properties of `/` and `%` -/

#align int.lt_div_add_one_mul_self Int.lt_ediv_add_one_mul_self

theorem abs_ediv_le_abs : ∀ a b : ℤ, |a / b| ≤ |a| :=
  suffices ∀ (a : ℤ) (n : ℕ), |a / n| ≤ |a| from fun a b =>
    match b, eq_nat_or_neg b with
    | _, ⟨n, Or.inl rfl⟩ => this _ _
    | _, ⟨n, Or.inr rfl⟩ => by rw [Int.ediv_neg, abs_neg]; apply this
  fun a n => by
  rw [abs_eq_natAbs, abs_eq_natAbs];
    exact
      ofNat_le_ofNat_of_le
        (match a, n with
        | (m : ℕ), n => Nat.div_le_self _ _
        | -[m+1], 0 => Nat.zero_le _
        | -[m+1], n + 1 => Nat.succ_le_succ (Nat.div_le_self _ _))
#align int.abs_div_le_abs Int.abs_ediv_le_abs

#align int.div_le_self Int.ediv_le_self

theorem emod_two_eq_zero_or_one (n : ℤ) : n % 2 = 0 ∨ n % 2 = 1 :=
  have h : n % 2 < 2 := abs_of_nonneg (show 0 ≤ (2 : ℤ) by decide) ▸ Int.emod_lt _ (by decide)
  have h₁ : 0 ≤ n % 2 := Int.emod_nonneg _ (by decide)
  match n % 2, h, h₁ with
  | (0 : ℕ), _ ,_ => Or.inl rfl
  | (1 : ℕ), _ ,_ => Or.inr rfl
  -- Porting note: this used to be `=> absurd h (by decide)`
  -- see https://github.com/leanprover-community/mathlib4/issues/994
  | (k + 2 : ℕ), h₁, _ => False.elim (h₁.not_le (by
    rw [Nat.cast_add]
    exact (le_add_iff_nonneg_left 2).2 (NonNeg.mk k)))
  -- Porting note: this used to be `=> absurd h₁ (by decide)`
  | -[a+1], _, h₁ => by cases h₁
#align int.mod_two_eq_zero_or_one Int.emod_two_eq_zero_or_one

/-! ### dvd -/

#align int.dvd_of_mod_eq_zero Int.dvd_of_emod_eq_zero

#align int.mod_eq_zero_of_dvd Int.emod_eq_zero_of_dvd

#align int.dvd_iff_mod_eq_zero Int.dvd_iff_emod_eq_zero

#align int.dvd_sub_of_mod_eq Int.dvd_sub_of_emod_eq

#align int.nat_abs_dvd Int.natAbs_dvd

#align int.dvd_nat_abs Int.dvd_natAbs

#align int.decidable_dvd Int.decidableDvd

#align int.div_mul_cancel Int.ediv_mul_cancel

#align int.mul_div_cancel' Int.mul_ediv_cancel'

theorem ediv_dvd_ediv : ∀ {a b c : ℤ}, a ∣ b → b ∣ c → b / a ∣ c / a
  | a, _, _, ⟨b, rfl⟩, ⟨c, rfl⟩ =>
    if az : a = 0 then by simp [az]
    else by
      rw [Int.mul_ediv_cancel_left _ az, mul_assoc, Int.mul_ediv_cancel_left _ az];
        apply dvd_mul_right
#align int.div_dvd_div Int.ediv_dvd_ediv

#align int.eq_mul_of_div_eq_right Int.eq_mul_of_ediv_eq_right

#align int.div_eq_of_eq_mul_right Int.ediv_eq_of_eq_mul_right

#align int.eq_div_of_mul_eq_right Int.eq_ediv_of_mul_eq_right

#align int.div_eq_iff_eq_mul_right Int.ediv_eq_iff_eq_mul_right

#align int.div_eq_iff_eq_mul_left Int.ediv_eq_iff_eq_mul_left

#align int.eq_mul_of_div_eq_left Int.eq_mul_of_ediv_eq_left

#align int.div_eq_of_eq_mul_left Int.ediv_eq_of_eq_mul_left

#align int.eq_zero_of_div_eq_zero Int.eq_zero_of_ediv_eq_zero

#align int.div_left_inj Int.ediv_left_inj

theorem abs_sign_of_nonzero {z : ℤ} (hz : z ≠ 0) : |z.sign| = 1 := by
  rw [abs_eq_natAbs, natAbs_sign_of_nonzero hz, Int.ofNat_one]
#align int.abs_sign_of_nonzero Int.abs_sign_of_nonzero

/-- If `n > 0` then `m` is not divisible by `n` iff it is between `n * k` and `n * (k + 1)`
  for some `k`. -/
theorem exists_lt_and_lt_iff_not_dvd (m : ℤ) {n : ℤ} (hn : 0 < n) :
    (∃ k, n * k < m ∧ m < n * (k + 1)) ↔ ¬n ∣ m := by
  constructor
  · rintro ⟨k, h1k, h2k⟩ ⟨l, rfl⟩
    rw [mul_lt_mul_left hn] at h1k h2k
    rw [lt_add_one_iff, ← not_lt] at h2k
    exact h2k h1k
  · intro h
    rw [dvd_iff_emod_eq_zero, ← Ne] at h
    have := (emod_nonneg m hn.ne.symm).lt_of_ne h.symm
    rw [← emod_add_ediv m n]
    refine' ⟨m / n, lt_add_of_pos_left _ this, _⟩
    rw [add_comm _ (1 : ℤ), left_distrib, mul_one]
    exact add_lt_add_right (emod_lt_of_pos _ hn) _
#align int.exists_lt_and_lt_iff_not_dvd Int.exists_lt_and_lt_iff_not_dvd

attribute [local simp] Int.ediv_zero

#align int.mul_div_assoc Int.mul_ediv_assoc

#align int.mul_div_assoc' Int.mul_ediv_assoc'

#align int.neg_div_of_dvd Int.neg_ediv_of_dvd

#align int.sub_div_of_dvd Int.sub_ediv_of_dvd

#align int.sub_div_of_dvd_sub Int.sub_ediv_of_dvd_sub

protected theorem sign_eq_ediv_abs (a : ℤ) : sign a = a / |a| :=
  if az : a = 0 then by simp [az]
  else (Int.ediv_eq_of_eq_mul_left (mt abs_eq_zero.1 az) (sign_mul_abs _).symm).symm
#align int.sign_eq_div_abs Int.sign_eq_ediv_abs

/-! ### `/` and ordering -/

#align int.div_mul_le Int.ediv_mul_le
#align int.div_le_of_le_mul Int.ediv_le_of_le_mul
#align int.mul_lt_of_lt_div Int.mul_lt_of_lt_ediv
#align int.mul_le_of_le_div Int.mul_le_of_le_ediv
#align int.le_div_of_mul_le Int.le_ediv_of_mul_le
#align int.le_div_iff_mul_le Int.le_ediv_iff_mul_le
#align int.div_le_div Int.ediv_le_ediv
#align int.div_lt_of_lt_mul Int.ediv_lt_of_lt_mul
#align int.lt_mul_of_div_lt Int.lt_mul_of_ediv_lt
#align int.div_lt_iff_lt_mul Int.ediv_lt_iff_lt_mul
#align int.le_mul_of_div_le Int.le_mul_of_ediv_le
#align int.lt_div_of_mul_lt Int.lt_ediv_of_mul_lt
#align int.lt_div_iff_mul_lt Int.lt_ediv_iff_mul_lt
#align int.div_pos_of_pos_of_dvd Int.ediv_pos_of_pos_of_dvd

theorem natAbs_eq_of_dvd_dvd {s t : ℤ} (hst : s ∣ t) (hts : t ∣ s) : natAbs s = natAbs t :=
  Nat.dvd_antisymm (natAbs_dvd_natAbs.mpr hst) (natAbs_dvd_natAbs.mpr hts)
#align int.nat_abs_eq_of_dvd_dvd Int.natAbs_eq_of_dvd_dvd

#align int.div_eq_div_of_mul_eq_mul Int.ediv_eq_ediv_of_mul_eq_mul

theorem ediv_dvd_of_dvd {s t : ℤ} (hst : s ∣ t) : t / s ∣ t := by
  rcases eq_or_ne s 0 with (rfl | hs)
  · simpa using hst
  rcases hst with ⟨c, hc⟩
  simp [hc, Int.mul_ediv_cancel_left _ hs]
#align int.div_dvd_of_dvd Int.ediv_dvd_of_dvd

/-! ### toNat -/


@[simp]
theorem toNat_le {a : ℤ} {n : ℕ} : toNat a ≤ n ↔ a ≤ n := by
  rw [ofNat_le.symm, toNat_eq_max, max_le_iff]; exact and_iff_left (ofNat_zero_le _)
#align int.to_nat_le Int.toNat_le

@[simp]
theorem lt_toNat {n : ℕ} {a : ℤ} : n < toNat a ↔ (n : ℤ) < a :=
  le_iff_le_iff_lt_iff_lt.1 toNat_le
#align int.lt_to_nat Int.lt_toNat

@[simp]
theorem natCast_nonpos_iff {n : ℕ} : (n : ℤ) ≤ 0 ↔ n = 0 :=
  ⟨fun h => le_antisymm (Int.ofNat_le.mp (h.trans Int.ofNat_zero.le)) n.zero_le,
   fun h => (natCast_eq_zero.mpr h).le⟩
#align int.coe_nat_nonpos_iff Int.natCast_nonpos_iff

theorem toNat_le_toNat {a b : ℤ} (h : a ≤ b) : toNat a ≤ toNat b := by
  rw [toNat_le]; exact le_trans h (self_le_toNat b)
#align int.to_nat_le_to_nat Int.toNat_le_toNat

theorem toNat_lt_toNat {a b : ℤ} (hb : 0 < b) : toNat a < toNat b ↔ a < b :=
  ⟨fun h => by cases a; exact lt_toNat.1 h; exact lt_trans (neg_of_sign_eq_neg_one rfl) hb,
   fun h => by rw [lt_toNat]; cases a; exact h; exact hb⟩
#align int.to_nat_lt_to_nat Int.toNat_lt_toNat

theorem lt_of_toNat_lt {a b : ℤ} (h : toNat a < toNat b) : a < b :=
  (toNat_lt_toNat <| lt_toNat.1 <| lt_of_le_of_lt (Nat.zero_le _) h).1 h
#align int.lt_of_to_nat_lt Int.lt_of_toNat_lt

@[simp]
theorem toNat_pred_coe_of_pos {i : ℤ} (h : 0 < i) : ((i.toNat - 1 : ℕ) : ℤ) = i - 1 := by
  simp [h, le_of_lt h, push_cast]
#align int.to_nat_pred_coe_of_pos Int.toNat_pred_coe_of_pos

@[simp]
theorem toNat_eq_zero : ∀ {n : ℤ}, n.toNat = 0 ↔ n ≤ 0
  | (n : ℕ) =>
    calc
      _ ↔ n = 0 := ⟨(toNat_natCast n).symm.trans, (toNat_natCast n).trans⟩
      _ ↔ _ := natCast_nonpos_iff.symm

  | -[n+1] =>
    show (-((n : ℤ) + 1)).toNat = 0 ↔ (-(n + 1) : ℤ) ≤ 0 from
      calc
        _ ↔ True := ⟨fun _ => trivial, fun _ => toNat_neg_nat _⟩
        _ ↔ _ := ⟨fun _ => neg_nonpos_of_nonneg (ofNat_zero_le _), fun _ => trivial⟩

#align int.to_nat_eq_zero Int.toNat_eq_zero

@[simp]
theorem toNat_sub_of_le {a b : ℤ} (h : b ≤ a) : (toNat (a - b) : ℤ) = a - b :=
  Int.toNat_of_nonneg (sub_nonneg_of_le h)
#align int.to_nat_sub_of_le Int.toNat_sub_of_le

end Int

section Group
variable {G : Type*} [Group G]

@[to_additive (attr := simp) abs_zsmul_eq_zero]
lemma zpow_abs_eq_one (a : G) (n : ℤ) : a ^ |n| = 1 ↔ a ^ n = 1 := by
  rw [← Int.natCast_natAbs, zpow_natCast, pow_natAbs_eq_one]

end Group

section bit0_bit1
variable {R}
set_option linter.deprecated false

-- The next four lemmas allow us to replace multiplication by a numeral with a `zsmul` expression.

section NonUnitalNonAssocRing
variable [NonUnitalNonAssocRing R] (n r : R)

lemma bit0_mul : bit0 n * r = (2 : ℤ) • (n * r) := by
  rw [bit0, add_mul, ← one_add_one_eq_two, add_zsmul, one_zsmul]
#align bit0_mul bit0_mul

lemma mul_bit0 : r * bit0 n = (2 : ℤ) • (r * n) := by
  rw [bit0, mul_add, ← one_add_one_eq_two, add_zsmul, one_zsmul]
#align mul_bit0 mul_bit0

end NonUnitalNonAssocRing

section NonAssocRing
variable [NonAssocRing R] (n r : R)

lemma bit1_mul : bit1 n * r = (2 : ℤ) • (n * r) + r := by rw [bit1, add_mul, bit0_mul, one_mul]
#align bit1_mul bit1_mul

lemma mul_bit1 {n r : R} : r * bit1 n = (2 : ℤ) • (r * n) + r := by
  rw [bit1, mul_add, mul_bit0, mul_one]
#align mul_bit1 mul_bit1

end NonAssocRing
end bit0_bit1

-- We should need only a minimal development of sets in order to get here.
assert_not_exists Set.range
