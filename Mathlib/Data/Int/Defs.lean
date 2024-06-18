/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Mathlib.Data.Nat.Defs
import Mathlib.Init.Data.Int.Basic
import Mathlib.Init.ZeroOne
import Mathlib.Logic.Nontrivial.Defs
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Lift

#align_import init.data.int.comp_lemmas from "leanprover-community/lean"@"4a03bdeb31b3688c31d02d7ff8e0ff2e5d6174db"

/-!
# Basic operations on the integers

This file contains some basic lemmas about integers.

See note [foundational algebra order theory].

## TODO

Split this file into:
* `Data.Int.Init` (or maybe `Data.Int.Batteries`?) for lemmas that could go to Batteries
* `Data.Int.Basic` for the lemmas that require mathlib definitions
-/

open Nat

namespace Int
variable {a b c d m n : ℤ}

#noalign int.ne_neg_of_ne
#noalign int.neg_ne_zero_of_ne
#noalign int.zero_ne_neg_of_ne
#noalign int.neg_ne_of_pos
#noalign int.ne_neg_of_pos
#noalign int.bit0_nonneg
#noalign int.bit1_nonneg
#noalign int.nonneg_of_pos
#noalign int.ne_of_nat_abs_ne_nat_abs_of_nonneg
#noalign int.ne_of_nat_ne_nonneg_case
#noalign int.nat_abs_bit0
#noalign int.nat_abs_bit0_step
#noalign int.nat_abs_bit1_nonneg
#noalign int.nat_abs_bit1_nonneg_step
#align int.neg_succ_lt_zero Int.negSucc_lt_zero
#align int.of_nat_nat_abs_eq_of_nonneg Int.ofNat_natAbs_eq_of_nonnegₓ
#align int.nat_abs_of_neg_succ_of_nat Int.natAbs_negSucc

section Order
variable {a b c : ℤ}

protected lemma le_rfl : a ≤ a := a.le_refl
protected lemma lt_or_lt_of_ne : a ≠ b → a < b ∨ b < a := Int.lt_or_gt_of_ne
protected lemma lt_or_le (a b : ℤ) : a < b ∨ b ≤ a := by rw [← Int.not_lt]; exact em _
protected lemma le_or_lt (a b : ℤ) : a ≤ b ∨ b < a := (b.lt_or_le a).symm
protected lemma lt_asymm : a < b → ¬ b < a := by rw [Int.not_lt]; exact Int.le_of_lt
protected lemma le_of_eq (hab : a = b) : a ≤ b := by rw [hab]; exact Int.le_rfl
protected lemma ge_of_eq (hab : a = b) : b ≤ a := Int.le_of_eq hab.symm
protected lemma le_antisymm_iff : a = b ↔ a ≤ b ∧ b ≤ a :=
  ⟨fun h ↦ ⟨Int.le_of_eq h, Int.ge_of_eq h⟩, fun h ↦ Int.le_antisymm h.1 h.2⟩
protected lemma le_iff_eq_or_lt : a ≤ b ↔ a = b ∨ a < b := by
  rw [Int.le_antisymm_iff, Int.lt_iff_le_not_le, ← and_or_left]; simp [em]
protected lemma le_iff_lt_or_eq : a ≤ b ↔ a < b ∨ a = b := by rw [Int.le_iff_eq_or_lt, or_comm]

end Order

-- TODO: Tag in Lean
attribute [simp] natAbs_pos

protected lemma one_pos : 0 < (1 : Int) := Int.zero_lt_one
#align int.one_pos Int.one_pos

protected lemma one_ne_zero : (1 : ℤ) ≠ 0 := by decide

protected lemma one_nonneg : 0 ≤ (1 : ℤ) := Int.le_of_lt Int.zero_lt_one
#align int.one_nonneg Int.one_nonneg

lemma zero_le_ofNat (n : ℕ) : 0 ≤ ofNat n := @le.intro _ _ n (by rw [Int.zero_add]; rfl)
#align int.zero_le_of_nat Int.zero_le_ofNat

-- We want to use these lemmas earlier than the lemmas simp can prove them with
@[simp, nolint simpNF]
protected lemma neg_pos : 0 < -a ↔ a < 0 := ⟨Int.neg_of_neg_pos, Int.neg_pos_of_neg⟩

@[simp, nolint simpNF]
protected lemma neg_nonneg : 0 ≤ -a ↔ a ≤ 0 := ⟨Int.nonpos_of_neg_nonneg, Int.neg_nonneg_of_nonpos⟩

@[simp, nolint simpNF]
protected lemma neg_neg_iff_pos : -a < 0 ↔ 0 < a := ⟨Int.pos_of_neg_neg, Int.neg_neg_of_pos⟩

@[simp, nolint simpNF]
protected lemma neg_nonpos_iff_nonneg : -a ≤ 0 ↔ 0 ≤ a :=
  ⟨Int.nonneg_of_neg_nonpos, Int.neg_nonpos_of_nonneg⟩

@[simp, nolint simpNF]
protected lemma sub_pos : 0 < a - b ↔ b < a := ⟨Int.lt_of_sub_pos, Int.sub_pos_of_lt⟩

@[simp, nolint simpNF]
protected lemma sub_nonneg : 0 ≤ a - b ↔ b ≤ a := ⟨Int.le_of_sub_nonneg, Int.sub_nonneg_of_le⟩

instance instNontrivial : Nontrivial ℤ := ⟨⟨0, 1, Int.zero_ne_one⟩⟩

@[simp] lemma ofNat_injective : Function.Injective ofNat := @Int.ofNat.inj

@[simp] lemma ofNat_eq_natCast (n : ℕ) : Int.ofNat n = n := rfl

@[deprecated ofNat_eq_natCast (since := "2024-03-24")]
protected lemma natCast_eq_ofNat (n : ℕ) : ↑n = Int.ofNat n := rfl
#align int.coe_nat_eq Int.natCast_eq_ofNat

@[norm_cast] lemma natCast_inj {m n : ℕ} : (m : ℤ) = (n : ℤ) ↔ m = n := ofNat_inj
#align int.coe_nat_inj' Int.natCast_inj

@[simp, norm_cast] lemma natAbs_cast (n : ℕ) : natAbs ↑n = n := rfl

@[norm_cast]
protected lemma natCast_sub {n m : ℕ} : n ≤ m → (↑(m - n) : ℤ) = ↑m - ↑n := ofNat_sub

-- We want to use this lemma earlier than the lemmas simp can prove it with
@[simp, nolint simpNF] lemma natCast_eq_zero {n : ℕ} : (n : ℤ) = 0 ↔ n = 0 := by omega
#align int.coe_nat_eq_zero Int.natCast_eq_zero

lemma natCast_ne_zero {n : ℕ} : (n : ℤ) ≠ 0 ↔ n ≠ 0 := by omega
#align int.coe_nat_ne_zero Int.natCast_ne_zero

lemma natCast_ne_zero_iff_pos {n : ℕ} : (n : ℤ) ≠ 0 ↔ 0 < n := by omega
#align int.coe_nat_ne_zero_iff_pos Int.natCast_ne_zero_iff_pos

-- We want to use this lemma earlier than the lemmas simp can prove it with
@[simp, nolint simpNF] lemma natCast_pos {n : ℕ} : (0 : ℤ) < n ↔ 0 < n := by omega
#align int.coe_nat_pos Int.natCast_pos

lemma natCast_succ_pos (n : ℕ) : 0 < (n.succ : ℤ) := natCast_pos.2 n.succ_pos
#align int.coe_nat_succ_pos Int.natCast_succ_pos

@[simp] lemma natCast_nonpos_iff {n : ℕ} : (n : ℤ) ≤ 0 ↔ n = 0 := by omega
#align int.coe_nat_nonpos_iff Int.natCast_nonpos_iff

#align int.neg_succ_not_nonneg Int.negSucc_not_nonneg
#align int.neg_succ_not_pos Int.negSucc_not_pos
#align int.neg_succ_sub_one Int.negSucc_sub_one
#align int.coe_nat_mul_neg_succ Int.ofNat_mul_negSucc
#align int.neg_succ_mul_coe_nat Int.negSucc_mul_ofNat
#align int.neg_succ_mul_neg_succ Int.negSucc_mul_negSucc

#align int.coe_nat_le Int.ofNat_le
#align int.coe_nat_lt Int.ofNat_lt

lemma natCast_nonneg (n : ℕ) : 0 ≤ (n : ℤ) := ofNat_le.2 (Nat.zero_le _)
#align int.coe_nat_nonneg Int.natCast_nonneg

#align int.neg_of_nat_ne_zero Int.negSucc_ne_zero
#align int.zero_ne_neg_of_nat Int.zero_ne_negSucc

@[simp] lemma sign_natCast_add_one (n : ℕ) : sign (n + 1) = 1 := rfl
#align int.sign_coe_add_one Int.sign_natCast_add_one

#align int.sign_neg_succ_of_nat Int.sign_negSucc

@[simp, norm_cast] lemma cast_id {n : ℤ} : Int.cast n = n := rfl

protected lemma two_mul : ∀ n : ℤ, 2 * n = n + n
  | (n : ℕ) => by norm_cast; exact n.two_mul
  | -[n+1] => by
    change (2 : ℕ) * (_ : ℤ) = _
    rw [Int.ofNat_mul_negSucc, Nat.two_mul, ofNat_add, Int.neg_add]
    rfl

section deprecated
set_option linter.deprecated false

@[norm_cast, deprecated (since := "2022-11-23")]
lemma ofNat_bit0 (n : ℕ) : (↑(bit0 n) : ℤ) = bit0 ↑n := rfl
#align int.coe_nat_bit0 Int.ofNat_bit0

@[norm_cast, deprecated (since := "2022-11-23")]
lemma ofNat_bit1 (n : ℕ) : (↑(bit1 n) : ℤ) = bit1 ↑n := rfl
#align int.coe_nat_bit1 Int.ofNat_bit1

end deprecated

protected lemma mul_le_mul_iff_of_pos_right (ha : 0 < a) : b * a ≤ c * a ↔ b ≤ c :=
  ⟨(le_of_mul_le_mul_right · ha), (Int.mul_le_mul_of_nonneg_right · (Int.le_of_lt ha))⟩

protected lemma mul_nonneg_iff_of_pos_right (hb : 0 < b) : 0 ≤ a * b ↔ 0 ≤ a := by
  simpa using (Int.mul_le_mul_iff_of_pos_right hb : 0 * b ≤ a * b ↔ 0 ≤ a)

/-! ### succ and pred -/

#align int.lt_add_one_iff Int.lt_add_one_iff
#align int.le_add_one Int.le_add_one

/-- Immediate successor of an integer: `succ n = n + 1` -/
def succ (a : ℤ) := a + 1
#align int.succ Int.succ

/-- Immediate predecessor of an integer: `pred n = n - 1` -/
def pred (a : ℤ) := a - 1
#align int.pred Int.pred

lemma natCast_succ (n : ℕ) : (Nat.succ n : ℤ) = Int.succ n := rfl
#align int.nat_succ_eq_int_succ Int.natCast_succ

lemma pred_succ (a : ℤ) : pred (succ a) = a := Int.add_sub_cancel _ _
#align int.pred_succ Int.pred_succ

lemma succ_pred (a : ℤ) : succ (pred a) = a := Int.sub_add_cancel _ _
#align int.succ_pred Int.succ_pred

lemma neg_succ (a : ℤ) : -succ a = pred (-a) := Int.neg_add
#align int.neg_succ Int.neg_succ

lemma succ_neg_succ (a : ℤ) : succ (-succ a) = -a := by rw [neg_succ, succ_pred]
#align int.succ_neg_succ Int.succ_neg_succ

lemma neg_pred (a : ℤ) : -pred a = succ (-a) := by
  rw [← Int.neg_eq_comm.mp (neg_succ (-a)), Int.neg_neg]
#align int.neg_pred Int.neg_pred

lemma pred_neg_pred (a : ℤ) : pred (-pred a) = -a := by rw [neg_pred, pred_succ]
#align int.pred_neg_pred Int.pred_neg_pred

lemma pred_nat_succ (n : ℕ) : pred (Nat.succ n) = n := pred_succ n
#align int.pred_nat_succ Int.pred_nat_succ

lemma neg_nat_succ (n : ℕ) : -(Nat.succ n : ℤ) = pred (-n) := neg_succ n
#align int.neg_nat_succ Int.neg_nat_succ

lemma succ_neg_natCast_succ (n : ℕ) : succ (-Nat.succ n) = -n := succ_neg_succ n
#align int.succ_neg_nat_succ Int.succ_neg_natCast_succ

@[norm_cast] lemma natCast_pred_of_pos {n : ℕ} (h : 0 < n) : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
  cases n; cases h; simp [ofNat_succ]
#align int.coe_pred_of_pos Int.natCast_pred_of_pos

lemma lt_succ_self (a : ℤ) : a < succ a := by unfold succ; omega
#align int.lt_succ_self Int.lt_succ_self

lemma pred_self_lt (a : ℤ) : pred a < a := by unfold pred; omega
#align int.pred_self_lt Int.pred_self_lt

lemma le_add_one_iff : m ≤ n + 1 ↔ m ≤ n ∨ m = n + 1 := by omega

lemma sub_one_lt_iff : m - 1 < n ↔ m ≤ n := by omega
#align int.sub_one_lt_iff Int.sub_one_lt_iff

lemma le_sub_one_iff : m ≤ n - 1 ↔ m < n := by omega
#align int.le_sub_one_iff Int.le_sub_one_iff

section
open Lean.Omega.Int

/-!
The following few lemmas are proved in the core implementation of the `omega` tactic. We expose
them here with nice user-facing names.
-/

protected lemma add_le_iff_le_sub : a + b ≤ c ↔ a ≤ c - b := add_le_iff_le_sub ..
protected lemma le_add_iff_sub_le : a ≤ b + c ↔ a - c ≤ b := le_add_iff_sub_le ..
protected lemma add_le_zero_iff_le_neg : a + b ≤ 0 ↔ a ≤ - b := add_le_zero_iff_le_neg ..
protected lemma add_le_zero_iff_le_neg' : a + b ≤ 0 ↔ b ≤ -a := add_le_zero_iff_le_neg' ..
protected lemma add_nonnneg_iff_neg_le : 0 ≤ a + b ↔ -b ≤ a := add_nonnneg_iff_neg_le ..
protected lemma add_nonnneg_iff_neg_le' : 0 ≤ a + b ↔ -a ≤ b := add_nonnneg_iff_neg_le' ..

end

@[elab_as_elim] protected lemma induction_on {p : ℤ → Prop} (i : ℤ)
    (hz : p 0) (hp : ∀ i : ℕ, p i → p (i + 1)) (hn : ∀ i : ℕ, p (-i) → p (-i - 1)) : p i := by
  induction i with
  | ofNat i =>
    induction i with
    | zero => exact hz
    | succ i ih => exact hp _ ih
  | negSucc i =>
    suffices ∀ n : ℕ, p (-n) from this (i + 1)
    intro n; induction n with
    | zero => simp [hz]
    | succ n ih => convert hn _ ih using 1; simp [ofNat_succ, Int.neg_add, Int.sub_eq_add_neg]
#align int.induction_on Int.induction_on

section inductionOn'

variable {C : ℤ → Sort*} (z b : ℤ)
  (H0 : C b) (Hs : ∀ k, b ≤ k → C k → C (k + 1)) (Hp : ∀ k ≤ b, C k → C (k - 1))

/-- Inductively define a function on `ℤ` by defining it at `b`, for the `succ` of a number greater
than `b`, and the `pred` of a number less than `b`. -/
@[elab_as_elim] protected def inductionOn' : C z :=
  cast (congr_arg C <| show b + (z - b) = z by rw [Int.add_comm, z.sub_add_cancel b]) <|
  match z - b with
  | .ofNat n => pos n
  | .negSucc n => neg n
where
  /-- The positive case of `Int.inductionOn'`. -/
  pos : ∀ n : ℕ, C (b + n)
  | 0 => cast (by erw [Int.add_zero]) H0
  | n+1 => cast (by rw [Int.add_assoc]; rfl) <|
    Hs _ (Int.le_add_of_nonneg_right (ofNat_nonneg _)) (pos n)

  /-- The negative case of `Int.inductionOn'`. -/
  neg : ∀ n : ℕ, C (b + -[n+1])
  | 0 => Hp _ Int.le_rfl H0
  | n+1 => by
    refine cast (by rw [Int.add_sub_assoc]; rfl) (Hp _ (Int.le_of_lt ?_) (neg n))
    conv => rhs; exact b.add_zero.symm
    rw [Int.add_lt_add_iff_left]; apply negSucc_lt_zero
#align int.induction_on' Int.inductionOn'

variable (b) {z b b H0 Hs Hp}

lemma inductionOn'_self : b.inductionOn' b H0 Hs Hp = H0 :=
  cast_eq_iff_heq.mpr <| .symm <| by rw [b.sub_self, ← cast_eq_iff_heq]; rfl

lemma inductionOn'_add_one (hz : b ≤ z) :
    (z + 1).inductionOn' b H0 Hs Hp = Hs z hz (z.inductionOn' b H0 Hs Hp) := by
  apply cast_eq_iff_heq.mpr
  lift z - b to ℕ using Int.sub_nonneg.mpr hz with zb hzb
  rw [show z + 1 - b = zb + 1 by omega]
  have : b + zb = z := by omega
  subst this
  convert cast_heq _ _
  rw [Int.inductionOn', cast_eq_iff_heq, ← hzb]

lemma inductionOn'_sub_one (hz : z ≤ b) :
    (z - 1).inductionOn' b H0 Hs Hp = Hp z hz (z.inductionOn' b H0 Hs Hp) := by
  apply cast_eq_iff_heq.mpr
  obtain ⟨n, hn⟩ := Int.eq_negSucc_of_lt_zero (show z - 1 - b < 0 by omega)
  rw [hn]
  obtain _|n := n
  · change _ = -1 at hn
    have : z = b := by omega
    subst this; rw [inductionOn'_self]; exact heq_of_eq rfl
  · have : z = b + -[n+1] := by rw [Int.negSucc_eq] at hn ⊢; omega
    subst this
    convert cast_heq _ _
    rw [Int.inductionOn', cast_eq_iff_heq, show b + -[n+1] - b = -[n+1] by omega]

end inductionOn'

/-- Inductively define a function on `ℤ` by defining it on `ℕ` and extending it from `n` to `-n`. -/
@[elab_as_elim] protected def negInduction {C : ℤ → Sort*} (nat : ∀ n : ℕ, C n)
    (neg : ∀ n : ℕ, C n → C (-n)) : ∀ n : ℤ, C n
  | .ofNat n => nat n
  | .negSucc n => neg _ <| nat <| n + 1

/-- See `Int.inductionOn'` for an induction in both directions. -/
protected lemma le_induction {P : ℤ → Prop} {m : ℤ} (h0 : P m)
    (h1 : ∀ n : ℤ, m ≤ n → P n → P (n + 1)) (n : ℤ) : m ≤ n → P n := by
  refine Int.inductionOn' n m ?_ ?_ ?_
  · intro
    exact h0
  · intro k hle hi _
    exact h1 k hle (hi hle)
  · intro k hle _ hle'
    omega
#align int.le_induction Int.le_induction

/-- See `Int.inductionOn'` for an induction in both directions. -/
protected theorem le_induction_down {P : ℤ → Prop} {m : ℤ} (h0 : P m)
    (h1 : ∀ n : ℤ, n ≤ m → P n → P (n - 1)) (n : ℤ) : n ≤ m → P n :=
  Int.inductionOn' n m (fun _ ↦ h0) (fun k hle _ hle' ↦ by omega)
    fun k hle hi _ ↦ h1 k hle (hi hle)
#align int.le_induction_down Int.le_induction_down

section strongRec

variable {P : ℤ → Sort*} (lt : ∀ n < m, P n) (ge : ∀ n ≥ m, (∀ k < n, P k) → P n)

/-- A strong recursor for `Int` that specifies explicit values for integers below a threshold,
and is analogous to `Nat.strongRec` for integers on or above the threshold. -/
@[elab_as_elim] protected def strongRec (n : ℤ) : P n := by
  refine if hnm : n < m then lt n hnm else ge n (by omega) (n.inductionOn' m lt ?_ ?_)
  · intro _n _ ih l _
    exact if hlm : l < m then lt l hlm else ge l (by omega) fun k _ ↦ ih k (by omega)
  · exact fun n _ hn l _ ↦ hn l (by omega)

variable {lt ge}
lemma strongRec_of_lt (hn : n < m) : m.strongRec lt ge n = lt n hn := dif_pos _

lemma strongRec_of_ge :
    ∀ hn : m ≤ n, m.strongRec lt ge n = ge n hn fun k _ ↦ m.strongRec lt ge k := by
  refine m.strongRec (fun n hnm hmn ↦ (Int.not_lt.mpr hmn hnm).elim) (fun n _ ih hn ↦ ?_) n
  rw [Int.strongRec, dif_neg (Int.not_lt.mpr hn)]
  congr; revert ih
  refine n.inductionOn' m (fun _ ↦ ?_) (fun k hmk ih' ih ↦ ?_) (fun k hkm ih' _ ↦ ?_) <;> ext l hl
  · rw [inductionOn'_self, strongRec_of_lt hl]
  · rw [inductionOn'_add_one hmk]; split_ifs with hlm
    · rw [strongRec_of_lt hlm]
    · rw [ih' fun l hl ↦ ih l (Int.lt_trans hl k.lt_succ), ih _ hl]
  · rw [inductionOn'_sub_one hkm, ih']
    exact fun l hlk hml ↦ (Int.not_lt.mpr hkm <| Int.lt_of_le_of_lt hml hlk).elim

end strongRec

/-! ### nat abs -/

#align int.nat_abs_dvd_iff_dvd Int.natAbs_dvd_natAbs

-- TODO: Rename `natAbs_ofNat` to `natAbs_natCast`
@[simp] lemma natAbs_ofNat' (n : ℕ) : natAbs (ofNat n) = n := rfl
#align int.nat_abs_of_nat_core Int.natAbs_ofNat'

lemma natAbs_add_of_nonneg : ∀ {a b : Int}, 0 ≤ a → 0 ≤ b → natAbs (a + b) = natAbs a + natAbs b
  | ofNat _, ofNat _, _, _ => rfl
#align int.nat_abs_add_nonneg Int.natAbs_add_of_nonneg

lemma natAbs_add_of_nonpos {a b : Int} (ha : a ≤ 0) (hb : b ≤ 0) :
    natAbs (a + b) = natAbs a + natAbs b := by
  omega
#align int.nat_abs_add_neg Int.natAbs_add_of_nonpos

lemma natAbs_surjective : natAbs.Surjective := fun n => ⟨n, natAbs_ofNat n⟩
#align int.nat_abs_surjective Int.natAbs_surjective

#align int.nat_abs_add_le Int.natAbs_add_le
#align int.nat_abs_sub_le Int.natAbs_sub_le
#align int.nat_abs_neg_of_nat Int.natAbs_negOfNat
#align int.nat_abs_mul Int.natAbs_mul
#align int.nat_abs_mul_nat_abs_eq Int.natAbs_mul_natAbs_eq
#align int.nat_abs_mul_self' Int.natAbs_mul_self'
#align int.neg_succ_of_nat_eq' Int.negSucc_eq'
#align int.nat_abs_ne_zero_of_ne_zero Int.natAbs_ne_zero
#align int.nat_abs_eq_zero Int.natAbs_eq_zero
#align int.nat_abs_ne_zero Int.natAbs_ne_zero
#align int.nat_abs_lt_nat_abs_of_nonneg_of_lt Int.natAbs_lt_natAbs_of_nonneg_of_lt
#align int.nat_abs_eq_nat_abs_iff Int.natAbs_eq_natAbs_iff
#align int.nat_abs_eq_iff Int.natAbs_eq_iff

lemma natAbs_pow (n : ℤ) (k : ℕ) : Int.natAbs (n ^ k) = Int.natAbs n ^ k := by
  induction' k with k ih
  · rfl
  · rw [Int.pow_succ, natAbs_mul, Nat.pow_succ, ih, Nat.mul_comm]
#align int.nat_abs_pow Int.natAbs_pow

lemma natAbs_sq (x : ℤ) : (x.natAbs : ℤ) ^ 2 = x ^ 2 := by
  simp [Int.pow_succ, Int.pow_zero, Int.natAbs_mul_self']
#align int.nat_abs_sq Int.natAbs_sq

alias natAbs_pow_two := natAbs_sq
#align int.nat_abs_pow_two Int.natAbs_pow_two

/-! ### `/`  -/

-- Porting note: Many of the lemmas in this section are dubious alignments because the default
-- division on `Int` has changed from the E-rounding convention to the T-rounding convention
-- (see `Int.ediv`). We have attempted to align the lemmas to continue to use the `/` symbol
-- where possible, but some lemmas fail to hold on T-rounding division and have been aligned to
-- `Int.ediv` instead.

#align int.of_nat_div Int.ofNat_div
#align int.div_nonpos Int.ediv_nonpos
#align int.add_mul_div_right Int.add_mul_ediv_right
#align int.add_mul_div_left Int.add_mul_ediv_left
#align int.mul_div_cancel Int.mul_ediv_cancel
#align int.mul_div_cancel_left Int.mul_ediv_cancel_left
#align int.div_self Int.ediv_self
#align int.add_div_of_dvd_right Int.add_ediv_of_dvd_right
#align int.add_div_of_dvd_left Int.add_ediv_of_dvd_left
#align int.lt_div_add_one_mul_self Int.lt_ediv_add_one_mul_self
#align int.div_le_self Int.ediv_le_self
#align int.eq_one_of_mul_eq_one_right Int.eq_one_of_mul_eq_one_right
#align int.eq_one_of_mul_eq_one_left Int.eq_one_of_mul_eq_one_left

@[simp, norm_cast] lemma natCast_div (m n : ℕ) : ((m / n : ℕ) : ℤ) = m / n := rfl
#align int.coe_nat_div Int.natCast_div

lemma natCast_ediv (m n : ℕ) : ((m / n : ℕ) : ℤ) = ediv m n := rfl

#align int.neg_succ_of_nat_div Int.negSucc_ediv

#align int.div_neg Int.div_negₓ -- int div alignment

lemma ediv_of_neg_of_pos {a b : ℤ} (Ha : a < 0) (Hb : 0 < b) : ediv a b = -((-a - 1) / b + 1) :=
  match a, b, eq_negSucc_of_lt_zero Ha, eq_succ_of_zero_lt Hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by
    rw [show (- -[m+1] : ℤ) = (m + 1 : ℤ) by rfl]; rw [Int.add_sub_cancel]; rfl
#align int.div_of_neg_of_pos Int.ediv_of_neg_of_pos

#align int.div_nonneg Int.div_nonnegₓ -- int div alignment
#align int.div_neg' Int.ediv_neg'
#align int.div_one Int.div_oneₓ -- int div alignment
#align int.div_eq_zero_of_lt Int.div_eq_zero_of_ltₓ -- int div alignment

/-! ### mod -/

#align int.of_nat_mod Int.ofNat_mod_ofNat
#align int.mod_nonneg Int.emod_nonneg
#align int.mod_lt_of_pos Int.emod_lt_of_pos
#align int.add_mul_mod_self Int.add_mul_emod_self
#align int.add_mul_mod_self_left Int.add_mul_emod_self_left
#align int.add_mod_self Int.add_emod_self
#align int.add_mod_self_left Int.add_emod_self_left
#align int.mod_add_mod Int.emod_add_emod
#align int.add_mod_mod Int.add_emod_emod
#align int.add_mod Int.add_emod
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
#align int.mod_eq_mod_iff_mod_sub_eq_zero Int.emod_eq_emod_iff_emod_sub_eq_zero
#align int.neg_succ_of_nat_mod Int.negSucc_emod
#align int.mod_neg Int.mod_negₓ -- int div alignment
#align int.zero_mod Int.zero_modₓ -- int div alignment
#align int.mod_zero Int.mod_zeroₓ -- int div alignment
#align int.mod_one Int.mod_oneₓ -- int div alignment
#align int.mod_eq_of_lt Int.emod_eq_of_lt -- int div alignment
#align int.mod_add_div Int.emod_add_ediv -- int div alignment
#align int.div_add_mod Int.div_add_modₓ -- int div alignment
#align int.mod_add_div' Int.mod_add_div'ₓ -- int div alignment
#align int.div_add_mod' Int.div_add_mod'ₓ -- int div alignment
#align int.mod_def Int.mod_defₓ -- int div alignment

-- Porting note: this should be a doc comment, but the lemma isn't here any more!
/- See also `Int.divModEquiv` for a similar statement as an `Equiv`. -/
#align int.div_mod_unique Int.ediv_emod_unique

@[simp, norm_cast] lemma natCast_mod (m n : ℕ) : (↑(m % n) : ℤ) = ↑m % ↑n := rfl
#align int.coe_nat_mod Int.natCast_mod

lemma add_emod_eq_add_mod_right {m n k : ℤ} (i : ℤ) (H : m % n = k % n) :
    (m + i) % n = (k + i) % n := by rw [← emod_add_emod, ← emod_add_emod k, H]
#align int.add_mod_eq_add_mod_right Int.add_emod_eq_add_emod_right

@[simp] lemma neg_emod_two (i : ℤ) : -i % 2 = i % 2 := by
  apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
  convert Int.mul_emod_right 2 (-i) using 2
  rw [Int.two_mul, Int.sub_eq_add_neg]
#align int.neg_mod_two Int.neg_emod_two

/-! ### properties of `/` and `%` -/

#align int.mul_div_mul_of_pos Int.mul_ediv_mul_of_pos
#align int.mul_div_mul_of_pos_left Int.mul_ediv_mul_of_pos_left
#align int.mul_mod_mul_of_pos Int.mul_emod_mul_of_pos
#align int.mul_div_cancel_of_mod_eq_zero Int.mul_div_cancel_of_mod_eq_zeroₓ -- int div alignment
#align int.div_mul_cancel_of_mod_eq_zero Int.div_mul_cancel_of_mod_eq_zeroₓ -- int div alignment
#align int.nat_abs_sign Int.natAbs_sign
#align int.nat_abs_sign_of_nonzero Int.natAbs_sign_of_nonzero
#align int.div_sign Int.div_sign -- int div alignment
#align int.of_nat_add_neg_succ_of_nat_of_lt Int.ofNat_add_negSucc_of_lt
#align int.neg_add_neg Int.negSucc_add_negSucc

lemma emod_two_eq_zero_or_one (n : ℤ) : n % 2 = 0 ∨ n % 2 = 1 :=
  have h : n % 2 < 2 :=  by omega
  have h₁ : 0 ≤ n % 2 := Int.emod_nonneg _ (by decide)
  match n % 2, h, h₁ with
  | (0 : ℕ), _ ,_ => Or.inl rfl
  | (1 : ℕ), _ ,_ => Or.inr rfl
  | (k + 2 : ℕ), h₁, _ => by omega
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
#align int.eq_mul_of_div_eq_right Int.eq_mul_of_ediv_eq_right
#align int.div_eq_of_eq_mul_right Int.ediv_eq_of_eq_mul_right
#align int.eq_div_of_mul_eq_right Int.eq_ediv_of_mul_eq_right
#align int.div_eq_iff_eq_mul_right Int.ediv_eq_iff_eq_mul_right
#align int.div_eq_iff_eq_mul_left Int.ediv_eq_iff_eq_mul_left
#align int.eq_mul_of_div_eq_left Int.eq_mul_of_ediv_eq_left
#align int.div_eq_of_eq_mul_left Int.ediv_eq_of_eq_mul_left
#align int.eq_zero_of_div_eq_zero Int.eq_zero_of_ediv_eq_zero
#align int.div_left_inj Int.ediv_left_inj
#align int.mul_div_assoc Int.mul_ediv_assoc
#align int.mul_div_assoc' Int.mul_ediv_assoc'
#align int.neg_div_of_dvd Int.neg_ediv_of_dvd
#align int.sub_div_of_dvd Int.sub_ediv_of_dvd
#align int.sub_div_of_dvd_sub Int.sub_ediv_of_dvd_sub
#align int.le_of_dvd Int.le_of_dvd
#align int.eq_one_of_dvd_one Int.eq_one_of_dvd_one
#align int.dvd_antisymm Int.dvd_antisymm

lemma ediv_dvd_ediv : ∀ {a b c : ℤ}, a ∣ b → b ∣ c → b / a ∣ c / a
  | a, _, _, ⟨b, rfl⟩, ⟨c, rfl⟩ =>
    if az : a = 0 then by simp [az]
    else by
      rw [Int.mul_ediv_cancel_left _ az, Int.mul_assoc, Int.mul_ediv_cancel_left _ az];
        apply Int.dvd_mul_right
#align int.div_dvd_div Int.ediv_dvd_ediv

/-- If `n > 0` then `m` is not divisible by `n` iff it is between `n * k` and `n * (k + 1)`
  for some `k`. -/
lemma exists_lt_and_lt_iff_not_dvd (m : ℤ) (hn : 0 < n) :
    (∃ k, n * k < m ∧ m < n * (k + 1)) ↔ ¬n ∣ m := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨k, h1k, h2k⟩ ⟨l, rfl⟩
    replace h1k := lt_of_mul_lt_mul_left h1k (by omega)
    replace h2k := lt_of_mul_lt_mul_left h2k (by omega)
    rw [Int.lt_add_one_iff, ← Int.not_lt] at h2k
    exact h2k h1k
  · rw [dvd_iff_emod_eq_zero, ← Ne] at h
    rw [← emod_add_ediv m n]
    refine ⟨m / n, Int.lt_add_of_pos_left _ ?_, ?_⟩
    · have := emod_nonneg m (Int.ne_of_gt hn)
      omega
    · rw [Int.add_comm _ (1 : ℤ), Int.mul_add, Int.mul_one]
      exact Int.add_lt_add_right (emod_lt_of_pos _ hn) _
#align int.exists_lt_and_lt_iff_not_dvd Int.exists_lt_and_lt_iff_not_dvd

@[norm_cast] lemma natCast_dvd_natCast {m n : ℕ} : (↑m : ℤ) ∣ ↑n ↔ m ∣ n where
  mp := by
    rintro ⟨a, h⟩
    obtain rfl | hm := m.eq_zero_or_pos
    · simpa using h
    have ha : 0 ≤ a := Int.not_lt.1 fun ha ↦ by
      simpa [← h, Int.not_lt.2 (Int.natCast_nonneg _)]
        using Int.mul_neg_of_pos_of_neg (natCast_pos.2 hm) ha
    lift a to ℕ using ha
    norm_cast at h
    exact ⟨a, h⟩
  mpr := by rintro ⟨a, rfl⟩; simp [Int.dvd_mul_right]
#align int.coe_nat_dvd Int.natCast_dvd_natCast

lemma natCast_dvd {m : ℕ} : (m : ℤ) ∣ n ↔ m ∣ n.natAbs := by
  obtain hn | hn := natAbs_eq n <;> rw [hn] <;> simp [← natCast_dvd_natCast, Int.dvd_neg]
#align int.coe_nat_dvd_left Int.natCast_dvd

lemma dvd_natCast {n : ℕ} : m ∣ (n : ℤ) ↔ m.natAbs ∣ n := by
  obtain hn | hn := natAbs_eq m <;> rw [hn] <;> simp [← natCast_dvd_natCast, Int.neg_dvd]
#align int.coe_nat_dvd_right Int.dvd_natCast

lemma natAbs_ediv (a b : ℤ) (H : b ∣ a) : natAbs (a / b) = natAbs a / natAbs b := by
  rcases Nat.eq_zero_or_pos (natAbs b) with (h | h)
  · rw [natAbs_eq_zero.1 h]
    simp [Int.ediv_zero]
  calc
    natAbs (a / b) = natAbs (a / b) * 1 := by rw [Nat.mul_one]
    _ = natAbs (a / b) * (natAbs b / natAbs b) := by rw [Nat.div_self h]
    _ = natAbs (a / b) * natAbs b / natAbs b := by rw [Nat.mul_div_assoc _ b.natAbs.dvd_refl]
    _ = natAbs (a / b * b) / natAbs b := by rw [natAbs_mul (a / b) b]
    _ = natAbs a / natAbs b := by rw [Int.ediv_mul_cancel H]
#align int.nat_abs_div Int.natAbs_ediv

lemma dvd_of_mul_dvd_mul_left (ha : a ≠ 0) (h : a * m ∣ a * n) : m ∣ n := by
  obtain ⟨b, hb⟩ := h
  rw [Int.mul_assoc, Int.mul_eq_mul_left_iff ha] at hb
  exact ⟨_, hb⟩
#align int.dvd_of_mul_dvd_mul_left Int.dvd_of_mul_dvd_mul_left

lemma dvd_of_mul_dvd_mul_right (ha : a ≠ 0) (h : m * a ∣ n * a) : m ∣ n :=
  dvd_of_mul_dvd_mul_left ha (by simpa [Int.mul_comm] using h)
#align int.dvd_of_mul_dvd_mul_right Int.dvd_of_mul_dvd_mul_right

lemma eq_mul_div_of_mul_eq_mul_of_dvd_left (hb : b ≠ 0) (hbc : b ∣ c) (h : b * a = c * d) :
    a = c / b * d := by
  obtain ⟨k, rfl⟩ := hbc
  rw [Int.mul_ediv_cancel_left _ hb]
  rwa [Int.mul_assoc, Int.mul_eq_mul_left_iff hb] at h
#align int.eq_mul_div_of_mul_eq_mul_of_dvd_left Int.eq_mul_div_of_mul_eq_mul_of_dvd_left

/-- If an integer with larger absolute value divides an integer, it is zero. -/
lemma eq_zero_of_dvd_of_natAbs_lt_natAbs (hmn : m ∣ n) (hnm : natAbs n < natAbs m) : n = 0 := by
  rw [← natAbs_dvd, ← dvd_natAbs, natCast_dvd_natCast] at hmn
  rw [← natAbs_eq_zero]
  exact Nat.eq_zero_of_dvd_of_lt hmn hnm
#align int.eq_zero_of_dvd_of_nat_abs_lt_nat_abs Int.eq_zero_of_dvd_of_natAbs_lt_natAbs

lemma eq_zero_of_dvd_of_nonneg_of_lt (hm : 0 ≤ m) (hmn : m < n) (hnm : n ∣ m) : m = 0 :=
  eq_zero_of_dvd_of_natAbs_lt_natAbs hnm (natAbs_lt_natAbs_of_nonneg_of_lt hm hmn)
#align int.eq_zero_of_dvd_of_nonneg_of_lt Int.eq_zero_of_dvd_of_nonneg_of_lt

/-- If two integers are congruent to a sufficiently large modulus, they are equal. -/
lemma eq_of_mod_eq_of_natAbs_sub_lt_natAbs {a b c : ℤ} (h1 : a % b = c)
    (h2 : natAbs (a - c) < natAbs b) : a = c :=
  Int.eq_of_sub_eq_zero (eq_zero_of_dvd_of_natAbs_lt_natAbs (dvd_sub_of_emod_eq h1) h2)
#align int.eq_of_mod_eq_of_nat_abs_sub_lt_nat_abs Int.eq_of_mod_eq_of_natAbs_sub_lt_natAbs

lemma ofNat_add_negSucc_of_ge {m n : ℕ} (h : n.succ ≤ m) :
    ofNat m + -[n+1] = ofNat (m - n.succ) := by
  rw [negSucc_eq, ofNat_eq_natCast, ofNat_eq_natCast, ← natCast_one, ← natCast_add,
    ← Int.sub_eq_add_neg, ← Int.natCast_sub h]
#align int.of_nat_add_neg_succ_of_nat_of_ge Int.ofNat_add_negSucc_of_ge

lemma natAbs_le_of_dvd_ne_zero (hmn : m ∣ n) (hn : n ≠ 0) : natAbs m ≤ natAbs n :=
  not_lt.mp (mt (eq_zero_of_dvd_of_natAbs_lt_natAbs hmn) hn)
#align int.nat_abs_le_of_dvd_ne_zero Int.natAbs_le_of_dvd_ne_zero

@[deprecated (since := "2024-04-02")] alias coe_nat_dvd := natCast_dvd_natCast
@[deprecated (since := "2024-04-02")] alias coe_nat_dvd_right := dvd_natCast
@[deprecated (since := "2024-04-02")] alias coe_nat_dvd_left := natCast_dvd

/-! #### `/` and ordering -/

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

lemma natAbs_eq_of_dvd_dvd (hmn : m ∣ n) (hnm : n ∣ m) : natAbs m = natAbs n :=
  Nat.dvd_antisymm (natAbs_dvd_natAbs.2 hmn) (natAbs_dvd_natAbs.2 hnm)
#align int.nat_abs_eq_of_dvd_dvd Int.natAbs_eq_of_dvd_dvd

#align int.div_eq_div_of_mul_eq_mul Int.ediv_eq_ediv_of_mul_eq_mul

lemma ediv_dvd_of_dvd (hmn : m ∣ n) : n / m ∣ n := by
  obtain rfl | hm := eq_or_ne m 0
  · simpa using hmn
  · obtain ⟨a, ha⟩ := hmn
    simp [ha, Int.mul_ediv_cancel_left _ hm, Int.dvd_mul_left]
#align int.div_dvd_of_dvd Int.ediv_dvd_of_dvd

lemma le_iff_pos_of_dvd (ha : 0 < a) (hab : a ∣ b) : a ≤ b ↔ 0 < b :=
  ⟨Int.lt_of_lt_of_le ha, (Int.le_of_dvd · hab)⟩

lemma le_add_iff_lt_of_dvd_sub (ha : 0 < a) (hab : a ∣ c - b) : a + b ≤ c ↔ b < c := by
  rw [Int.add_le_iff_le_sub, ← Int.sub_pos, le_iff_pos_of_dvd ha hab]

/-! ### sign -/

lemma sign_natCast_of_ne_zero {n : ℕ} (hn : n ≠ 0) : Int.sign n = 1 := sign_ofNat_of_nonzero hn
#align int.sign_coe_nat_of_nonzero Int.sign_natCast_of_ne_zero

lemma sign_add_eq_of_sign_eq : ∀ {m n : ℤ}, m.sign = n.sign → (m + n).sign = n.sign := by
  have : (1 : ℤ) ≠ -1 := by decide
  rintro ((_ | m) | m) ((_ | n) | n) <;> simp [this, this.symm, Int.negSucc_add_negSucc]
  rw [Int.sign_eq_one_iff_pos]
  apply Int.add_pos <;> omega
#align int.sign_add_eq_of_sign_eq Int.sign_add_eq_of_sign_eq

/-! ### toNat -/

#align int.to_nat_eq_max Int.toNat_eq_max
#align int.to_nat_zero Int.toNat_zero
#align int.to_nat_one Int.toNat_one
#align int.to_nat_of_nonneg Int.toNat_of_nonneg

@[simp] lemma toNat_natCast (n : ℕ) : toNat ↑n = n := rfl
#align int.to_nat_coe_nat Int.toNat_natCast

@[simp] lemma toNat_natCast_add_one {n : ℕ} : ((n : ℤ) + 1).toNat = n + 1 := rfl
#align int.to_nat_coe_nat_add_one Int.toNat_natCast_add_one

@[simp] lemma toNat_le {n : ℕ} : toNat m ≤ n ↔ m ≤ n := by
  rw [ofNat_le.symm, toNat_eq_max, Int.max_le]; exact and_iff_left (ofNat_zero_le _)
#align int.to_nat_le Int.toNat_le

@[simp]
lemma lt_toNat {m : ℕ} : m < toNat n ↔ (m : ℤ) < n := by rw [← Int.not_le, ← Nat.not_le, toNat_le]
#align int.lt_to_nat Int.lt_toNat

lemma toNat_le_toNat {a b : ℤ} (h : a ≤ b) : toNat a ≤ toNat b := by
  rw [toNat_le]; exact Int.le_trans h (self_le_toNat b)
#align int.to_nat_le_to_nat Int.toNat_le_toNat

lemma toNat_lt_toNat {a b : ℤ} (hb : 0 < b) : toNat a < toNat b ↔ a < b where
  mp h := by cases a; exacts [lt_toNat.1 h, Int.lt_trans (neg_of_sign_eq_neg_one rfl) hb]
  mpr h := by rw [lt_toNat]; cases a; exacts [h, hb]
#align int.to_nat_lt_to_nat Int.toNat_lt_toNat

lemma lt_of_toNat_lt {a b : ℤ} (h : toNat a < toNat b) : a < b :=
  (toNat_lt_toNat <| lt_toNat.1 <| Nat.lt_of_le_of_lt (Nat.zero_le _) h).1 h
#align int.lt_of_to_nat_lt Int.lt_of_toNat_lt

@[simp] lemma toNat_pred_coe_of_pos {i : ℤ} (h : 0 < i) : ((i.toNat - 1 : ℕ) : ℤ) = i - 1 := by
  simp [h, Int.le_of_lt h, push_cast]
#align int.to_nat_pred_coe_of_pos Int.toNat_pred_coe_of_pos

@[simp] lemma toNat_eq_zero : ∀ {n : ℤ}, n.toNat = 0 ↔ n ≤ 0
  | (n : ℕ) => by simp
  | -[n+1] => by simpa [toNat] using Int.le_of_lt (negSucc_lt_zero n)

#align int.to_nat_eq_zero Int.toNat_eq_zero

@[simp]
theorem toNat_sub_of_le {a b : ℤ} (h : b ≤ a) : (toNat (a - b) : ℤ) = a - b :=
  Int.toNat_of_nonneg (Int.sub_nonneg_of_le h)
#align int.to_nat_sub_of_le Int.toNat_sub_of_le

@[deprecated (since := "2024-04-05")] alias coe_nat_pos := natCast_pos
@[deprecated (since := "2024-04-05")] alias coe_nat_succ_pos := natCast_succ_pos

lemma toNat_lt' {n : ℕ} (hn : n ≠ 0) : m.toNat < n ↔ m < n := by
  rw [← toNat_lt_toNat, toNat_natCast]; omega
#align int.to_nat_lt Int.toNat_lt'

lemma natMod_lt {n : ℕ} (hn : n ≠ 0) : m.natMod n < n :=
  (toNat_lt' hn).2 <| emod_lt_of_pos _ <| by omega
#align int.nat_mod_lt Int.natMod_lt

attribute [simp] natCast_pow

@[deprecated (since := "2024-05-25")] alias coe_nat_pow := natCast_pow
#align int.coe_nat_pow Int.natCast_pow

#align int.le_to_nat Int.self_le_toNat
#align int.le_to_nat_iff Int.le_toNat
#align int.to_nat_add Int.toNat_add
#align int.to_nat_add_nat Int.toNat_add_nat
#align int.pred_to_nat Int.pred_toNat
#align int.to_nat_sub_to_nat_neg Int.toNat_sub_toNat_neg
#align int.to_nat_add_to_nat_neg_eq_nat_abs Int.toNat_add_toNat_neg_eq_natAbs
#align int.mem_to_nat' Int.mem_toNat'
#align int.to_nat_neg_nat Int.toNat_neg_nat

-- Porting note: this was added in an ad hoc port for use in `Tactic/NormNum/Basic`
@[simp] lemma pow_eq (m : ℤ) (n : ℕ) : m.pow n = m ^ n := rfl

@[deprecated (since := "2024-04-02")] alias ofNat_eq_cast := ofNat_eq_natCast
@[deprecated (since := "2024-04-02")] alias cast_eq_cast_iff_Nat := natCast_inj
@[deprecated (since := "2024-04-02")] alias coe_nat_sub := Int.natCast_sub
@[deprecated (since := "2024-04-02")] alias coe_nat_nonneg := natCast_nonneg
@[deprecated (since := "2024-04-02")] alias sign_coe_add_one := sign_natCast_add_one
@[deprecated (since := "2024-04-02")] alias nat_succ_eq_int_succ := natCast_succ
@[deprecated (since := "2024-04-02")] alias succ_neg_nat_succ := succ_neg_natCast_succ
@[deprecated (since := "2024-04-02")] alias coe_pred_of_pos := natCast_pred_of_pos
@[deprecated (since := "2024-04-02")] alias coe_nat_div := natCast_div
@[deprecated (since := "2024-04-02")] alias coe_nat_ediv := natCast_ediv
@[deprecated (since := "2024-04-02")] alias sign_coe_nat_of_nonzero := sign_natCast_of_ne_zero
@[deprecated (since := "2024-04-02")] alias toNat_coe_nat := toNat_natCast
@[deprecated (since := "2024-04-02")] alias toNat_coe_nat_add_one := toNat_natCast_add_one
