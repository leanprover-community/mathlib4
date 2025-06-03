/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Batteries.Logic
import Batteries.Tactic.Init
import Mathlib.Data.Int.Notation
import Mathlib.Data.Nat.Notation
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar

/-!
# Basic operations on the integers

This file contains some basic lemmas about integers.

See note [foundational algebra order theory].

This file should not depend on anything defined in Mathlib (except for notation), so that it can be
upstreamed to Batteries easily.
-/

open Nat

namespace Int

variable {a b c d m n : ℤ}

protected theorem neg_eq_neg {a b : ℤ} (h : -a = -b) : a = b := Int.neg_inj.1 h

@[deprecated (since := "2025-03-07")] alias neg_nonpos_iff_nonneg := Int.neg_nonpos_iff

/-! ### succ and pred -/

/-- Immediate successor of an integer: `succ n = n + 1` -/
def succ (a : ℤ) := a + 1

/-- Immediate predecessor of an integer: `pred n = n - 1` -/
def pred (a : ℤ) := a - 1

lemma pred_succ (a : ℤ) : pred (succ a) = a := Int.add_sub_cancel _ _

lemma succ_pred (a : ℤ) : succ (pred a) = a := Int.sub_add_cancel _ _

lemma neg_succ (a : ℤ) : -succ a = pred (-a) := Int.neg_add

lemma succ_neg_succ (a : ℤ) : succ (-succ a) = -a := by rw [neg_succ, succ_pred]

lemma neg_pred (a : ℤ) : -pred a = succ (-a) := by
  rw [← Int.neg_eq_comm.mp (neg_succ (-a)), Int.neg_neg]

lemma pred_neg_pred (a : ℤ) : pred (-pred a) = -a := by rw [neg_pred, pred_succ]

lemma pred_nat_succ (n : ℕ) : pred (Nat.succ n) = n := pred_succ n

lemma neg_nat_succ (n : ℕ) : -(Nat.succ n : ℤ) = pred (-n) := neg_succ n

lemma succ_neg_natCast_succ (n : ℕ) : succ (-Nat.succ n) = -n := succ_neg_succ n

@[norm_cast] lemma natCast_pred_of_pos {n : ℕ} (h : 0 < n) : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
  cases n; cases h; simp [natCast_succ]

lemma lt_succ_self (a : ℤ) : a < succ a := by unfold succ; omega

lemma pred_self_lt (a : ℤ) : pred a < a := by unfold pred; omega

/--
Induction on integers: prove a proposition `p i` by proving the base case `p 0`,
the upwards induction step `p i → p (i + 1)` and the downwards induction step `p (-i) → p (-i - 1)`.

It is used as the default induction principle for the `induction` tactic.
-/
@[elab_as_elim, induction_eliminator] protected lemma induction_on {p : ℤ → Prop} (i : ℤ)
    (hz : p 0) (hp : ∀ i : ℕ, p i → p (i + 1)) (hn : ∀ i : ℕ, p (-i) → p (-i - 1)) : p i := by
  cases i with
  | ofNat i =>
    induction i with
    | zero => exact hz
    | succ i ih => exact hp _ ih
  | negSucc i =>
    suffices ∀ n : ℕ, p (-n) from this (i + 1)
    intro n; induction n with
    | zero => simp [hz]
    | succ n ih => simpa [natCast_succ, Int.neg_add, Int.sub_eq_add_neg] using hn _ ih

section inductionOn'

variable {C : ℤ → Sort*} (z b : ℤ)
  (H0 : C b) (Hs : ∀ k, b ≤ k → C k → C (k + 1)) (Hp : ∀ k ≤ b, C k → C (k - 1))

/-- Inductively define a function on `ℤ` by defining it at `b`, for the `succ` of a number greater
than `b`, and the `pred` of a number less than `b`. -/
@[elab_as_elim] protected def inductionOn' : C z :=
  cast (congrArg C <| show b + (z - b) = z by rw [Int.add_comm, z.sub_add_cancel b]) <|
  match z - b with
  | .ofNat n => pos n
  | .negSucc n => neg n
where
  /-- The positive case of `Int.inductionOn'`. -/
  pos : ∀ n : ℕ, C (b + n)
  | 0 => cast (by simp) H0
  | n+1 => cast (by rw [Int.add_assoc]; rfl) <|
    Hs _ (Int.le_add_of_nonneg_right (natCast_nonneg _)) (pos n)
  /-- The negative case of `Int.inductionOn'`. -/
  neg : ∀ n : ℕ, C (b + -[n+1])
  | 0 => Hp _ Int.le_rfl H0
  | n+1 => by
    refine cast (by rw [Int.add_sub_assoc]; rfl) (Hp _ (Int.le_of_lt ?_) (neg n))
    omega

variable {z b H0 Hs Hp}

lemma inductionOn'_self : b.inductionOn' b H0 Hs Hp = H0 :=
  cast_eq_iff_heq.mpr <| .symm <| by rw [b.sub_self, ← cast_eq_iff_heq]; rfl

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
    refine (cast_heq _ _).trans ?_
    congr
    symm
    rw [Int.inductionOn', cast_eq_iff_heq, show b + -[n+1] - b = -[n+1] by omega]

end inductionOn'

/-- Inductively define a function on `ℤ` by defining it on `ℕ` and extending it from `n` to `-n`. -/
@[elab_as_elim] protected def negInduction {C : ℤ → Sort*} (nat : ∀ n : ℕ, C n)
    (neg : (∀ n : ℕ, C n) → ∀ n : ℕ, C (-n)) : ∀ n : ℤ, C n
  | .ofNat n => nat n
  | .negSucc n => neg nat <| n + 1

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

/-- See `Int.inductionOn'` for an induction in both directions. -/
protected theorem le_induction_down {P : ℤ → Prop} {m : ℤ} (h0 : P m)
    (h1 : ∀ n : ℤ, n ≤ m → P n → P (n - 1)) (n : ℤ) : n ≤ m → P n :=
  Int.inductionOn' n m (fun _ ↦ h0) (fun k hle _ hle' ↦ by omega)
    fun k hle hi _ ↦ h1 k hle (hi hle)

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

end strongRec

/-! ### mul -/

/-! ### natAbs -/

alias natAbs_sq := natAbs_pow_two

theorem sign_mul_self_eq_natAbs (a : Int) : sign a * a = natAbs a :=
  sign_mul_self a

/-! ### `/` -/

lemma natCast_div (m n : ℕ) : ((m / n : ℕ) : ℤ) = m / n := natCast_ediv m n

lemma ediv_of_neg_of_pos {a b : ℤ} (Ha : a < 0) (Hb : 0 < b) : ediv a b = -((-a - 1) / b + 1) :=
  match a, b, eq_negSucc_of_lt_zero Ha, eq_succ_of_zero_lt Hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by
    rw [show (- -[m+1] : ℤ) = (m + 1 : ℤ) by rfl]; rw [Int.add_sub_cancel]; rfl

/-! ### mod -/

@[simp, norm_cast] lemma natCast_mod (m n : ℕ) : (↑(m % n) : ℤ) = ↑m % ↑n := natCast_emod m n

@[deprecated (since := "2025-04-16")] alias add_emod_eq_add_mod_right := add_emod_eq_add_emod_right

lemma div_le_iff_of_dvd_of_pos (hb : 0 < b) (hba : b ∣ a) : a / b ≤ c ↔ a ≤ b * c :=
  ediv_le_iff_of_dvd_of_pos hb hba

lemma div_le_iff_of_dvd_of_neg (hb : b < 0) (hba : b ∣ a) : a / b ≤ c ↔ b * c ≤ a :=
  ediv_le_iff_of_dvd_of_neg hb hba

lemma div_lt_iff_of_dvd_of_pos (hb : 0 < b) (hba : b ∣ a) : a / b < c ↔ a < b * c :=
  ediv_lt_iff_of_dvd_of_pos hb hba

lemma div_lt_iff_of_dvd_of_neg (hb : b < 0) (hba : b ∣ a) : a / b < c ↔ b * c < a :=
  ediv_lt_iff_of_dvd_of_neg hb hba

lemma le_div_iff_of_dvd_of_pos (hc : 0 < c) (hcb : c ∣ b) : a ≤ b / c ↔ c * a ≤ b :=
  le_ediv_iff_of_dvd_of_pos hc hcb

lemma le_div_iff_of_dvd_of_neg (hc : c < 0) (hcb : c ∣ b) : a ≤ b / c ↔ b ≤ c * a :=
  le_ediv_iff_of_dvd_of_neg hc hcb

lemma lt_div_iff_of_dvd_of_pos (hc : 0 < c) (hcb : c ∣ b) : a < b / c ↔ c * a < b :=
  lt_ediv_iff_of_dvd_of_pos hc hcb

lemma lt_div_iff_of_dvd_of_neg (hc : c < 0) (hcb : c ∣ b) : a < b / c ↔ b < c * a :=
  lt_ediv_iff_of_dvd_of_neg hc hcb

lemma div_le_div_iff_of_dvd_of_pos_of_pos (hb : 0 < b) (hd : 0 < d) (hba : b ∣ a)
    (hdc : d ∣ c) : a / b ≤ c / d ↔ d * a ≤ c * b :=
  ediv_le_ediv_iff_of_dvd_of_pos_of_pos hb hd hba hdc

lemma div_le_div_iff_of_dvd_of_pos_of_neg (hb : 0 < b) (hd : d < 0) (hba : b ∣ a) (hdc : d ∣ c) :
    a / b ≤ c / d ↔ c * b ≤ d * a :=
  ediv_le_ediv_iff_of_dvd_of_pos_of_neg hb hd hba hdc

lemma div_le_div_iff_of_dvd_of_neg_of_pos (hb : b < 0) (hd : 0 < d) (hba : b ∣ a)  (hdc : d ∣ c) :
    a / b ≤ c / d ↔ c * b ≤ d * a :=
  ediv_le_ediv_iff_of_dvd_of_neg_of_pos hb hd hba hdc

lemma div_le_div_iff_of_dvd_of_neg_of_neg (hb : b < 0) (hd : d < 0) (hba : b ∣ a) (hdc : d ∣ c) :
    a / b ≤ c / d ↔ d * a ≤ c * b :=
  ediv_le_ediv_iff_of_dvd_of_neg_of_neg hb hd hba hdc

lemma div_lt_div_iff_of_dvd_of_pos (hb : 0 < b) (hd : 0 < d) (hba : b ∣ a) (hdc : d ∣ c) :
    a / b < c / d ↔ d * a < c * b :=
  ediv_lt_ediv_iff_of_dvd_of_pos hb hd hba hdc

lemma div_lt_div_iff_of_dvd_of_pos_of_neg (hb : 0 < b) (hd : d < 0) (hba : b ∣ a) (hdc : d ∣ c) :
    a / b < c / d ↔ c * b < d * a :=
  ediv_lt_ediv_iff_of_dvd_of_pos_of_neg hb hd hba hdc

lemma div_lt_div_iff_of_dvd_of_neg_of_pos (hb : b < 0) (hd : 0 < d) (hba : b ∣ a) (hdc : d ∣ c) :
    a / b < c / d ↔ c * b < d * a :=
  ediv_lt_ediv_iff_of_dvd_of_neg_of_pos hb hd hba hdc

lemma div_lt_div_iff_of_dvd_of_neg_of_neg (hb : b < 0) (hd : d < 0) (hba : b ∣ a) (hdc : d ∣ c) :
    a / b < c / d ↔ d * a < c * b :=
  ediv_lt_ediv_iff_of_dvd_of_neg_of_neg hb hd hba hdc

/-! ### properties of `/` and `%` -/

lemma emod_two_eq_zero_or_one (n : ℤ) : n % 2 = 0 ∨ n % 2 = 1 :=
  emod_two_eq n

/-! ### dvd -/

lemma dvd_mul_of_div_dvd (h : b ∣ a) (hdiv : a / b ∣ c) : a ∣ b * c :=
  dvd_mul_of_ediv_dvd h hdiv

lemma div_dvd_iff_dvd_mul (h : b ∣ a) (hb : b ≠ 0) : a / b ∣ c ↔ a ∣ b * c :=
  ediv_dvd_iff_dvd_mul h hb

lemma mul_dvd_of_dvd_div (hcb : c ∣ b) (h : a ∣ b / c) : c * a ∣ b :=
  mul_dvd_of_dvd_ediv hcb h

lemma dvd_div_of_mul_dvd (h : a * b ∣ c) : b ∣ c / a :=
  dvd_ediv_of_mul_dvd h

lemma dvd_div_iff_mul_dvd (hbc : c ∣ b) : a ∣ b / c ↔ c * a ∣ b := by
  simp [hbc]

/-- If `n > 0` then `m` is not divisible by `n` iff it is between `n * k` and `n * (k + 1)`
  for some `k`. -/
lemma exists_lt_and_lt_iff_not_dvd (m : ℤ) (hn : 0 < n) :
    (∃ k, n * k < m ∧ m < n * (k + 1)) ↔ ¬n ∣ m :=
  (not_dvd_iff_lt_mul_succ m hn).symm

lemma eq_mul_div_of_mul_eq_mul_of_dvd_left (hb : b ≠ 0) (hbc : b ∣ c) (h : b * a = c * d) :
    a = c / b * d := by
  obtain ⟨k, rfl⟩ := hbc
  rw [Int.mul_ediv_cancel_left _ hb]
  rwa [Int.mul_assoc, Int.mul_eq_mul_left_iff hb] at h

lemma ofNat_add_negSucc_of_ge {m n : ℕ} (h : n.succ ≤ m) :
    ofNat m + -[n+1] = ofNat (m - n.succ) := by
  rw [negSucc_eq, ofNat_eq_natCast, ofNat_eq_natCast, ← Int.natCast_one, ← Int.natCast_add,
    ← Int.sub_eq_add_neg, ← Int.natCast_sub h]

/-! #### `/` and ordering -/

lemma le_iff_pos_of_dvd (ha : 0 < a) (hab : a ∣ b) : a ≤ b ↔ 0 < b :=
  ⟨Int.lt_of_lt_of_le ha, (Int.le_of_dvd · hab)⟩

lemma le_add_iff_lt_of_dvd_sub (ha : 0 < a) (hab : a ∣ c - b) : a + b ≤ c ↔ b < c := by
  rw [Int.add_le_iff_le_sub, ← Int.sub_pos, le_iff_pos_of_dvd ha hab]

/-! ### sign -/

lemma sign_add_eq_of_sign_eq : ∀ {m n : ℤ}, m.sign = n.sign → (m + n).sign = n.sign := by
  have : (1 : ℤ) ≠ -1 := by decide
  rintro ((_ | m) | m) ((_ | n) | n) <;> simp [this, this.symm] <;> omega

/-! ### toNat -/

@[simp] lemma toNat_pred_coe_of_pos {i : ℤ} (h : 0 < i) : ((i.toNat - 1 : ℕ) : ℤ) = i - 1 := by
  simp only [lt_toNat, Int.cast_ofNat_Int, h, natCast_pred_of_pos, Int.le_of_lt h, toNat_of_nonneg]

lemma toNat_lt'' {n : ℕ} (hn : n ≠ 0) : m.toNat < n ↔ m < n := by omega

/-- The modulus of an integer by another as a natural. Uses the E-rounding convention. -/
def natMod (m n : ℤ) : ℕ := (m % n).toNat

lemma natMod_lt {n : ℕ} (hn : n ≠ 0) : m.natMod n < n :=
  (toNat_lt'' hn).2 <| emod_lt_of_pos _ <| by omega

/-- For use in `Mathlib/Tactic/NormNum/Pow.lean` -/
@[simp] lemma pow_eq (m : ℤ) (n : ℕ) : m.pow n = m ^ n := rfl

end Int
