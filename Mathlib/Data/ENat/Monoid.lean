/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Ring.WithTop
public import Mathlib.Data.ENat.Basic

import Mathlib.Algebra.Group.Nat.Units
import Mathlib.Data.Nat.Cast.Order.Basic

/-!
# `LinearOrderedAddCommMonoidWithTop` structure on `ENat`
-/

@[expose] public section

deriving instance
  AddMonoidWithOne, CommSemiring, LinearOrderedAddCommMonoidWithTop,
  OrderedSub, CanonicallyOrderedAdd, IsOrderedRing,
  CharZero, NoZeroDivisors
  for ENat

namespace ENat

variable {a b c m n : ℕ∞}

@[simp] lemma natCast_mul (m n : ℕ) : ↑(m * n) = (m * n : ℕ∞) := rfl

@[deprecated (since := "2026-07-17")] alias coe_mul := natCast_mul

@[simp] theorem mul_top (hm : m ≠ 0) : m * ⊤ = ⊤ := WithTop.mul_top hm
@[simp] theorem top_mul (hm : m ≠ 0) : ⊤ * m = ⊤ := WithTop.top_mul hm

/-- A version of `mul_top` where the RHS is stated as an `ite` -/
theorem mul_top' : m * ⊤ = if m = 0 then 0 else ⊤ := WithTop.mul_top' m

/-- A version of `top_mul` where the RHS is stated as an `ite` -/
theorem top_mul' : ⊤ * m = if m = 0 then 0 else ⊤ := WithTop.top_mul' m

@[simp] lemma top_pow {n : ℕ} (hn : n ≠ 0) : (⊤ : ℕ∞) ^ n = ⊤ := WithTop.top_pow hn

@[simp] lemma pow_eq_top_iff {n : ℕ} : a ^ n = ⊤ ↔ a = ⊤ ∧ n ≠ 0 := WithTop.pow_eq_top_iff

lemma pow_ne_top_iff {n : ℕ} : a ^ n ≠ ⊤ ↔ a ≠ ⊤ ∨ n = 0 := WithTop.pow_ne_top_iff

@[simp] lemma pow_lt_top_iff {n : ℕ} : a ^ n < ⊤ ↔ a < ⊤ ∨ n = 0 := WithTop.pow_lt_top_iff

lemma eq_top_of_pow (n : ℕ) (ha : a ^ n = ⊤) : a = ⊤ := WithTop.eq_top_of_pow n ha

@[simp] theorem lift_add (a b : ℕ∞) (h : a + b < ⊤) :
    lift (a + b) h = lift a (add_lt_top.1 h).1 + lift b (add_lt_top.1 h).2 := by
  apply natCast_inj.1
  simp

/-- Homomorphism from `ℕ∞` to `ℕ` sending `∞` to `0`. -/
def toNatHom : MonoidWithZeroHom ℕ∞ ℕ where
  toFun := toNat
  map_one' := rfl
  map_zero' := rfl
  map_mul' := WithTop.untopD_zero_mul

@[simp, norm_cast] lemma coe_toNatHom : toNatHom = toNat := rfl

lemma toNatHom_apply (n : ℕ) : toNatHom n = toNat n := rfl

@[simp]
theorem natCast_toNat_eq_self : ENat.toNat n = n ↔ n ≠ ⊤ :=
  ENat.recTopCoe (by decide) (fun _ => by simp [toNat_natCast]) n

@[deprecated (since := "2026-07-17")] alias coe_toNat_eq_self := natCast_toNat_eq_self

alias ⟨_, natCast_toNat⟩ := natCast_toNat_eq_self

@[deprecated (since := "2026-07-17")] alias coe_toNat := natCast_toNat

@[simp] lemma toNat_eq_iff_eq_natCast (n : ℕ∞) (m : ℕ) [NeZero m] :
    n.toNat = m ↔ n = m := by
  cases n
  · simpa using NeZero.ne' m
  · simp

@[simp] theorem toNat_mul (a b : ℕ∞) : (a * b).toNat = a.toNat * b.toNat := by
  cases a <;> cases b
  · simp
  · rename_i b; cases b <;> simp
  · rename_i a; cases a <;> simp
  · simp only [toNat_natCast]; rw [← natCast_mul, toNat_natCast]

theorem toNat_eq_iff {m : ℕ∞} {n : ℕ} (hn : n ≠ 0) : toNat m = n ↔ m = n := by
  induction m <;> simp [hn.symm]

lemma toNat_le_of_le_natCast {m : ℕ∞} {n : ℕ} (h : m ≤ n) : toNat m ≤ n := by
  lift m to ℕ using ne_top_of_le_ne_top (natCast_ne_top n) h
  simpa using h

@[deprecated (since := "2026-07-17")] alias toNat_le_of_le_coe := toNat_le_of_le_natCast

@[gcongr]
lemma toNat_le_toNat {m n : ℕ∞} (h : m ≤ n) (hn : n ≠ ⊤) : toNat m ≤ toNat n :=
  toNat_le_of_le_natCast <| h.trans_eq (natCast_toNat hn).symm

@[deprecated (since := "2026-07-17")] alias toNat_eq_iff_eq_coe := toNat_eq_iff_eq_natCast

@[deprecated add_pos_of_right (since := "2026-05-25")]
lemma add_one_pos : 0 < n + 1 :=
  add_pos_of_right zero_lt_one n

lemma natCast_lt_succ {n : ℕ} :
    (n : ℕ∞) < (n : ℕ∞) + 1 := by
  rw [← Nat.cast_one, ← Nat.cast_add, natCast_lt_natCast]
  exact lt_add_one n

protected lemma le_sub_of_add_le_left (ha : a ≠ ⊤) : a + b ≤ c → b ≤ c - a :=
  (addLECancellable_of_ne_top ha).le_tsub_of_add_le_left

protected lemma le_sub_of_add_le_right (hb : b ≠ ⊤) : a + b ≤ c → a ≤ c - b :=
  (addLECancellable_of_ne_top hb).le_tsub_of_add_le_right

lemma lt_add_left {n k : ℕ∞} (h : n ≠ ⊤) (h' : 0 < k) : n < k + n := calc
    _ = 0 + n := (zero_add n).symm
    _ < k + n := (add_lt_add_iff_right h).mpr h'

protected lemma sub_sub_cancel (h : a ≠ ⊤) (h2 : b ≤ a) : a - (a - b) = b :=
  (addLECancellable_of_ne_top <| ne_top_of_le_ne_top h tsub_le_self).tsub_tsub_cancel_of_le h2

lemma add_left_injective_of_ne_top {n : ℕ∞} (hn : n ≠ ⊤) : Function.Injective (· + n) := by
  intro a b e
  exact le_antisymm
    ((WithTop.add_le_add_iff_right hn).mp e.le)
    ((WithTop.add_le_add_iff_right hn).mp e.ge)

lemma add_right_injective_of_ne_top {n : ℕ∞} (hn : n ≠ ⊤) : Function.Injective (n + ·) := by
  simp_rw [add_comm n _]
  exact add_left_injective_of_ne_top hn

lemma mul_right_strictMono (ha : a ≠ 0) (h_top : a ≠ ⊤) : StrictMono (a * ·) :=
  WithTop.mul_right_strictMono (pos_iff_ne_zero.2 ha) h_top

lemma mul_left_strictMono (ha : a ≠ 0) (h_top : a ≠ ⊤) : StrictMono (· * a) :=
  WithTop.mul_left_strictMono (pos_iff_ne_zero.2 ha) h_top

@[simp]
lemma mul_le_mul_left_iff {x y : ℕ∞} (ha : a ≠ 0) (h_top : a ≠ ⊤) : a * x ≤ a * y ↔ x ≤ y :=
  (ENat.mul_right_strictMono ha h_top).le_iff_le

@[simp]
lemma mul_le_mul_right_iff {x y : ℕ∞} (ha : a ≠ 0) (h_top : a ≠ ⊤) : x * a ≤ y * a ↔ x ≤ y :=
  (ENat.mul_left_strictMono ha h_top).le_iff_le

@[gcongr]
lemma mul_le_mul_of_le_right {x y : ℕ∞} (hxy : x ≤ y) (ha : a ≠ 0) (h_top : a ≠ ⊤) :
    x * a ≤ y * a := by
  simpa [ha, h_top]

lemma self_le_mul_right (a : ℕ∞) (hc : c ≠ 0) : a ≤ a * c := by
  have hc' : 1 ≤ c := by
    cases c with
    | coe => simpa [Nat.one_le_iff_ne_zero] using hc
    | top => simp
  cases a with
  | top => rw [top_mul hc]
  | coe a => cases a with
    | zero => simp
    | succ a =>
      nth_rewrite 1 [← mul_one (M := ℕ∞) (a + 1 :)]
      rwa [ENat.mul_le_mul_left_iff] <;> simp

-- TODO: match name with `le_mul_of_one_le_left'`?
lemma self_le_mul_left (a : ℕ∞) (hc : c ≠ 0) : a ≤ c * a := by
  rw [mul_comm]
  exact ENat.self_le_mul_right a hc

instance : Unique ℕ∞ˣ where
  uniq x := by
    have := x.val_inv
    have x_top : x.val ≠ ⊤ := by
      intro h
      simp [h] at this
    have x_inv_top : x.inv ≠ ⊤ := by
      intro h
      simp only [h, ne_eq, x.ne_zero, not_false_eq_true, mul_top, top_ne_one] at this
    obtain ⟨y, x_y⟩ := ne_top_iff_exists.1 x_top
    obtain ⟨z, x_z⟩ := ne_top_iff_exists.1 x_inv_top
    replace x_y := x_y.symm
    rw [x_y, ← x_z, ← natCast_mul, ← natCast_one, natCast_inj, _root_.mul_eq_one] at this
    rwa [this.1, Nat.cast_one, Units.val_eq_one] at x_y

lemma add_one_natCast_le_withTop_of_lt {m : ℕ} {n : WithTop ℕ∞} (h : m < n) : (m + 1 : ℕ) ≤ n := by
  match n with
  | ⊤ => exact le_top
  | (⊤ : ℕ∞) => exact WithTop.coe_le_coe.2 (OrderTop.le_top _)
  | (n : ℕ) => simpa only [Nat.cast_le, ge_iff_le, Nat.cast_lt] using! h

@[simp] lemma coe_top_add_one : ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 = (⊤ : ℕ∞) := rfl

@[simp] lemma add_one_eq_coe_top_iff {n : WithTop ℕ∞} : n + 1 = (⊤ : ℕ∞) ↔ n = (⊤ : ℕ∞) := by
  match n with
  | ⊤ => exact Iff.rfl
  | (⊤ : ℕ∞) => simp
  | (n : ℕ) =>
    norm_cast
    simp only [natCast_ne_top]

@[simp] lemma natCast_ne_coe_top (n : ℕ) : (n : WithTop ℕ∞) ≠ (⊤ : ℕ∞) := nofun

lemma one_le_iff_ne_zero_withTop {n : WithTop ℕ∞} : 1 ≤ n ↔ n ≠ 0 :=
  ⟨fun h ↦ (zero_lt_one.trans_le h).ne',
    fun h ↦ add_one_natCast_le_withTop_of_lt (pos_iff_ne_zero.mpr h)⟩

lemma natCast_le_of_coe_top_le_withTop {N : WithTop ℕ∞} (hN : (⊤ : ℕ∞) ≤ N) (n : ℕ) : n ≤ N :=
  le_trans (mod_cast le_top) hN

lemma natCast_lt_of_coe_top_le_withTop {N : WithTop ℕ∞} (hN : (⊤ : ℕ∞) ≤ N) (n : ℕ) : n < N :=
  lt_of_lt_of_le (mod_cast lt_add_one n) (natCast_le_of_coe_top_le_withTop hN (n + 1))

section AddMonoidWithOne
variable {α : Type*} [AddMonoidWithOne α] [PartialOrder α] [AddLeftMono α] [ZeroLEOneClass α]

@[simp] lemma map_natCast_nonneg : 0 ≤ n.map (Nat.cast : ℕ → α) := by
  cases n <;> simp

variable [CharZero α]

lemma map_natCast_strictMono : StrictMono (map (Nat.cast : ℕ → α)) :=
  strictMono_map_iff.2 Nat.strictMono_cast

lemma map_natCast_injective : Function.Injective (map (Nat.cast : ℕ → α)) :=
  map_natCast_strictMono.injective

@[simp] lemma map_natCast_inj : m.map (Nat.cast : ℕ → α) = n.map Nat.cast ↔ m = n :=
  map_natCast_injective.eq_iff

@[simp] lemma map_natCast_eq_zero : n.map (Nat.cast : ℕ → α) = 0 ↔ n = 0 := by
  simp [← map_natCast_inj (α := α)]

end AddMonoidWithOne

/-- A version of `WithTop.map` for `AddMonoidHom`s. -/
@[simps -fullyApplied]
protected def _root_.AddMonoidHom.ENatMap {N : Type*} [AddZeroClass N]
    (f : ℕ →+ N) : ℕ∞ →+ WithTop N :=
  { ZeroHom.ENatMap f.toZeroHom, AddHom.ENatMap f.toAddHom with toFun := ENat.map f }

/-- A version of `ENat.map` for `MonoidWithZeroHom`s. -/
@[simps -fullyApplied]
protected def _root_.MonoidWithZeroHom.ENatMap {S : Type*} [MulZeroOneClass S] [DecidableEq S]
    [Nontrivial S] (f : ℕ →*₀ S)
    (hf : Function.Injective f) : ℕ∞ →*₀ WithTop S :=
  { f.toZeroHom.ENatMap, f.toMonoidHom.toOneHom.ENatMap with
    toFun := ENat.map f
    map_mul' := fun x y => by
      have : ∀ z, map f z = 0 ↔ z = 0 := fun z =>
        (WithTop.map_injective hf).eq_iff' f.toZeroHom.ENatMap.map_zero
      rcases Decidable.eq_or_ne x 0 with (rfl | hx)
      · simp
      rcases Decidable.eq_or_ne y 0 with (rfl | hy)
      · simp
      induction x with
      | top => simp [hy, this]
      | coe x =>
        induction y with
        | top =>
          have : (f x : WithTop S) ≠ 0 := by simpa [hf.eq_iff' (map_zero f)] using hx
          simp [mul_top hx, WithTop.mul_top this]
        | coe y => simp [← Nat.cast_mul, -natCast_mul] }

/-- A version of `ENat.map` for `RingHom`s. -/
@[simps -fullyApplied]
protected def _root_.RingHom.ENatMap {S : Type*} [CommSemiring S] [PartialOrder S]
    [CanonicallyOrderedAdd S]
    [DecidableEq S] [Nontrivial S] (f : ℕ →+* S) (hf : Function.Injective f) : ℕ∞ →+* WithTop S :=
  { MonoidWithZeroHom.ENatMap f.toMonoidWithZeroHom hf, f.toAddMonoidHom.ENatMap with }

@[simp]
lemma map_natCast_mul {R : Type*} [NonAssocSemiring R] [DecidableEq R] [CharZero R] (a b : ℕ∞) :
    (map Nat.cast (a * b) : WithTop R) = map Nat.cast a * map Nat.cast b :=
  map_mul ((.ofClass (Nat.castRingHom R) : ℕ →*₀ R).ENatMap Nat.cast_injective) a b

namespace WithBot

@[simp]
lemma add_natCast_cancel {a b : WithBot ℕ∞} {c : ℕ} : a + c = b + c ↔ a = b :=
  (IsAddRightRegular.all c).withTop.withBot.eq_iff

@[simp]
lemma add_one_cancel {a b : WithBot ℕ∞} : a + 1 = b + 1 ↔ a = b :=
  (IsAddRightRegular.all 1).withTop.withBot.eq_iff

lemma add_ofNat_cancel {a b : WithBot ℕ∞} {c : ℕ} [c.AtLeastTwo] :
    a + ofNat(c) = b + ofNat(c) ↔ a = b :=
  WithBot.add_natCast_cancel

@[simp]
lemma natCast_add_cancel {a b : WithBot ℕ∞} {c : ℕ} : c + a = c + b ↔ a = b :=
  (IsAddLeftRegular.all c).withTop.withBot.eq_iff

@[simp]
lemma one_add_cancel {a b : WithBot ℕ∞} : 1 + a = 1 + b ↔ a = b :=
  (IsAddLeftRegular.all 1).withTop.withBot.eq_iff

lemma ofNat_add_cancel {a b : WithBot ℕ∞} {c : ℕ} [c.AtLeastTwo] :
    ofNat(c) + a = ofNat(c) + b ↔ a = b :=
  WithBot.natCast_add_cancel

lemma add_le_add_natCast_right_iff {a b : WithBot ℕ∞} {c : ℕ} : a + c ≤ b + c ↔ a ≤ b :=
  (Contravariant.AddLECancellable (a := c)).withTop.withBot.add_le_add_iff_right

lemma add_le_add_one_right_iff {a b : WithBot ℕ∞} : a + 1 ≤ b + 1 ↔ a ≤ b :=
  WithBot.add_le_add_natCast_right_iff

lemma add_le_add_natCast_left_iff {a b : WithBot ℕ∞} {c : ℕ} : c + a ≤ c + b ↔ a ≤ b := by
  rw [add_comm _ a, add_comm _ b, WithBot.add_le_add_natCast_right_iff]

lemma add_le_add_one_left_iff {a b : WithBot ℕ∞} : 1 + a ≤ 1 + b ↔ a ≤ b :=
  WithBot.add_le_add_natCast_left_iff

end WithBot
end ENat
