/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.PSub
import Mathlib.Data.Nat.Size
import Mathlib.Data.Num.Bitwise

/-!
# Properties of the binary representation of integers
-/

open Int

attribute [local simp] add_assoc

namespace PosNum

variable {α : Type*}

@[simp, norm_cast]
theorem cast_one [One α] [Add α] : ((1 : PosNum) : α) = 1 :=
  rfl

@[simp]
theorem cast_one' [One α] [Add α] : (PosNum.one : α) = 1 :=
  rfl

@[simp, norm_cast]
theorem cast_bit0 [One α] [Add α] (n : PosNum) : (n.bit0 : α) = (n : α) + n :=
  rfl

@[simp, norm_cast]
theorem cast_bit1 [One α] [Add α] (n : PosNum) : (n.bit1 : α) = ((n : α) + n) + 1 :=
  rfl

@[simp, norm_cast]
theorem cast_to_nat [AddMonoidWithOne α] : ∀ n : PosNum, ((n : ℕ) : α) = n
  | 1 => Nat.cast_one
  | bit0 p => by dsimp; rw [Nat.cast_add, p.cast_to_nat]
  | bit1 p => by dsimp; rw [Nat.cast_add, Nat.cast_add, Nat.cast_one, p.cast_to_nat]

@[norm_cast]
theorem to_nat_to_int (n : PosNum) : ((n : ℕ) : ℤ) = n :=
  cast_to_nat _

@[simp, norm_cast]
theorem cast_to_int [AddGroupWithOne α] (n : PosNum) : ((n : ℤ) : α) = n := by
  rw [← to_nat_to_int, Int.cast_natCast, cast_to_nat]

theorem succ_to_nat : ∀ n, (succ n : ℕ) = n + 1
  | 1 => rfl
  | bit0 _ => rfl
  | bit1 p =>
    (congr_arg (fun n ↦ n + n) (succ_to_nat p)).trans <|
      show ↑p + 1 + ↑p + 1 = ↑p + ↑p + 1 + 1 by simp [add_left_comm]

theorem one_add (n : PosNum) : 1 + n = succ n := by cases n <;> rfl

theorem add_one (n : PosNum) : n + 1 = succ n := by cases n <;> rfl

@[norm_cast]
theorem add_to_nat : ∀ m n, ((m + n : PosNum) : ℕ) = m + n
  | 1, b => by rw [one_add b, succ_to_nat, add_comm, cast_one]
  | a, 1 => by rw [add_one a, succ_to_nat, cast_one]
  | bit0 a, bit0 b => (congr_arg (fun n ↦ n + n) (add_to_nat a b)).trans <| add_add_add_comm _ _ _ _
  | bit0 a, bit1 b =>
    (congr_arg (fun n ↦ (n + n) + 1) (add_to_nat a b)).trans <|
      show (a + b + (a + b) + 1 : ℕ) = a + a + (b + b + 1) by simp [add_left_comm]
  | bit1 a, bit0 b =>
    (congr_arg (fun n ↦ (n + n) + 1) (add_to_nat a b)).trans <|
      show (a + b + (a + b) + 1 : ℕ) = a + a + 1 + (b + b) by simp [add_comm, add_left_comm]
  | bit1 a, bit1 b =>
    show (succ (a + b) + succ (a + b) : ℕ) = a + a + 1 + (b + b + 1) by
      rw [succ_to_nat, add_to_nat a b]; simp [add_left_comm]

theorem add_succ : ∀ m n : PosNum, m + succ n = succ (m + n)
  | 1, b => by simp [one_add]
  | bit0 a, 1 => congr_arg bit0 (add_one a)
  | bit1 a, 1 => congr_arg bit1 (add_one a)
  | bit0 _, bit0 _ => rfl
  | bit0 a, bit1 b => congr_arg bit0 (add_succ a b)
  | bit1 _, bit0 _ => rfl
  | bit1 a, bit1 b => congr_arg bit1 (add_succ a b)

theorem bit0_of_bit0 : ∀ n, n + n = bit0 n
  | 1 => rfl
  | bit0 p => congr_arg bit0 (bit0_of_bit0 p)
  | bit1 p => show bit0 (succ (p + p)) = _ by rw [bit0_of_bit0 p, succ]

theorem bit1_of_bit1 (n : PosNum) : (n + n) + 1 = bit1 n :=
  show (n + n) + 1 = bit1 n by rw [add_one, bit0_of_bit0, succ]

@[norm_cast]
theorem mul_to_nat (m) : ∀ n, ((m * n : PosNum) : ℕ) = m * n
  | 1 => (mul_one _).symm
  | bit0 p => show (↑(m * p) + ↑(m * p) : ℕ) = ↑m * (p + p) by rw [mul_to_nat m p, left_distrib]
  | bit1 p =>
    (add_to_nat (bit0 (m * p)) m).trans <|
      show (↑(m * p) + ↑(m * p) + ↑m : ℕ) = ↑m * (p + p) + m by rw [mul_to_nat m p, left_distrib]

theorem to_nat_pos : ∀ n : PosNum, 0 < (n : ℕ)
  | 1 => Nat.zero_lt_one
  | bit0 p =>
    let h := to_nat_pos p
    add_pos h h
  | bit1 _p => Nat.succ_pos _

theorem cmp_to_nat_lemma {m n : PosNum} : (m : ℕ) < n → (bit1 m : ℕ) < bit0 n :=
  show (m : ℕ) < n → (m + m + 1 + 1 : ℕ) ≤ n + n by
    intro h; rw [Nat.add_right_comm m m 1, add_assoc]; exact Nat.add_le_add h h

theorem cmp_swap (m) : ∀ n, (cmp m n).swap = cmp n m := by
  induction m with | one => ?_ | bit1 m IH => ?_ | bit0 m IH => ?_ <;>
    intro n <;> obtain - | n | n := n <;> unfold cmp <;>
      try { rfl } <;> rw [← IH] <;> cases cmp m n <;> rfl

theorem cmp_to_nat : ∀ m n, (Ordering.casesOn (cmp m n) ((m : ℕ) < n) (m = n) ((n : ℕ) < m) : Prop)
  | 1, 1 => rfl
  | bit0 a, 1 =>
    let h : (1 : ℕ) ≤ a := to_nat_pos a
    Nat.add_le_add h h
  | bit1 a, 1 => Nat.succ_lt_succ <| to_nat_pos <| bit0 a
  | 1, bit0 b =>
    let h : (1 : ℕ) ≤ b := to_nat_pos b
    Nat.add_le_add h h
  | 1, bit1 b => Nat.succ_lt_succ <| to_nat_pos <| bit0 b
  | bit0 a, bit0 b => by
    dsimp [cmp]
    have := cmp_to_nat a b; revert this; cases cmp a b <;> dsimp <;> intro this
    · exact Nat.add_lt_add this this
    · rw [this]
    · exact Nat.add_lt_add this this
  | bit0 a, bit1 b => by
    dsimp [cmp]
    have := cmp_to_nat a b; revert this; cases cmp a b <;> dsimp <;> intro this
    · exact Nat.le_succ_of_le (Nat.add_lt_add this this)
    · rw [this]
      apply Nat.lt_succ_self
    · exact cmp_to_nat_lemma this
  | bit1 a, bit0 b => by
    dsimp [cmp]
    have := cmp_to_nat a b; revert this; cases cmp a b <;> dsimp <;> intro this
    · exact cmp_to_nat_lemma this
    · rw [this]
      apply Nat.lt_succ_self
    · exact Nat.le_succ_of_le (Nat.add_lt_add this this)
  | bit1 a, bit1 b => by
    dsimp [cmp]
    have := cmp_to_nat a b; revert this; cases cmp a b <;> dsimp <;> intro this
    · exact Nat.succ_lt_succ (Nat.add_lt_add this this)
    · rw [this]
    · exact Nat.succ_lt_succ (Nat.add_lt_add this this)

@[norm_cast]
theorem lt_to_nat {m n : PosNum} : (m : ℕ) < n ↔ m < n :=
  show (m : ℕ) < n ↔ cmp m n = Ordering.lt from
    match cmp m n, cmp_to_nat m n with
    | Ordering.lt, h => by simp [h]
    | Ordering.eq, h => by simp [h]
    | Ordering.gt, h => by simp [not_lt_of_gt h]

@[norm_cast]
theorem le_to_nat {m n : PosNum} : (m : ℕ) ≤ n ↔ m ≤ n := by
  rw [← not_lt]; exact not_congr lt_to_nat

end PosNum

namespace Num

variable {α : Type*}

open PosNum

theorem add_zero (n : Num) : n + 0 = n := by cases n <;> rfl

theorem zero_add (n : Num) : 0 + n = n := by cases n <;> rfl

theorem add_one : ∀ n : Num, n + 1 = succ n
  | 0 => rfl
  | pos p => by cases p <;> rfl

theorem add_succ : ∀ m n : Num, m + succ n = succ (m + n)
  | 0, n => by simp [zero_add]
  | pos p, 0 => show pos (p + 1) = succ (pos p + 0) by rw [PosNum.add_one, add_zero, succ, succ']
  | pos _, pos _ => congr_arg pos (PosNum.add_succ _ _)

theorem bit0_of_bit0 : ∀ n : Num, n + n = n.bit0
  | 0 => rfl
  | pos p => congr_arg pos p.bit0_of_bit0

theorem bit1_of_bit1 : ∀ n : Num, (n + n) + 1 = n.bit1
  | 0 => rfl
  | pos p => congr_arg pos p.bit1_of_bit1

@[simp]
theorem ofNat'_zero : Num.ofNat' 0 = 0 := by simp [Num.ofNat']

theorem ofNat'_bit (b n) : ofNat' (Nat.bit b n) = cond b Num.bit1 Num.bit0 (ofNat' n) :=
  Nat.binaryRec_eq _ _ (.inl rfl)

@[simp]
theorem ofNat'_one : Num.ofNat' 1 = 1 := by erw [ofNat'_bit true 0, cond, ofNat'_zero]; rfl

theorem bit1_succ : ∀ n : Num, n.bit1.succ = n.succ.bit0
  | 0 => rfl
  | pos _n => rfl

theorem ofNat'_succ : ∀ {n}, ofNat' (n + 1) = ofNat' n + 1 :=
  @(Nat.binaryRec (by simp [zero_add]) fun b n ih => by
    cases b
    · erw [ofNat'_bit true n, ofNat'_bit]
      simp only [← bit1_of_bit1, ← bit0_of_bit0, cond]
    · rw [show n.bit true + 1 = (n + 1).bit false by simp [Nat.bit, mul_add],
        ofNat'_bit, ofNat'_bit, ih]
      simp only [cond, add_one, bit1_succ])

@[simp]
theorem add_ofNat' (m n) : Num.ofNat' (m + n) = Num.ofNat' m + Num.ofNat' n := by
  induction n
  · simp only [Nat.add_zero, ofNat'_zero, add_zero]
  · simp only [Nat.add_succ, Nat.add_zero, ofNat'_succ, add_one, add_succ, *]

@[simp, norm_cast]
theorem cast_zero [Zero α] [One α] [Add α] : ((0 : Num) : α) = 0 :=
  rfl

@[simp]
theorem cast_zero' [Zero α] [One α] [Add α] : (Num.zero : α) = 0 :=
  rfl

@[simp, norm_cast]
theorem cast_one [Zero α] [One α] [Add α] : ((1 : Num) : α) = 1 :=
  rfl

@[simp]
theorem cast_pos [Zero α] [One α] [Add α] (n : PosNum) : (Num.pos n : α) = n :=
  rfl

theorem succ'_to_nat : ∀ n, (succ' n : ℕ) = n + 1
  | 0 => (Nat.zero_add _).symm
  | pos _p => PosNum.succ_to_nat _

theorem succ_to_nat (n) : (succ n : ℕ) = n + 1 :=
  succ'_to_nat n

@[simp, norm_cast]
theorem cast_to_nat [AddMonoidWithOne α] : ∀ n : Num, ((n : ℕ) : α) = n
  | 0 => Nat.cast_zero
  | pos p => p.cast_to_nat

@[norm_cast]
theorem add_to_nat : ∀ m n, ((m + n : Num) : ℕ) = m + n
  | 0, 0 => rfl
  | 0, pos _q => (Nat.zero_add _).symm
  | pos _p, 0 => rfl
  | pos _p, pos _q => PosNum.add_to_nat _ _

@[norm_cast]
theorem mul_to_nat : ∀ m n, ((m * n : Num) : ℕ) = m * n
  | 0, 0 => rfl
  | 0, pos _q => (zero_mul _).symm
  | pos _p, 0 => rfl
  | pos _p, pos _q => PosNum.mul_to_nat _ _

theorem cmp_to_nat : ∀ m n, (Ordering.casesOn (cmp m n) ((m : ℕ) < n) (m = n) ((n : ℕ) < m) : Prop)
  | 0, 0 => rfl
  | 0, pos _ => to_nat_pos _
  | pos _, 0 => to_nat_pos _
  | pos a, pos b => by
    have := PosNum.cmp_to_nat a b; revert this; dsimp [cmp]; cases PosNum.cmp a b
    exacts [id, congr_arg pos, id]

@[norm_cast]
theorem lt_to_nat {m n : Num} : (m : ℕ) < n ↔ m < n :=
  show (m : ℕ) < n ↔ cmp m n = Ordering.lt from
    match cmp m n, cmp_to_nat m n with
    | Ordering.lt, h => by simp [h]
    | Ordering.eq, h => by simp [h]
    | Ordering.gt, h => by simp [not_lt_of_gt h]

@[norm_cast]
theorem le_to_nat {m n : Num} : (m : ℕ) ≤ n ↔ m ≤ n := by
  rw [← not_lt]; exact not_congr lt_to_nat

end Num

namespace PosNum

@[simp]
theorem of_to_nat' : ∀ n : PosNum, Num.ofNat' (n : ℕ) = Num.pos n
  | 1 => by erw [@Num.ofNat'_bit true 0, Num.ofNat'_zero]; rfl
  | bit0 p => by
      simpa only [Nat.bit_false, cond_false, two_mul, of_to_nat' p] using Num.ofNat'_bit false p
  | bit1 p => by
      simpa only [Nat.bit_true, cond_true, two_mul, of_to_nat' p] using Num.ofNat'_bit true p

end PosNum

namespace Num

@[simp, norm_cast]
theorem of_to_nat' : ∀ n : Num, Num.ofNat' (n : ℕ) = n
  | 0 => ofNat'_zero
  | pos p => p.of_to_nat'

lemma toNat_injective : Function.Injective (castNum : Num → ℕ) :=
  Function.LeftInverse.injective of_to_nat'

@[norm_cast]
theorem to_nat_inj {m n : Num} : (m : ℕ) = n ↔ m = n := toNat_injective.eq_iff

/-- This tactic tries to turn an (in)equality about `Num`s to one about `Nat`s by rewriting.
```lean
example (n : Num) (m : Num) : n ≤ n + m := by
  transfer_rw
  exact Nat.le_add_right _ _
```
-/
scoped macro (name := transfer_rw) "transfer_rw" : tactic => `(tactic|
    (repeat first | rw [← to_nat_inj] | rw [← lt_to_nat] | rw [← le_to_nat]
     repeat first | rw [add_to_nat] | rw [mul_to_nat] | rw [cast_one] | rw [cast_zero]))

/--
This tactic tries to prove (in)equalities about `Num`s by transferring them to the `Nat` world and
then trying to call `simp`.
```lean
example (n : Num) (m : Num) : n ≤ n + m := by transfer
```
-/
scoped macro (name := transfer) "transfer" : tactic => `(tactic|
    (intros; transfer_rw; try simp))

instance addMonoid : AddMonoid Num where
  zero_add := zero_add
  add_zero := add_zero
  add_assoc := by transfer
  nsmul := nsmulRec

instance addMonoidWithOne : AddMonoidWithOne Num :=
  { Num.addMonoid with
    natCast := Num.ofNat'
    natCast_zero := ofNat'_zero
    natCast_succ := fun _ => ofNat'_succ }

instance commSemiring : CommSemiring Num where
  __ := Num.addMonoid
  __ := Num.addMonoidWithOne
  npow := @npowRec Num ⟨1⟩ ⟨(· * ·)⟩
  mul_zero _ := by rw [← to_nat_inj, mul_to_nat, cast_zero, mul_zero]
  zero_mul _ := by rw [← to_nat_inj, mul_to_nat, cast_zero, zero_mul]
  mul_one _ := by rw [← to_nat_inj, mul_to_nat, cast_one, mul_one]
  one_mul _ := by rw [← to_nat_inj, mul_to_nat, cast_one, one_mul]
  add_comm _ _ := by simp_rw [← to_nat_inj, add_to_nat, add_comm]
  mul_comm _ _ := by simp_rw [← to_nat_inj, mul_to_nat, mul_comm]
  mul_assoc _ _ _ := by simp_rw [← to_nat_inj, mul_to_nat, mul_assoc]
  left_distrib _ _ _ := by simp only [← to_nat_inj, mul_to_nat, add_to_nat, mul_add]
  right_distrib _ _ _ := by simp only [← to_nat_inj, mul_to_nat, add_to_nat, add_mul]

instance partialOrder : PartialOrder Num where
  lt_iff_le_not_ge a b := by simp only [← lt_to_nat, ← le_to_nat, lt_iff_le_not_ge]
  le_refl := by transfer
  le_trans a b c := by transfer_rw; apply le_trans
  le_antisymm a b := by transfer_rw; apply le_antisymm

instance isOrderedCancelAddMonoid : IsOrderedCancelAddMonoid Num where
  add_le_add_left a b h c := by revert h; transfer_rw; exact fun h => add_le_add_left h c
  le_of_add_le_add_left a b c := by transfer_rw; apply le_of_add_le_add_left

instance linearOrder : LinearOrder Num :=
  { le_total := by
      intro a b
      transfer_rw
      apply le_total
    toDecidableLT := Num.decidableLT
    toDecidableLE := Num.decidableLE
    -- This is relying on an automatically generated instance name,
    -- generated in a `deriving` handler.
    -- See https://github.com/leanprover/lean4/issues/2343
    toDecidableEq := instDecidableEqNum }

instance isStrictOrderedRing : IsStrictOrderedRing Num where
  zero_le_one := by decide
  exists_pair_ne := ⟨0, 1, by decide⟩
  mul_lt_mul_of_pos_left a ha b c := by
    revert ha
    transfer_rw
    apply flip mul_lt_mul_of_pos_left
  mul_lt_mul_of_pos_right a ha b c := by
    revert ha
    transfer_rw
    apply flip mul_lt_mul_of_pos_right

@[norm_cast]
theorem add_of_nat (m n) : ((m + n : ℕ) : Num) = m + n :=
  add_ofNat' _ _

@[norm_cast]
theorem to_nat_to_int (n : Num) : ((n : ℕ) : ℤ) = n :=
  cast_to_nat _

@[simp, norm_cast]
theorem cast_to_int {α} [AddGroupWithOne α] (n : Num) : ((n : ℤ) : α) = n := by
  rw [← to_nat_to_int, Int.cast_natCast, cast_to_nat]

theorem to_of_nat : ∀ n : ℕ, ((n : Num) : ℕ) = n
  | 0 => by rw [Nat.cast_zero, cast_zero]
  | n + 1 => by rw [Nat.cast_succ, add_one, succ_to_nat, to_of_nat n]

@[simp, norm_cast]
theorem of_natCast {α} [AddMonoidWithOne α] (n : ℕ) : ((n : Num) : α) = n := by
  rw [← cast_to_nat, to_of_nat]

@[norm_cast]
theorem of_nat_inj {m n : ℕ} : (m : Num) = n ↔ m = n :=
  ⟨fun h => Function.LeftInverse.injective to_of_nat h, congr_arg _⟩

-- The priority should be `high`er than `cast_to_nat`.
@[simp high, norm_cast]
theorem of_to_nat : ∀ n : Num, ((n : ℕ) : Num) = n :=
  of_to_nat'

@[norm_cast]
theorem dvd_to_nat (m n : Num) : (m : ℕ) ∣ n ↔ m ∣ n :=
  ⟨fun ⟨k, e⟩ => ⟨k, by rw [← of_to_nat n, e]; simp⟩, fun ⟨k, e⟩ => ⟨k, by simp [e, mul_to_nat]⟩⟩

end Num

namespace PosNum

variable {α : Type*}

open Num

-- The priority should be `high`er than `cast_to_nat`.
@[simp high, norm_cast]
theorem of_to_nat : ∀ n : PosNum, ((n : ℕ) : Num) = Num.pos n :=
  of_to_nat'

@[norm_cast]
theorem to_nat_inj {m n : PosNum} : (m : ℕ) = n ↔ m = n :=
  ⟨fun h => Num.pos.inj <| by rw [← PosNum.of_to_nat, ← PosNum.of_to_nat, h], congr_arg _⟩

theorem pred'_to_nat : ∀ n, (pred' n : ℕ) = Nat.pred n
  | 1 => rfl
  | bit0 n =>
    have : Nat.succ ↑(pred' n) = ↑n := by
      rw [pred'_to_nat n, Nat.succ_pred_eq_of_pos (to_nat_pos n)]
    match (motive :=
        ∀ k : Num, Nat.succ ↑k = ↑n → ↑(Num.casesOn k 1 bit1 : PosNum) = Nat.pred (n + n))
      pred' n, this with
    | 0, (h : ((1 : Num) : ℕ) = n) => by rw [← to_nat_inj.1 h]; rfl
    | Num.pos p, (h : Nat.succ ↑p = n) => by rw [← h]; exact (Nat.succ_add p p).symm
  | bit1 _ => rfl

@[simp]
theorem pred'_succ' (n) : pred' (succ' n) = n :=
  Num.to_nat_inj.1 <| by rw [pred'_to_nat, succ'_to_nat, Nat.add_one, Nat.pred_succ]

@[simp]
theorem succ'_pred' (n) : succ' (pred' n) = n :=
  to_nat_inj.1 <| by
    rw [succ'_to_nat, pred'_to_nat, Nat.add_one, Nat.succ_pred_eq_of_pos (to_nat_pos _)]

instance dvd : Dvd PosNum :=
  ⟨fun m n => pos m ∣ pos n⟩

@[norm_cast]
theorem dvd_to_nat {m n : PosNum} : (m : ℕ) ∣ n ↔ m ∣ n :=
  Num.dvd_to_nat (pos m) (pos n)

theorem size_to_nat : ∀ n, (size n : ℕ) = Nat.size n
  | 1 => Nat.size_one.symm
  | bit0 n => by
      rw [size, succ_to_nat, size_to_nat n, cast_bit0, ← two_mul, ← Nat.bit_false_apply,
        Nat.size_bit]
      have := to_nat_pos n
      dsimp [Nat.bit]; cutsat
  | bit1 n => by
      rw [size, succ_to_nat, size_to_nat n, cast_bit1, ← two_mul, ← Nat.bit_true_apply,
        Nat.size_bit]
      dsimp [Nat.bit]; cutsat

theorem size_eq_natSize : ∀ n, (size n : ℕ) = natSize n
  | 1 => rfl
  | bit0 n => by rw [size, succ_to_nat, natSize, size_eq_natSize n]
  | bit1 n => by rw [size, succ_to_nat, natSize, size_eq_natSize n]

theorem natSize_to_nat (n) : natSize n = Nat.size n := by rw [← size_eq_natSize, size_to_nat]

theorem natSize_pos (n) : 0 < natSize n := by cases n <;> apply Nat.succ_pos

/-- This tactic tries to turn an (in)equality about `PosNum`s to one about `Nat`s by rewriting.
```lean
example (n : PosNum) (m : PosNum) : n ≤ n + m := by
  transfer_rw
  exact Nat.le_add_right _ _
```
-/
scoped macro (name := transfer_rw) "transfer_rw" : tactic => `(tactic|
    (repeat first | rw [← to_nat_inj] | rw [← lt_to_nat] | rw [← le_to_nat]
     repeat first | rw [add_to_nat] | rw [mul_to_nat] | rw [cast_one] | rw [cast_zero]))

/--
This tactic tries to prove (in)equalities about `PosNum`s by transferring them to the `Nat` world
and then trying to call `simp`.
```lean
example (n : PosNum) (m : PosNum) : n ≤ n + m := by transfer
```
-/
scoped macro (name := transfer) "transfer" : tactic => `(tactic|
    (intros; transfer_rw; try simp [add_comm, add_left_comm, mul_comm, mul_left_comm]))

instance addCommSemigroup : AddCommSemigroup PosNum where
  add_assoc := by transfer
  add_comm := by transfer

instance commMonoid : CommMonoid PosNum where
  npow := @npowRec PosNum ⟨1⟩ ⟨(· * ·)⟩
  mul_assoc := by transfer
  one_mul := by transfer
  mul_one := by transfer
  mul_comm := by transfer

instance distrib : Distrib PosNum where
  left_distrib := by transfer; simp [mul_add]
  right_distrib := by transfer; simp [mul_add, mul_comm]

instance linearOrder : LinearOrder PosNum where
  lt_iff_le_not_ge := by
    intro a b
    transfer_rw
    apply lt_iff_le_not_ge
  le_refl := by transfer
  le_trans := by
    intro a b c
    transfer_rw
    apply le_trans
  le_antisymm := by
    intro a b
    transfer_rw
    apply le_antisymm
  le_total := by
    intro a b
    transfer_rw
    apply le_total
  toDecidableLT := by infer_instance
  toDecidableLE := by infer_instance
  toDecidableEq := by infer_instance

@[simp]
theorem cast_to_num (n : PosNum) : ↑n = Num.pos n := by rw [← cast_to_nat, ← of_to_nat n]

@[simp, norm_cast]
theorem bit_to_nat (b n) : (bit b n : ℕ) = Nat.bit b n := by cases b <;> simp [bit, two_mul]

@[simp, norm_cast]
theorem cast_add [AddMonoidWithOne α] (m n) : ((m + n : PosNum) : α) = m + n := by
  rw [← cast_to_nat, add_to_nat, Nat.cast_add, cast_to_nat, cast_to_nat]

@[simp 500, norm_cast]
theorem cast_succ [AddMonoidWithOne α] (n : PosNum) : (succ n : α) = n + 1 := by
  rw [← add_one, cast_add, cast_one]

@[simp, norm_cast]
theorem cast_inj [AddMonoidWithOne α] [CharZero α] {m n : PosNum} : (m : α) = n ↔ m = n := by
  rw [← cast_to_nat m, ← cast_to_nat n, Nat.cast_inj, to_nat_inj]

@[simp]
theorem one_le_cast [Semiring α] [PartialOrder α] [IsStrictOrderedRing α] (n : PosNum) :
    (1 : α) ≤ n := by
  rw [← cast_to_nat, ← Nat.cast_one, Nat.cast_le (α := α)]; apply to_nat_pos

@[simp]
theorem cast_pos [Semiring α] [PartialOrder α] [IsStrictOrderedRing α] (n : PosNum) : 0 < (n : α) :=
  lt_of_lt_of_le zero_lt_one (one_le_cast n)

@[simp, norm_cast]
theorem cast_mul [NonAssocSemiring α] (m n) : ((m * n : PosNum) : α) = m * n := by
  rw [← cast_to_nat, mul_to_nat, Nat.cast_mul, cast_to_nat, cast_to_nat]

@[simp]
theorem cmp_eq (m n) : cmp m n = Ordering.eq ↔ m = n := by
  have := cmp_to_nat m n
  -- Porting note: `cases` didn't rewrite at `this`, so `revert` & `intro` are required.
  revert this; cases cmp m n <;> intro this <;> simp at this ⊢ <;> try { exact this } <;>
    simp [show m ≠ n from fun e => by rw [e] at this; exact lt_irrefl _ this]

@[simp, norm_cast]
theorem cast_lt [Semiring α] [PartialOrder α] [IsStrictOrderedRing α] {m n : PosNum} :
    (m : α) < n ↔ m < n := by
  rw [← cast_to_nat m, ← cast_to_nat n, Nat.cast_lt (α := α), lt_to_nat]

@[simp, norm_cast]
theorem cast_le [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] {m n : PosNum} :
    (m : α) ≤ n ↔ m ≤ n := by
  rw [← not_lt]; exact not_congr cast_lt

end PosNum

namespace Num

variable {α : Type*}

open PosNum

theorem bit_to_nat (b n) : (bit b n : ℕ) = Nat.bit b n := by
  cases b <;> cases n <;> simp [bit, two_mul] <;> rfl

theorem cast_succ' [AddMonoidWithOne α] (n) : (succ' n : α) = n + 1 := by
  rw [← PosNum.cast_to_nat, succ'_to_nat, Nat.cast_add_one, cast_to_nat]

theorem cast_succ [AddMonoidWithOne α] (n) : (succ n : α) = n + 1 :=
  cast_succ' n

@[simp, norm_cast]
theorem cast_add [AddMonoidWithOne α] (m n) : ((m + n : Num) : α) = m + n := by
  rw [← cast_to_nat, add_to_nat, Nat.cast_add, cast_to_nat, cast_to_nat]

@[simp, norm_cast]
theorem cast_bit0 [NonAssocSemiring α] (n : Num) : (n.bit0 : α) = 2 * (n : α) := by
  rw [← bit0_of_bit0, two_mul, cast_add]

@[simp, norm_cast]
theorem cast_bit1 [NonAssocSemiring α] (n : Num) : (n.bit1 : α) = 2 * (n : α) + 1 := by
  rw [← bit1_of_bit1, bit0_of_bit0, cast_add, cast_bit0]; rfl

@[simp, norm_cast]
theorem cast_mul [NonAssocSemiring α] : ∀ m n, ((m * n : Num) : α) = m * n
  | 0, 0 => (zero_mul _).symm
  | 0, pos _q => (zero_mul _).symm
  | pos _p, 0 => (mul_zero _).symm
  | pos _p, pos _q => PosNum.cast_mul _ _

theorem size_to_nat : ∀ n, (size n : ℕ) = Nat.size n
  | 0 => Nat.size_zero.symm
  | pos p => p.size_to_nat

theorem size_eq_natSize : ∀ n, (size n : ℕ) = natSize n
  | 0 => rfl
  | pos p => p.size_eq_natSize

theorem natSize_to_nat (n) : natSize n = Nat.size n := by rw [← size_eq_natSize, size_to_nat]

@[simp 999]
theorem ofNat'_eq : ∀ n, Num.ofNat' n = n :=
  Nat.binaryRec (by simp) fun b n IH => by tauto

theorem zneg_toZNum (n : Num) : -n.toZNum = n.toZNumNeg := by cases n <;> rfl

theorem zneg_toZNumNeg (n : Num) : -n.toZNumNeg = n.toZNum := by cases n <;> rfl

theorem toZNum_inj {m n : Num} : m.toZNum = n.toZNum ↔ m = n :=
  ⟨fun h => by cases m <;> cases n <;> cases h <;> rfl, congr_arg _⟩

@[simp]
theorem cast_toZNum [Zero α] [One α] [Add α] [Neg α] : ∀ n : Num, (n.toZNum : α) = n
  | 0 => rfl
  | Num.pos _p => rfl

@[simp]
theorem cast_toZNumNeg [SubtractionMonoid α] [One α] : ∀ n : Num, (n.toZNumNeg : α) = -n
  | 0 => neg_zero.symm
  | Num.pos _p => rfl

@[simp]
theorem add_toZNum (m n : Num) : Num.toZNum (m + n) = m.toZNum + n.toZNum := by
  cases m <;> cases n <;> rfl

end Num

namespace PosNum

open Num

theorem pred_to_nat {n : PosNum} (h : 1 < n) : (pred n : ℕ) = Nat.pred n := by
  unfold pred
  cases e : pred' n
  · have : (1 : ℕ) ≤ Nat.pred n := Nat.pred_le_pred ((@cast_lt ℕ _ _ _).2 h)
    rw [← pred'_to_nat, e] at this
    exact absurd this (by decide)
  · rw [← pred'_to_nat, e]
    rfl

theorem sub'_one (a : PosNum) : sub' a 1 = (pred' a).toZNum := by cases a <;> rfl

theorem one_sub' (a : PosNum) : sub' 1 a = (pred' a).toZNumNeg := by cases a <;> rfl

theorem lt_iff_cmp {m n} : m < n ↔ cmp m n = Ordering.lt :=
  Iff.rfl

theorem le_iff_cmp {m n} : m ≤ n ↔ cmp m n ≠ Ordering.gt :=
  not_congr <| lt_iff_cmp.trans <| by rw [← cmp_swap]; cases cmp m n <;> decide

end PosNum

namespace Num

variable {α : Type*}

open PosNum

theorem pred_to_nat : ∀ n : Num, (pred n : ℕ) = Nat.pred n
  | 0 => rfl
  | pos p => by rw [pred, PosNum.pred'_to_nat]; rfl

theorem ppred_to_nat : ∀ n : Num, (↑) <$> ppred n = Nat.ppred n
  | 0 => rfl
  | pos p => by
    rw [ppred, Option.map_eq_map, Option.map_some, Nat.ppred_eq_some.2]
    rw [PosNum.pred'_to_nat, Nat.succ_pred_eq_of_pos (PosNum.to_nat_pos _)]
    rfl

theorem cmp_swap (m n) : (cmp m n).swap = cmp n m := by
  cases m <;> cases n <;> try { rfl }; apply PosNum.cmp_swap

theorem cmp_eq (m n) : cmp m n = Ordering.eq ↔ m = n := by
  have := cmp_to_nat m n
  -- Porting note: `cases` didn't rewrite at `this`, so `revert` & `intro` are required.
  revert this; cases cmp m n <;> intro this <;> simp at this ⊢ <;> try { exact this } <;>
    simp [show m ≠ n from fun e => by rw [e] at this; exact lt_irrefl _ this]

@[simp, norm_cast]
theorem cast_lt [Semiring α] [PartialOrder α] [IsStrictOrderedRing α] {m n : Num} :
    (m : α) < n ↔ m < n := by
  rw [← cast_to_nat m, ← cast_to_nat n, Nat.cast_lt (α := α), lt_to_nat]

@[simp, norm_cast]
theorem cast_le [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] {m n : Num} :
    (m : α) ≤ n ↔ m ≤ n := by
  rw [← not_lt]; exact not_congr cast_lt

@[simp, norm_cast]
theorem cast_inj [Semiring α] [PartialOrder α] [IsStrictOrderedRing α] {m n : Num} :
    (m : α) = n ↔ m = n := by
  rw [← cast_to_nat m, ← cast_to_nat n, Nat.cast_inj, to_nat_inj]

theorem lt_iff_cmp {m n} : m < n ↔ cmp m n = Ordering.lt :=
  Iff.rfl

theorem le_iff_cmp {m n} : m ≤ n ↔ cmp m n ≠ Ordering.gt :=
  not_congr <| lt_iff_cmp.trans <| by rw [← cmp_swap]; cases cmp m n <;> decide

theorem castNum_eq_bitwise {f : Num → Num → Num} {g : Bool → Bool → Bool}
    (p : PosNum → PosNum → Num)
    (gff : g false false = false) (f00 : f 0 0 = 0)
    (f0n : ∀ n, f 0 (pos n) = cond (g false true) (pos n) 0)
    (fn0 : ∀ n, f (pos n) 0 = cond (g true false) (pos n) 0)
    (fnn : ∀ m n, f (pos m) (pos n) = p m n) (p11 : p 1 1 = cond (g true true) 1 0)
    (p1b : ∀ b n, p 1 (PosNum.bit b n) = bit (g true b) (cond (g false true) (pos n) 0))
    (pb1 : ∀ a m, p (PosNum.bit a m) 1 = bit (g a true) (cond (g true false) (pos m) 0))
    (pbb : ∀ a b m n, p (PosNum.bit a m) (PosNum.bit b n) = bit (g a b) (p m n)) :
    ∀ m n : Num, (f m n : ℕ) = Nat.bitwise g m n := by
  intro m n
  obtain - | m := m <;> obtain - | n := n <;>
      try simp only [show zero = 0 from rfl, show ((0 : Num) : ℕ) = 0 from rfl]
  · rw [f00, Nat.bitwise_zero]; rfl
  · rw [f0n, Nat.bitwise_zero_left]
    cases g false true <;> rfl
  · rw [fn0, Nat.bitwise_zero_right]
    cases g true false <;> rfl
  · rw [fnn]
    have this b (n : PosNum) : (cond b (↑n) 0 : ℕ) = ↑(cond b (pos n) 0 : Num) := by
      cases b <;> rfl
    have this' b (n : PosNum) : ↑(pos (PosNum.bit b n)) = Nat.bit b ↑n := by
      cases b <;> simp
    induction m generalizing n with | one => ?_ | bit1 m IH => ?_ | bit0 m IH => ?_ <;>
    obtain - | n | n := n
    any_goals simp only [show one = 1 from rfl, show pos 1 = 1 from rfl,
      show PosNum.bit0 = PosNum.bit false from rfl, show PosNum.bit1 = PosNum.bit true from rfl,
      show ((1 : Num) : ℕ) = Nat.bit true 0 from rfl]
    all_goals
      repeat rw [this']
      rw [Nat.bitwise_bit gff]
    any_goals rw [Nat.bitwise_zero, p11]; cases g true true <;> rfl
    any_goals rw [Nat.bitwise_zero_left, ← Bool.cond_eq_ite, this, ← bit_to_nat, p1b]
    any_goals rw [Nat.bitwise_zero_right, ← Bool.cond_eq_ite, this, ← bit_to_nat, pb1]
    all_goals
      rw [← show ∀ n : PosNum, ↑(p m n) = Nat.bitwise g ↑m ↑n from IH]
      rw [← bit_to_nat, pbb]

@[simp, norm_cast]
theorem castNum_or : ∀ m n : Num, ↑(m ||| n) = (↑m ||| ↑n : ℕ) := by
  apply castNum_eq_bitwise fun x y => pos (PosNum.lor x y) <;>
    (try rintro (_ | _)) <;> (try rintro (_ | _)) <;> intros <;> rfl

@[simp, norm_cast]
theorem castNum_and : ∀ m n : Num, ↑(m &&& n) = (↑m &&& ↑n : ℕ) := by
  apply castNum_eq_bitwise PosNum.land <;> intros <;> (try cases_type* Bool) <;> rfl

@[simp, norm_cast]
theorem castNum_ldiff : ∀ m n : Num, (ldiff m n : ℕ) = Nat.ldiff m n := by
  apply castNum_eq_bitwise PosNum.ldiff <;> intros <;> (try cases_type* Bool) <;> rfl

@[simp, norm_cast]
theorem castNum_xor : ∀ m n : Num, ↑(m ^^^ n) = (↑m ^^^ ↑n : ℕ) := by
  apply castNum_eq_bitwise PosNum.lxor <;> intros <;> (try cases_type* Bool) <;> rfl

@[simp, norm_cast]
theorem castNum_shiftLeft (m : Num) (n : Nat) : ↑(m <<< n) = (m : ℕ) <<< (n : ℕ) := by
  cases m <;> dsimp only [← shiftl_eq_shiftLeft, shiftl]
  · symm
    apply Nat.zero_shiftLeft
  simp only [cast_pos]
  induction n with
  | zero => rfl
  | succ n IH =>
    simp [PosNum.shiftl_succ_eq_bit0_shiftl, Nat.shiftLeft_succ, IH, mul_comm,
      -shiftl_eq_shiftLeft, -PosNum.shiftl_eq_shiftLeft, mul_two]

@[simp, norm_cast]
theorem castNum_shiftRight (m : Num) (n : Nat) : ↑(m >>> n) = (m : ℕ) >>> (n : ℕ) := by
  obtain - | m := m <;> dsimp only [← shiftr_eq_shiftRight, shiftr]
  · symm
    apply Nat.zero_shiftRight
  induction n generalizing m with
  | zero => cases m <;> rfl
  | succ n IH => ?_
  have hdiv2 : ∀ m, Nat.div2 (m + m) = m := by intro; rw [Nat.div2_val]; omega
  obtain - | m | m := m <;> dsimp only [PosNum.shiftr, ← PosNum.shiftr_eq_shiftRight]
  · rw [Nat.shiftRight_eq_div_pow]
    symm
    apply Nat.div_eq_of_lt
    simp
  · trans
    · apply IH
    change Nat.shiftRight m n = Nat.shiftRight (m + m + 1) (n + 1)
    rw [add_comm n 1, @Nat.shiftRight_eq _ (1 + n), Nat.shiftRight_add]
    apply congr_arg fun x => Nat.shiftRight x n
    simp [-add_assoc, Nat.shiftRight_succ, Nat.shiftRight_zero, ← Nat.div2_val, hdiv2]
  · trans
    · apply IH
    change Nat.shiftRight m n = Nat.shiftRight (m + m) (n + 1)
    rw [add_comm n 1, @Nat.shiftRight_eq _ (1 + n), Nat.shiftRight_add]
    apply congr_arg fun x => Nat.shiftRight x n
    simp [-add_assoc, Nat.shiftRight_succ, Nat.shiftRight_zero, ← Nat.div2_val, hdiv2]

@[simp]
theorem castNum_testBit (m n) : testBit m n = Nat.testBit m n := by
  cases m with dsimp only [testBit]
  | zero =>
    rw [show (Num.zero : Nat) = 0 from rfl, Nat.zero_testBit]
  | pos m =>
    rw [cast_pos]
    induction n generalizing m <;> obtain - | m | m := m
        <;> simp only [PosNum.testBit]
    · rfl
    · rw [PosNum.cast_bit1, ← two_mul, ← congr_fun Nat.bit_true, Nat.testBit_bit_zero]
    · rw [PosNum.cast_bit0, ← two_mul, ← congr_fun Nat.bit_false, Nat.testBit_bit_zero]
    · simp [Nat.testBit_add_one]
    case succ.bit1 n IH =>
      rw [PosNum.cast_bit1, ← two_mul, ← congr_fun Nat.bit_true, Nat.testBit_bit_succ, IH]
    case succ.bit0 n IH =>
      rw [PosNum.cast_bit0, ← two_mul, ← congr_fun Nat.bit_false, Nat.testBit_bit_succ, IH]

end Num

namespace Int

/-- Cast a `SNum` to the corresponding integer. -/
def ofSnum : SNum → ℤ :=
  SNum.rec' (fun a => cond a (-1) 0) fun a _p IH => cond a (2 * IH + 1) (2 * IH)

instance snumCoe : Coe SNum ℤ :=
  ⟨ofSnum⟩

end Int

instance SNum.lt : LT SNum :=
  ⟨fun a b => (a : ℤ) < b⟩

instance SNum.le : LE SNum :=
  ⟨fun a b => (a : ℤ) ≤ b⟩
