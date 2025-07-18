/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Algebra.Order.Ring.Cast
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Num.Lemmas

/-!
# Properties of the `ZNum` representation of integers

This file was split from `Mathlib/Data/Num/Lemmas.lean` to keep the former under 1500 lines.
-/

open Int

attribute [local simp] add_assoc

namespace ZNum

variable {α : Type*}

open PosNum

@[simp, norm_cast]
theorem cast_zero [Zero α] [One α] [Add α] [Neg α] : ((0 : ZNum) : α) = 0 :=
  rfl

@[simp]
theorem cast_zero' [Zero α] [One α] [Add α] [Neg α] : (ZNum.zero : α) = 0 :=
  rfl

@[simp, norm_cast]
theorem cast_one [Zero α] [One α] [Add α] [Neg α] : ((1 : ZNum) : α) = 1 :=
  rfl

@[simp]
theorem cast_pos [Zero α] [One α] [Add α] [Neg α] (n : PosNum) : (pos n : α) = n :=
  rfl

@[simp]
theorem cast_neg [Zero α] [One α] [Add α] [Neg α] (n : PosNum) : (neg n : α) = -n :=
  rfl

@[simp, norm_cast]
theorem cast_zneg [SubtractionMonoid α] [One α] : ∀ n, ((-n : ZNum) : α) = -n
  | 0 => neg_zero.symm
  | pos _p => rfl
  | neg _p => (neg_neg _).symm

theorem neg_zero : (-0 : ZNum) = 0 :=
  rfl

theorem zneg_pos (n : PosNum) : -pos n = neg n :=
  rfl

theorem zneg_neg (n : PosNum) : -neg n = pos n :=
  rfl

theorem zneg_zneg (n : ZNum) : - -n = n := by cases n <;> rfl

theorem zneg_bit1 (n : ZNum) : -n.bit1 = (-n).bitm1 := by cases n <;> rfl

theorem zneg_bitm1 (n : ZNum) : -n.bitm1 = (-n).bit1 := by cases n <;> rfl

theorem zneg_succ (n : ZNum) : -n.succ = (-n).pred := by
  cases n <;> try { rfl }; rw [succ, Num.zneg_toZNumNeg]; rfl

theorem zneg_pred (n : ZNum) : -n.pred = (-n).succ := by
  rw [← zneg_zneg (succ (-n)), zneg_succ, zneg_zneg]

@[simp]
theorem abs_to_nat : ∀ n, (abs n : ℕ) = Int.natAbs n
  | 0 => rfl
  | pos p => congr_arg Int.natAbs p.to_nat_to_int
  | neg p => show Int.natAbs ((p : ℕ) : ℤ) = Int.natAbs (-p) by rw [p.to_nat_to_int, Int.natAbs_neg]

@[simp]
theorem abs_toZNum : ∀ n : Num, abs n.toZNum = n
  | 0 => rfl
  | Num.pos _p => rfl

@[simp, norm_cast]
theorem cast_to_int [AddGroupWithOne α] : ∀ n : ZNum, ((n : ℤ) : α) = n
  | 0 => by rw [cast_zero, cast_zero, Int.cast_zero]
  | pos p => by rw [cast_pos, cast_pos, PosNum.cast_to_int]
  | neg p => by rw [cast_neg, cast_neg, Int.cast_neg, PosNum.cast_to_int]

theorem bit0_of_bit0 : ∀ n : ZNum, n + n = n.bit0
  | 0 => rfl
  | pos a => congr_arg pos a.bit0_of_bit0
  | neg a => congr_arg neg a.bit0_of_bit0

theorem bit1_of_bit1 : ∀ n : ZNum, n + n + 1 = n.bit1
  | 0 => rfl
  | pos a => congr_arg pos a.bit1_of_bit1
  | neg a => show PosNum.sub' 1 (a + a) = _ by rw [PosNum.one_sub', a.bit0_of_bit0]; rfl

@[simp, norm_cast]
theorem cast_bit0 [AddGroupWithOne α] : ∀ n : ZNum, (n.bit0 : α) = (n : α) + n
  | 0 => (add_zero _).symm
  | pos p => by rw [ZNum.bit0, cast_pos, cast_pos]; rfl
  | neg p => by
    rw [ZNum.bit0, cast_neg, cast_neg, PosNum.cast_bit0, neg_add_rev]

@[simp, norm_cast]
theorem cast_bit1 [AddGroupWithOne α] : ∀ n : ZNum, (n.bit1 : α) = ((n : α) + n) + 1
  | 0 => by simp [ZNum.bit1]
  | pos p => by rw [ZNum.bit1, cast_pos, cast_pos]; rfl
  | neg p => by
    rw [ZNum.bit1, cast_neg, cast_neg]
    rcases e : pred' p with - | a <;>
      have ep : p = _ := (succ'_pred' p).symm.trans (congr_arg Num.succ' e)
    · conv at ep => change p = 1
      subst p
      simp
    · dsimp only [Num.succ'] at ep
      subst p
      have : (↑(-↑a : ℤ) : α) = -1 + ↑(-↑a + 1 : ℤ) := by simp [add_comm (- ↑a : ℤ) 1]
      simpa using this

@[simp]
theorem cast_bitm1 [AddGroupWithOne α] (n : ZNum) : (n.bitm1 : α) = (n : α) + n - 1 := by
  conv =>
    lhs
    rw [← zneg_zneg n]
  rw [← zneg_bit1, cast_zneg, cast_bit1]
  have : ((-1 + n + n : ℤ) : α) = (n + n + -1 : ℤ) := by simp [add_comm]
  simpa [sub_eq_add_neg] using this

theorem add_zero (n : ZNum) : n + 0 = n := by cases n <;> rfl

theorem zero_add (n : ZNum) : 0 + n = n := by cases n <;> rfl

theorem add_one : ∀ n : ZNum, n + 1 = succ n
  | 0 => rfl
  | pos p => congr_arg pos p.add_one
  | neg p => by cases p <;> rfl

end ZNum

namespace PosNum

variable {α : Type*}

theorem cast_to_znum : ∀ n : PosNum, (n : ZNum) = ZNum.pos n
  | 1 => rfl
  | bit0 p => by
      have := congr_arg ZNum.bit0 (cast_to_znum p)
      rwa [← ZNum.bit0_of_bit0] at this
  | bit1 p => by
      have := congr_arg ZNum.bit1 (cast_to_znum p)
      rwa [← ZNum.bit1_of_bit1] at this

theorem cast_sub' [AddGroupWithOne α] : ∀ m n : PosNum, (sub' m n : α) = m - n
  | a, 1 => by
    rw [sub'_one, Num.cast_toZNum, ← Num.cast_to_nat, pred'_to_nat, ← Nat.sub_one]
    simp
  | 1, b => by
    rw [one_sub', Num.cast_toZNumNeg, ← neg_sub, neg_inj, ← Num.cast_to_nat, pred'_to_nat,
        ← Nat.sub_one]
    simp
  | bit0 a, bit0 b => by
    rw [sub', ZNum.cast_bit0, cast_sub' a b]
    have : ((a + -b + (a + -b) : ℤ) : α) = a + a + (-b + -b) := by simp [add_left_comm]
    simpa [sub_eq_add_neg] using this
  | bit0 a, bit1 b => by
    rw [sub', ZNum.cast_bitm1, cast_sub' a b]
    have : ((-b + (a + (-b + -1)) : ℤ) : α) = (a + -1 + (-b + -b) : ℤ) := by
      simp [add_comm, add_left_comm]
    simpa [sub_eq_add_neg] using this
  | bit1 a, bit0 b => by
    rw [sub', ZNum.cast_bit1, cast_sub' a b]
    have : ((-b + (a + (-b + 1)) : ℤ) : α) = (a + 1 + (-b + -b) : ℤ) := by
      simp [add_comm, add_left_comm]
    simpa [sub_eq_add_neg] using this
  | bit1 a, bit1 b => by
    rw [sub', ZNum.cast_bit0, cast_sub' a b]
    have : ((-b + (a + -b) : ℤ) : α) = a + (-b + -b) := by simp [add_left_comm]
    simpa [sub_eq_add_neg] using this

theorem to_nat_eq_succ_pred (n : PosNum) : (n : ℕ) = n.pred' + 1 := by
  rw [← Num.succ'_to_nat, n.succ'_pred']

theorem to_int_eq_succ_pred (n : PosNum) : (n : ℤ) = (n.pred' : ℕ) + 1 := by
  rw [← n.to_nat_to_int, to_nat_eq_succ_pred]; rfl

end PosNum

namespace Num

variable {α : Type*}

@[simp]
theorem cast_sub' [AddGroupWithOne α] : ∀ m n : Num, (sub' m n : α) = m - n
  | 0, 0 => (sub_zero _).symm
  | pos _a, 0 => (sub_zero _).symm
  | 0, pos _b => (zero_sub _).symm
  | pos _a, pos _b => PosNum.cast_sub' _ _

theorem toZNum_succ : ∀ n : Num, n.succ.toZNum = n.toZNum.succ
  | 0 => rfl
  | pos _n => rfl

theorem toZNumNeg_succ : ∀ n : Num, n.succ.toZNumNeg = n.toZNumNeg.pred
  | 0 => rfl
  | pos _n => rfl

@[simp]
theorem pred_succ : ∀ n : ZNum, n.pred.succ = n
  | 0 => rfl
  | ZNum.neg p => show toZNumNeg (pos p).succ'.pred' = _ by rw [PosNum.pred'_succ']; rfl
  | ZNum.pos p => by rw [ZNum.pred, ← toZNum_succ, Num.succ, PosNum.succ'_pred', toZNum]

theorem succ_ofInt' : ∀ n, ZNum.ofInt' (n + 1) = ZNum.ofInt' n + 1
  | (n : ℕ) => by
    change ZNum.ofInt' (n + 1 : ℕ) = ZNum.ofInt' (n : ℕ) + 1
    dsimp only [ZNum.ofInt', ZNum.ofInt']
    rw [Num.ofNat'_succ, Num.add_one, toZNum_succ, ZNum.add_one]
  | -[0+1] => by
    change ZNum.ofInt' 0 = ZNum.ofInt' (-[0+1]) + 1
    dsimp only [ZNum.ofInt', ZNum.ofInt']
    rw [ofNat'_succ, ofNat'_zero]; rfl
  | -[(n + 1)+1] => by
    change ZNum.ofInt' -[n+1] = ZNum.ofInt' -[(n + 1)+1] + 1
    dsimp only [ZNum.ofInt', ZNum.ofInt']
    rw [@Num.ofNat'_succ (n + 1), Num.add_one, toZNumNeg_succ,
      @ofNat'_succ n, Num.add_one, ZNum.add_one, pred_succ]

theorem ofInt'_toZNum : ∀ n : ℕ, toZNum n = ZNum.ofInt' n
  | 0 => rfl
  | n + 1 => by
    rw [Nat.cast_succ, Num.add_one, toZNum_succ, ofInt'_toZNum n, Nat.cast_succ, succ_ofInt',
      ZNum.add_one]

theorem mem_ofZNum' : ∀ {m : Num} {n : ZNum}, m ∈ ofZNum' n ↔ n = toZNum m
  | 0, 0 => ⟨fun _ => rfl, fun _ => rfl⟩
  | pos _, 0 => ⟨nofun, nofun⟩
  | m, ZNum.pos p =>
    Option.some_inj.trans <| by cases m <;> constructor <;> intro h <;> try cases h <;> rfl
  | m, ZNum.neg p => ⟨nofun, fun h => by cases m <;> cases h⟩

theorem ofZNum'_toNat : ∀ n : ZNum, (↑) <$> ofZNum' n = Int.toNat? n
  | 0 => rfl
  | ZNum.pos p => show _ = Int.toNat? p by rw [← PosNum.to_nat_to_int p]; rfl
  | ZNum.neg p =>
    (congr_arg fun x => Int.toNat? (-x)) <|
      show ((p.pred' + 1 : ℕ) : ℤ) = p by rw [← succ'_to_nat]; simp

theorem ofZNum_toNat : ∀ n : ZNum, (ofZNum n : ℕ) = Int.toNat n
  | 0 => rfl
  | ZNum.pos p => show _ = Int.toNat p by rw [← PosNum.to_nat_to_int p]; rfl
  | ZNum.neg p =>
    (congr_arg fun x => Int.toNat (-x)) <|
      show ((p.pred' + 1 : ℕ) : ℤ) = p by rw [← succ'_to_nat]; simp

@[simp]
theorem cast_ofZNum [AddMonoidWithOne α] (n : ZNum) : (ofZNum n : α) = Int.toNat n := by
  rw [← cast_to_nat, ofZNum_toNat]

@[simp, norm_cast]
theorem sub_to_nat (m n) : ((m - n : Num) : ℕ) = m - n :=
  show (ofZNum _ : ℕ) = _ by
    rw [ofZNum_toNat, cast_sub', ← to_nat_to_int, ← to_nat_to_int, Int.toNat_sub]

end Num

namespace ZNum

variable {α : Type*}

@[simp, norm_cast]
theorem cast_add [AddGroupWithOne α] : ∀ m n, ((m + n : ZNum) : α) = m + n
  | 0, a => by cases a <;> exact (_root_.zero_add _).symm
  | b, 0 => by cases b <;> exact (_root_.add_zero _).symm
  | pos _, pos _ => PosNum.cast_add _ _
  | pos a, neg b => by simpa only [sub_eq_add_neg] using PosNum.cast_sub' (α := α) _ _
  | neg a, pos b =>
    have : (↑b + -↑a : α) = -↑a + ↑b := by
      rw [← PosNum.cast_to_int a, ← PosNum.cast_to_int b, ← Int.cast_neg, ← Int.cast_add (-a)]
      simp [add_comm]
    (PosNum.cast_sub' _ _).trans <| (sub_eq_add_neg _ _).trans this
  | neg a, neg b =>
    show -(↑(a + b) : α) = -a + -b by
      rw [PosNum.cast_add, neg_eq_iff_eq_neg, neg_add_rev, neg_neg, neg_neg,
          ← PosNum.cast_to_int a, ← PosNum.cast_to_int b, ← Int.cast_add, ← Int.cast_add, add_comm]

@[simp]
theorem cast_succ [AddGroupWithOne α] (n) : ((succ n : ZNum) : α) = n + 1 := by
  rw [← add_one, cast_add, cast_one]

@[simp, norm_cast]
theorem mul_to_int : ∀ m n, ((m * n : ZNum) : ℤ) = m * n
  | 0, a => by cases a <;> exact (zero_mul _).symm
  | b, 0 => by cases b <;> exact (mul_zero _).symm
  | pos a, pos b => PosNum.cast_mul a b
  | pos a, neg b => show -↑(a * b) = ↑a * -↑b by rw [PosNum.cast_mul, neg_mul_eq_mul_neg]
  | neg a, pos b => show -↑(a * b) = -↑a * ↑b by rw [PosNum.cast_mul, neg_mul_eq_neg_mul]
  | neg a, neg b => show ↑(a * b) = -↑a * -↑b by rw [PosNum.cast_mul, neg_mul_neg]

theorem cast_mul [NonAssocRing α] (m n) : ((m * n : ZNum) : α) = m * n := by
  rw [← cast_to_int, mul_to_int, Int.cast_mul, cast_to_int, cast_to_int]

theorem ofInt'_neg : ∀ n : ℤ, ofInt' (-n) = -ofInt' n
  | -[n+1] => show ofInt' (n + 1 : ℕ) = _ by simp only [ofInt', Num.zneg_toZNumNeg]
  | 0 => show Num.toZNum (Num.ofNat' 0) = -Num.toZNum (Num.ofNat' 0) by rw [Num.ofNat'_zero]; rfl
  | (n + 1 : ℕ) => show Num.toZNumNeg _ = -Num.toZNum _ by rw [Num.zneg_toZNum]

theorem of_to_int' : ∀ n : ZNum, ZNum.ofInt' n = n
  | 0 => by
    dsimp [ofInt', cast_zero]
    simp only [Num.ofNat'_zero, Num.toZNum]
  | pos a => by rw [cast_pos, ← PosNum.cast_to_nat, ← Num.ofInt'_toZNum, PosNum.of_to_nat]; rfl
  | neg a => by
    rw [cast_neg, ofInt'_neg, ← PosNum.cast_to_nat, ← Num.ofInt'_toZNum, PosNum.of_to_nat]; rfl

theorem to_int_inj {m n : ZNum} : (m : ℤ) = n ↔ m = n :=
  ⟨fun h => Function.LeftInverse.injective of_to_int' h, congr_arg _⟩

theorem cmp_to_int : ∀ m n, (Ordering.casesOn (cmp m n) ((m : ℤ) < n) (m = n) ((n : ℤ) < m) : Prop)
  | 0, 0 => rfl
  | pos a, pos b => by
    have := PosNum.cmp_to_nat a b; revert this; dsimp [cmp]
    cases PosNum.cmp a b <;> [simp; exact congr_arg pos; simp]
  | neg a, neg b => by
    have := PosNum.cmp_to_nat b a; revert this; dsimp [cmp]
    cases PosNum.cmp b a <;> [simp; simp +contextual; simp]
  | pos _, 0 => PosNum.cast_pos _
  | pos _, neg _ => lt_trans (neg_lt_zero.2 <| PosNum.cast_pos _) (PosNum.cast_pos _)
  | 0, neg _ => neg_lt_zero.2 <| PosNum.cast_pos _
  | neg _, 0 => neg_lt_zero.2 <| PosNum.cast_pos _
  | neg _, pos _ => lt_trans (neg_lt_zero.2 <| PosNum.cast_pos _) (PosNum.cast_pos _)
  | 0, pos _ => PosNum.cast_pos _

@[norm_cast]
theorem lt_to_int {m n : ZNum} : (m : ℤ) < n ↔ m < n :=
  show (m : ℤ) < n ↔ cmp m n = Ordering.lt from
    match cmp m n, cmp_to_int m n with
    | Ordering.lt, h => by simp only at h; simp [h]
    | Ordering.eq, h => by simp only at h; simp [h]
    | Ordering.gt, h => by simp [not_lt_of_gt h]

theorem le_to_int {m n : ZNum} : (m : ℤ) ≤ n ↔ m ≤ n := by
  rw [← not_lt]; exact not_congr lt_to_int

@[simp, norm_cast]
theorem cast_lt [Ring α] [PartialOrder α] [IsStrictOrderedRing α] {m n : ZNum} :
    (m : α) < n ↔ m < n := by
  rw [← cast_to_int m, ← cast_to_int n, Int.cast_lt, lt_to_int]

@[simp, norm_cast]
theorem cast_le [Ring α] [LinearOrder α] [IsStrictOrderedRing α] {m n : ZNum} :
    (m : α) ≤ n ↔ m ≤ n := by
  rw [← not_lt]; exact not_congr cast_lt

@[simp, norm_cast]
theorem cast_inj [Ring α] [PartialOrder α] [IsStrictOrderedRing α] {m n : ZNum} :
    (m : α) = n ↔ m = n := by
  rw [← cast_to_int m, ← cast_to_int n, Int.cast_inj (α := α), to_int_inj]

/-- This tactic tries to turn an (in)equality about `ZNum`s to one about `Int`s by rewriting.
```lean
example (n : ZNum) (m : ZNum) : n ≤ n + m * m := by
  transfer_rw
  exact le_add_of_nonneg_right (mul_self_nonneg _)
```
-/
scoped macro (name := transfer_rw) "transfer_rw" : tactic => `(tactic|
    (repeat first | rw [← to_int_inj] | rw [← lt_to_int] | rw [← le_to_int]
     repeat first | rw [cast_add] | rw [mul_to_int] | rw [cast_one] | rw [cast_zero]))

/--
This tactic tries to prove (in)equalities about `ZNum`s by transferring them to the `Int` world and
then trying to call `simp`.
```lean
example (n : ZNum) (m : ZNum) : n ≤ n + m * m := by
  transfer
  exact mul_self_nonneg _
```
-/
scoped macro (name := transfer) "transfer" : tactic => `(tactic|
    (intros; transfer_rw; try simp [add_comm, add_left_comm, mul_comm, mul_left_comm]))

instance linearOrder : LinearOrder ZNum where
  lt := (· < ·)
  lt_iff_le_not_ge := by
    intro a b
    transfer_rw
    apply lt_iff_le_not_ge
  le := (· ≤ ·)
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
  -- This is relying on an automatically generated instance name, generated in a `deriving` handler.
  -- See https://github.com/leanprover/lean4/issues/2343
  toDecidableEq := instDecidableEqZNum
  toDecidableLE := ZNum.decidableLE
  toDecidableLT := ZNum.decidableLT

instance addMonoid : AddMonoid ZNum where
  add := (· + ·)
  add_assoc := by transfer
  zero := 0
  zero_add := zero_add
  add_zero := add_zero
  nsmul := nsmulRec

instance addCommGroup : AddCommGroup ZNum :=
  { ZNum.addMonoid with
    add_comm := by transfer
    neg := Neg.neg
    zsmul := zsmulRec
    neg_add_cancel := by transfer }

instance addMonoidWithOne : AddMonoidWithOne ZNum :=
  { ZNum.addMonoid with
    one := 1
    natCast := fun n => ZNum.ofInt' n
    natCast_zero := show (Num.ofNat' 0).toZNum = 0 by rw [Num.ofNat'_zero]; rfl
    natCast_succ := fun n =>
      show (Num.ofNat' (n + 1)).toZNum = (Num.ofNat' n).toZNum + 1 by
        rw [Num.ofNat'_succ, Num.add_one, Num.toZNum_succ, ZNum.add_one] }

-- The next theorems are declared outside of the instance to prevent timeouts.

private theorem mul_comm : ∀ (a b : ZNum), a * b = b * a := by transfer

private theorem add_le_add_left : ∀ (a b : ZNum), a ≤ b → ∀ (c : ZNum), c + a ≤ c + b := by
  intro a b h c
  revert h
  transfer_rw
  exact fun h => _root_.add_le_add_left h c

instance commRing : CommRing ZNum :=
  { ZNum.addCommGroup, ZNum.addMonoidWithOne with
    mul := (· * ·)
    mul_assoc a b c := by transfer
    zero_mul := by transfer
    mul_zero := by transfer
    one_mul := by transfer
    mul_one := by transfer
    left_distrib := by
      transfer
      simp [mul_add]
    right_distrib := by
      transfer
      simp [mul_add, _root_.mul_comm]
    mul_comm := mul_comm }

instance nontrivial : Nontrivial ZNum :=
  { exists_pair_ne := ⟨0, 1, by decide⟩ }

instance zeroLEOneClass : ZeroLEOneClass ZNum :=
  { zero_le_one := by decide }

instance isOrderedAddMonoid : IsOrderedAddMonoid ZNum :=
  { add_le_add_left := add_le_add_left }

instance isStrictOrderedRing : IsStrictOrderedRing ZNum :=
  .of_mul_pos fun a b ↦ by
    transfer_rw
    apply mul_pos

@[simp, norm_cast]
theorem cast_sub [AddCommGroupWithOne α] (m n) : ((m - n : ZNum) : α) = m - n := by
  simp [sub_eq_neg_add]

@[norm_cast]
theorem neg_of_int : ∀ n, ((-n : ℤ) : ZNum) = -n
  | (_ + 1 : ℕ) => rfl
  | 0 => by rw [Int.cast_neg]
  | -[_+1] => (zneg_zneg _).symm

@[simp]
theorem ofInt'_eq : ∀ n : ℤ, ZNum.ofInt' n = n
  | (n : ℕ) => rfl
  | -[n+1] => by
    change Num.toZNumNeg (n + 1 : ℕ) = -(n + 1 : ℕ)
    rw [← neg_inj, neg_neg, Nat.cast_succ, Num.add_one, Num.zneg_toZNumNeg, Num.toZNum_succ,
      Nat.cast_succ, ZNum.add_one]
    rfl

@[simp]
theorem of_nat_toZNum (n : ℕ) : Num.toZNum n = n :=
  rfl

-- The priority should be `high`er than `cast_to_int`.
@[simp high, norm_cast]
theorem of_to_int (n : ZNum) : ((n : ℤ) : ZNum) = n := by rw [← ofInt'_eq, of_to_int']

theorem to_of_int (n : ℤ) : ((n : ZNum) : ℤ) = n :=
  Int.inductionOn' n 0 (by simp) (by simp) (by simp)

@[simp]
theorem of_nat_toZNumNeg (n : ℕ) : Num.toZNumNeg n = -n := by rw [← of_nat_toZNum, Num.zneg_toZNum]

@[simp, norm_cast]
theorem of_intCast [AddGroupWithOne α] (n : ℤ) : ((n : ZNum) : α) = n := by
  rw [← cast_to_int, to_of_int]

@[simp, norm_cast]
theorem of_natCast [AddGroupWithOne α] (n : ℕ) : ((n : ZNum) : α) = n := by
  rw [← Int.cast_natCast, of_intCast, Int.cast_natCast]

@[simp, norm_cast]
theorem dvd_to_int (m n : ZNum) : (m : ℤ) ∣ n ↔ m ∣ n :=
  ⟨fun ⟨k, e⟩ => ⟨k, by rw [← of_to_int n, e]; simp⟩, fun ⟨k, e⟩ => ⟨k, by simp [e]⟩⟩

end ZNum

namespace PosNum

theorem divMod_to_nat_aux {n d : PosNum} {q r : Num} (h₁ : (r : ℕ) + d * ((q : ℕ) + q) = n)
    (h₂ : (r : ℕ) < 2 * d) :
    ((divModAux d q r).2 + d * (divModAux d q r).1 : ℕ) = ↑n ∧ ((divModAux d q r).2 : ℕ) < d := by
  unfold divModAux
  have : ∀ {r₂}, Num.ofZNum' (Num.sub' r (Num.pos d)) = some r₂ ↔ (r : ℕ) = r₂ + d := by
    intro r₂
    apply Num.mem_ofZNum'.trans
    rw [← ZNum.to_int_inj, Num.cast_toZNum, Num.cast_sub', sub_eq_iff_eq_add, ← Int.natCast_inj]
    simp
  rcases e : Num.ofZNum' (Num.sub' r (Num.pos d)) with - | r₂
  · rw [Num.cast_bit0, two_mul]
    refine ⟨h₁, lt_of_not_ge fun h => ?_⟩
    obtain ⟨r₂, e'⟩ := Nat.le.dest h
    rw [← Num.to_of_nat r₂, add_comm] at e'
    cases e.symm.trans (this.2 e'.symm)
  · have := this.1 e
    simp only [Num.cast_bit1]
    constructor
    · rwa [two_mul, add_comm _ 1, mul_add, mul_one, ← add_assoc, ← this]
    · rwa [this, two_mul, add_lt_add_iff_right] at h₂

theorem divMod_to_nat (d n : PosNum) :
    (n / d : ℕ) = (divMod d n).1 ∧ (n % d : ℕ) = (divMod d n).2 := by
  rw [Nat.div_mod_unique (PosNum.cast_pos _)]
  induction' n with n IH n IH
  · exact
      divMod_to_nat_aux (by simp) (Nat.mul_le_mul_left 2 (PosNum.cast_pos d : (0 : ℕ) < d))
  · unfold divMod
    -- Porting note: `cases'` didn't rewrite at `this`, so `revert` & `intro` are required.
    revert IH; obtain ⟨q, r⟩ := divMod d n; intro IH
    simp only at IH ⊢
    apply divMod_to_nat_aux <;> simp only [Num.cast_bit1, cast_bit1]
    · rw [← two_mul, ← two_mul, add_right_comm, mul_left_comm, ← mul_add, IH.1]
    · omega
  · unfold divMod
    -- Porting note: `cases'` didn't rewrite at `this`, so `revert` & `intro` are required.
    revert IH; obtain ⟨q, r⟩ := divMod d n; intro IH
    simp only at IH ⊢
    apply divMod_to_nat_aux
    · simp only [Num.cast_bit0, cast_bit0]
      rw [← two_mul, ← two_mul, mul_left_comm, ← mul_add, ← IH.1]
    · simpa using IH.2

@[simp]
theorem div'_to_nat (n d) : (div' n d : ℕ) = n / d :=
  (divMod_to_nat _ _).1.symm

@[simp]
theorem mod'_to_nat (n d) : (mod' n d : ℕ) = n % d :=
  (divMod_to_nat _ _).2.symm

end PosNum

namespace Num

@[simp]
protected theorem div_zero (n : Num) : n / 0 = 0 :=
  show n.div 0 = 0 by
    cases n
    · rfl
    · simp [Num.div]

@[simp, norm_cast]
theorem div_to_nat : ∀ n d, ((n / d : Num) : ℕ) = n / d
  | 0, 0 => by simp
  | 0, pos _ => (Nat.zero_div _).symm
  | pos _, 0 => (Nat.div_zero _).symm
  | pos _, pos _ => PosNum.div'_to_nat _ _

@[simp]
protected theorem mod_zero (n : Num) : n % 0 = n :=
  show n.mod 0 = n by
    cases n
    · rfl
    · simp [Num.mod]

@[simp, norm_cast]
theorem mod_to_nat : ∀ n d, ((n % d : Num) : ℕ) = n % d
  | 0, 0 => by simp
  | 0, pos _ => (Nat.zero_mod _).symm
  | pos _, 0 => (Nat.mod_zero _).symm
  | pos _, pos _ => PosNum.mod'_to_nat _ _

theorem gcd_to_nat_aux :
    ∀ {n} {a b : Num}, a ≤ b → (a * b).natSize ≤ n → (gcdAux n a b : ℕ) = Nat.gcd a b
  | 0, 0, _, _ab, _h => (Nat.gcd_zero_left _).symm
  | 0, pos _, 0, ab, _h => (not_lt_of_ge ab).elim rfl
  | 0, pos _, pos _, _ab, h => (not_lt_of_ge h).elim <| PosNum.natSize_pos _
  | Nat.succ _, 0, _, _ab, _h => (Nat.gcd_zero_left _).symm
  | Nat.succ n, pos a, b, ab, h => by
    simp only [gcdAux, cast_pos]
    rw [Nat.gcd_rec, gcd_to_nat_aux, mod_to_nat]
    · rfl
    · rw [← le_to_nat, mod_to_nat]
      exact le_of_lt (Nat.mod_lt _ (PosNum.cast_pos _))
    rw [natSize_to_nat, mul_to_nat, Nat.size_le] at h ⊢
    rw [mod_to_nat, mul_comm]
    rw [pow_succ, ← Nat.mod_add_div b (pos a)] at h
    refine lt_of_mul_lt_mul_right (lt_of_le_of_lt ?_ h) (Nat.zero_le 2)
    rw [mul_two, mul_add]
    refine
      add_le_add_left
        (Nat.mul_le_mul_left _ (le_trans (le_of_lt (Nat.mod_lt _ (PosNum.cast_pos _))) ?_)) _
    suffices 1 ≤ _ by simpa using Nat.mul_le_mul_left (pos a) this
    rw [Nat.le_div_iff_mul_le a.cast_pos, one_mul]
    exact le_to_nat.2 ab

@[simp]
theorem gcd_to_nat : ∀ a b, (gcd a b : ℕ) = Nat.gcd a b := by
  have : ∀ a b : Num, (a * b).natSize ≤ a.natSize + b.natSize := by
    intros
    simp only [natSize_to_nat, cast_mul]
    rw [Nat.size_le, pow_add]
    exact mul_lt_mul'' (Nat.lt_size_self _) (Nat.lt_size_self _) (Nat.zero_le _) (Nat.zero_le _)
  intros
  unfold gcd
  split_ifs with h
  · exact gcd_to_nat_aux h (this _ _)
  · rw [Nat.gcd_comm]
    exact gcd_to_nat_aux (le_of_not_ge h) (this _ _)

theorem dvd_iff_mod_eq_zero {m n : Num} : m ∣ n ↔ n % m = 0 := by
  rw [← dvd_to_nat, Nat.dvd_iff_mod_eq_zero, ← to_nat_inj, mod_to_nat]; rfl

instance decidableDvd : DecidableRel ((· ∣ ·) : Num → Num → Prop)
  | _a, _b => decidable_of_iff' _ dvd_iff_mod_eq_zero

end Num

instance PosNum.decidableDvd : DecidableRel ((· ∣ ·) : PosNum → PosNum → Prop)
  | _a, _b => Num.decidableDvd _ _

namespace ZNum

@[simp]
protected theorem div_zero (n : ZNum) : n / 0 = 0 :=
  show n.div 0 = 0 by cases n <;> rfl

@[simp, norm_cast]
theorem div_to_int : ∀ n d, ((n / d : ZNum) : ℤ) = n / d
  | 0, 0 => by simp [Int.ediv_zero]
  | 0, pos _ => (Int.zero_ediv _).symm
  | 0, neg _ => (Int.zero_ediv _).symm
  | pos _, 0 => (Int.ediv_zero _).symm
  | neg _, 0 => (Int.ediv_zero _).symm
  | pos n, pos d => (Num.cast_toZNum _).trans <| by rw [← Num.to_nat_to_int]; simp
  | pos n, neg d => (Num.cast_toZNumNeg _).trans <| by rw [← Num.to_nat_to_int]; simp
  | neg n, pos d =>
    show -_ = -_ / ↑d by
      rw [n.to_int_eq_succ_pred, d.to_int_eq_succ_pred, ← PosNum.to_nat_to_int, Num.succ'_to_nat,
        Num.div_to_nat]
      change -[n.pred' / ↑d+1] = -[n.pred' / (d.pred' + 1)+1]
      rw [d.to_nat_eq_succ_pred]
  | neg n, neg d =>
    show ↑(PosNum.pred' n / Num.pos d).succ' = -_ / -↑d by
      rw [n.to_int_eq_succ_pred, d.to_int_eq_succ_pred, ← PosNum.to_nat_to_int, Num.succ'_to_nat,
        Num.div_to_nat]
      change (Nat.succ (_ / d) : ℤ) = Nat.succ (n.pred' / (d.pred' + 1))
      rw [d.to_nat_eq_succ_pred]

@[simp, norm_cast]
theorem mod_to_int : ∀ n d, ((n % d : ZNum) : ℤ) = n % d
  | 0, _ => (Int.zero_emod _).symm
  | pos n, d =>
    (Num.cast_toZNum _).trans <| by
      rw [← Num.to_nat_to_int, cast_pos, Num.mod_to_nat, ← PosNum.to_nat_to_int, abs_to_nat]
      rfl
  | neg n, d =>
    (Num.cast_sub' _ _).trans <| by
      rw [← Num.to_nat_to_int, cast_neg, ← Num.to_nat_to_int, Num.succ_to_nat, Num.mod_to_nat,
          abs_to_nat, ← Int.subNatNat_eq_coe, n.to_int_eq_succ_pred]
      rfl

@[simp]
theorem gcd_to_nat (a b) : (gcd a b : ℕ) = Int.gcd a b :=
  (Num.gcd_to_nat _ _).trans <| by simp only [abs_to_nat]; rfl

theorem dvd_iff_mod_eq_zero {m n : ZNum} : m ∣ n ↔ n % m = 0 := by
  rw [← dvd_to_int, Int.dvd_iff_emod_eq_zero, ← to_int_inj, mod_to_int]; rfl

instance decidableDvd : DecidableRel ((· ∣ ·) : ZNum → ZNum → Prop)
  | _a, _b => decidable_of_iff' _ dvd_iff_mod_eq_zero

end ZNum
