/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module algebra.modeq
! leanprover-community/mathlib commit a07d750983b94c530ab69a726862c2ab6802b38c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Int.ModEq
import Mathlib.GroupTheory.QuotientGroup

/-!
# Equality modulo an element

This file defines equality modulo an element in a commutative group.

## Main definitions

* `a ≡ b [PMOD p]`: `a` and `b` are congruent modulo a`p`.

## See also

`SModEq` is a generalisation to arbitrary submodules.

## TODO

Delete `Int.ModEq` in favour of `AddCommGroup.ModEq`. Generalise `SModEq` to `AddSubgroup` and
redefine `AddCommGroup.ModEq` using it. Once this is done, we can rename `AddCommGroup.ModEq`
to `AddSubgroup.ModEq` and multiplicativise it. Longer term, we could generalise to submonoids and
also unify with `Nat.ModEq`.
-/


namespace AddCommGroup

variable {α : Type _}

section AddCommGroup

variable [AddCommGroup α] {p a a₁ a₂ b b₁ b₂ c : α} {n : ℕ} {z : ℤ}

/-- `a ≡ b [PMOD p]` means that `b` is congruent to `a` modulo `p`.

Equivalently (as shown in `Algebra.Order.ToIntervalMod`), `b` does not lie in the open interval
`(a, a + p)` modulo `p`, or `toIcoMod hp a` disagrees with `toIocMod hp a` at `b`, or
`toIcoDiv hp a` disagrees with `toIocDiv hp a` at `b`. -/
def ModEq (p a b : α) : Prop :=
  ∃ z : ℤ, b - a = z • p
#align add_comm_group.modeq AddCommGroup.ModEq

notation:50 a " ≡ " b " [PMOD " p "]" => ModEq p a b

@[refl, simp]
theorem modeq_refl (a : α) : a ≡ a [PMOD p] :=
  ⟨0, by simp⟩
#align add_comm_group.modeq_refl AddCommGroup.modeq_refl

theorem modeq_rfl : a ≡ a [PMOD p] :=
  modeq_refl _
#align add_comm_group.modeq_rfl AddCommGroup.modeq_rfl

theorem modeq_comm : a ≡ b [PMOD p] ↔ b ≡ a [PMOD p] :=
  (Equiv.neg _).exists_congr_left.trans <| by simp [ModEq, ← neg_eq_iff_eq_neg]
#align add_comm_group.modeq_comm AddCommGroup.modeq_comm

alias modeq_comm ↔ ModEq.symm _
#align add_comm_group.modeq.symm AddCommGroup.ModEq.symm

attribute [symm] ModEq.symm

@[trans]
theorem ModEq.trans : a ≡ b [PMOD p] → b ≡ c [PMOD p] → a ≡ c [PMOD p] := fun ⟨m, hm⟩ ⟨n, hn⟩ =>
  ⟨m + n, by simp [add_smul, ← hm, ← hn]⟩
#align add_comm_group.modeq.trans AddCommGroup.ModEq.trans

instance : IsRefl _ (ModEq p) :=
  ⟨modeq_refl⟩

@[simp]
theorem neg_modeq_neg : -a ≡ -b [PMOD p] ↔ a ≡ b [PMOD p] :=
  modeq_comm.trans <| by simp [ModEq, neg_add_eq_sub]
#align add_comm_group.neg_modeq_neg AddCommGroup.neg_modeq_neg

alias neg_modeq_neg ↔ ModEq.of_neg ModEq.neg
#align add_comm_group.modeq.of_neg AddCommGroup.ModEq.of_neg
#align add_comm_group.modeq.neg AddCommGroup.ModEq.neg

@[simp]
theorem modeq_neg : a ≡ b [PMOD -p] ↔ a ≡ b [PMOD p] :=
  modeq_comm.trans <| by simp [ModEq, ← neg_eq_iff_eq_neg]
#align add_comm_group.modeq_neg AddCommGroup.modeq_neg

alias modeq_neg ↔ ModEq.of_neg' ModEq.neg'
#align add_comm_group.modeq.of_neg' AddCommGroup.ModEq.of_neg'
#align add_comm_group.modeq.neg' AddCommGroup.ModEq.neg'

theorem modeq_sub (a b : α) : a ≡ b [PMOD b - a] :=
  ⟨1, (one_smul _ _).symm⟩
#align add_comm_group.modeq_sub AddCommGroup.modeq_sub

@[simp]
theorem modeq_zero : a ≡ b [PMOD 0] ↔ a = b := by simp [ModEq, sub_eq_zero, eq_comm]
#align add_comm_group.modeq_zero AddCommGroup.modeq_zero

@[simp]
theorem self_modeq_zero : p ≡ 0 [PMOD p] :=
  ⟨-1, by simp⟩
#align add_comm_group.self_modeq_zero AddCommGroup.self_modeq_zero

@[simp]
theorem zsmul_modeq_zero (z : ℤ) : z • p ≡ 0 [PMOD p] :=
  ⟨-z, by simp⟩
#align add_comm_group.zsmul_modeq_zero AddCommGroup.zsmul_modeq_zero

theorem add_zsmul_modeq (z : ℤ) : a + z • p ≡ a [PMOD p] :=
  ⟨-z, by simp⟩
#align add_comm_group.add_zsmul_modeq AddCommGroup.add_zsmul_modeq

theorem zsmul_add_modeq (z : ℤ) : z • p + a ≡ a [PMOD p] :=
  ⟨-z, by simp [← sub_sub]⟩
#align add_comm_group.zsmul_add_modeq AddCommGroup.zsmul_add_modeq

theorem add_nsmul_modeq (n : ℕ) : a + n • p ≡ a [PMOD p] :=
  ⟨-n, by simp⟩
#align add_comm_group.add_nsmul_modeq AddCommGroup.add_nsmul_modeq

theorem nsmul_add_modeq (n : ℕ) : n • p + a ≡ a [PMOD p] :=
  ⟨-n, by simp [← sub_sub]⟩
#align add_comm_group.nsmul_add_modeq AddCommGroup.nsmul_add_modeq

namespace ModEq

protected theorem add_zsmul (z : ℤ) : a ≡ b [PMOD p] → a + z • p ≡ b [PMOD p] :=
  (add_zsmul_modeq _).trans
#align add_comm_group.modeq.add_zsmul AddCommGroup.ModEq.add_zsmul

protected theorem zsmul_add (z : ℤ) : a ≡ b [PMOD p] → z • p + a ≡ b [PMOD p] :=
  (zsmul_add_modeq _).trans
#align add_comm_group.modeq.zsmul_add AddCommGroup.ModEq.zsmul_add

protected theorem add_nsmul (n : ℕ) : a ≡ b [PMOD p] → a + n • p ≡ b [PMOD p] :=
  (add_nsmul_modeq _).trans
#align add_comm_group.modeq.add_nsmul AddCommGroup.ModEq.add_nsmul

protected theorem nsmul_add (n : ℕ) : a ≡ b [PMOD p] → n • p + a ≡ b [PMOD p] :=
  (nsmul_add_modeq _).trans
#align add_comm_group.modeq.nsmul_add AddCommGroup.ModEq.nsmul_add

protected theorem of_zsmul : a ≡ b [PMOD z • p] → a ≡ b [PMOD p] := fun ⟨m, hm⟩ =>
  ⟨m * z, by rwa [mul_smul]⟩
#align add_comm_group.modeq.of_zsmul AddCommGroup.ModEq.of_zsmul

protected theorem of_nsmul : a ≡ b [PMOD n • p] → a ≡ b [PMOD p] := fun ⟨m, hm⟩ =>
  ⟨m * n, by rwa [mul_smul, coe_nat_zsmul]⟩
#align add_comm_group.modeq.of_nsmul AddCommGroup.ModEq.of_nsmul

protected theorem zsmul : a ≡ b [PMOD p] → z • a ≡ z • b [PMOD z • p] :=
  Exists.imp fun m hm => by rw [← smul_sub, hm, smul_comm]
#align add_comm_group.modeq.zsmul AddCommGroup.ModEq.zsmul

protected theorem nsmul : a ≡ b [PMOD p] → n • a ≡ n • b [PMOD n • p] :=
  Exists.imp fun m hm => by rw [← smul_sub, hm, smul_comm]
#align add_comm_group.modeq.nsmul AddCommGroup.ModEq.nsmul

end ModEq

@[simp]
theorem zsmul_modeq_zsmul [NoZeroSMulDivisors ℤ α] (hn : z ≠ 0) :
    z • a ≡ z • b [PMOD z • p] ↔ a ≡ b [PMOD p] :=
  exists_congr fun m => by rw [← smul_sub, smul_comm, smul_right_inj hn]
#align add_comm_group.zsmul_modeq_zsmul AddCommGroup.zsmul_modeq_zsmul

@[simp]
theorem nsmul_modeq_nsmul [NoZeroSMulDivisors ℕ α] (hn : n ≠ 0) :
    n • a ≡ n • b [PMOD n • p] ↔ a ≡ b [PMOD p] :=
  exists_congr fun m => by rw [← smul_sub, smul_comm, smul_right_inj hn]
#align add_comm_group.nsmul_modeq_nsmul AddCommGroup.nsmul_modeq_nsmul

alias zsmul_modeq_zsmul ↔ ModEq.zsmul_cancel _
#align add_comm_group.modeq.zsmul_cancel AddCommGroup.ModEq.zsmul_cancel

alias nsmul_modeq_nsmul ↔ ModEq.nsmul_cancel _
#align add_comm_group.modeq.nsmul_cancel AddCommGroup.ModEq.nsmul_cancel

namespace ModEq

@[simp]
protected theorem add_iff_left :
    a₁ ≡ b₁ [PMOD p] → (a₁ + a₂ ≡ b₁ + b₂ [PMOD p] ↔ a₂ ≡ b₂ [PMOD p]) := fun ⟨m, hm⟩ =>
  (Equiv.addLeft m).symm.exists_congr_left.trans <| by simp [add_sub_add_comm, hm, add_smul, ModEq]

#align add_comm_group.modeq.add_iff_left AddCommGroup.ModEq.add_iff_left

@[simp]
protected theorem add_iff_right :
    a₂ ≡ b₂ [PMOD p] → (a₁ + a₂ ≡ b₁ + b₂ [PMOD p] ↔ a₁ ≡ b₁ [PMOD p]) := fun ⟨m, hm⟩ =>
  (Equiv.addRight m).symm.exists_congr_left.trans <| by simp [add_sub_add_comm, hm, add_smul, ModEq]
#align add_comm_group.modeq.add_iff_right AddCommGroup.ModEq.add_iff_right

@[simp]
protected theorem sub_iff_left :
    a₁ ≡ b₁ [PMOD p] → (a₁ - a₂ ≡ b₁ - b₂ [PMOD p] ↔ a₂ ≡ b₂ [PMOD p]) := fun ⟨m, hm⟩ =>
  (Equiv.subLeft m).symm.exists_congr_left.trans <| by simp [sub_sub_sub_comm, hm, sub_smul, ModEq]
#align add_comm_group.modeq.sub_iff_left AddCommGroup.ModEq.sub_iff_left

@[simp]
protected theorem sub_iff_right :
    a₂ ≡ b₂ [PMOD p] → (a₁ - a₂ ≡ b₁ - b₂ [PMOD p] ↔ a₁ ≡ b₁ [PMOD p]) := fun ⟨m, hm⟩ =>
  (Equiv.subRight m).symm.exists_congr_left.trans <| by simp [sub_sub_sub_comm, hm, sub_smul, ModEq]
#align add_comm_group.modeq.sub_iff_right AddCommGroup.ModEq.sub_iff_right

alias ModEq.add_iff_left ↔ add_left_cancel add
#align add_comm_group.modeq.add_left_cancel AddCommGroup.ModEq.add_left_cancel
#align add_comm_group.modeq.add AddCommGroup.ModEq.add

alias ModEq.add_iff_right ↔ add_right_cancel _
#align add_comm_group.modeq.add_right_cancel AddCommGroup.ModEq.add_right_cancel

alias ModEq.sub_iff_left ↔ sub_left_cancel sub
#align add_comm_group.modeq.sub_left_cancel AddCommGroup.ModEq.sub_left_cancel
#align add_comm_group.modeq.sub AddCommGroup.ModEq.sub

alias ModEq.sub_iff_right ↔ sub_right_cancel _
#align add_comm_group.modeq.sub_right_cancel AddCommGroup.ModEq.sub_right_cancel

-- porting note: doesn't work
-- attribute [protected] add_left_cancel add_right_cancel add sub_left_cancel sub_right_cancel sub

protected theorem add_left (c : α) (h : a ≡ b [PMOD p]) : c + a ≡ c + b [PMOD p] :=
  modeq_rfl.add h
#align add_comm_group.modeq.add_left AddCommGroup.ModEq.add_left

protected theorem sub_left (c : α) (h : a ≡ b [PMOD p]) : c - a ≡ c - b [PMOD p] :=
  modeq_rfl.sub h
#align add_comm_group.modeq.sub_left AddCommGroup.ModEq.sub_left

protected theorem add_right (c : α) (h : a ≡ b [PMOD p]) : a + c ≡ b + c [PMOD p] :=
  h.add modeq_rfl
#align add_comm_group.modeq.add_right AddCommGroup.ModEq.add_right

protected theorem sub_right (c : α) (h : a ≡ b [PMOD p]) : a - c ≡ b - c [PMOD p] :=
  h.sub modeq_rfl
#align add_comm_group.modeq.sub_right AddCommGroup.ModEq.sub_right

protected theorem add_left_cancel' (c : α) : c + a ≡ c + b [PMOD p] → a ≡ b [PMOD p] :=
  modeq_rfl.add_left_cancel
#align add_comm_group.modeq.add_left_cancel' AddCommGroup.ModEq.add_left_cancel'

protected theorem add_right_cancel' (c : α) : a + c ≡ b + c [PMOD p] → a ≡ b [PMOD p] :=
  modeq_rfl.add_right_cancel
#align add_comm_group.modeq.add_right_cancel' AddCommGroup.ModEq.add_right_cancel'

protected theorem sub_left_cancel' (c : α) : c - a ≡ c - b [PMOD p] → a ≡ b [PMOD p] :=
  modeq_rfl.sub_left_cancel
#align add_comm_group.modeq.sub_left_cancel' AddCommGroup.ModEq.sub_left_cancel'

protected theorem sub_right_cancel' (c : α) : a - c ≡ b - c [PMOD p] → a ≡ b [PMOD p] :=
  modeq_rfl.sub_right_cancel
#align add_comm_group.modeq.sub_right_cancel' AddCommGroup.ModEq.sub_right_cancel'

end ModEq

theorem modeq_sub_iff_add_modeq' : a ≡ b - c [PMOD p] ↔ c + a ≡ b [PMOD p] := by
  simp [ModEq, sub_sub]
#align add_comm_group.modeq_sub_iff_add_modeq' AddCommGroup.modeq_sub_iff_add_modeq'

theorem modeq_sub_iff_add_modeq : a ≡ b - c [PMOD p] ↔ a + c ≡ b [PMOD p] :=
  modeq_sub_iff_add_modeq'.trans <| by rw [add_comm]
#align add_comm_group.modeq_sub_iff_add_modeq AddCommGroup.modeq_sub_iff_add_modeq

theorem sub_modeq_iff_modeq_add' : a - b ≡ c [PMOD p] ↔ a ≡ b + c [PMOD p] :=
  modeq_comm.trans <| modeq_sub_iff_add_modeq'.trans modeq_comm
#align add_comm_group.sub_modeq_iff_modeq_add' AddCommGroup.sub_modeq_iff_modeq_add'

theorem sub_modeq_iff_modeq_add : a - b ≡ c [PMOD p] ↔ a ≡ c + b [PMOD p] :=
  modeq_comm.trans <| modeq_sub_iff_add_modeq.trans modeq_comm
#align add_comm_group.sub_modeq_iff_modeq_add AddCommGroup.sub_modeq_iff_modeq_add

@[simp]
theorem sub_modeq_zero : a - b ≡ 0 [PMOD p] ↔ a ≡ b [PMOD p] := by simp [sub_modeq_iff_modeq_add]
#align add_comm_group.sub_modeq_zero AddCommGroup.sub_modeq_zero

@[simp]
theorem add_modeq_left : a + b ≡ a [PMOD p] ↔ b ≡ 0 [PMOD p] := by simp [← modeq_sub_iff_add_modeq']
#align add_comm_group.add_modeq_left AddCommGroup.add_modeq_left

@[simp]
theorem add_modeq_right : a + b ≡ b [PMOD p] ↔ a ≡ 0 [PMOD p] := by simp [← modeq_sub_iff_add_modeq]
#align add_comm_group.add_modeq_right AddCommGroup.add_modeq_right

theorem modeq_iff_eq_add_zsmul : a ≡ b [PMOD p] ↔ ∃ z : ℤ, b = a + z • p := by
  simp_rw [ModEq, sub_eq_iff_eq_add']
#align add_comm_group.modeq_iff_eq_add_zsmul AddCommGroup.modeq_iff_eq_add_zsmul

theorem not_modeq_iff_ne_add_zsmul : ¬a ≡ b [PMOD p] ↔ ∀ z : ℤ, b ≠ a + z • p := by
  rw [modeq_iff_eq_add_zsmul, not_exists]
#align add_comm_group.not_modeq_iff_ne_add_zsmul AddCommGroup.not_modeq_iff_ne_add_zsmul

theorem modeq_iff_eq_mod_zmultiples : a ≡ b [PMOD p] ↔ (b : α ⧸ AddSubgroup.zmultiples p) = a := by
  simp_rw [modeq_iff_eq_add_zsmul, QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_zmultiples_iff,
    eq_sub_iff_add_eq', eq_comm]
#align add_comm_group.modeq_iff_eq_mod_zmultiples AddCommGroup.modeq_iff_eq_mod_zmultiples

theorem not_modeq_iff_ne_mod_zmultiples :
    ¬a ≡ b [PMOD p] ↔ (b : α ⧸ AddSubgroup.zmultiples p) ≠ a :=
  modeq_iff_eq_mod_zmultiples.not
#align add_comm_group.not_modeq_iff_ne_mod_zmultiples AddCommGroup.not_modeq_iff_ne_mod_zmultiples

end AddCommGroup

@[simp]
theorem modeq_iff_int_modeq {a b z : ℤ} : a ≡ b [PMOD z] ↔ a ≡ b [ZMOD z] := by
  simp [ModEq, dvd_iff_exists_eq_mul_left, Int.modEq_iff_dvd]
#align add_comm_group.modeq_iff_int_modeq AddCommGroup.modeq_iff_int_modeq

section AddCommGroupWithOne

variable [AddCommGroupWithOne α] [CharZero α]

@[simp, norm_cast]
theorem int_cast_modeq_int_cast {a b z : ℤ} : a ≡ b [PMOD (z : α)] ↔ a ≡ b [PMOD z] := by
  simp_rw [ModEq, ← Int.cast_mul_eq_zsmul_cast]
  norm_cast
#align add_comm_group.int_cast_modeq_int_cast AddCommGroup.int_cast_modeq_int_cast

@[simp, norm_cast]
theorem nat_cast_modeq_nat_cast {a b n : ℕ} : a ≡ b [PMOD (n : α)] ↔ a ≡ b [MOD n] := by
  simp_rw [← Int.coe_nat_modEq_iff, ← modeq_iff_int_modeq, ← @int_cast_modeq_int_cast α,
    Int.cast_ofNat]
#align add_comm_group.nat_cast_modeq_nat_cast AddCommGroup.nat_cast_modeq_nat_cast

alias int_cast_modeq_int_cast ↔ ModEq.of_int_cast ModEq.int_cast
#align add_comm_group.modeq.of_int_cast AddCommGroup.ModEq.of_int_cast
#align add_comm_group.modeq.int_cast AddCommGroup.ModEq.int_cast

alias nat_cast_modeq_nat_cast ↔ _root_.Nat.ModEq.of_nat_cast ModEq.nat_cast
#align nat.modeq.of_nat_cast Nat.ModEq.of_nat_cast
#align add_comm_group.modeq.nat_cast AddCommGroup.ModEq.nat_cast

end AddCommGroupWithOne

end AddCommGroup
