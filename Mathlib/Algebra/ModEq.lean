/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.NoZeroSMulDivisors.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

/-!
# Equality modulo an element

This file defines equality modulo an element in a commutative group.

## Main definitions

* `a ≡ b [PMOD p]`: `a` and `b` are congruent modulo `p`.

## See also

`SModEq` is a generalisation to arbitrary submodules.

## TODO

Delete `Int.ModEq` in favour of `AddCommGroup.ModEq`. Generalise `SModEq` to `AddSubgroup` and
redefine `AddCommGroup.ModEq` using it. Once this is done, we can rename `AddCommGroup.ModEq`
to `AddSubgroup.ModEq` and multiplicativise it. Longer term, we could generalise to submonoids and
also unify with `Nat.ModEq`.
-/


namespace AddCommGroup

variable {α : Type*}

section AddCommGroup

variable [AddCommGroup α] {p a a₁ a₂ b b₁ b₂ c : α} {n : ℕ} {z : ℤ}

/-- `a ≡ b [PMOD p]` means that `b` is congruent to `a` modulo `p`.

Equivalently (as shown in `Algebra.Order.ToIntervalMod`), `b` does not lie in the open interval
`(a, a + p)` modulo `p`, or `toIcoMod hp a` disagrees with `toIocMod hp a` at `b`, or
`toIcoDiv hp a` disagrees with `toIocDiv hp a` at `b`. -/
def ModEq (p a b : α) : Prop :=
  ∃ z : ℤ, b - a = z • p

@[inherit_doc]
notation:50 a " ≡ " b " [PMOD " p "]" => ModEq p a b

@[refl, simp]
theorem modEq_refl (a : α) : a ≡ a [PMOD p] :=
  ⟨0, by simp⟩

theorem modEq_rfl : a ≡ a [PMOD p] :=
  modEq_refl _

theorem modEq_comm : a ≡ b [PMOD p] ↔ b ≡ a [PMOD p] :=
  (Equiv.neg _).exists_congr_left.trans <| by simp [ModEq, ← neg_eq_iff_eq_neg]

alias ⟨ModEq.symm, _⟩ := modEq_comm

attribute [symm] ModEq.symm

@[trans]
theorem ModEq.trans : a ≡ b [PMOD p] → b ≡ c [PMOD p] → a ≡ c [PMOD p] := fun ⟨m, hm⟩ ⟨n, hn⟩ =>
  ⟨m + n, by simp [add_smul, ← hm, ← hn]⟩

instance : IsRefl _ (ModEq p) :=
  ⟨modEq_refl⟩

@[simp]
theorem neg_modEq_neg : -a ≡ -b [PMOD p] ↔ a ≡ b [PMOD p] :=
  modEq_comm.trans <| by simp [ModEq, neg_add_eq_sub]

alias ⟨ModEq.of_neg, ModEq.neg⟩ := neg_modEq_neg

@[simp]
theorem modEq_neg : a ≡ b [PMOD -p] ↔ a ≡ b [PMOD p] :=
  modEq_comm.trans <| by simp [ModEq, ← neg_eq_iff_eq_neg]

alias ⟨ModEq.of_neg', ModEq.neg'⟩ := modEq_neg

theorem modEq_sub (a b : α) : a ≡ b [PMOD b - a] :=
  ⟨1, (one_smul _ _).symm⟩

@[simp]
theorem modEq_zero : a ≡ b [PMOD 0] ↔ a = b := by simp [ModEq, sub_eq_zero, eq_comm]

@[simp]
theorem self_modEq_zero : p ≡ 0 [PMOD p] :=
  ⟨-1, by simp⟩

@[simp]
theorem zsmul_modEq_zero (z : ℤ) : z • p ≡ 0 [PMOD p] :=
  ⟨-z, by simp⟩

theorem add_zsmul_modEq (z : ℤ) : a + z • p ≡ a [PMOD p] :=
  ⟨-z, by simp⟩

theorem zsmul_add_modEq (z : ℤ) : z • p + a ≡ a [PMOD p] :=
  ⟨-z, by simp [← sub_sub]⟩

theorem add_nsmul_modEq (n : ℕ) : a + n • p ≡ a [PMOD p] :=
  ⟨-n, by simp⟩

theorem nsmul_add_modEq (n : ℕ) : n • p + a ≡ a [PMOD p] :=
  ⟨-n, by simp [← sub_sub]⟩

namespace ModEq

protected theorem add_zsmul (z : ℤ) : a ≡ b [PMOD p] → a + z • p ≡ b [PMOD p] :=
  (add_zsmul_modEq _).trans

protected theorem zsmul_add (z : ℤ) : a ≡ b [PMOD p] → z • p + a ≡ b [PMOD p] :=
  (zsmul_add_modEq _).trans

protected theorem add_nsmul (n : ℕ) : a ≡ b [PMOD p] → a + n • p ≡ b [PMOD p] :=
  (add_nsmul_modEq _).trans

protected theorem nsmul_add (n : ℕ) : a ≡ b [PMOD p] → n • p + a ≡ b [PMOD p] :=
  (nsmul_add_modEq _).trans

protected theorem of_zsmul : a ≡ b [PMOD z • p] → a ≡ b [PMOD p] := fun ⟨m, hm⟩ =>
  ⟨m * z, by rwa [mul_smul]⟩

protected theorem of_nsmul : a ≡ b [PMOD n • p] → a ≡ b [PMOD p] := fun ⟨m, hm⟩ =>
  ⟨m * n, by rwa [mul_smul, natCast_zsmul]⟩

protected theorem zsmul : a ≡ b [PMOD p] → z • a ≡ z • b [PMOD z • p] :=
  Exists.imp fun m hm => by rw [← smul_sub, hm, smul_comm]

protected theorem nsmul : a ≡ b [PMOD p] → n • a ≡ n • b [PMOD n • p] :=
  Exists.imp fun m hm => by rw [← smul_sub, hm, smul_comm]

end ModEq

@[simp]
theorem zsmul_modEq_zsmul [NoZeroSMulDivisors ℤ α] (hn : z ≠ 0) :
    z • a ≡ z • b [PMOD z • p] ↔ a ≡ b [PMOD p] :=
  exists_congr fun m => by rw [← smul_sub, smul_comm, smul_right_inj hn]

@[simp]
theorem nsmul_modEq_nsmul [NoZeroSMulDivisors ℕ α] (hn : n ≠ 0) :
    n • a ≡ n • b [PMOD n • p] ↔ a ≡ b [PMOD p] :=
  exists_congr fun m => by rw [← smul_sub, smul_comm, smul_right_inj hn]

alias ⟨ModEq.zsmul_cancel, _⟩ := zsmul_modEq_zsmul

alias ⟨ModEq.nsmul_cancel, _⟩ := nsmul_modEq_nsmul

namespace ModEq

@[simp]
protected theorem add_iff_left :
    a₁ ≡ b₁ [PMOD p] → (a₁ + a₂ ≡ b₁ + b₂ [PMOD p] ↔ a₂ ≡ b₂ [PMOD p]) := fun ⟨m, hm⟩ =>
  (Equiv.addLeft m).symm.exists_congr_left.trans <| by simp [add_sub_add_comm, hm, add_smul, ModEq]

@[simp]
protected theorem add_iff_right :
    a₂ ≡ b₂ [PMOD p] → (a₁ + a₂ ≡ b₁ + b₂ [PMOD p] ↔ a₁ ≡ b₁ [PMOD p]) := fun ⟨m, hm⟩ =>
  (Equiv.addRight m).symm.exists_congr_left.trans <| by simp [add_sub_add_comm, hm, add_smul, ModEq]

@[simp]
protected theorem sub_iff_left :
    a₁ ≡ b₁ [PMOD p] → (a₁ - a₂ ≡ b₁ - b₂ [PMOD p] ↔ a₂ ≡ b₂ [PMOD p]) := fun ⟨m, hm⟩ =>
  (Equiv.subLeft m).symm.exists_congr_left.trans <| by simp [sub_sub_sub_comm, hm, sub_smul, ModEq]

@[simp]
protected theorem sub_iff_right :
    a₂ ≡ b₂ [PMOD p] → (a₁ - a₂ ≡ b₁ - b₂ [PMOD p] ↔ a₁ ≡ b₁ [PMOD p]) := fun ⟨m, hm⟩ =>
  (Equiv.subRight m).symm.exists_congr_left.trans <| by simp [sub_sub_sub_comm, hm, sub_smul, ModEq]

protected alias ⟨add_left_cancel, add⟩ := ModEq.add_iff_left

protected alias ⟨add_right_cancel, _⟩ := ModEq.add_iff_right

protected alias ⟨sub_left_cancel, sub⟩ := ModEq.sub_iff_left

protected alias ⟨sub_right_cancel, _⟩ := ModEq.sub_iff_right

protected theorem add_left (c : α) (h : a ≡ b [PMOD p]) : c + a ≡ c + b [PMOD p] :=
  modEq_rfl.add h

protected theorem sub_left (c : α) (h : a ≡ b [PMOD p]) : c - a ≡ c - b [PMOD p] :=
  modEq_rfl.sub h

protected theorem add_right (c : α) (h : a ≡ b [PMOD p]) : a + c ≡ b + c [PMOD p] :=
  h.add modEq_rfl

protected theorem sub_right (c : α) (h : a ≡ b [PMOD p]) : a - c ≡ b - c [PMOD p] :=
  h.sub modEq_rfl

protected theorem add_left_cancel' (c : α) : c + a ≡ c + b [PMOD p] → a ≡ b [PMOD p] :=
  modEq_rfl.add_left_cancel

protected theorem add_right_cancel' (c : α) : a + c ≡ b + c [PMOD p] → a ≡ b [PMOD p] :=
  modEq_rfl.add_right_cancel

protected theorem sub_left_cancel' (c : α) : c - a ≡ c - b [PMOD p] → a ≡ b [PMOD p] :=
  modEq_rfl.sub_left_cancel

protected theorem sub_right_cancel' (c : α) : a - c ≡ b - c [PMOD p] → a ≡ b [PMOD p] :=
  modEq_rfl.sub_right_cancel

end ModEq

theorem modEq_sub_iff_add_modEq' : a ≡ b - c [PMOD p] ↔ c + a ≡ b [PMOD p] := by
  simp [ModEq, sub_sub]

theorem modEq_sub_iff_add_modEq : a ≡ b - c [PMOD p] ↔ a + c ≡ b [PMOD p] :=
  modEq_sub_iff_add_modEq'.trans <| by rw [add_comm]

theorem sub_modEq_iff_modEq_add' : a - b ≡ c [PMOD p] ↔ a ≡ b + c [PMOD p] :=
  modEq_comm.trans <| modEq_sub_iff_add_modEq'.trans modEq_comm

theorem sub_modEq_iff_modEq_add : a - b ≡ c [PMOD p] ↔ a ≡ c + b [PMOD p] :=
  modEq_comm.trans <| modEq_sub_iff_add_modEq.trans modEq_comm

@[simp]
theorem sub_modEq_zero : a - b ≡ 0 [PMOD p] ↔ a ≡ b [PMOD p] := by simp [sub_modEq_iff_modEq_add]

@[simp]
theorem add_modEq_left : a + b ≡ a [PMOD p] ↔ b ≡ 0 [PMOD p] := by simp [← modEq_sub_iff_add_modEq']

@[simp]
theorem add_modEq_right : a + b ≡ b [PMOD p] ↔ a ≡ 0 [PMOD p] := by simp [← modEq_sub_iff_add_modEq]

theorem modEq_iff_eq_add_zsmul : a ≡ b [PMOD p] ↔ ∃ z : ℤ, b = a + z • p := by
  simp_rw [ModEq, sub_eq_iff_eq_add']

theorem not_modEq_iff_ne_add_zsmul : ¬a ≡ b [PMOD p] ↔ ∀ z : ℤ, b ≠ a + z • p := by
  rw [modEq_iff_eq_add_zsmul, not_exists]

theorem modEq_iff_eq_mod_zmultiples : a ≡ b [PMOD p] ↔ (b : α ⧸ AddSubgroup.zmultiples p) = a := by
  simp_rw [modEq_iff_eq_add_zsmul, QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_zmultiples_iff,
    eq_sub_iff_add_eq', eq_comm]

theorem not_modEq_iff_ne_mod_zmultiples :
    ¬a ≡ b [PMOD p] ↔ (b : α ⧸ AddSubgroup.zmultiples p) ≠ a :=
  modEq_iff_eq_mod_zmultiples.not

end AddCommGroup

@[simp]
theorem modEq_iff_int_modEq {a b z : ℤ} : a ≡ b [PMOD z] ↔ a ≡ b [ZMOD z] := by
  simp [ModEq, dvd_iff_exists_eq_mul_left, Int.modEq_iff_dvd]

section AddCommGroupWithOne

variable [AddCommGroupWithOne α] [CharZero α]

@[simp, norm_cast]
theorem intCast_modEq_intCast {a b z : ℤ} : a ≡ b [PMOD (z : α)] ↔ a ≡ b [PMOD z] := by
  simp_rw [ModEq, ← Int.cast_mul_eq_zsmul_cast]
  norm_cast

@[simp, norm_cast]
lemma intCast_modEq_intCast' {a b : ℤ} {n : ℕ} : a ≡ b [PMOD (n : α)] ↔ a ≡ b [PMOD (n : ℤ)] := by
  simpa using intCast_modEq_intCast (α := α) (z := n)

@[simp, norm_cast]
theorem natCast_modEq_natCast {a b n : ℕ} : a ≡ b [PMOD (n : α)] ↔ a ≡ b [MOD n] := by
  simp_rw [← Int.natCast_modEq_iff, ← modEq_iff_int_modEq, ← @intCast_modEq_intCast α,
    Int.cast_natCast]

alias ⟨ModEq.of_intCast, ModEq.intCast⟩ := intCast_modEq_intCast

alias ⟨_root_.Nat.ModEq.of_natCast, ModEq.natCast⟩ := natCast_modEq_natCast

end AddCommGroupWithOne

section DivisionRing
variable [DivisionRing α] {a b c p : α}

@[simp] lemma div_modEq_div (hc : c ≠ 0) : a / c ≡ b / c [PMOD p] ↔ a ≡ b [PMOD (p * c)] := by
  simp [ModEq, ← sub_div, div_eq_iff hc, mul_assoc]

@[simp] lemma mul_modEq_mul_right (hc : c ≠ 0) : a * c ≡ b * c [PMOD p] ↔ a ≡ b [PMOD (p / c)] := by
  rw [div_eq_mul_inv, ← div_modEq_div (inv_ne_zero hc), div_inv_eq_mul, div_inv_eq_mul]

end DivisionRing

section Field
variable [Field α] {a b c p : α}

@[simp] lemma mul_modEq_mul_left (hc : c ≠ 0) : c * a ≡ c * b [PMOD p] ↔ a ≡ b [PMOD (p / c)] := by
  simp [mul_comm c, hc]

end Field
end AddCommGroup
