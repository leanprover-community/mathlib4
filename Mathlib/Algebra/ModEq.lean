/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Int.ModEq
public import Mathlib.GroupTheory.QuotientGroup.Defs

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

public section

assert_not_exists Module

namespace AddCommGroup

section AddCommMonoid

variable {M : Type*} [AddCommMonoid M] {a b c d p : M}

/-- `a ≡ b [PMOD p]` means that `b` is congruent to `a` modulo `p`.

Equivalently (as shown in `Algebra.Order.ToIntervalMod`), `b` does not lie in the open interval
`(a, a + p)` modulo `p`, or `toIcoMod hp a` disagrees with `toIocMod hp a` at `b`, or
`toIcoDiv hp a` disagrees with `toIocDiv hp a` at `b`. -/
def ModEq (p a b : M) : Prop :=
  ∃ m n : ℕ, m • p + a = n • p + b

@[inherit_doc]
notation:50 a " ≡ " b " [PMOD " p "]" => ModEq p a b

theorem modEq_iff_nsmul : a ≡ b [PMOD p] ↔ ∃ m n : ℕ, m • p + a = n • p + b := by
  rfl

@[refl, simp]
theorem modEq_refl (a : M) : a ≡ a [PMOD p] :=
  ⟨0, 0, by simp⟩

theorem modEq_rfl : a ≡ a [PMOD p] :=
  modEq_refl _

instance : Std.Refl (ModEq p) := ⟨modEq_refl⟩

@[symm]
protected theorem ModEq.symm (h : a ≡ b [PMOD p]) : b ≡ a [PMOD p] := by
  rw [modEq_iff_nsmul] at *
  rcases h with ⟨m, n, h⟩
  exact ⟨n, m, h.symm⟩

instance : Std.Symm (ModEq p) := ⟨fun _ _ ↦ .symm⟩

theorem modEq_comm : a ≡ b [PMOD p] ↔ b ≡ a [PMOD p] := ⟨.symm, .symm⟩

@[trans]
protected theorem ModEq.trans (hab : a ≡ b [PMOD p]) (hbc : b ≡ c [PMOD p]) :
    a ≡ c [PMOD p] := by
  rw [modEq_iff_nsmul] at *
  rcases hab with ⟨m, n, hab⟩
  rcases hbc with ⟨k, l, hbc⟩
  use k + m, n + l
  rw [add_nsmul, add_assoc, hab, add_nsmul, add_assoc, ← hbc, add_left_comm]

instance : IsTrans M (ModEq p) := ⟨fun _ _ _ ↦ .trans⟩

@[simp]
theorem modEq_zero : a ≡ b [PMOD 0] ↔ a = b := by simp [modEq_iff_nsmul]

@[simp]
theorem self_modEq_zero : p ≡ 0 [PMOD p] :=
  ⟨0, 1, by simp⟩

theorem add_nsmul_modEq (n : ℕ) : a + n • p ≡ a [PMOD p] :=
  ⟨0, n, by simp [add_comm]⟩

theorem nsmul_add_modEq (n : ℕ) : n • p + a ≡ a [PMOD p] :=
  ⟨0, n, by simp⟩

protected theorem ModEq.add (hab : a ≡ b [PMOD p]) (hcd : c ≡ d [PMOD p]) :
    a + c ≡ b + d [PMOD p] := by
  rw [modEq_iff_nsmul] at *
  rcases hab with ⟨k, l, hab⟩
  rcases hcd with ⟨m, n, hcd⟩
  use k + m, l + n
  rw [add_nsmul, add_add_add_comm, hab, hcd, add_nsmul, add_add_add_comm]

protected theorem ModEq.of_nsmul {n : ℕ} : a ≡ b [PMOD n • p] → a ≡ b [PMOD p] := fun ⟨k, l, h⟩ =>
  ⟨k * n, l * n, by simpa [mul_nsmul']⟩

protected theorem ModEq.nsmul {n : ℕ} (h : a ≡ b [PMOD p]) : n • a ≡ n • b [PMOD n • p] := by
  rw [modEq_iff_nsmul] at *
  rcases h with ⟨k, l, h⟩
  use k, l
  rw [← mul_nsmul, mul_nsmul', ← nsmul_add, h, nsmul_add, ← mul_nsmul, mul_nsmul']

@[simp]
theorem nsmul_modEq_nsmul [IsAddTorsionFree M] {n : ℕ} (hn : n ≠ 0) :
    n • a ≡ n • b [PMOD n • p] ↔ a ≡ b [PMOD p] := by
  simp only [modEq_iff_nsmul, ← mul_nsmul _ n, mul_nsmul' _ n, ← nsmul_add, nsmul_right_inj hn]

alias ⟨ModEq.nsmul_cancel, _⟩ := nsmul_modEq_nsmul

end AddCommMonoid

section AddCancelCommMonoid

variable {M : Type*} [AddCancelCommMonoid M] {a b c d p : M}

namespace ModEq

@[simp]
protected theorem add_iff_left (h : a ≡ b [PMOD p]) :
    a + c ≡ b + d [PMOD p] ↔ c ≡ d [PMOD p] := by
  refine ⟨fun hadd ↦ ?_, h.add⟩
  rw [modEq_iff_nsmul] at *
  rcases h with ⟨k, l, h⟩
  rcases hadd with ⟨m, n, hadd⟩
  use m + l, n + k
  apply add_right_cancel (b := a)
  rw [add_assoc, add_comm c, add_nsmul, add_right_comm, hadd, ← add_assoc, add_right_comm _ b,
    add_right_comm _ b, add_assoc, ← h, add_add_add_comm, add_nsmul, ← add_assoc]

@[simp]
protected theorem add_iff_right (h : c ≡ d [PMOD p]) :
    a + c ≡ b + d [PMOD p] ↔ a ≡ b [PMOD p] := by
  simpa only [add_comm c, add_comm d] using h.add_iff_left

protected alias ⟨add_left_cancel, _⟩ := ModEq.add_iff_left

protected alias ⟨add_right_cancel, _⟩ := ModEq.add_iff_right

end ModEq

end AddCancelCommMonoid

section AddCommGroup

variable {G : Type*} [AddCommGroup G] {p a a₁ a₂ b b₁ b₂ c : G} {n : ℕ} {z : ℤ}

theorem modEq_iff_zsmul : a ≡ b [PMOD p] ↔ ∃ m : ℤ, m • p = b - a := by
  rw [modEq_iff_nsmul]
  constructor
  · rintro ⟨m, n, h⟩
    use m - n
    rw [sub_zsmul, ← sub_eq_add_neg, sub_eq_sub_iff_add_eq_add, add_comm b]
    exact mod_cast h
  · rintro ⟨m, h⟩
    use m.toNat, (-m).toNat
    rwa [add_comm _ b, ← sub_eq_sub_iff_add_eq_add, ← natCast_zsmul, ← natCast_zsmul,
      sub_eq_add_neg, ← sub_zsmul, m.toNat_sub_toNat_neg]

theorem modEq_iff_zsmul' : a ≡ b [PMOD p] ↔ ∃ m : ℤ, b - a = m • p := by
  simp only [modEq_iff_zsmul, eq_comm]

@[simp]
theorem neg_modEq_neg : -a ≡ -b [PMOD p] ↔ a ≡ b [PMOD p] :=
  modEq_comm.trans <| by simp [modEq_iff_zsmul, neg_add_eq_sub]

alias ⟨ModEq.of_neg, ModEq.neg⟩ := neg_modEq_neg

@[simp]
theorem modEq_neg : a ≡ b [PMOD -p] ↔ a ≡ b [PMOD p] :=
  modEq_comm.trans <| by simp [modEq_iff_zsmul, neg_eq_iff_eq_neg]

alias ⟨ModEq.of_neg', ModEq.neg'⟩ := modEq_neg

theorem modEq_sub (a b : G) : a ≡ b [PMOD b - a] :=
  ⟨1, 0, by simp⟩

@[simp]
theorem zsmul_modEq_zero (z : ℤ) : z • p ≡ 0 [PMOD p] :=
  modEq_iff_zsmul.mpr ⟨-z, by simp⟩

theorem add_zsmul_modEq (z : ℤ) : a + z • p ≡ a [PMOD p] :=
  modEq_iff_zsmul.mpr ⟨-z, by simp⟩

theorem zsmul_add_modEq (z : ℤ) : z • p + a ≡ a [PMOD p] :=
  modEq_iff_zsmul.mpr ⟨-z, by simp⟩

namespace ModEq

protected theorem add_zsmul (z : ℤ) : a ≡ b [PMOD p] → a + z • p ≡ b [PMOD p] :=
  (add_zsmul_modEq _).trans

protected theorem zsmul_add (z : ℤ) : a ≡ b [PMOD p] → z • p + a ≡ b [PMOD p] :=
  (zsmul_add_modEq _).trans

protected theorem add_nsmul (n : ℕ) : a ≡ b [PMOD p] → a + n • p ≡ b [PMOD p] :=
  (add_nsmul_modEq _).trans

protected theorem nsmul_add (n : ℕ) : a ≡ b [PMOD p] → n • p + a ≡ b [PMOD p] :=
  (nsmul_add_modEq _).trans

protected theorem of_zsmul (h : a ≡ b [PMOD z • p]) : a ≡ b [PMOD p] := by
  rw [modEq_iff_zsmul] at *
  rcases h with ⟨m, h⟩
  simp [← h, ← mul_zsmul]

protected theorem zsmul (h : a ≡ b [PMOD p]) : z • a ≡ z • b [PMOD z • p] := by
  rw [modEq_iff_zsmul] at *
  rcases h with ⟨m, h⟩
  use m
  rw [← zsmul_sub, ← h, ← mul_zsmul, ← mul_zsmul']

end ModEq

@[simp]
theorem zsmul_modEq_zsmul [IsAddTorsionFree G] (hn : z ≠ 0) :
    z • a ≡ z • b [PMOD z • p] ↔ a ≡ b [PMOD p] := by
  simp [modEq_iff_zsmul, ← zsmul_sub, zsmul_comm, zsmul_right_inj hn]

alias ⟨ModEq.zsmul_cancel, _⟩ := zsmul_modEq_zsmul

namespace ModEq

@[simp]
protected theorem sub_iff_left (h : a₁ ≡ b₁ [PMOD p]) :
    a₁ - a₂ ≡ b₁ - b₂ [PMOD p] ↔ a₂ ≡ b₂ [PMOD p] := by
  simp [sub_eq_add_neg, h]

@[simp]
protected theorem sub_iff_right (h : a₂ ≡ b₂ [PMOD p]) :
    a₁ - a₂ ≡ b₁ - b₂ [PMOD p] ↔ a₁ ≡ b₁ [PMOD p] := by
  simp [h, sub_eq_add_neg]

protected alias ⟨sub_left_cancel, sub⟩ := ModEq.sub_iff_left

protected alias ⟨sub_right_cancel, _⟩ := ModEq.sub_iff_right

protected theorem add_left (c : G) (h : a ≡ b [PMOD p]) : c + a ≡ c + b [PMOD p] :=
  modEq_rfl.add h

protected theorem sub_left (c : G) (h : a ≡ b [PMOD p]) : c - a ≡ c - b [PMOD p] :=
  modEq_rfl.sub h

protected theorem add_right (c : G) (h : a ≡ b [PMOD p]) : a + c ≡ b + c [PMOD p] :=
  h.add modEq_rfl

protected theorem sub_right (c : G) (h : a ≡ b [PMOD p]) : a - c ≡ b - c [PMOD p] :=
  h.sub modEq_rfl

protected theorem add_left_cancel' (c : G) : c + a ≡ c + b [PMOD p] → a ≡ b [PMOD p] :=
  modEq_rfl.add_left_cancel

protected theorem add_right_cancel' (c : G) : a + c ≡ b + c [PMOD p] → a ≡ b [PMOD p] :=
  modEq_rfl.add_right_cancel

protected theorem sub_left_cancel' (c : G) : c - a ≡ c - b [PMOD p] → a ≡ b [PMOD p] :=
  modEq_rfl.sub_left_cancel

protected theorem sub_right_cancel' (c : G) : a - c ≡ b - c [PMOD p] → a ≡ b [PMOD p] :=
  modEq_rfl.sub_right_cancel

end ModEq

theorem modEq_sub_iff_add_modEq' : a ≡ b - c [PMOD p] ↔ c + a ≡ b [PMOD p] := by
  simp [modEq_iff_zsmul', sub_sub]

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

-- this matches `Int.modEq_iff_add_fac`
theorem modEq_iff_eq_add_zsmul : a ≡ b [PMOD p] ↔ ∃ z : ℤ, b = a + z • p := by
  simp_rw [modEq_iff_zsmul', sub_eq_iff_eq_add']

-- this roughly matches `Int.modEq_zero_iff_dvd`
theorem modEq_zero_iff_eq_zsmul : a ≡ 0 [PMOD p] ↔ ∃ z : ℤ, a = z • p := by
  rw [modEq_comm, modEq_iff_eq_add_zsmul]
  simp_rw [zero_add]

theorem not_modEq_iff_ne_add_zsmul : ¬a ≡ b [PMOD p] ↔ ∀ z : ℤ, b ≠ a + z • p := by
  rw [modEq_iff_eq_add_zsmul, not_exists]

theorem modEq_iff_eq_mod_zmultiples : a ≡ b [PMOD p] ↔ (a : G ⧸ AddSubgroup.zmultiples p) = b := by
  rw [modEq_comm]
  simp_rw [modEq_iff_eq_add_zsmul, QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_zmultiples_iff,
    eq_sub_iff_add_eq', eq_comm]

theorem not_modEq_iff_ne_mod_zmultiples :
    ¬a ≡ b [PMOD p] ↔ (a : G ⧸ AddSubgroup.zmultiples p) ≠ b :=
  modEq_iff_eq_mod_zmultiples.not

/-- If `a ≡ b [PMOD p]`, then mod `n • p` there are `n` cases. -/
theorem modEq_nsmul_cases (n : ℕ) (hn : n ≠ 0) :
    a ≡ b [PMOD p] ↔ ∃ i < n, a ≡ b + i • p [PMOD (n • p)] := by
  simp_rw [← sub_modEq_iff_modEq_add, modEq_comm (b := b)]
  simp_rw [modEq_iff_zsmul', sub_right_comm, sub_eq_iff_eq_add (b := _ • _), ← natCast_zsmul,
    ← mul_zsmul, ← add_zsmul]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨(k % n).toNat, ?_⟩
    rw [← Int.ofNat_lt, Int.toNat_of_nonneg (Int.emod_nonneg _ (mod_cast hn))]
    refine ⟨?_, k / n, ?_⟩
    · refine Int.emod_lt_of_pos _ ?_
      lia
    · rw [hk, Int.ediv_mul_add_emod]
  · rintro ⟨k, _, j, hj⟩
    rw [hj]
    exact ⟨_, rfl⟩

alias ⟨ModEq.nsmul_cases, _⟩ := AddCommGroup.modEq_nsmul_cases

end AddCommGroup

@[simp]
theorem modEq_iff_int_modEq {a b z : ℤ} : a ≡ b [PMOD z] ↔ a ≡ b [ZMOD z] := by
  simp [modEq_iff_zsmul, dvd_iff_exists_eq_mul_left, Int.modEq_iff_dvd, eq_comm]

section AddCommGroupWithOne

variable {G : Type*} [AddCommGroupWithOne G] [CharZero G]

@[simp, norm_cast]
theorem intCast_modEq_intCast {a b z : ℤ} : a ≡ b [PMOD (z : G)] ↔ a ≡ b [PMOD z] := by
  simp_rw [modEq_iff_zsmul', ← Int.cast_mul_eq_zsmul_cast]
  norm_cast

@[simp, norm_cast]
lemma intCast_modEq_intCast' {a b : ℤ} {n : ℕ} : a ≡ b [PMOD (n : G)] ↔ a ≡ b [PMOD (n : ℤ)] := by
  simpa using intCast_modEq_intCast (G := G) (z := n)

@[simp, norm_cast]
theorem natCast_modEq_natCast {a b n : ℕ} : a ≡ b [PMOD (n : G)] ↔ a ≡ b [MOD n] := by
  simp_rw [← Int.natCast_modEq_iff, ← modEq_iff_int_modEq, ← @intCast_modEq_intCast G,
    Int.cast_natCast]

alias ⟨ModEq.of_intCast, ModEq.intCast⟩ := intCast_modEq_intCast

alias ⟨_root_.Nat.ModEq.of_natCast, ModEq.natCast⟩ := natCast_modEq_natCast

end AddCommGroupWithOne

section DivisionRing
variable {K : Type*} [DivisionRing K] {a b c p : K}

@[simp] lemma div_modEq_div (hc : c ≠ 0) : a / c ≡ b / c [PMOD p] ↔ a ≡ b [PMOD (p * c)] := by
  simp [modEq_iff_zsmul, ← sub_div, eq_div_iff hc, mul_assoc]

@[simp] lemma mul_modEq_mul_right (hc : c ≠ 0) : a * c ≡ b * c [PMOD p] ↔ a ≡ b [PMOD (p / c)] := by
  rw [div_eq_mul_inv, ← div_modEq_div (inv_ne_zero hc), div_inv_eq_mul, div_inv_eq_mul]

end DivisionRing

section Field
variable {K : Type*} [Field K] {a b c p : K}

@[simp] lemma mul_modEq_mul_left (hc : c ≠ 0) : c * a ≡ c * b [PMOD p] ↔ a ≡ b [PMOD (p / c)] := by
  simp [mul_comm c, hc]

end Field
end AddCommGroup
