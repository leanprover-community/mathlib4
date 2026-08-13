/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Yuyang Zhao
-/
module

public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Tactic.Bound.Attribute
public import Mathlib.Tactic.Monotonicity.Attr

import Mathlib.Data.Set.Function
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Util.CompileInductive

/-!
# Lemmas on the monotone multiplication typeclasses

This file builds on `Mathlib/Algebra/Order/GroupWithZero/Unbundled/Defs.lean` by proving several
lemmas that do not immediately follow from the typeclass specifications.
-/

public section

open Function

variable {α M₀ G₀ : Type*}

section MulZeroClass

variable [MulZeroClass α] {a b c d : α}

section Preorder

variable [Preorder α]

/-- Assumes left covariance. -/
theorem Left.mul_pos [PosMulStrictMono α] (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  simpa only [mul_zero] using mul_lt_mul_of_pos_left hb ha

alias mul_pos := Left.mul_pos

theorem mul_neg_of_pos_of_neg [PosMulStrictMono α] (ha : 0 < a) (hb : b < 0) : a * b < 0 := by
  simpa only [mul_zero] using mul_lt_mul_of_pos_left hb ha

@[simp]
theorem mul_pos_iff_of_pos_left [PosMulStrictMono α] [PosMulReflectLT α] (h : 0 < a) :
    0 < a * b ↔ 0 < b := by simpa using mul_lt_mul_iff_right₀ (b := 0) h

/-- Assumes right covariance. -/
theorem Right.mul_pos [MulPosStrictMono α] (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  simpa only [zero_mul] using mul_lt_mul_of_pos_right ha hb

theorem mul_neg_of_neg_of_pos [MulPosStrictMono α] (ha : a < 0) (hb : 0 < b) : a * b < 0 := by
  simpa only [zero_mul] using mul_lt_mul_of_pos_right ha hb

@[simp]
theorem mul_pos_iff_of_pos_right [MulPosStrictMono α] [MulPosReflectLT α] (h : 0 < b) :
    0 < a * b ↔ 0 < a := by simpa using mul_lt_mul_iff_left₀ (b := 0) h

/-- Assumes left covariance. -/
theorem Left.mul_nonneg [PosMulMono α] (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  simpa only [mul_zero] using mul_le_mul_of_nonneg_left hb ha

alias mul_nonneg := Left.mul_nonneg

theorem mul_nonpos_of_nonneg_of_nonpos [PosMulMono α] (ha : 0 ≤ a) (hb : b ≤ 0) : a * b ≤ 0 := by
  simpa only [mul_zero] using mul_le_mul_of_nonneg_left hb ha

/-- Assumes right covariance. -/
theorem Right.mul_nonneg [MulPosMono α] (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  simpa only [zero_mul] using mul_le_mul_of_nonneg_right ha hb

theorem mul_nonpos_of_nonpos_of_nonneg [MulPosMono α] (ha : a ≤ 0) (hb : 0 ≤ b) : a * b ≤ 0 := by
  simpa only [zero_mul] using mul_le_mul_of_nonneg_right ha hb

theorem pos_of_mul_pos_right [PosMulReflectLT α] (h : 0 < a * b) (ha : 0 ≤ a) : 0 < b :=
  lt_of_mul_lt_mul_left ((mul_zero a).symm ▸ h : a * 0 < a * b) ha

theorem pos_of_mul_pos_left [MulPosReflectLT α] (h : 0 < a * b) (hb : 0 ≤ b) : 0 < a :=
  lt_of_mul_lt_mul_right ((zero_mul b).symm ▸ h : 0 * b < a * b) hb

theorem pos_iff_pos_of_mul_pos [PosMulReflectLT α] [MulPosReflectLT α] (hab : 0 < a * b) :
    0 < a ↔ 0 < b :=
  ⟨pos_of_mul_pos_right hab ∘ le_of_lt, pos_of_mul_pos_left hab ∘ le_of_lt⟩

/-- Assumes left strict covariance. -/
theorem Left.mul_lt_mul_of_nonneg [PosMulStrictMono α] [MulPosMono α]
    (h₁ : a < b) (h₂ : c < d) (a0 : 0 ≤ a) (c0 : 0 ≤ c) : a * c < b * d :=
  mul_lt_mul_of_le_of_lt_of_nonneg_of_pos h₁.le h₂ c0 (a0.trans_lt h₁)

/-- Assumes right strict covariance. -/
theorem Right.mul_lt_mul_of_nonneg [PosMulMono α] [MulPosStrictMono α]
    (h₁ : a < b) (h₂ : c < d) (a0 : 0 ≤ a) (c0 : 0 ≤ c) : a * c < b * d :=
  mul_lt_mul_of_lt_of_le_of_nonneg_of_pos h₁ h₂.le a0 (c0.trans_lt h₂)

alias mul_lt_mul_of_nonneg := Left.mul_lt_mul_of_nonneg

alias mul_lt_mul'' := Left.mul_lt_mul_of_nonneg
attribute [gcongr] mul_lt_mul''

theorem mul_self_le_mul_self [PosMulMono α] [MulPosMono α] (ha : 0 ≤ a) (hab : a ≤ b) :
    a * a ≤ b * b :=
  mul_le_mul hab hab ha <| ha.trans hab

end Preorder

section PartialOrder

/-- Local notation for the positive elements of a type `α`. -/
local notation3 "α>0" => { x : α // 0 < x }

variable [PartialOrder α]

theorem posMulMono_iff_covariant_pos :
    PosMulMono α ↔ CovariantClass α>0 α (fun x y => x * y) (· ≤ ·) where
  mp _ := PosMulMono.to_covariantClass_pos_mul_le
  mpr h :=
    { mul_le_mul_of_nonneg_left a ha b c hbc := by
        obtain ha | ha := ha.eq_or_lt
        · simp [← ha]
        · exact @CovariantClass.elim α>0 α (fun x y => x * y) (· ≤ ·) _ ⟨_, ha⟩ _ _ hbc }

theorem mulPosMono_iff_covariant_pos :
    MulPosMono α ↔ CovariantClass α>0 α (fun x y => y * x) (· ≤ ·) where
  mp _ := MulPosMono.to_covariantClass_pos_mul_le
  mpr h :=
    { mul_le_mul_of_nonneg_right a ha b c hbc := by
        obtain ha | ha := ha.eq_or_lt
        · simp [← ha]
        · exact @CovariantClass.elim α>0 α (fun x y => y * x) (· ≤ ·) _ ⟨_, ha⟩ _ _ hbc }

theorem posMulReflectLT_iff_contravariant_pos :
    PosMulReflectLT α ↔ ContravariantClass α>0 α (fun x y => x * y) (· < ·) :=
  ⟨@PosMulReflectLT.to_contravariantClass_pos_mul_lt _ _ _ _, fun h =>
    { elim a b c h := by
        obtain ha | ha := a.prop.eq_or_lt
        · simp [← ha] at h
        · exact @ContravariantClass.elim α>0 α (fun x y => x * y) (· < ·) _ ⟨_, ha⟩ _ _ h }⟩

theorem mulPosReflectLT_iff_contravariant_pos :
    MulPosReflectLT α ↔ ContravariantClass α>0 α (fun x y => y * x) (· < ·) :=
  ⟨@MulPosReflectLT.to_contravariantClass_pos_mul_lt _ _ _ _, fun h =>
    { elim a b c h := by
        obtain ha | ha := a.prop.eq_or_lt
        · simp [← ha] at h
        · exact @ContravariantClass.elim α>0 α (fun x y => y * x) (· < ·) _ ⟨_, ha⟩ _ _ h }⟩

-- see Note [lower instance priority]
instance (priority := 100) PosMulStrictMono.toPosMulMono [PosMulStrictMono α] : PosMulMono α :=
  posMulMono_iff_covariant_pos.2 (covariantClass_le_of_lt _ _ _)

-- see Note [lower instance priority]
instance (priority := 100) MulPosStrictMono.toMulPosMono [MulPosStrictMono α] : MulPosMono α :=
  mulPosMono_iff_covariant_pos.2 (covariantClass_le_of_lt _ _ _)

-- see Note [lower instance priority]
instance (priority := 100) PosMulReflectLE.toPosMulReflectLT [PosMulReflectLE α] :
    PosMulReflectLT α :=
  posMulReflectLT_iff_contravariant_pos.2
    ⟨fun a b c h =>
      (le_of_mul_le_mul_of_pos_left h.le a.2).lt_of_ne <| by
        rintro rfl
        simp at h⟩

-- see Note [lower instance priority]
instance (priority := 100) MulPosReflectLE.toMulPosReflectLT [MulPosReflectLE α] :
    MulPosReflectLT α :=
  mulPosReflectLT_iff_contravariant_pos.2
    ⟨fun a b c h =>
      (le_of_mul_le_mul_of_pos_right h.le a.2).lt_of_ne <| by
        rintro rfl
        simp at h⟩

theorem mul_left_cancel_iff_of_pos [PosMulReflectLE α] (a0 : 0 < a) : a * b = a * c ↔ b = c :=
  ⟨fun h => (le_of_mul_le_mul_of_pos_left h.le a0).antisymm <|
    le_of_mul_le_mul_of_pos_left h.ge a0, congr_arg _⟩

theorem mul_right_cancel_iff_of_pos [MulPosReflectLE α] (b0 : 0 < b) : a * b = c * b ↔ a = c :=
  ⟨fun h => (le_of_mul_le_mul_of_pos_right h.le b0).antisymm <|
    le_of_mul_le_mul_of_pos_right h.ge b0, congr_arg (· * b)⟩

theorem mul_eq_mul_iff_eq_and_eq_of_pos [PosMulStrictMono α] [MulPosStrictMono α]
    (hab : a ≤ b) (hcd : c ≤ d) (a0 : 0 < a) (d0 : 0 < d) :
    a * c = b * d ↔ a = b ∧ c = d := by
  refine ⟨fun h ↦ ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  simp only [eq_iff_le_not_lt, hab, hcd, true_and]
  refine ⟨fun hab ↦ h.not_lt ?_, fun hcd ↦ h.not_lt ?_⟩
  · exact (mul_le_mul_of_nonneg_left hcd a0.le).trans_lt (mul_lt_mul_of_pos_right hab d0)
  · exact (mul_lt_mul_of_pos_left hcd a0).trans_le (mul_le_mul_of_nonneg_right hab d0.le)

theorem mul_eq_mul_iff_eq_and_eq_of_pos' [PosMulStrictMono α] [MulPosStrictMono α]
    (hab : a ≤ b) (hcd : c ≤ d) (b0 : 0 < b) (c0 : 0 < c) :
    a * c = b * d ↔ a = b ∧ c = d := by
  refine ⟨fun h ↦ ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  simp only [eq_iff_le_not_lt, hab, hcd, true_and]
  refine ⟨fun hab ↦ h.not_lt ?_, fun hcd ↦ h.not_lt ?_⟩
  · exact (mul_lt_mul_of_pos_right hab c0).trans_le (mul_le_mul_of_nonneg_left hcd b0.le)
  · exact (mul_le_mul_of_nonneg_right hab c0.le).trans_lt (mul_lt_mul_of_pos_left hcd b0)

theorem eq_and_eq_of_pos_of_le_of_mul_le_mul [PosMulReflectLE α] [MulPosReflectLE α]
    [PosMulMono α] [MulPosMono α] (ha : 0 < a) (hc : 0 < c) (hab : a ≤ b) (hcd : c ≤ d)
    (h : b * d ≤ a * c) : a = b ∧ c = d := by
  refine ⟨le_antisymm hab ?_, le_antisymm hcd ?_⟩
  · grw [hcd] at h
    · exact le_of_mul_le_mul_of_pos_right h <| hc.trans_le hcd
    · exact ha.le
  · grw [hab] at h
    · exact le_of_mul_le_mul_of_pos_left h <| ha.trans_le hab
    · exact hc.le

theorem PosMulMono.toPosMulStrictMono [IsLeftCancelMulZero α] [PosMulMono α] :
    PosMulStrictMono α where
  mul_lt_mul_of_pos_left _a ha _b _c hbc :=
    (mul_le_mul_of_nonneg_left hbc.le ha.le).lt_of_ne (hbc.ne ∘ mul_left_cancel₀ ha.ne')

theorem posMulMono_iff_posMulStrictMono [IsLeftCancelMulZero α] :
    PosMulMono α ↔ PosMulStrictMono α :=
  ⟨(·.toPosMulStrictMono), (·.toPosMulMono)⟩

theorem MulPosMono.toMulPosStrictMono [IsRightCancelMulZero α] [MulPosMono α] :
    MulPosStrictMono α where
  mul_lt_mul_of_pos_right _a ha _b _c hbc :=
    (mul_le_mul_of_nonneg_right hbc.le ha.le).lt_of_ne (hbc.ne ∘ mul_right_cancel₀ ha.ne')

theorem mulPosMono_iff_mulPosStrictMono [IsRightCancelMulZero α] :
    MulPosMono α ↔ MulPosStrictMono α :=
  ⟨(·.toMulPosStrictMono), (·.toMulPosMono)⟩

theorem PosMulReflectLT.toPosMulReflectLE [IsLeftCancelMulZero α] [PosMulReflectLT α] :
    PosMulReflectLE α where
  elim := fun x _ _ h =>
    h.eq_or_lt.elim (le_of_eq ∘ mul_left_cancel₀ x.2.ne.symm) fun h' =>
      (lt_of_mul_lt_mul_left h' x.2.le).le

theorem posMulReflectLE_iff_posMulReflectLT [IsLeftCancelMulZero α] :
    PosMulReflectLE α ↔ PosMulReflectLT α :=
  ⟨(·.toPosMulReflectLT), (·.toPosMulReflectLE)⟩

theorem MulPosReflectLT.toMulPosReflectLE [IsRightCancelMulZero α] [MulPosReflectLT α] :
    MulPosReflectLE α where
  elim := fun x _ _ h => h.eq_or_lt.elim (le_of_eq ∘ mul_right_cancel₀ x.2.ne.symm) fun h' =>
    (lt_of_mul_lt_mul_right h' x.2.le).le

theorem mulPosReflectLE_iff_mulPosReflectLT [IsRightCancelMulZero α] :
    MulPosReflectLE α ↔ MulPosReflectLT α :=
  ⟨(·.toMulPosReflectLT), (·.toMulPosReflectLE)⟩

end PartialOrder

section LinearOrder

variable [LinearOrder α]

theorem pos_and_pos_or_neg_and_neg_of_mul_pos [PosMulMono α] [MulPosMono α] (hab : 0 < a * b) :
    0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0 := by
  rcases lt_trichotomy a 0 with (ha | rfl | ha)
  · refine Or.inr ⟨ha, lt_imp_lt_of_le_imp_le (fun hb => ?_) hab⟩
    exact mul_nonpos_of_nonpos_of_nonneg ha.le hb
  · rw [zero_mul] at hab
    exact hab.false.elim
  · refine Or.inl ⟨ha, lt_imp_lt_of_le_imp_le (fun hb => ?_) hab⟩
    exact mul_nonpos_of_nonneg_of_nonpos ha.le hb

theorem neg_of_mul_pos_right [PosMulMono α] [MulPosMono α] (h : 0 < a * b) (ha : a ≤ 0) : b < 0 :=
  ((pos_and_pos_or_neg_and_neg_of_mul_pos h).resolve_left fun h => h.1.not_ge ha).2

theorem neg_of_mul_pos_left [PosMulMono α] [MulPosMono α] (h : 0 < a * b) (ha : b ≤ 0) : a < 0 :=
  ((pos_and_pos_or_neg_and_neg_of_mul_pos h).resolve_left fun h => h.2.not_ge ha).1

theorem neg_iff_neg_of_mul_pos [PosMulMono α] [MulPosMono α] (hab : 0 < a * b) : a < 0 ↔ b < 0 :=
  ⟨neg_of_mul_pos_right hab ∘ le_of_lt, neg_of_mul_pos_left hab ∘ le_of_lt⟩

theorem Left.neg_of_mul_neg_right [PosMulMono α] (h : a * b < 0) (a0 : 0 ≤ a) : b < 0 :=
  lt_of_not_ge fun b0 : b ≥ 0 => (Left.mul_nonneg a0 b0).not_gt h

alias neg_of_mul_neg_right := Left.neg_of_mul_neg_right

theorem Right.neg_of_mul_neg_right [MulPosMono α] (h : a * b < 0) (a0 : 0 ≤ a) : b < 0 :=
  lt_of_not_ge fun b0 : b ≥ 0 => (Right.mul_nonneg a0 b0).not_gt h

theorem Left.neg_of_mul_neg_left [PosMulMono α] (h : a * b < 0) (b0 : 0 ≤ b) : a < 0 :=
  lt_of_not_ge fun a0 : a ≥ 0 => (Left.mul_nonneg a0 b0).not_gt h

alias neg_of_mul_neg_left := Left.neg_of_mul_neg_left

theorem Right.neg_of_mul_neg_left [MulPosMono α] (h : a * b < 0) (b0 : 0 ≤ b) : a < 0 :=
  lt_of_not_ge fun a0 : a ≥ 0 => (Right.mul_nonneg a0 b0).not_gt h

end LinearOrder

end MulZeroClass

section MulOneClass

variable [MulOneClass α] [Zero α] {a b c d : α}

section Preorder

variable [Preorder α]

/-! Lemmas of the form `a ≤ a * b ↔ 1 ≤ b` and `a * b ≤ a ↔ b ≤ 1`, assuming left covariance. -/

lemma one_lt_of_lt_mul_left₀ [PosMulReflectLT α] (ha : 0 ≤ a) (h : a < a * b) : 1 < b :=
  lt_of_mul_lt_mul_left (by simpa) ha

lemma one_lt_of_lt_mul_right₀ [MulPosReflectLT α] (hb : 0 ≤ b) (h : b < a * b) : 1 < a :=
  lt_of_mul_lt_mul_right (by simpa) hb

lemma one_le_of_le_mul_left₀ [PosMulReflectLE α] (ha : 0 < a) (h : a ≤ a * b) : 1 ≤ b :=
  le_of_mul_le_mul_left (by simpa) ha

lemma one_le_of_le_mul_right₀ [MulPosReflectLE α] (hb : 0 < b) (h : b ≤ a * b) : 1 ≤ a :=
  le_of_mul_le_mul_right (by simpa) hb

@[simp]
lemma le_mul_iff_one_le_right [PosMulMono α] [PosMulReflectLE α] (a0 : 0 < a) : a ≤ a * b ↔ 1 ≤ b :=
  Iff.trans (by rw [mul_one]) (mul_le_mul_iff_right₀ a0)

@[simp]
theorem lt_mul_iff_one_lt_right [PosMulStrictMono α] [PosMulReflectLT α] (a0 : 0 < a) :
    a < a * b ↔ 1 < b :=
  Iff.trans (by rw [mul_one]) (mul_lt_mul_iff_right₀ a0)

@[simp]
lemma mul_le_iff_le_one_right [PosMulMono α] [PosMulReflectLE α] (a0 : 0 < a) : a * b ≤ a ↔ b ≤ 1 :=
  Iff.trans (by rw [mul_one]) (mul_le_mul_iff_right₀ a0)

@[simp]
theorem mul_lt_iff_lt_one_right [PosMulStrictMono α] [PosMulReflectLT α] (a0 : 0 < a) :
    a * b < a ↔ b < 1 :=
  Iff.trans (by rw [mul_one]) (mul_lt_mul_iff_right₀ a0)

/-! Lemmas of the form `a ≤ b * a ↔ 1 ≤ b` and `a * b ≤ b ↔ a ≤ 1`, assuming right covariance. -/

@[simp]
lemma le_mul_iff_one_le_left [MulPosMono α] [MulPosReflectLE α] (a0 : 0 < a) : a ≤ b * a ↔ 1 ≤ b :=
  Iff.trans (by rw [one_mul]) (mul_le_mul_iff_left₀ a0)

@[simp]
theorem lt_mul_iff_one_lt_left [MulPosStrictMono α] [MulPosReflectLT α] (a0 : 0 < a) :
    a < b * a ↔ 1 < b :=
  Iff.trans (by rw [one_mul]) (mul_lt_mul_iff_left₀ a0)

@[simp]
lemma mul_le_iff_le_one_left [MulPosMono α] [MulPosReflectLE α] (b0 : 0 < b) : a * b ≤ b ↔ a ≤ 1 :=
  Iff.trans (by rw [one_mul]) (mul_le_mul_iff_left₀ b0)

@[simp]
theorem mul_lt_iff_lt_one_left [MulPosStrictMono α] [MulPosReflectLT α] (b0 : 0 < b) :
    a * b < b ↔ a < 1 :=
  Iff.trans (by rw [one_mul]) (mul_lt_mul_iff_left₀ b0)

/-! Lemmas of the form `1 ≤ b → a ≤ a * b`.

Variants with `< 0` and `≤ 0` instead of `0 <` and `0 ≤` appear in `Mathlib/Algebra/Order/Ring/Defs`
(which imports this file) as they need additional results which are not yet available here. -/

theorem mul_le_of_le_one_left [MulPosMono α] (hb : 0 ≤ b) (h : a ≤ 1) : a * b ≤ b := by
  simpa only [one_mul] using mul_le_mul_of_nonneg_right h hb

theorem le_mul_of_one_le_left [MulPosMono α] (hb : 0 ≤ b) (h : 1 ≤ a) : b ≤ a * b := by
  simpa only [one_mul] using mul_le_mul_of_nonneg_right h hb

theorem mul_le_of_le_one_right [PosMulMono α] (ha : 0 ≤ a) (h : b ≤ 1) : a * b ≤ a := by
  simpa only [mul_one] using mul_le_mul_of_nonneg_left h ha

theorem le_mul_of_one_le_right [PosMulMono α] (ha : 0 ≤ a) (h : 1 ≤ b) : a ≤ a * b := by
  simpa only [mul_one] using mul_le_mul_of_nonneg_left h ha

theorem mul_lt_of_lt_one_left [MulPosStrictMono α] (hb : 0 < b) (h : a < 1) : a * b < b := by
  simpa only [one_mul] using mul_lt_mul_of_pos_right h hb

theorem lt_mul_of_one_lt_left [MulPosStrictMono α] (hb : 0 < b) (h : 1 < a) : b < a * b := by
  simpa only [one_mul] using mul_lt_mul_of_pos_right h hb

theorem mul_lt_of_lt_one_right [PosMulStrictMono α] (ha : 0 < a) (h : b < 1) : a * b < a := by
  simpa only [mul_one] using mul_lt_mul_of_pos_left h ha

theorem lt_mul_of_one_lt_right [PosMulStrictMono α] (ha : 0 < a) (h : 1 < b) : a < a * b := by
  simpa only [mul_one] using mul_lt_mul_of_pos_left h ha

end Preorder

end MulOneClass

section MulZero

variable [Mul M₀] [Zero M₀] [Preorder M₀] [Preorder α] {f g : α → M₀}

lemma Monotone.mul [PosMulMono M₀] [MulPosMono M₀] (hf : Monotone f) (hg : Monotone g)
    (hf₀ : ∀ x, 0 ≤ f x) (hg₀ : ∀ x, 0 ≤ g x) : Monotone (f * g) :=
  fun _ _ h ↦ mul_le_mul (hf h) (hg h) (hg₀ _) (hf₀ _)

lemma MonotoneOn.mul [PosMulMono M₀] [MulPosMono M₀] {s : Set α} (hf : MonotoneOn f s)
    (hg : MonotoneOn g s) (hf₀ : ∀ x ∈ s, 0 ≤ f x) (hg₀ : ∀ x ∈ s, 0 ≤ g x) :
    MonotoneOn (f * g) s :=
  fun _ ha _ hb h ↦ mul_le_mul (hf ha hb h) (hg ha hb h) (hg₀ _ ha) (hf₀ _ hb)

end MulZero

section MonoidWithZero
variable [MonoidWithZero M₀]

section Preorder
variable [Preorder M₀] {a b : M₀} {m n : ℕ}

@[simp] lemma pow_succ_nonneg [PosMulMono M₀] (ha : 0 ≤ a) : ∀ n, 0 ≤ a ^ (n + 1)
  | 0 => (pow_one a).symm ▸ ha
  | _ + 1 => pow_succ a _ ▸ mul_nonneg (pow_succ_nonneg ha _) ha

@[simp] lemma pow_nonneg [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 0 ≤ a) : ∀ n, 0 ≤ a ^ n
  | 0 => pow_zero a ▸ zero_le_one
  | n + 1 => pow_succ a n ▸ mul_nonneg (pow_nonneg ha _) ha

lemma zero_pow_le_one [ZeroLEOneClass M₀] : ∀ n : ℕ, (0 : M₀) ^ n ≤ 1
  | 0 => (pow_zero _).le
  | n + 1 => by rw [zero_pow n.succ_ne_zero]; exact zero_le_one

lemma pow_right_anti₀ [PosMulMono M₀] (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) : Antitone (fun n : ℕ ↦ a ^ n) :=
  antitone_nat_of_succ_le fun n ↦ by
    have : ZeroLEOneClass M₀ := ⟨ha₀.trans ha₁⟩
    rw [← mul_one (a ^ n), pow_succ]
    gcongr
    exact pow_nonneg ha₀ n

lemma pow_le_pow_of_le_one [PosMulMono M₀] (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) {m n : ℕ}
    (hmn : m ≤ n) : a ^ n ≤ a ^ m := pow_right_anti₀ ha₀ ha₁ hmn

lemma pow_le_of_le_one [PosMulMono M₀] (h₀ : 0 ≤ a) (h₁ : a ≤ 1) (hn : n ≠ 0) : a ^ n ≤ a :=
  (pow_one a).subst (pow_le_pow_of_le_one h₀ h₁ (Nat.pos_of_ne_zero hn))

lemma sq_le [PosMulMono M₀] (h₀ : 0 ≤ a) (h₁ : a ≤ 1) : a ^ 2 ≤ a :=
  pow_le_of_le_one h₀ h₁ two_ne_zero

lemma pow_le_one₀ [PosMulMono M₀] {n : ℕ} (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) : a ^ n ≤ 1 :=
  pow_zero a ▸ pow_right_anti₀ ha₀ ha₁ (Nat.zero_le n)

lemma one_le_mul_of_one_le_of_one_le [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (1 : M₀) ≤ a * b := ha.trans <| le_mul_of_one_le_right (zero_le_one.trans ha) hb

lemma one_lt_mul_of_le_of_lt [ZeroLEOneClass M₀] [MulPosMono M₀] (ha : 1 ≤ a) (hb : 1 < b) :
    1 < a * b := hb.trans_le <| le_mul_of_one_le_left (zero_le_one.trans hb.le) ha

lemma one_lt_mul_of_lt_of_le [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 < a) (hb : 1 ≤ b) :
    1 < a * b := ha.trans_le <| le_mul_of_one_le_right (zero_le_one.trans ha.le) hb

alias one_lt_mul := one_lt_mul_of_le_of_lt

lemma mul_lt_one_of_nonneg_of_lt_one_left [PosMulMono M₀] (ha₀ : 0 ≤ a) (ha : a < 1) (hb : b ≤ 1) :
    a * b < 1 := (mul_le_of_le_one_right ha₀ hb).trans_lt ha

lemma mul_lt_one_of_nonneg_of_lt_one_right [MulPosMono M₀] (ha : a ≤ 1) (hb₀ : 0 ≤ b) (hb : b < 1) :
    a * b < 1 := (mul_le_of_le_one_left hb₀ ha).trans_lt hb

@[bound]
protected lemma Bound.one_lt_mul [ZeroLEOneClass M₀] [PosMulMono M₀] [MulPosMono M₀] :
    1 ≤ a ∧ 1 < b ∨ 1 < a ∧ 1 ≤ b → 1 < a * b := by
  rintro (⟨ha, hb⟩ | ⟨ha, hb⟩); exacts [one_lt_mul ha hb, one_lt_mul_of_lt_of_le ha hb]

@[bound]
lemma mul_le_one₀ [MulPosMono M₀] (ha : a ≤ 1) (hb₀ : 0 ≤ b) (hb : b ≤ 1) : a * b ≤ 1 :=
  (mul_le_mul_of_nonneg_right ha hb₀).trans <| by rwa [one_mul]

lemma pow_lt_one₀ [PosMulMono M₀] (h₀ : 0 ≤ a) (h₁ : a < 1) : ∀ {n : ℕ}, n ≠ 0 → a ^ n < 1
  | 0, h => (h rfl).elim
  | n + 1, _ => by
    rw [pow_succ']; exact mul_lt_one_of_nonneg_of_lt_one_left h₀ h₁ (pow_le_one₀ h₀ h₁.le)

lemma pow_right_mono₀ [ZeroLEOneClass M₀] [PosMulMono M₀] (h : 1 ≤ a) : Monotone (a ^ ·) :=
  monotone_nat_of_le_succ fun n => by
    rw [pow_succ]; exact le_mul_of_one_le_right (pow_nonneg (zero_le_one.trans h) _) h

lemma one_le_pow₀ [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 ≤ a) {n : ℕ} : 1 ≤ a ^ n :=
  pow_zero a ▸ pow_right_mono₀ ha n.zero_le

lemma one_lt_pow₀ [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 < a) : ∀ {n : ℕ}, n ≠ 0 → 1 < a ^ n
  | 0, h => (h rfl).elim
  | n + 1, _ => by rw [pow_succ']; exact one_lt_mul_of_lt_of_le ha (one_le_pow₀ ha.le)

/-- `bound` lemma for branching on `1 ≤ a ∨ a ≤ 1` when proving `a ^ n ≤ a ^ m` -/
@[bound]
lemma Bound.pow_le_pow_right_of_le_one_or_one_le [ZeroLEOneClass M₀] [PosMulMono M₀]
    (h : 1 ≤ a ∧ n ≤ m ∨ 0 ≤ a ∧ a ≤ 1 ∧ m ≤ n) :
    a ^ n ≤ a ^ m := by
  obtain ⟨a1, nm⟩ | ⟨a0, a1, mn⟩ := h
  · exact pow_right_mono₀ a1 nm
  · exact pow_le_pow_of_le_one a0 a1 mn

@[gcongr]
lemma pow_le_pow_right₀ [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 ≤ a) (hmn : m ≤ n) :
    a ^ m ≤ a ^ n :=
  pow_right_mono₀ ha hmn

lemma le_self_pow₀ [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 ≤ a) (hn : n ≠ 0) : a ≤ a ^ n := by
  simpa only [pow_one] using pow_le_pow_right₀ ha <| Nat.pos_iff_ne_zero.2 hn

/-- The `bound` tactic can't handle `m ≠ 0` goals yet, so we express as `0 < m` -/
@[bound]
lemma Bound.le_self_pow_of_pos [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 ≤ a) (hn : 0 < n) :
    a ≤ a ^ n := le_self_pow₀ ha hn.ne'

@[mono, gcongr, bound]
theorem pow_le_pow_left₀ [PosMulMono M₀] [MulPosMono M₀]
    (ha : 0 ≤ a) (hab : a ≤ b) : ∀ n, a ^ n ≤ b ^ n
  | 0 => by simp
  | 1 => by simpa using hab
  | n + 2 => by simpa only [pow_succ']
      using mul_le_mul hab (pow_le_pow_left₀ ha hab _) (pow_succ_nonneg ha _) (ha.trans hab)

lemma pow_left_monotoneOn [PosMulMono M₀] [MulPosMono M₀] :
    MonotoneOn (fun a : M₀ ↦ a ^ n) {x | 0 ≤ x} :=
  fun _a ha _b _ hab ↦ pow_le_pow_left₀ ha hab _

variable [Preorder α] {f g : α → M₀}

lemma monotone_mul_left_of_nonneg [PosMulMono M₀] (ha : 0 ≤ a) : Monotone fun x ↦ a * x :=
  fun _ _ h ↦ mul_le_mul_of_nonneg_left h ha

lemma monotone_mul_right_of_nonneg [MulPosMono M₀] (ha : 0 ≤ a) : Monotone fun x ↦ x * a :=
  fun _ _ h ↦ mul_le_mul_of_nonneg_right h ha

lemma Monotone.mul_const [MulPosMono M₀] (hf : Monotone f) (ha : 0 ≤ a) :
    Monotone fun x ↦ f x * a := (monotone_mul_right_of_nonneg ha).comp hf

lemma Monotone.const_mul [PosMulMono M₀] (hf : Monotone f) (ha : 0 ≤ a) :
    Monotone fun x ↦ a * f x := (monotone_mul_left_of_nonneg ha).comp hf

lemma Antitone.mul_const [MulPosMono M₀] (hf : Antitone f) (ha : 0 ≤ a) :
    Antitone fun x ↦ f x * a := (monotone_mul_right_of_nonneg ha).comp_antitone hf

lemma Antitone.const_mul [PosMulMono M₀] (hf : Antitone f) (ha : 0 ≤ a) :
    Antitone fun x ↦ a * f x := (monotone_mul_left_of_nonneg ha).comp_antitone hf

end Preorder

section PartialOrder
variable [PartialOrder M₀] {a b c d : M₀} {m n : ℕ}

lemma mul_self_lt_mul_self [PosMulStrictMono M₀] [MulPosMono M₀] (ha : 0 ≤ a) (hab : a < b) :
    a * a < b * b := mul_lt_mul' hab.le hab ha <| ha.trans_lt hab

-- In the next lemma, we used to write `Set.Ici 0` instead of `{x | 0 ≤ x}`.
-- As this lemma is not used outside this file,
-- and the import for `Set.Ici` is not otherwise needed until later,
-- we choose not to use it here.
lemma strictMonoOn_mul_self [PosMulStrictMono M₀] [MulPosMono M₀] :
    StrictMonoOn (fun x ↦ x * x) {x : M₀ | 0 ≤ x} := fun _ hx _ _ hxy ↦ mul_self_lt_mul_self hx hxy

-- See Note [decidable namespace]
protected lemma Decidable.mul_lt_mul'' [PosMulMono M₀] [PosMulStrictMono M₀] [MulPosStrictMono M₀]
    [DecidableLE M₀] (h1 : a < c) (h2 : b < d) (h3 : 0 ≤ a) (h4 : 0 ≤ b) : a * b < c * d :=
  h4.lt_or_eq_dec.elim (fun b0 ↦ mul_lt_mul h1 h2.le b0 <| h3.trans h1.le) fun b0 ↦ by
    rw [← b0, mul_zero]; exact mul_pos (h3.trans_lt h1) (h4.trans_lt h2)

lemma lt_mul_left [MulPosStrictMono M₀] (ha : 0 < a) (hb : 1 < b) : a < b * a := by
  simpa using mul_lt_mul_of_pos_right hb ha

lemma lt_mul_right [PosMulStrictMono M₀] (ha : 0 < a) (hb : 1 < b) : a < a * b := by
  simpa using mul_lt_mul_of_pos_left hb ha

lemma lt_mul_self [ZeroLEOneClass M₀] [MulPosStrictMono M₀] (ha : 1 < a) : a < a * a :=
  lt_mul_left (ha.trans_le' zero_le_one) ha

lemma sq_pos_of_pos [PosMulStrictMono M₀] (ha : 0 < a) : 0 < a ^ 2 := by
  simpa only [sq] using mul_pos ha ha

section strict_mono
variable [PosMulStrictMono M₀]

@[simp] lemma pow_succ_pos (ha : 0 < a) : ∀ n, 0 < a ^ (n + 1)
  | 0 => by simpa using ha
  | _ + 1 => pow_succ a _ ▸ mul_pos (pow_succ_pos ha _) ha

@[simp] lemma pow_pos [ZeroLEOneClass M₀] (ha : 0 < a) : ∀ n, 0 < a ^ n
  | 0 => by nontriviality; rw [pow_zero]; exact zero_lt_one
  | _ + 1 => pow_succ a _ ▸ mul_pos (pow_pos ha _) ha

@[gcongr, bound]
lemma pow_lt_pow_left₀ [MulPosMono M₀] (hab : a < b)
    (ha : 0 ≤ a) : ∀ {n : ℕ}, n ≠ 0 → a ^ n < b ^ n
  | 1, _ => by simpa using hab
  | n + 2, _ => by
    simpa only [pow_succ] using mul_lt_mul_of_le_of_lt_of_nonneg_of_pos
      (pow_le_pow_left₀ ha hab.le _) hab ha (pow_succ_pos (ha.trans_lt hab) _)

/-- See also `pow_left_strictMono₀` and `Nat.pow_left_strictMono`. -/
lemma pow_left_strictMonoOn₀ [MulPosMono M₀] (hn : n ≠ 0) :
    StrictMonoOn (· ^ n : M₀ → M₀) {a | 0 ≤ a} :=
  fun _a ha _b _ hab ↦ pow_lt_pow_left₀ hab ha hn

section ZeroLEOneClass

variable [ZeroLEOneClass M₀]

/-- See also `pow_right_strictMono'`. -/
lemma pow_right_strictMono₀ (h : 1 < a) : StrictMono (a ^ ·) :=
  strictMono_nat_of_lt_succ fun n => by
    simpa only [one_mul, pow_succ] using lt_mul_right (pow_pos (zero_le_one.trans_lt h) _) h

@[gcongr]
lemma pow_lt_pow_right₀ (h : 1 < a) (hmn : m < n) : a ^ m < a ^ n := pow_right_strictMono₀ h hmn

lemma pow_lt_pow_iff_right₀ (h : 1 < a) : a ^ n < a ^ m ↔ n < m :=
  (pow_right_strictMono₀ h).lt_iff_lt

lemma pow_le_pow_iff_right₀ (h : 1 < a) : a ^ n ≤ a ^ m ↔ n ≤ m :=
  (pow_right_strictMono₀ h).le_iff_le

lemma lt_self_pow₀ (h : 1 < a) (hm : 1 < m) : a < a ^ m := by
  simpa only [pow_one] using pow_lt_pow_right₀ h hm

end ZeroLEOneClass

lemma pow_right_strictAnti₀ (h₀ : 0 < a) (h₁ : a < 1) : StrictAnti (a ^ ·) :=
  strictAnti_nat_of_succ_lt fun n => by
    have : ZeroLEOneClass M₀ := ⟨(h₀.trans h₁).le⟩
    simpa only [pow_succ, mul_one] using mul_lt_mul_of_pos_left h₁ (pow_pos h₀ n)

lemma pow_le_pow_iff_right_of_lt_one₀ (ha₀ : 0 < a) (ha₁ : a < 1) : a ^ m ≤ a ^ n ↔ n ≤ m :=
  (pow_right_strictAnti₀ ha₀ ha₁).le_iff_ge

lemma pow_lt_pow_iff_right_of_lt_one₀ (h₀ : 0 < a) (h₁ : a < 1) : a ^ m < a ^ n ↔ n < m :=
  (pow_right_strictAnti₀ h₀ h₁).lt_iff_gt

lemma pow_lt_pow_right_of_lt_one₀ (h₀ : 0 < a) (h₁ : a < 1) (hmn : m < n) : a ^ n < a ^ m :=
  (pow_lt_pow_iff_right_of_lt_one₀ h₀ h₁).2 hmn

lemma pow_lt_self_of_lt_one₀ (h₀ : 0 < a) (h₁ : a < 1) (hn : 1 < n) : a ^ n < a := by
  simpa only [pow_one] using pow_lt_pow_right_of_lt_one₀ h₀ h₁ hn

end strict_mono

variable [Preorder α] {f g : α → M₀}

lemma strictMono_mul_left_of_pos [PosMulStrictMono M₀] (ha : 0 < a) :
    StrictMono fun x ↦ a * x := fun _ _ b_lt_c ↦ mul_lt_mul_of_pos_left b_lt_c ha

lemma strictMono_mul_right_of_pos [MulPosStrictMono M₀] (ha : 0 < a) :
    StrictMono fun x ↦ x * a := fun _ _ b_lt_c ↦ mul_lt_mul_of_pos_right b_lt_c ha

lemma StrictMono.mul_const [MulPosStrictMono M₀] (hf : StrictMono f) (ha : 0 < a) :
    StrictMono fun x ↦ f x * a := (strictMono_mul_right_of_pos ha).comp hf

lemma StrictMono.const_mul [PosMulStrictMono M₀] (hf : StrictMono f) (ha : 0 < a) :
    StrictMono fun x ↦ a * f x := (strictMono_mul_left_of_pos ha).comp hf

lemma StrictAnti.mul_const [MulPosStrictMono M₀] (hf : StrictAnti f) (ha : 0 < a) :
    StrictAnti fun x ↦ f x * a := (strictMono_mul_right_of_pos ha).comp_strictAnti hf

lemma StrictAnti.const_mul [PosMulStrictMono M₀] (hf : StrictAnti f) (ha : 0 < a) :
    StrictAnti fun x ↦ a * f x := (strictMono_mul_left_of_pos ha).comp_strictAnti hf

lemma StrictMono.mul_monotone [PosMulMono M₀] [MulPosStrictMono M₀] (hf : StrictMono f)
    (hg : Monotone g) (hf₀ : ∀ x, 0 ≤ f x) (hg₀ : ∀ x, 0 < g x) :
    StrictMono (f * g) := fun _ _ h ↦ mul_lt_mul (hf h) (hg h.le) (hg₀ _) (hf₀ _)

lemma Monotone.mul_strictMono [PosMulStrictMono M₀] [MulPosMono M₀] (hf : Monotone f)
    (hg : StrictMono g) (hf₀ : ∀ x, 0 < f x) (hg₀ : ∀ x, 0 ≤ g x) :
    StrictMono (f * g) := fun _ _ h ↦ mul_lt_mul' (hf h.le) (hg h) (hg₀ _) (hf₀ _)

lemma StrictMono.mul [PosMulStrictMono M₀] [MulPosStrictMono M₀] (hf : StrictMono f)
    (hg : StrictMono g) (hf₀ : ∀ x, 0 ≤ f x) (hg₀ : ∀ x, 0 ≤ g x) :
    StrictMono (f * g) := fun _ _ h ↦ mul_lt_mul'' (hf h) (hg h) (hf₀ _) (hg₀ _)

end PartialOrder

section LinearOrder
variable [LinearOrder M₀] [PosMulStrictMono M₀] {a b : M₀}
  {m n : ℕ}

lemma pow_le_pow_iff_left₀ [MulPosMono M₀] (ha : 0 ≤ a) (hb : 0 ≤ b) (hn : n ≠ 0) :
    a ^ n ≤ b ^ n ↔ a ≤ b :=
  (pow_left_strictMonoOn₀ hn).le_iff_le ha hb

lemma pow_lt_pow_iff_left₀ [MulPosMono M₀] (ha : 0 ≤ a) (hb : 0 ≤ b) (hn : n ≠ 0) :
    a ^ n < b ^ n ↔ a < b :=
  (pow_left_strictMonoOn₀ hn).lt_iff_lt ha hb

@[simp]
lemma pow_left_inj₀ [MulPosMono M₀] (ha : 0 ≤ a) (hb : 0 ≤ b) (hn : n ≠ 0) :
    a ^ n = b ^ n ↔ a = b :=
  (pow_left_strictMonoOn₀ hn).eq_iff_eq ha hb

section ZeroLEOneClass

variable [ZeroLEOneClass M₀]

lemma pow_right_injective₀ (ha₀ : 0 < a) (ha₁ : a ≠ 1) : Injective (a ^ ·) := by
  obtain ha₁ | ha₁ := ha₁.lt_or_gt
  · exact (pow_right_strictAnti₀ ha₀ ha₁).injective
  · exact (pow_right_strictMono₀ ha₁).injective

@[simp]
lemma pow_right_inj₀ (ha₀ : 0 < a) (ha₁ : a ≠ 1) : a ^ m = a ^ n ↔ m = n :=
  (pow_right_injective₀ ha₀ ha₁).eq_iff

lemma pow_le_one_iff_of_nonneg (ha : 0 ≤ a) (hn : n ≠ 0) : a ^ n ≤ 1 ↔ a ≤ 1 := by
  refine ⟨fun h ↦ ?_, pow_le_one₀ ha⟩
  contrapose! h
  exact one_lt_pow₀ h hn

lemma one_le_pow_iff_of_nonneg (ha : 0 ≤ a) (hn : n ≠ 0) : 1 ≤ a ^ n ↔ 1 ≤ a := by
  refine ⟨fun h ↦ ?_, fun h ↦ one_le_pow₀ h⟩
  contrapose! h
  exact pow_lt_one₀ ha h hn

lemma pow_lt_one_iff_of_nonneg (ha : 0 ≤ a) (hn : n ≠ 0) : a ^ n < 1 ↔ a < 1 :=
  lt_iff_lt_of_le_iff_le (one_le_pow_iff_of_nonneg ha hn)

lemma one_lt_pow_iff_of_nonneg (ha : 0 ≤ a) (hn : n ≠ 0) : 1 < a ^ n ↔ 1 < a := by
  simp only [← not_le, pow_le_one_iff_of_nonneg ha hn]

lemma pow_eq_one_iff_of_nonneg (ha : 0 ≤ a) (hn : n ≠ 0) : a ^ n = 1 ↔ a = 1 := by
  simp only [le_antisymm_iff, pow_le_one_iff_of_nonneg ha hn, one_le_pow_iff_of_nonneg ha hn]

lemma sq_le_one_iff₀ (ha : 0 ≤ a) : a ^ 2 ≤ 1 ↔ a ≤ 1 :=
  pow_le_one_iff_of_nonneg ha (Nat.succ_ne_zero _)

lemma sq_lt_one_iff₀ (ha : 0 ≤ a) : a ^ 2 < 1 ↔ a < 1 :=
  pow_lt_one_iff_of_nonneg ha (Nat.succ_ne_zero _)

lemma one_le_sq_iff₀ (ha : 0 ≤ a) : 1 ≤ a ^ 2 ↔ 1 ≤ a :=
  one_le_pow_iff_of_nonneg ha (Nat.succ_ne_zero _)

lemma one_lt_sq_iff₀ (ha : 0 ≤ a) : 1 < a ^ 2 ↔ 1 < a :=
  one_lt_pow_iff_of_nonneg ha (Nat.succ_ne_zero _)

end ZeroLEOneClass

variable [MulPosMono M₀]

lemma lt_of_pow_lt_pow_left₀ (n : ℕ) (hb : 0 ≤ b) (h : a ^ n < b ^ n) : a < b :=
  lt_of_not_ge fun hn => not_lt_of_ge (pow_le_pow_left₀ hb hn _) h

lemma le_of_pow_le_pow_left₀ (hn : n ≠ 0) (hb : 0 ≤ b) (h : a ^ n ≤ b ^ n) : a ≤ b :=
  le_of_not_gt fun h1 => not_le_of_gt (pow_lt_pow_left₀ h1 hb hn) h

lemma sq_eq_sq₀ (ha : 0 ≤ a) (hb : 0 ≤ b) : a ^ 2 = b ^ 2 ↔ a = b := by
  simp [ha, hb]

lemma lt_of_mul_self_lt_mul_self₀ (hb : 0 ≤ b) : a * a < b * b → a < b := by
  simp only [← sq]
  exact lt_of_pow_lt_pow_left₀ _ hb

lemma sq_lt_sq₀ (ha : 0 ≤ a) (hb : 0 ≤ b) : a ^ 2 < b ^ 2 ↔ a < b :=
  pow_lt_pow_iff_left₀ ha hb two_ne_zero

lemma sq_le_sq₀ (ha : 0 ≤ a) (hb : 0 ≤ b) : a ^ 2 ≤ b ^ 2 ↔ a ≤ b :=
  pow_le_pow_iff_left₀ ha hb two_ne_zero

end MonoidWithZero.LinearOrder

section GroupWithZero
variable [GroupWithZero G₀]

section Preorder
variable [Preorder G₀] {a b c : G₀}

/-- Equality holds when `a ≠ 0`. See `mul_inv_cancel_left`. -/
lemma mul_inv_left_le (hb : 0 ≤ b) : a * (a⁻¹ * b) ≤ b := by
  obtain rfl | ha := eq_or_ne a 0 <;> simp [*]

/-- Equality holds when `a ≠ 0`. See `mul_inv_cancel_left`. -/
lemma le_mul_inv_left (hb : b ≤ 0) : b ≤ a * (a⁻¹ * b) := by
  obtain rfl | ha := eq_or_ne a 0 <;> simp [*]

/-- Equality holds when `a ≠ 0`. See `inv_mul_cancel_left`. -/
lemma inv_mul_left_le (hb : 0 ≤ b) : a⁻¹ * (a * b) ≤ b := by
  obtain rfl | ha := eq_or_ne a 0 <;> simp [*]

/-- Equality holds when `a ≠ 0`. See `inv_mul_cancel_left`. -/
lemma le_inv_mul_left (hb : b ≤ 0) : b ≤ a⁻¹ * (a * b) := by
  obtain rfl | ha := eq_or_ne a 0 <;> simp [*]

/-- Equality holds when `b ≠ 0`. See `mul_inv_cancel_right`. -/
lemma mul_inv_right_le (ha : 0 ≤ a) : a * b * b⁻¹ ≤ a := by
  obtain rfl | hb := eq_or_ne b 0 <;> simp [*]

/-- Equality holds when `b ≠ 0`. See `mul_inv_cancel_right`. -/
lemma le_mul_inv_right (ha : a ≤ 0) : a ≤ a * b * b⁻¹ := by
  obtain rfl | hb := eq_or_ne b 0 <;> simp [*]

/-- Equality holds when `b ≠ 0`. See `inv_mul_cancel_right`. -/
lemma inv_mul_right_le (ha : 0 ≤ a) : a * b⁻¹ * b ≤ a := by
  obtain rfl | hb := eq_or_ne b 0 <;> simp [*]

/-- Equality holds when `b ≠ 0`. See `inv_mul_cancel_right`. -/
lemma le_inv_mul_right (ha : a ≤ 0) : a ≤ a * b⁻¹ * b := by
  obtain rfl | hb := eq_or_ne b 0 <;> simp [*]

/-- Equality holds when `c ≠ 0`. See `mul_div_mul_right`. -/
lemma mul_div_mul_right_le (h : 0 ≤ a / b) : a * c / (b * c) ≤ a / b := by
  obtain rfl | hc := eq_or_ne c 0
  · simpa
  · rw [mul_div_mul_right _ _ hc]

/-- Equality holds when `c ≠ 0`. See `mul_div_mul_right`. -/
lemma le_mul_div_mul_right (h : a / b ≤ 0) : a / b ≤ a * c / (b * c) := by
  obtain rfl | hc := eq_or_ne c 0
  · simpa
  · rw [mul_div_mul_right _ _ hc]

end Preorder

section Preorder
variable [Preorder G₀] [ZeroLEOneClass G₀] {a b c : G₀}

/-- See `div_self` for the version with equality when `a ≠ 0`. -/
lemma div_self_le_one (a : G₀) : a / a ≤ 1 := by obtain rfl | ha := eq_or_ne a 0 <;> simp [*]

/-- Equality holds when `a ≠ 0`. See `mul_inv_cancel`. -/
lemma mul_inv_le_one : a * a⁻¹ ≤ 1 := by simpa only [div_eq_mul_inv] using div_self_le_one a

/-- Equality holds when `a ≠ 0`. See `inv_mul_cancel`. -/
lemma inv_mul_le_one : a⁻¹ * a ≤ 1 := by obtain rfl | ha := eq_or_ne a 0 <;> simp [*]

end Preorder

section PartialOrder
variable [PartialOrder G₀]

section PosMulReflectLT

variable [PosMulReflectLT G₀] {a b c : G₀}

@[simp] lemma inv_pos : 0 < a⁻¹ ↔ 0 < a := by
  suffices ∀ a : G₀, 0 < a → 0 < a⁻¹ from ⟨fun h ↦ inv_inv a ▸ this _ h, this a⟩
  intro a ha
  apply lt_of_mul_lt_mul_left _ ha.le
  apply lt_of_mul_lt_mul_left _ ha.le
  simpa [ha.ne']

alias ⟨_, inv_pos_of_pos⟩ := inv_pos

@[simp] lemma inv_nonneg : 0 ≤ a⁻¹ ↔ 0 ≤ a := by simp only [le_iff_eq_or_lt, inv_pos, zero_eq_inv]

alias ⟨_, inv_nonneg_of_nonneg⟩ := inv_nonneg

lemma one_div_pos : 0 < 1 / a ↔ 0 < a := one_div a ▸ inv_pos
lemma one_div_nonneg : 0 ≤ 1 / a ↔ 0 ≤ a := one_div a ▸ inv_nonneg

variable (G₀) in
/-- For a group with zero, `PosMulReflectLT G₀` implies `PosMulStrictMono G₀`. -/
theorem PosMulReflectLT.toPosMulStrictMono : PosMulStrictMono G₀ where
  mul_lt_mul_of_pos_left a ha b c hbc :=
    lt_of_mul_lt_mul_left (by simpa [ha.ne']) (inv_pos_of_pos ha).le

variable (G₀) in
/-- For a group with zero, `PosMulReflectLT G₀`
allows us to upgrade `MulPosMono G₀` to `MulPosReflectLE G₀`.
The other implication holds without the `PosMulReflectLT G₀` assumption,
see `MulPosReflectLT.toMulPosStrictMono` for a stronger version below.

This theorem shows that in the presence of the assumption `PosMulReflectLT G₀`,
it makes no sense to optimize between assumptions `MulPosMono G₀`, `MulPosStrictMono G₀`,
`MulPosReflectLT G₀`, and `MulPosReflectLE G₀`. -/
theorem MulPosReflectLE.of_posMulReflectLT_of_mulPosMono [MulPosMono G₀] : MulPosReflectLE G₀ where
  elim := by
    rintro ⟨a, ha⟩ b c h
    simpa [ha.ne'] using mul_le_mul_of_nonneg_right h (inv_nonneg.2 ha.le)

attribute [local instance] PosMulReflectLT.toPosMulStrictMono PosMulReflectLT.toPosMulReflectLE

lemma div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b := by
  rw [div_eq_mul_inv]; exact mul_pos ha (inv_pos.2 hb)

lemma div_nonneg (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a / b := by
  rw [div_eq_mul_inv]; exact mul_nonneg ha (inv_nonneg.2 hb)

/-- See `le_inv_mul_iff₀'` for a version with multiplication on the other side. -/
lemma le_inv_mul_iff₀ (hc : 0 < c) : a ≤ c⁻¹ * b ↔ c * a ≤ b := by
  rw [← mul_le_mul_iff_of_pos_left hc, mul_inv_cancel_left₀ hc.ne']

/-- See `inv_mul_le_iff₀'` for a version with multiplication on the other side. -/
lemma inv_mul_le_iff₀ (hc : 0 < c) : c⁻¹ * b ≤ a ↔ b ≤ c * a := by
  rw [← mul_le_mul_iff_of_pos_left hc, mul_inv_cancel_left₀ hc.ne']

lemma one_le_inv_mul₀ (ha : 0 < a) : 1 ≤ a⁻¹ * b ↔ a ≤ b := by rw [le_inv_mul_iff₀ ha, mul_one]
lemma inv_mul_le_one₀ (ha : 0 < a) : a⁻¹ * b ≤ 1 ↔ b ≤ a := by rw [inv_mul_le_iff₀ ha, mul_one]

/-- See `inv_le_iff_one_le_mul₀` for a version with multiplication on the other side. -/
lemma inv_le_iff_one_le_mul₀' (ha : 0 < a) : a⁻¹ ≤ b ↔ 1 ≤ a * b := by
  rw [← inv_mul_le_iff₀ ha, mul_one]

lemma one_le_inv₀ (ha : 0 < a) : 1 ≤ a⁻¹ ↔ a ≤ 1 := by simpa using one_le_inv_mul₀ ha (b := 1)
lemma inv_le_one₀ (ha : 0 < a) : a⁻¹ ≤ 1 ↔ 1 ≤ a := by simpa using inv_mul_le_one₀ ha (b := 1)

@[bound] alias ⟨_, Bound.one_le_inv₀⟩ := one_le_inv₀

/-- One direction of `le_inv_mul_iff₀` where `c` is allowed to be `0` (but `b` must be nonnegative).
-/
lemma mul_le_of_le_inv_mul₀ (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a ≤ c⁻¹ * b) : c * a ≤ b := by
  obtain rfl | hc := hc.eq_or_lt
  · simpa using hb
  · rwa [le_inv_mul_iff₀ hc] at h

/-- One direction of `inv_mul_le_iff₀` where `b` is allowed to be `0` (but `c` must be nonnegative).
-/
lemma inv_mul_le_of_le_mul₀ (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a ≤ b * c) : b⁻¹ * a ≤ c := by
  obtain rfl | hb := hb.eq_or_lt
  · simp [hc]
  · rwa [inv_mul_le_iff₀ hb]

/-- See `lt_inv_mul_iff₀'` for a version with multiplication on the other side. -/
lemma lt_inv_mul_iff₀ (hc : 0 < c) : a < c⁻¹ * b ↔ c * a < b := by
  rw [← mul_lt_mul_iff_of_pos_left hc, mul_inv_cancel_left₀ hc.ne']

/-- See `inv_mul_lt_iff₀'` for a version with multiplication on the other side. -/
lemma inv_mul_lt_iff₀ (hc : 0 < c) : c⁻¹ * b < a ↔ b < c * a := by
  rw [← mul_lt_mul_iff_of_pos_left hc, mul_inv_cancel_left₀ hc.ne']

/-- See `inv_lt_iff_one_lt_mul₀` for a version with multiplication on the other side. -/
lemma inv_lt_iff_one_lt_mul₀' (ha : 0 < a) : a⁻¹ < b ↔ 1 < a * b := by
  rw [← inv_mul_lt_iff₀ ha, mul_one]

lemma one_lt_inv_mul₀ (ha : 0 < a) : 1 < a⁻¹ * b ↔ a < b := by rw [lt_inv_mul_iff₀ ha, mul_one]
lemma inv_mul_lt_one₀ (ha : 0 < a) : a⁻¹ * b < 1 ↔ b < a := by rw [inv_mul_lt_iff₀ ha, mul_one]

lemma one_lt_inv₀ (ha : 0 < a) : 1 < a⁻¹ ↔ a < 1 := by simpa using one_lt_inv_mul₀ ha (b := 1)
lemma inv_lt_one₀ (ha : 0 < a) : a⁻¹ < 1 ↔ 1 < a := by simpa using inv_mul_lt_one₀ ha (b := 1)

section ZeroLEOneClass

variable [ZeroLEOneClass G₀]

@[bound]
lemma inv_lt_one_of_one_lt₀ (ha : 1 < a) : a⁻¹ < 1 := (inv_lt_one₀ <| zero_lt_one.trans ha).2 ha

lemma one_lt_inv_iff₀ : 1 < a⁻¹ ↔ 0 < a ∧ a < 1 where
  mp h := ⟨inv_pos.1 (zero_lt_one.trans h), inv_inv a ▸ (inv_lt_one₀ <| zero_lt_one.trans h).2 h⟩
  mpr h := (one_lt_inv₀ h.1).2 h.2

@[bound]
lemma inv_le_one_of_one_le₀ (ha : 1 ≤ a) : a⁻¹ ≤ 1 :=
  (inv_le_one₀ <| zero_lt_one.trans_le ha).2 ha

lemma one_le_inv_iff₀ : 1 ≤ a⁻¹ ↔ 0 < a ∧ a ≤ 1 where
  mp h := ⟨inv_pos.1 (zero_lt_one.trans_le h),
    inv_inv a ▸ (inv_le_one₀ <| zero_lt_one.trans_le h).2 h⟩
  mpr h := (one_le_inv₀ h.1).2 h.2

@[bound]
lemma inv_mul_le_one_of_le₀ (h : a ≤ b) (hb : 0 ≤ b) : b⁻¹ * a ≤ 1 :=
  inv_mul_le_of_le_mul₀ hb zero_le_one <| by rwa [mul_one]

section ZPow
variable {m n : ℤ}

lemma zpow_nonneg (ha : 0 ≤ a) : ∀ n : ℤ, 0 ≤ a ^ n
  | (n : ℕ) => by rw [zpow_natCast]; exact pow_nonneg ha _
  | -(n + 1 : ℕ) => by rw [zpow_neg, inv_nonneg, zpow_natCast]; exact pow_nonneg ha _

lemma zpow_pos (ha : 0 < a) : ∀ n : ℤ, 0 < a ^ n
  | (n : ℕ) => by rw [zpow_natCast]; exact pow_pos ha _
  | -(n + 1 : ℕ) => by rw [zpow_neg, inv_pos, zpow_natCast]; exact pow_pos ha _

lemma zpow_right_mono₀ (ha : 1 ≤ a) : Monotone fun n : ℤ ↦ a ^ n := by
  refine monotone_int_of_le_succ fun n ↦ ?_
  rw [zpow_add_one₀ (zero_lt_one.trans_le ha).ne']
  exact le_mul_of_one_le_right (zpow_nonneg (zero_le_one.trans ha) _) ha

lemma zpow_right_anti₀ (ha₀ : 0 < a) (ha₁ : a ≤ 1) : Antitone fun n : ℤ ↦ a ^ n := by
  refine antitone_int_of_succ_le fun n ↦ ?_
  rw [zpow_add_one₀ ha₀.ne']
  exact mul_le_of_le_one_right (zpow_nonneg ha₀.le _) ha₁

lemma zpow_right_strictMono₀ (ha : 1 < a) : StrictMono fun n : ℤ ↦ a ^ n := by
  refine strictMono_int_of_lt_succ fun n ↦ ?_
  rw [zpow_add_one₀ (zero_lt_one.trans ha).ne']
  exact lt_mul_of_one_lt_right (zpow_pos (zero_lt_one.trans ha) _) ha

lemma zpow_right_strictAnti₀ (ha₀ : 0 < a) (ha₁ : a < 1) : StrictAnti fun n : ℤ ↦ a ^ n := by
  refine strictAnti_int_of_succ_lt fun n ↦ ?_
  rw [zpow_add_one₀ ha₀.ne']
  exact mul_lt_of_lt_one_right (zpow_pos ha₀ _) ha₁

@[gcongr]
lemma zpow_le_zpow_right₀ (ha : 1 ≤ a) (hmn : m ≤ n) : a ^ m ≤ a ^ n := zpow_right_mono₀ ha hmn

lemma zpow_le_zpow_right_of_le_one₀ (ha₀ : 0 < a) (ha₁ : a ≤ 1) (hmn : m ≤ n) : a ^ n ≤ a ^ m :=
  zpow_right_anti₀ ha₀ ha₁ hmn

lemma one_le_zpow₀ (ha : 1 ≤ a) (hn : 0 ≤ n) : 1 ≤ a ^ n := by simpa using zpow_right_mono₀ ha hn

lemma zpow_le_one₀ (ha₀ : 0 < a) (ha₁ : a ≤ 1) (hn : 0 ≤ n) : a ^ n ≤ 1 := by
  simpa using zpow_right_anti₀ ha₀ ha₁ hn

lemma zpow_le_one_of_nonpos₀ (ha : 1 ≤ a) (hn : n ≤ 0) : a ^ n ≤ 1 := by
  simpa using zpow_right_mono₀ ha hn

lemma one_le_zpow_of_nonpos₀ (ha₀ : 0 < a) (ha₁ : a ≤ 1) (hn : n ≤ 0) : 1 ≤ a ^ n := by
  simpa using zpow_right_anti₀ ha₀ ha₁ hn

@[gcongr]
lemma zpow_lt_zpow_right₀ (ha : 1 < a) (hmn : m < n) : a ^ m < a ^ n :=
  zpow_right_strictMono₀ ha hmn

lemma zpow_lt_zpow_right_of_lt_one₀ (ha₀ : 0 < a) (ha₁ : a < 1) (hmn : m < n) : a ^ n < a ^ m :=
  zpow_right_strictAnti₀ ha₀ ha₁ hmn

lemma one_lt_zpow₀ (ha : 1 < a) (hn : 0 < n) : 1 < a ^ n := by
  simpa using zpow_right_strictMono₀ ha hn

lemma zpow_lt_one₀ (ha₀ : 0 < a) (ha₁ : a < 1) (hn : 0 < n) : a ^ n < 1 := by
  simpa using zpow_right_strictAnti₀ ha₀ ha₁ hn

lemma zpow_lt_one_of_neg₀ (ha : 1 < a) (hn : n < 0) : a ^ n < 1 := by
  simpa using zpow_right_strictMono₀ ha hn

lemma one_lt_zpow_of_neg₀ (ha₀ : 0 < a) (ha₁ : a < 1) (hn : n < 0) : 1 < a ^ n := by
  simpa using zpow_right_strictAnti₀ ha₀ ha₁ hn

@[simp] lemma zpow_le_zpow_iff_right₀ (ha : 1 < a) : a ^ m ≤ a ^ n ↔ m ≤ n :=
  (zpow_right_strictMono₀ ha).le_iff_le

@[simp] lemma zpow_lt_zpow_iff_right₀ (ha : 1 < a) : a ^ m < a ^ n ↔ m < n :=
  (zpow_right_strictMono₀ ha).lt_iff_lt

lemma zpow_le_zpow_iff_right_of_lt_one₀ (ha₀ : 0 < a) (ha₁ : a < 1) :
    a ^ m ≤ a ^ n ↔ n ≤ m := (zpow_right_strictAnti₀ ha₀ ha₁).le_iff_ge

lemma zpow_lt_zpow_iff_right_of_lt_one₀ (ha₀ : 0 < a) (ha₁ : a < 1) :
    a ^ m < a ^ n ↔ n < m := (zpow_right_strictAnti₀ ha₀ ha₁).lt_iff_gt

@[simp] lemma one_le_zpow_iff_right₀ (ha : 1 < a) : 1 ≤ a ^ n ↔ 0 ≤ n := by
  simp [← zpow_le_zpow_iff_right₀ ha]

@[simp] lemma one_lt_zpow_iff_right₀ (ha : 1 < a) : 1 < a ^ n ↔ 0 < n := by
  simp [← zpow_lt_zpow_iff_right₀ ha]

@[simp] lemma one_le_zpow_iff_right_of_lt_one₀ (ha₀ : 0 < a) (ha₁ : a < 1) : 1 ≤ a ^ n ↔ n ≤ 0 := by
  simp [← zpow_le_zpow_iff_right_of_lt_one₀ ha₀ ha₁]

@[simp] lemma one_lt_zpow_iff_right_of_lt_one₀ (ha₀ : 0 < a) (ha₁ : a < 1) : 1 < a ^ n ↔ n < 0 := by
  simp [← zpow_lt_zpow_iff_right_of_lt_one₀ ha₀ ha₁]

@[simp] lemma zpow_le_one_iff_right₀ (ha : 1 < a) : a ^ n ≤ 1 ↔ n ≤ 0 := by
  simp [← zpow_le_zpow_iff_right₀ ha]

@[simp] lemma zpow_lt_one_iff_right₀ (ha : 1 < a) : a ^ n < 1 ↔ n < 0 := by
  simp [← zpow_lt_zpow_iff_right₀ ha]

@[simp] lemma zpow_le_one_iff_right_of_lt_one₀ (ha₀ : 0 < a) (ha₁ : a < 1) : a ^ n ≤ 1 ↔ 0 ≤ n := by
  simp [← zpow_le_zpow_iff_right_of_lt_one₀ ha₀ ha₁]

@[simp] lemma zpow_lt_one_iff_right_of_lt_one₀ (ha₀ : 0 < a) (ha₁ : a < 1) : a ^ n < 1 ↔ 0 < n := by
  simp [← zpow_lt_zpow_iff_right_of_lt_one₀ ha₀ ha₁]

end ZPow

end ZeroLEOneClass

section MulPosMono

variable [MulPosMono G₀] {n : ℤ}

lemma zpow_left_monoOn₀ (hn : 0 ≤ n) : MonotoneOn (fun a : G₀ ↦ a ^ n) {a | 0 ≤ a} := by
  lift n to ℕ using hn; simpa using pow_left_monotoneOn

lemma zpow_left_strictMonoOn₀ (hn : 0 < n) : StrictMonoOn (fun a : G₀ ↦ a ^ n) {a | 0 ≤ a} := by
  lift n to ℕ using hn.le; simpa using pow_left_strictMonoOn₀ (by lia)

lemma zpow_le_zpow_left₀ (hn : 0 ≤ n) (ha : 0 ≤ a) (h : a ≤ b) : a ^ n ≤ b ^ n :=
  zpow_left_monoOn₀ (G₀ := G₀) hn ha (by grind) h

lemma zpow_lt_zpow_left₀ (hn : 0 < n) (ha : 0 ≤ a) (h : a < b) : a ^ n < b ^ n :=
  zpow_left_strictMonoOn₀ (G₀ := G₀) hn ha (by grind) h

end MulPosMono

end PosMulReflectLT

section MulPosReflectLT
variable [MulPosReflectLT G₀] {a b c : G₀}

namespace Right

lemma inv_pos : 0 < a⁻¹ ↔ 0 < a := by
  suffices ∀ a : G₀, 0 < a → 0 < a⁻¹ from ⟨fun h ↦ inv_inv a ▸ this _ h, this a⟩
  intro a ha
  apply lt_of_mul_lt_mul_right _ ha.le
  apply lt_of_mul_lt_mul_right _ ha.le
  simpa [ha.ne']

variable (G₀) in
/-- For a group with zero, `MulPosReflectLT G₀` implies `MulPosStrictMono G₀`. -/
theorem _root_.MulPosReflectLT.toMulPosStrictMono : MulPosStrictMono G₀ where
  mul_lt_mul_of_pos_right a ha b c hbc :=
    lt_of_mul_lt_mul_right (by simpa [ha.ne']) (inv_pos.2 ha).le

lemma inv_nonneg : 0 ≤ a⁻¹ ↔ 0 ≤ a := by simp only [le_iff_eq_or_lt, inv_pos, zero_eq_inv]

end Right

attribute [local instance] PosMulReflectLT.toPosMulStrictMono
  MulPosReflectLT.toMulPosStrictMono MulPosReflectLT.toMulPosReflectLE

lemma div_nonpos_of_nonpos_of_nonneg (ha : a ≤ 0) (hb : 0 ≤ b) : a / b ≤ 0 := by
  rw [div_eq_mul_inv]; exact mul_nonpos_of_nonpos_of_nonneg ha (Right.inv_nonneg.2 hb)

/-- See `le_mul_inv_iff₀'` for a version with multiplication on the other side. -/
lemma le_mul_inv_iff₀ (hc : 0 < c) : a ≤ b * c⁻¹ ↔ a * c ≤ b := by
  rw [← mul_le_mul_iff_of_pos_right hc, inv_mul_cancel_right₀ hc.ne']

/-- See `mul_inv_le_iff₀'` for a version with multiplication on the other side. -/
lemma mul_inv_le_iff₀ (hc : 0 < c) : b * c⁻¹ ≤ a ↔ b ≤ a * c := by
  rw [← mul_le_mul_iff_of_pos_right hc, inv_mul_cancel_right₀ hc.ne']

/-- See `lt_mul_inv_iff₀'` for a version with multiplication on the other side. -/
lemma lt_mul_inv_iff₀ (hc : 0 < c) : a < b * c⁻¹ ↔ a * c < b := by
  rw [← mul_lt_mul_iff_of_pos_right hc, inv_mul_cancel_right₀ hc.ne']

/-- See `mul_inv_lt_iff₀'` for a version with multiplication on the other side. -/
lemma mul_inv_lt_iff₀ (hc : 0 < c) : b * c⁻¹ < a ↔ b < a * c := by
  rw [← mul_lt_mul_iff_of_pos_right hc, inv_mul_cancel_right₀ hc.ne']

/-- See `le_div_iff₀'` for a version with multiplication on the other side. -/
lemma le_div_iff₀ (hc : 0 < c) : a ≤ b / c ↔ a * c ≤ b := by
  rw [div_eq_mul_inv, le_mul_inv_iff₀ hc]

/-- See `div_le_iff₀'` for a version with multiplication on the other side. -/
lemma div_le_iff₀ (hc : 0 < c) : b / c ≤ a ↔ b ≤ a * c := by
  rw [div_eq_mul_inv, mul_inv_le_iff₀ hc]

/-- See `lt_div_iff₀'` for a version with multiplication on the other side. -/
lemma lt_div_iff₀ (hc : 0 < c) : a < b / c ↔ a * c < b := by
  rw [div_eq_mul_inv, lt_mul_inv_iff₀ hc]

/-- See `div_lt_iff₀'` for a version with multiplication on the other side. -/
lemma div_lt_iff₀ (hc : 0 < c) : b / c < a ↔ b < a * c := by
  rw [div_eq_mul_inv, mul_inv_lt_iff₀ hc]

lemma div_le_div_iff_of_pos_right (hc : 0 < c) : a / c ≤ b / c ↔ a ≤ b := by
  rw [div_le_iff₀ hc, div_mul_cancel₀ _ hc.ne']

lemma div_lt_div_iff_of_pos_right (hc : 0 < c) : a / c < b / c ↔ a < b := by
  rw [div_lt_iff₀ hc, div_mul_cancel₀ _ hc.ne']

/-- See `inv_le_iff_one_le_mul₀'` for a version with multiplication on the other side. -/
lemma inv_le_iff_one_le_mul₀ (ha : 0 < a) : a⁻¹ ≤ b ↔ 1 ≤ b * a := by
  rw [← mul_inv_le_iff₀ ha, one_mul]

/-- See `inv_lt_iff_one_lt_mul₀'` for a version with multiplication on the other side. -/
lemma inv_lt_iff_one_lt_mul₀ (ha : 0 < a) : a⁻¹ < b ↔ 1 < b * a := by
  rw [← mul_inv_lt_iff₀ ha, one_mul]

lemma one_le_div₀ (hb : 0 < b) : 1 ≤ a / b ↔ b ≤ a := by rw [le_div_iff₀ hb, one_mul]
lemma one_lt_div₀ (hb : 0 < b) : 1 < a / b ↔ b < a := by rw [lt_div_iff₀ hb, one_mul]
lemma div_le_one₀ (hb : 0 < b) : a / b ≤ 1 ↔ a ≤ b := by rw [div_le_iff₀ hb, one_mul]
lemma div_lt_one₀ (hb : 0 < b) : a / b < 1 ↔ a < b := by rw [div_lt_iff₀ hb, one_mul]

/-- One direction of `le_mul_inv_iff₀` where `c` is allowed to be `0` (but `b` must be nonnegative).
-/
lemma mul_le_of_le_mul_inv₀ (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a ≤ b * c⁻¹) : a * c ≤ b := by
  obtain rfl | hc := hc.eq_or_lt
  · simpa using hb
  · rwa [le_mul_inv_iff₀ hc] at h

/-- One direction of `mul_inv_le_iff₀` where `b` is allowed to be `0` (but `c` must be nonnegative).
-/
lemma mul_inv_le_of_le_mul₀ (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a ≤ c * b) : a * b⁻¹ ≤ c := by
  obtain rfl | hb := hb.eq_or_lt
  · simp [hc]
  · rwa [mul_inv_le_iff₀ hb]

/-- One direction of `le_div_iff₀` where `c` is allowed to be `0` (but `b` must be nonnegative). -/
lemma mul_le_of_le_div₀ (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a ≤ b / c) : a * c ≤ b :=
  mul_le_of_le_mul_inv₀ hb hc (div_eq_mul_inv b _ ▸ h)

/-- One direction of `div_le_iff₀` where `b` is allowed to be `0` (but `c` must be nonnegative). -/
lemma div_le_of_le_mul₀ (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a ≤ c * b) : a / b ≤ c :=
  div_eq_mul_inv a _ ▸ mul_inv_le_of_le_mul₀ hb hc h

@[bound]
lemma mul_inv_le_one_of_le₀ [ZeroLEOneClass G₀] (h : a ≤ b) (hb : 0 ≤ b) : a * b⁻¹ ≤ 1 :=
  mul_inv_le_of_le_mul₀ hb zero_le_one <| by rwa [one_mul]

@[bound]
lemma div_le_one_of_le₀ [ZeroLEOneClass G₀] (h : a ≤ b) (hb : 0 ≤ b) : a / b ≤ 1 :=
  div_le_of_le_mul₀ hb zero_le_one <| by rwa [one_mul]

@[mono, gcongr, bound]
lemma div_le_div_of_nonneg_right (hab : a ≤ b) (hc : 0 ≤ c) : a / c ≤ b / c := by
  rw [div_eq_mul_inv a c, div_eq_mul_inv b c]
  gcongr; exact Right.inv_nonneg.2 hc

@[gcongr, bound]
lemma div_lt_div_of_pos_right (h : a < b) (hc : 0 < c) : a / c < b / c := by
  rw [div_eq_mul_inv a c, div_eq_mul_inv b c]
  exact mul_lt_mul_of_pos_right h (Right.inv_pos.2 hc)

end MulPosReflectLT

section Both

variable [PosMulReflectLT G₀] [MulPosReflectLT G₀] {a b c d : G₀}

attribute [local instance] PosMulReflectLT.toPosMulStrictMono PosMulReflectLT.toPosMulReflectLE
  MulPosReflectLT.toMulPosStrictMono MulPosReflectLT.toMulPosReflectLE

/-- See `inv_anti₀` for the implication from right-to-left with one fewer assumption. -/
lemma inv_le_inv₀ (ha : 0 < a) (hb : 0 < b) : a⁻¹ ≤ b⁻¹ ↔ b ≤ a := by
  rw [inv_le_iff_one_le_mul₀' ha, le_mul_inv_iff₀ hb, one_mul]

/-- See `inv_strictAnti₀` for the implication from right-to-left with one fewer assumption. -/
lemma inv_lt_inv₀ (ha : 0 < a) (hb : 0 < b) : a⁻¹ < b⁻¹ ↔ b < a := by
  rw [inv_lt_iff_one_lt_mul₀' ha, lt_mul_inv_iff₀ hb, one_mul]

@[gcongr, bound]
lemma inv_anti₀ (hb : 0 < b) (hba : b ≤ a) : a⁻¹ ≤ b⁻¹ := (inv_le_inv₀ (hb.trans_le hba) hb).2 hba

@[gcongr, bound]
lemma inv_strictAnti₀ (hb : 0 < b) (hba : b < a) : a⁻¹ < b⁻¹ :=
  (inv_lt_inv₀ (hb.trans hba) hb).2 hba

lemma strictAntiOn_inv_pos : StrictAntiOn (fun x : G₀ ↦ x⁻¹) {r | 0 < r} :=
  fun ⦃_⦄ ha ⦃_⦄ _ h ↦ inv_strictAnti₀ (Set.mem_ofPred.mp ha) h

lemma antitoneOn_inv_pos : AntitoneOn (fun x : G₀ ↦ x⁻¹) {r | 0 < r} :=
  strictAntiOn_inv_pos.antitoneOn

/-- See also `inv_le_of_inv_le₀` for a one-sided implication with one fewer assumption. -/
lemma inv_le_comm₀ (ha : 0 < a) (hb : 0 < b) : a⁻¹ ≤ b ↔ b⁻¹ ≤ a := by
  rw [← inv_le_inv₀ hb (inv_pos.2 ha), inv_inv]

/-- See also `inv_lt_of_inv_lt₀` for a one-sided implication with one fewer assumption. -/
lemma inv_lt_comm₀ (ha : 0 < a) (hb : 0 < b) : a⁻¹ < b ↔ b⁻¹ < a := by
  rw [← inv_lt_inv₀ hb (inv_pos.2 ha), inv_inv]

lemma inv_le_of_inv_le₀ (ha : 0 < a) (h : a⁻¹ ≤ b) : b⁻¹ ≤ a :=
  (inv_le_comm₀ ha <| (inv_pos.2 ha).trans_le h).1 h

lemma inv_lt_of_inv_lt₀ (ha : 0 < a) (h : a⁻¹ < b) : b⁻¹ < a :=
  (inv_lt_comm₀ ha <| (inv_pos.2 ha).trans h).1 h

/-- See also `le_inv_of_le_inv₀` for a one-sided implication with one fewer assumption. -/
lemma le_inv_comm₀ (ha : 0 < a) (hb : 0 < b) : a ≤ b⁻¹ ↔ b ≤ a⁻¹ := by
  rw [← inv_le_inv₀ (inv_pos.2 hb) ha, inv_inv]

/-- See also `lt_inv_of_lt_inv₀` for a one-sided implication with one fewer assumption. -/
lemma lt_inv_comm₀ (ha : 0 < a) (hb : 0 < b) : a < b⁻¹ ↔ b < a⁻¹ := by
  rw [← inv_lt_inv₀ (inv_pos.2 hb) ha, inv_inv]

lemma le_inv_of_le_inv₀ (ha : 0 < a) (h : a ≤ b⁻¹) : b ≤ a⁻¹ :=
  (le_inv_comm₀ ha <| inv_pos.1 <| ha.trans_le h).1 h

lemma lt_inv_of_lt_inv₀ (ha : 0 < a) (h : a < b⁻¹) : b < a⁻¹ :=
  (lt_inv_comm₀ ha <| inv_pos.1 <| ha.trans h).1 h

lemma div_le_div_iff_of_pos_left (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / b ≤ a / c ↔ c ≤ b := by
  simp only [div_eq_mul_inv, mul_le_mul_iff_right₀ ha, inv_le_inv₀ hb hc]

lemma div_lt_div_iff_of_pos_left (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / b < a / c ↔ c < b :=
  lt_iff_lt_of_le_iff_le' (div_le_div_iff_of_pos_left ha hc hb)
    (div_le_div_iff_of_pos_left ha hb hc)

-- Not a `mono` lemma b/c `div_le_div₀` is strictly more general
lemma div_le_div_of_nonneg_left (ha : 0 ≤ a) (hc : 0 < c) (h : c ≤ b) : a / b ≤ a / c := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  gcongr
  exacts [ha, hc]

@[gcongr, bound]
lemma div_lt_div_of_pos_left (ha : 0 < a) (hc : 0 < c) (h : c < b) : a / b < a / c :=
  (div_lt_div_iff_of_pos_left ha (hc.trans h) hc).mpr h

@[mono, gcongr, bound]
lemma div_le_div₀ (hc : 0 ≤ c) (hac : a ≤ c) (hd : 0 < d) (hdb : d ≤ b) : a / b ≤ c / d := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  gcongr
  exacts [inv_nonneg.2 <| hd.le.trans hdb, hc, hd]

@[gcongr]
lemma div_lt_div₀ (hac : a < c) (hdb : d ≤ b) (hc : 0 ≤ c) (hd : 0 < d) : a / b < c / d := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  apply mul_lt_mul hac (by gcongr; assumption) _ hc
  exact inv_pos.2 (hd.trans_le hdb)

lemma div_lt_div₀' (hac : a ≤ c) (hdb : d < b) (hc : 0 < c) (hd : 0 < d) : a / b < c / d := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_lt_mul' hac ((inv_lt_inv₀ (hd.trans hdb) hd).2 hdb)
    (inv_nonneg.2 <| hd.le.trans hdb.le) hc

end Both

end PartialOrder

section LinearOrder
variable [LinearOrder G₀] {a b c d : G₀}

section PosMulMono
variable [PosMulMono G₀]

@[simp] lemma inv_neg'' : a⁻¹ < 0 ↔ a < 0 := by
  have := PosMulMono.toPosMulReflectLT (α := G₀); simp only [← not_le, inv_nonneg]

@[simp] lemma inv_nonpos : a⁻¹ ≤ 0 ↔ a ≤ 0 := by
  have := PosMulMono.toPosMulReflectLT (α := G₀); simp only [← not_lt, inv_pos]

alias inv_lt_zero := inv_neg''

lemma one_div_neg : 1 / a < 0 ↔ a < 0 := one_div a ▸ inv_neg''
lemma one_div_nonpos : 1 / a ≤ 0 ↔ a ≤ 0 := one_div a ▸ inv_nonpos

lemma div_nonpos_of_nonneg_of_nonpos (ha : 0 ≤ a) (hb : b ≤ 0) : a / b ≤ 0 := by
  rw [div_eq_mul_inv]; exact mul_nonpos_of_nonneg_of_nonpos ha (inv_nonpos.2 hb)

lemma neg_of_div_neg_right (h : a / b < 0) (ha : 0 ≤ a) : b < 0 :=
  have := PosMulMono.toPosMulReflectLT (α := G₀)
  lt_of_not_ge fun hb ↦ (div_nonneg ha hb).not_gt h

lemma neg_of_div_neg_left (h : a / b < 0) (hb : 0 ≤ b) : a < 0 :=
  have := PosMulMono.toPosMulReflectLT (α := G₀)
  lt_of_not_ge fun ha ↦ (div_nonneg ha hb).not_gt h

end PosMulMono

variable {m n : ℤ}

section ZeroLEOne

variable [PosMulStrictMono G₀]

variable [ZeroLEOneClass G₀]

lemma inv_lt_one_iff₀ : a⁻¹ < 1 ↔ a ≤ 0 ∨ 1 < a := by
  simp_rw [← not_le, one_le_inv_iff₀, not_and_or, not_lt]

lemma inv_le_one_iff₀ : a⁻¹ ≤ 1 ↔ a ≤ 0 ∨ 1 ≤ a := by
  simp only [← not_lt, one_lt_inv_iff₀, not_and_or]

lemma zpow_right_injective₀ (ha₀ : 0 < a) (ha₁ : a ≠ 1) : Injective fun n : ℤ ↦ a ^ n := by
  obtain ha₁ | ha₁ := ha₁.lt_or_gt
  · exact (zpow_right_strictAnti₀ ha₀ ha₁).injective
  · exact (zpow_right_strictMono₀ ha₁).injective

@[simp] lemma zpow_right_inj₀ (ha₀ : 0 < a) (ha₁ : a ≠ 1) : a ^ m = a ^ n ↔ m = n :=
  (zpow_right_injective₀ ha₀ ha₁).eq_iff

lemma zpow_eq_one_iff_right₀ (ha₀ : 0 ≤ a) (ha₁ : a ≠ 1) {n : ℤ} : a ^ n = 1 ↔ n = 0 := by
  obtain rfl | ha₀ := ha₀.eq_or_lt
  · exact zero_zpow_eq_one₀
  simpa using zpow_right_inj₀ ha₀ ha₁ (n := 0)

end ZeroLEOne

section MulPosMono

variable [PosMulReflectLT G₀] [MulPosMono G₀]

lemma zpow_le_zpow_iff_left₀ (ha : 0 ≤ a) (hb : 0 ≤ b) (hn : 0 < n) : a ^ n ≤ b ^ n ↔ a ≤ b :=
  (zpow_left_strictMonoOn₀ (G₀ := G₀) hn).le_iff_le ha hb

lemma zpow_lt_zpow_iff_left₀ (ha : 0 ≤ a) (hb : 0 ≤ b) (hn : 0 < n) : a ^ n < b ^ n ↔ a < b :=
  (zpow_left_strictMonoOn₀ (G₀ := G₀) hn).lt_iff_lt ha hb

end MulPosMono

section PosMulStrictMono
variable [PosMulStrictMono G₀] [MulPosMono G₀]

lemma zpow_left_injOn₀ : ∀ {n : ℤ}, n ≠ 0 → {a | 0 ≤ a}.InjOn fun a : G₀ ↦ a ^ n
  | (n + 1 : ℕ), _ => by simpa using! mod_cast (pow_left_strictMonoOn₀ n.succ_ne_zero).injOn
  | .negSucc n, _ => by
    simpa using! inv_injective.comp_injOn (pow_left_strictMonoOn₀ n.succ_ne_zero).injOn

lemma zpow_left_inj₀ (ha : 0 ≤ a) (hb : 0 ≤ b) (hn : n ≠ 0) :
    a ^ n = b ^ n ↔ a = b := (zpow_left_injOn₀ hn).eq_iff ha hb

end PosMulStrictMono
end GroupWithZero.LinearOrder

section CommGroupWithZero

section Preorder
variable [CommGroupWithZero G₀] [Preorder G₀] {a b c : G₀}

/-- Equality holds when `c ≠ 0`. See `mul_div_mul_left`. -/
lemma mul_div_mul_left_le (h : 0 ≤ a / b) : c * a / (c * b) ≤ a / b := by
  obtain rfl | hc := eq_or_ne c 0
  · simpa
  · rw [mul_div_mul_left _ _ hc]

/-- Equality holds when `c ≠ 0`. See `mul_div_mul_left`. -/
lemma le_mul_div_mul_left (h : a / b ≤ 0) : a / b ≤ c * a / (c * b) := by
  obtain rfl | hc := eq_or_ne c 0
  · simpa
  · rw [mul_div_mul_left _ _ hc]

end Preorder

variable [CommGroupWithZero G₀] [PartialOrder G₀] [PosMulReflectLT G₀] {a b c d : G₀}

attribute [local instance] PosMulReflectLT.toPosMulStrictMono PosMulMono.toMulPosMono
  PosMulStrictMono.toMulPosStrictMono PosMulReflectLT.toMulPosReflectLT

/-- See `le_inv_mul_iff₀` for a version with multiplication on the other side. -/
lemma le_inv_mul_iff₀' (hc : 0 < c) : a ≤ c⁻¹ * b ↔ a * c ≤ b := by
  rw [le_inv_mul_iff₀ hc, mul_comm]

/-- See `inv_mul_le_iff₀` for a version with multiplication on the other side. -/
lemma inv_mul_le_iff₀' (hc : 0 < c) : c⁻¹ * b ≤ a ↔ b ≤ a * c := by
  rw [inv_mul_le_iff₀ hc, mul_comm]

/-- See `le_mul_inv_iff₀` for a version with multiplication on the other side. -/
lemma le_mul_inv_iff₀' (hc : 0 < c) : a ≤ b * c⁻¹ ↔ c * a ≤ b := by
  rw [le_mul_inv_iff₀ hc, mul_comm]

/-- See `mul_inv_le_iff₀` for a version with multiplication on the other side. -/
lemma mul_inv_le_iff₀' (hc : 0 < c) : b * c⁻¹ ≤ a ↔ b ≤ c * a := by
  rw [mul_inv_le_iff₀ hc, mul_comm]

lemma div_le_div_iff₀ (hb : 0 < b) (hd : 0 < d) : a / b ≤ c / d ↔ a * d ≤ c * b := by
  rw [div_le_iff₀ hb, ← mul_div_right_comm, le_div_iff₀ hd]

/-- See `le_div_iff₀` for a version with multiplication on the other side. -/
lemma le_div_iff₀' (hc : 0 < c) : a ≤ b / c ↔ c * a ≤ b := by
  rw [le_div_iff₀ hc, mul_comm]

/-- See `div_le_iff₀` for a version with multiplication on the other side. -/
lemma div_le_iff₀' (hc : 0 < c) : b / c ≤ a ↔ b ≤ c * a := by
  rw [div_le_iff₀ hc, mul_comm]

lemma le_div_comm₀ (ha : 0 < a) (hc : 0 < c) : a ≤ b / c ↔ c ≤ b / a := by
  rw [le_div_iff₀ ha, le_div_iff₀' hc]

lemma div_le_comm₀ (hb : 0 < b) (hc : 0 < c) : a / b ≤ c ↔ a / c ≤ b := by
  rw [div_le_iff₀ hb, div_le_iff₀' hc]

/-- See `lt_inv_mul_iff₀` for a version with multiplication on the other side. -/
lemma lt_inv_mul_iff₀' (hc : 0 < c) : a < c⁻¹ * b ↔ a * c < b := by
  rw [lt_inv_mul_iff₀ hc, mul_comm]

/-- See `inv_mul_lt_iff₀` for a version with multiplication on the other side. -/
lemma inv_mul_lt_iff₀' (hc : 0 < c) : c⁻¹ * b < a ↔ b < a * c := by
  rw [inv_mul_lt_iff₀ hc, mul_comm]

/-- See `lt_mul_inv_iff₀` for a version with multiplication on the other side. -/
lemma lt_mul_inv_iff₀' (hc : 0 < c) : a < b * c⁻¹ ↔ c * a < b := by
  rw [lt_mul_inv_iff₀ hc, mul_comm]

/-- See `mul_inv_lt_iff₀` for a version with multiplication on the other side. -/
lemma mul_inv_lt_iff₀' (hc : 0 < c) : b * c⁻¹ < a ↔ b < c * a := by
  rw [mul_inv_lt_iff₀ hc, mul_comm]

lemma div_lt_div_iff₀ (hb : 0 < b) (hd : 0 < d) : a / b < c / d ↔ a * d < c * b := by
  rw [div_lt_iff₀ hb, ← mul_div_right_comm, lt_div_iff₀ hd]

/-- See `lt_div_iff₀` for a version with multiplication on the other side. -/
lemma lt_div_iff₀' (hc : 0 < c) : a < b / c ↔ c * a < b := by
  rw [lt_div_iff₀ hc, mul_comm]

/-- See `div_lt_iff₀` for a version with multiplication on the other side. -/
lemma div_lt_iff₀' (hc : 0 < c) : b / c < a ↔ b < c * a := by
  rw [div_lt_iff₀ hc, mul_comm]

lemma lt_div_comm₀ (ha : 0 < a) (hc : 0 < c) : a < b / c ↔ c < b / a := by
  rw [lt_div_iff₀ ha, lt_div_iff₀' hc]

lemma div_lt_comm₀ (hb : 0 < b) (hc : 0 < c) : a / b < c ↔ a / c < b := by
  rw [div_lt_iff₀ hb, div_lt_iff₀' hc]

end CommGroupWithZero
