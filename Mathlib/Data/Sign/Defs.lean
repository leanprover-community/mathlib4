/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.DeriveFintype

/-!
# Sign type

This file defines the type of signs $\{-1, 0, 1\}$ and its basic arithmetic instances.
-/

-- Don't generate unnecessary `sizeOf_spec` lemmas which the `simpNF` linter will complain about.
set_option genSizeOfSpec false in
/-- The type of signs. -/
inductive SignType
  | zero
  | neg
  | pos
  deriving DecidableEq, Inhabited, Fintype

namespace SignType

instance : Zero SignType :=
  ⟨zero⟩

instance : One SignType :=
  ⟨pos⟩

instance : Neg SignType :=
  ⟨fun s =>
    match s with
    | neg => pos
    | zero => zero
    | pos => neg⟩

@[simp]
theorem zero_eq_zero : zero = 0 :=
  rfl

@[simp]
theorem neg_eq_neg_one : neg = -1 :=
  rfl

@[simp]
theorem pos_eq_one : pos = 1 :=
  rfl

theorem trichotomy (a : SignType) : a = -1 ∨ a = 0 ∨ a = 1 := by
  cases a <;> simp

instance : Mul SignType :=
  ⟨fun x y =>
    match x with
    | neg => -y
    | zero => zero
    | pos => y⟩

/-- The less-than-or-equal relation on signs. -/
protected inductive LE : SignType → SignType → Prop
  | of_neg (a) : SignType.LE neg a
  | zero : SignType.LE zero zero
  | of_pos (a) : SignType.LE a pos

instance : LE SignType :=
  ⟨SignType.LE⟩

instance LE.decidableRel : DecidableRel SignType.LE := fun a b => by
  cases a <;> cases b <;> first | exact isTrue (by constructor) | exact isFalse (by rintro ⟨_⟩)

private lemma mul_comm : ∀ (a b : SignType), a * b = b * a := by rintro ⟨⟩ ⟨⟩ <;> rfl
private lemma mul_assoc : ∀ (a b c : SignType), (a * b) * c = a * (b * c) := by
  rintro ⟨⟩ ⟨⟩ ⟨⟩ <;> rfl

/- We can define a `Field` instance on `SignType`, but it's not mathematically sensible,
so we only define the `CommGroupWithZero`. -/
instance : CommGroupWithZero SignType where
  zero := 0
  one := 1
  mul := (· * ·)
  inv := id
  mul_zero a := by cases a <;> rfl
  zero_mul a := by cases a <;> rfl
  mul_one a := by cases a <;> rfl
  one_mul a := by cases a <;> rfl
  mul_inv_cancel a ha := by cases a <;> trivial
  mul_comm := mul_comm
  mul_assoc := mul_assoc
  exists_pair_ne := ⟨0, 1, by rintro ⟨_⟩⟩
  inv_zero := rfl

private lemma le_antisymm (a b : SignType) (_ : a ≤ b) (_ : b ≤ a) : a = b := by
  cases a <;> cases b <;> trivial

private lemma le_trans (a b c : SignType) (_ : a ≤ b) (_ : b ≤ c) : a ≤ c := by
  cases a <;> cases b <;> cases c <;> tauto

instance : LinearOrder SignType where
  le := (· ≤ ·)
  le_refl a := by cases a <;> constructor
  le_total a b := by cases a <;> cases b <;> first | left; constructor | right; constructor
  le_antisymm := le_antisymm
  le_trans := le_trans
  toDecidableLE := LE.decidableRel

instance : BoundedOrder SignType where
  top := 1
  le_top := LE.of_pos
  bot := -1
  bot_le :=
    #adaptation_note /-- https://github.com/leanprover/lean4/pull/6053
    Added `by exact`, but don't understand why it was needed. -/
    by exact LE.of_neg

instance : HasDistribNeg SignType where
  neg_neg := by rintro ⟨_⟩ <;> rfl
  neg_mul := by rintro ⟨_⟩ ⟨_⟩ <;> rfl
  mul_neg := by rintro ⟨_⟩ ⟨_⟩ <;> rfl

/-- `SignType` is equivalent to `Fin 3`. -/
def fin3Equiv : SignType ≃* Fin 3 where
  toFun a :=
    match a with
    | 0 => ⟨0, by simp⟩
    | 1 => ⟨1, by simp⟩
    | -1 => ⟨2, by simp⟩
  invFun a :=
    match a with
    | ⟨0, _⟩ => 0
    | ⟨1, _⟩ => 1
    | ⟨2, _⟩ => -1
  left_inv a := by cases a <;> rfl
  right_inv a :=
    match a with
    | ⟨0, _⟩ => by simp
    | ⟨1, _⟩ => by simp
    | ⟨2, _⟩ => by simp
  map_mul' a b := by
    cases a <;> cases b <;> rfl

section CaseBashing

theorem nonneg_iff {a : SignType} : 0 ≤ a ↔ a = 0 ∨ a = 1 := by decide +revert

theorem nonneg_iff_ne_neg_one {a : SignType} : 0 ≤ a ↔ a ≠ -1 := by decide +revert

theorem neg_one_lt_iff {a : SignType} : -1 < a ↔ 0 ≤ a := by decide +revert

theorem nonpos_iff {a : SignType} : a ≤ 0 ↔ a = -1 ∨ a = 0 := by decide +revert

theorem nonpos_iff_ne_one {a : SignType} : a ≤ 0 ↔ a ≠ 1 := by decide +revert

theorem lt_one_iff {a : SignType} : a < 1 ↔ a ≤ 0 := by decide +revert

@[simp]
theorem neg_iff {a : SignType} : a < 0 ↔ a = -1 := by decide +revert

@[simp]
theorem le_neg_one_iff {a : SignType} : a ≤ -1 ↔ a = -1 :=
  le_bot_iff

@[simp]
theorem pos_iff {a : SignType} : 0 < a ↔ a = 1 := by decide +revert

@[simp]
theorem one_le_iff {a : SignType} : 1 ≤ a ↔ a = 1 :=
  top_le_iff

@[simp]
theorem neg_one_le (a : SignType) : -1 ≤ a :=
  bot_le

@[simp]
theorem le_one (a : SignType) : a ≤ 1 :=
  le_top

@[simp]
theorem not_lt_neg_one (a : SignType) : ¬a < -1 :=
  not_lt_bot

@[simp]
theorem not_one_lt (a : SignType) : ¬1 < a :=
  not_top_lt

@[simp]
theorem self_eq_neg_iff {a : SignType} : a = -a ↔ a = 0 := by decide +revert

@[simp]
theorem neg_eq_self_iff {a : SignType} : -a = a ↔ a = 0 := by decide +revert

@[simp]
theorem neg_eq_zero_iff {a : SignType} : -a = 0 ↔ a = 0 := by decide +revert

@[simp]
theorem neg_one_lt_one : (-1 : SignType) < 1 :=
  bot_lt_top

end CaseBashing

section cast

variable {α : Type*} [Zero α] [One α] [Neg α]

/-- Turn a `SignType` into zero, one, or minus one. This is a coercion instance. -/
@[coe]
def cast : SignType → α
  | zero => 0
  | pos => 1
  | neg => -1

/-- This is a `CoeTail` since the type on the right (trivially) determines the type on the left.

`outParam`-wise it could be a `Coe`, but we don't want to try applying this instance for a
coercion to any `α`.
-/
instance : CoeTail SignType α :=
  ⟨cast⟩

/-- Casting out of `SignType` respects composition with functions preserving `0, 1, -1`. -/
lemma map_cast' {β : Type*} [One β] [Neg β] [Zero β]
    (f : α → β) (h₁ : f 1 = 1) (h₂ : f 0 = 0) (h₃ : f (-1) = -1) (s : SignType) :
    f s = s := by
  cases s <;> simp only [SignType.cast, h₁, h₂, h₃]

/-- Casting out of `SignType` respects composition with suitable bundled homomorphism types. -/
lemma map_cast {α β F : Type*} [AddGroupWithOne α] [One β] [SubtractionMonoid β]
    [FunLike F α β] [AddMonoidHomClass F α β] [OneHomClass F α β] (f : F) (s : SignType) :
    f s = s := by
  apply map_cast' <;> simp

@[simp]
theorem coe_zero : ↑(0 : SignType) = (0 : α) :=
  rfl

@[simp]
theorem coe_one : ↑(1 : SignType) = (1 : α) :=
  rfl

@[simp]
theorem coe_neg_one : ↑(-1 : SignType) = (-1 : α) :=
  rfl

@[simp, norm_cast]
lemma coe_neg {α : Type*} [One α] [SubtractionMonoid α] (s : SignType) :
    (↑(-s) : α) = -↑s := by
  cases s <;> simp

end cast

end SignType

variable {α : Type*}

open SignType

section Preorder

variable [Zero α] [Preorder α] [DecidableLT α] {a : α}

/-- The sign of an element is 1 if it's positive, -1 if negative, 0 otherwise. -/
def SignType.sign : α →o SignType :=
  ⟨fun a => if 0 < a then 1 else if a < 0 then -1 else 0, fun a b h => by
    dsimp
    split_ifs with h₁ h₂ h₃ h₄ _ _ h₂ h₃ <;> try constructor
    · cases lt_irrefl 0 (h₁.trans <| h.trans_lt h₃)
    · cases h₂ (h₁.trans_le h)
    · cases h₄ (h.trans_lt h₃)⟩

theorem sign_apply : sign a = ite (0 < a) 1 (ite (a < 0) (-1) 0) :=
  rfl

@[simp]
theorem sign_zero : sign (0 : α) = 0 := by simp [sign_apply]

@[simp]
theorem sign_pos (ha : 0 < a) : sign a = 1 := by rwa [sign_apply, if_pos]

@[simp]
theorem sign_neg (ha : a < 0) : sign a = -1 := by rwa [sign_apply, if_neg <| asymm ha, if_pos]

theorem sign_eq_one_iff : sign a = 1 ↔ 0 < a := by
  refine ⟨fun h => ?_, fun h => sign_pos h⟩
  by_contra hn
  rw [sign_apply, if_neg hn] at h
  split_ifs at h

theorem sign_eq_neg_one_iff : sign a = -1 ↔ a < 0 := by
  refine ⟨fun h => ?_, fun h => sign_neg h⟩
  rw [sign_apply] at h
  split_ifs at h
  assumption

end Preorder

section LinearOrder

variable [Zero α] [LinearOrder α] {a : α}

/-- `SignType.sign` respects strictly monotone zero-preserving maps. -/
lemma StrictMono.sign_comp {β F : Type*} [Zero β] [Preorder β] [DecidableLT β]
    [FunLike F α β] [ZeroHomClass F α β] {f : F} (hf : StrictMono f) (a : α) :
    sign (f a) = sign a := by
  simp only [sign_apply, ← map_zero f, hf.lt_iff_lt]

@[simp]
theorem sign_eq_zero_iff : sign a = 0 ↔ a = 0 := by
  refine ⟨fun h => ?_, fun h => h.symm ▸ sign_zero⟩
  rw [sign_apply] at h
  split_ifs at h with h_1 h_2
  cases h
  exact (le_of_not_gt h_1).eq_of_not_lt h_2

theorem sign_ne_zero : sign a ≠ 0 ↔ a ≠ 0 :=
  sign_eq_zero_iff.not

@[simp]
theorem sign_nonneg_iff : 0 ≤ sign a ↔ 0 ≤ a := by
  rcases lt_trichotomy 0 a with (h | h | h)
  · simp [h, h.le]
  · simp [← h]
  · simp [h, h.not_ge]

@[simp]
theorem sign_nonpos_iff : sign a ≤ 0 ↔ a ≤ 0 := by
  rcases lt_trichotomy 0 a with (h | h | h)
  · simp [h, h.not_ge]
  · simp [← h]
  · simp [h, h.le]

end LinearOrder

section OrderedSemiring

variable [Semiring α] [PartialOrder α] [IsOrderedRing α] [DecidableLT α] [Nontrivial α]

theorem sign_one : sign (1 : α) = 1 :=
  sign_pos zero_lt_one

end OrderedSemiring

section AddGroup

variable [AddGroup α] [Preorder α] [DecidableLT α]

theorem Left.sign_neg [AddLeftStrictMono α] (a : α) : sign (-a) = -sign a := by
  simp_rw [sign_apply, Left.neg_pos_iff, Left.neg_neg_iff]
  split_ifs with h h'
  · exact False.elim (lt_asymm h h')
  · simp
  · simp
  · simp

theorem Right.sign_neg [AddRightStrictMono α] (a : α) :
    sign (-a) = -sign a := by
  simp_rw [sign_apply, Right.neg_pos_iff, Right.neg_neg_iff]
  split_ifs with h h'
  · exact False.elim (lt_asymm h h')
  · simp
  · simp
  · simp

end AddGroup

theorem Int.sign_eq_sign (n : ℤ) : Int.sign n = SignType.sign n := by
  obtain (n | _) | _ := n <;> simp [sign, negSucc_lt_zero]
