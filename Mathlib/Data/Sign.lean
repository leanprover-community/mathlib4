/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Cast
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.DeriveFintype

/-!
# Sign function

This file defines the sign function for types with zero and a decidable less-than relation, and
proves some basic theorems about it.
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
  cases a <;> cases b <;> first | exact isTrue (by constructor)| exact isFalse (by rintro ⟨_⟩)

instance decidableEq : DecidableEq SignType := fun a b => by
  cases a <;> cases b <;> first | exact isTrue (by constructor)| exact isFalse (by rintro ⟨_⟩)

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
  toDecidableEq := SignType.decidableEq

instance : BoundedOrder SignType where
  top := 1
  le_top := LE.of_pos
  bot := -1
  bot_le :=
    #adaptation_note /-- https://github.com/leanprover/lean4/pull/6053
    Added `by exact`, but don't understand why it was needed. -/
    by exact LE.of_neg

instance : HasDistribNeg SignType :=
  { neg_neg := fun x => by cases x <;> rfl
    neg_mul := fun x y => by cases x <;> cases y <;> rfl
    mul_neg := fun x y => by cases x <;> cases y <;> rfl }

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
theorem self_eq_neg_iff (a : SignType) : a = -a ↔ a = 0 := by decide +revert

@[simp]
theorem neg_eq_self_iff (a : SignType) : -a = a ↔ a = 0 := by decide +revert

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

/-- Casting `SignType → ℤ → α` is the same as casting directly `SignType → α`. -/
@[simp, norm_cast]
lemma intCast_cast {α : Type*} [AddGroupWithOne α] (s : SignType) : ((s : ℤ) : α) = s :=
  map_cast' _ Int.cast_one Int.cast_zero (@Int.cast_one α _ ▸ Int.cast_neg 1) _

end cast

/-- `SignType.cast` as a `MulWithZeroHom`. -/
@[simps]
def castHom {α} [MulZeroOneClass α] [HasDistribNeg α] : SignType →*₀ α where
  toFun := cast
  map_zero' := rfl
  map_one' := rfl
  map_mul' x y := by cases x <;> cases y <;> simp [zero_eq_zero, pos_eq_one, neg_eq_neg_one]

theorem univ_eq : (Finset.univ : Finset SignType) = {0, -1, 1} := by
  decide

theorem range_eq {α} (f : SignType → α) : Set.range f = {f zero, f neg, f pos} := by
  classical rw [← Fintype.coe_image_univ, univ_eq]
  classical simp [Finset.coe_insert]

@[simp, norm_cast] lemma coe_mul {α} [MulZeroOneClass α] [HasDistribNeg α] (a b : SignType) :
    ↑(a * b) = (a : α) * b :=
  map_mul SignType.castHom _ _

@[simp, norm_cast] lemma coe_pow {α} [MonoidWithZero α] [HasDistribNeg α] (a : SignType) (k : ℕ) :
    ↑(a ^ k) = (a : α) ^ k :=
  map_pow SignType.castHom _ _

@[simp, norm_cast] lemma coe_zpow {α} [GroupWithZero α] [HasDistribNeg α] (a : SignType) (k : ℤ) :
    ↑(a ^ k) = (a : α) ^ k :=
  map_zpow₀ SignType.castHom _ _

end SignType

-- The lemma `exists_signed_sum` needs explicit universe handling in its statement.
universe u

variable {α : Type u}

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

section OrderedRing

@[simp]
lemma sign_intCast {α : Type*} [Ring α] [PartialOrder α] [IsOrderedRing α]
    [Nontrivial α] [DecidableLT α] (n : ℤ) :
    sign (n : α) = sign n := by
  simp only [sign_apply, Int.cast_pos, Int.cast_lt_zero]

end OrderedRing

section LinearOrderedRing

variable [Ring α] [LinearOrder α] [IsStrictOrderedRing α]

theorem sign_mul (x y : α) : sign (x * y) = sign x * sign y := by
  rcases lt_trichotomy x 0 with (hx | hx | hx) <;> rcases lt_trichotomy y 0 with (hy | hy | hy) <;>
    simp [hx, hy, mul_pos_of_neg_of_neg, mul_neg_of_neg_of_pos, mul_neg_of_pos_of_neg]

@[simp] theorem sign_mul_abs (x : α) : (sign x * |x| : α) = x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx <;> simp [*, abs_of_pos, abs_of_neg]

@[simp] theorem abs_mul_sign (x : α) : (|x| * sign x : α) = x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx <;> simp [*, abs_of_pos, abs_of_neg]

@[simp]
theorem sign_mul_self (x : α) : sign x * x = |x| := by
  rcases lt_trichotomy x 0 with hx | rfl | hx <;> simp [*, abs_of_pos, abs_of_neg]

@[simp]
theorem self_mul_sign (x : α) : x * sign x = |x| := by
  rcases lt_trichotomy x 0 with hx | rfl | hx <;> simp [*, abs_of_pos, abs_of_neg]

/-- `SignType.sign` as a `MonoidWithZeroHom` for a nontrivial ordered semiring. Note that linearity
is required; consider ℂ with the order `z ≤ w` iff they have the same imaginary part and
`z - w ≤ 0` in the reals; then `1 + I` and `1 - I` are incomparable to zero, and thus we have:
`0 * 0 = SignType.sign (1 + I) * SignType.sign (1 - I) ≠ SignType.sign 2 = 1`.
(`Complex.orderedCommRing`) -/
def signHom : α →*₀ SignType where
  toFun := sign
  map_zero' := sign_zero
  map_one' := sign_one
  map_mul' := sign_mul

theorem sign_pow (x : α) (n : ℕ) : sign (x ^ n) = sign x ^ n := map_pow signHom x n

end LinearOrderedRing

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

section LinearOrderedAddCommGroup

variable [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]

theorem sign_sum {ι : Type*} {s : Finset ι} {f : ι → α} (hs : s.Nonempty) (t : SignType)
    (h : ∀ i ∈ s, sign (f i) = t) : sign (∑ i ∈ s, f i) = t := by
  cases t
  · simp_rw [zero_eq_zero, sign_eq_zero_iff] at h ⊢
    exact Finset.sum_eq_zero h
  · simp_rw [neg_eq_neg_one, sign_eq_neg_one_iff] at h ⊢
    exact Finset.sum_neg h hs
  · simp_rw [pos_eq_one, sign_eq_one_iff] at h ⊢
    exact Finset.sum_pos h hs

end LinearOrderedAddCommGroup

namespace Int

theorem sign_eq_sign (n : ℤ) : Int.sign n = SignType.sign n := by
  obtain (n | _) | _ := n <;> simp [sign, Int.sign_neg, negSucc_lt_zero]

end Int

open Finset Nat

section exists_signed_sum

/-!
In this section we explicitly handle universe variables,
because Lean creates a fresh universe variable for the type whose existence is asserted.
But we want the type to live in the same universe as the input type.
-/

private theorem exists_signed_sum_aux [DecidableEq α] (s : Finset α) (f : α → ℤ) :
    ∃ (β : Type u) (t : Finset β) (sgn : β → SignType) (g : β → α),
      (∀ b, g b ∈ s) ∧
        (#t = ∑ a ∈ s, (f a).natAbs) ∧
          ∀ a ∈ s, (∑ b ∈ t, if g b = a then (sgn b : ℤ) else 0) = f a := by
  refine
    ⟨(Σ _ : { x // x ∈ s }, ℕ), Finset.univ.sigma fun a => range (f a).natAbs,
      fun a => sign (f a.1), fun a => a.1, fun a => a.1.2, ?_, ?_⟩
  · simp [sum_attach (f := fun a => (f a).natAbs)]
  · intro x hx
    simp [sum_sigma, hx, ← Int.sign_eq_sign, Int.sign_mul_abs, mul_comm |f _|,
      sum_attach (s := s) (f := fun y => if y = x then f y else 0)]

/-- We can decompose a sum of absolute value `n` into a sum of `n` signs. -/
theorem exists_signed_sum [DecidableEq α] (s : Finset α) (f : α → ℤ) :
    ∃ (β : Type u) (_ : Fintype β) (sgn : β → SignType) (g : β → α),
      (∀ b, g b ∈ s) ∧
        (Fintype.card β = ∑ a ∈ s, (f a).natAbs) ∧
          ∀ a ∈ s, (∑ b, if g b = a then (sgn b : ℤ) else 0) = f a :=
  let ⟨β, t, sgn, g, hg, ht, hf⟩ := exists_signed_sum_aux s f
  ⟨t, inferInstance, fun b => sgn b, fun b => g b, fun b => hg b, by simp [ht], fun a ha =>
    (sum_attach t fun b ↦ ite (g b = a) (sgn b : ℤ) 0).trans <| hf _ ha⟩

/-- We can decompose a sum of absolute value less than `n` into a sum of at most `n` signs. -/
theorem exists_signed_sum' [Nonempty α] [DecidableEq α] (s : Finset α) (f : α → ℤ)
    (n : ℕ) (h : (∑ i ∈ s, (f i).natAbs) ≤ n) :
    ∃ (β : Type u) (_ : Fintype β) (sgn : β → SignType) (g : β → α),
      (∀ b, g b ∉ s → sgn b = 0) ∧
        Fintype.card β = n ∧ ∀ a ∈ s, (∑ i, if g i = a then (sgn i : ℤ) else 0) = f a := by
  obtain ⟨β, _, sgn, g, hg, hβ, hf⟩ := exists_signed_sum s f
  refine
    ⟨β ⊕ (Fin (n - ∑ i ∈ s, (f i).natAbs)), inferInstance, Sum.elim sgn 0,
      Sum.elim g (Classical.arbitrary (Fin (n - Finset.sum s fun i => Int.natAbs (f i)) → α)),
        ?_, by simp [hβ, h], fun a ha => by simp [hf _ ha]⟩
  rintro (b | b) hb
  · cases hb (hg _)
  · rfl

end exists_signed_sum
