/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Monoid.OrderDual
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Order.WithBot

#align_import algebra.order.monoid.with_top from "leanprover-community/mathlib"@"0111834459f5d7400215223ea95ae38a1265a907"

/-! # Adjoining top/bottom elements to ordered monoids.
-/

universe u v

variable {α : Type u} {β : Type v}

open Function

namespace WithTop

section One

variable [One α] {a : α}

@[to_additive]
instance one : One (WithTop α) :=
  ⟨(1 : α)⟩
#align with_top.has_one WithTop.one
#align with_top.has_zero WithTop.zero

@[to_additive (attr := simp, norm_cast)]
theorem coe_one : ((1 : α) : WithTop α) = 1 :=
  rfl
#align with_top.coe_one WithTop.coe_one
#align with_top.coe_zero WithTop.coe_zero

@[to_additive (attr := simp, norm_cast)]
lemma coe_eq_one : (a : WithTop α) = 1 ↔ a = 1 := coe_eq_coe
#align with_top.coe_eq_one WithTop.coe_eq_one
#align with_top.coe_eq_zero WithTop.coe_eq_zero

@[to_additive (attr := simp, norm_cast)]
lemma one_eq_coe : 1 = (a : WithTop α) ↔ a = 1 := eq_comm.trans coe_eq_one
#align with_top.one_eq_coe WithTop.one_eq_coe
#align with_top.zero_eq_coe WithTop.zero_eq_coe

@[to_additive (attr := simp)] lemma top_ne_one : (⊤ : WithTop α) ≠ 1 := top_ne_coe
#align with_top.top_ne_one WithTop.top_ne_one
#align with_top.top_ne_zero WithTop.top_ne_zero

@[to_additive (attr := simp)] lemma one_ne_top : (1 : WithTop α) ≠ ⊤ := coe_ne_top
#align with_top.one_ne_top WithTop.one_ne_top
#align with_top.zero_ne_top WithTop.zero_ne_top

@[to_additive (attr := simp)]
theorem untop_one : (1 : WithTop α).untop coe_ne_top = 1 :=
  rfl
#align with_top.untop_one WithTop.untop_one
#align with_top.untop_zero WithTop.untop_zero

@[to_additive (attr := simp)]
theorem untop_one' (d : α) : (1 : WithTop α).untop' d = 1 :=
  rfl
#align with_top.untop_one' WithTop.untop_one'
#align with_top.untop_zero' WithTop.untop_zero'

@[to_additive (attr := simp, norm_cast) coe_nonneg]
theorem one_le_coe [LE α] {a : α} : 1 ≤ (a : WithTop α) ↔ 1 ≤ a :=
  coe_le_coe
#align with_top.one_le_coe WithTop.one_le_coe
#align with_top.coe_nonneg WithTop.coe_nonneg

@[to_additive (attr := simp, norm_cast) coe_le_zero]
theorem coe_le_one [LE α] {a : α} : (a : WithTop α) ≤ 1 ↔ a ≤ 1 :=
  coe_le_coe
#align with_top.coe_le_one WithTop.coe_le_one
#align with_top.coe_le_zero WithTop.coe_le_zero

@[to_additive (attr := simp, norm_cast) coe_pos]
theorem one_lt_coe [LT α] {a : α} : 1 < (a : WithTop α) ↔ 1 < a :=
  coe_lt_coe
#align with_top.one_lt_coe WithTop.one_lt_coe
#align with_top.coe_pos WithTop.coe_pos

@[to_additive (attr := simp, norm_cast) coe_lt_zero]
theorem coe_lt_one [LT α] {a : α} : (a : WithTop α) < 1 ↔ a < 1 :=
  coe_lt_coe
#align with_top.coe_lt_one WithTop.coe_lt_one
#align with_top.coe_lt_zero WithTop.coe_lt_zero

@[to_additive (attr := simp)]
protected theorem map_one {β} (f : α → β) : (1 : WithTop α).map f = (f 1 : WithTop β) :=
  rfl
#align with_top.map_one WithTop.map_one
#align with_top.map_zero WithTop.map_zero

instance zeroLEOneClass [Zero α] [LE α] [ZeroLEOneClass α] : ZeroLEOneClass (WithTop α) :=
  ⟨coe_le_coe.2 zero_le_one⟩

end One

section Add

variable [Add α] {a b c d : WithTop α} {x y : α}

instance add : Add (WithTop α) :=
  ⟨Option.map₂ (· + ·)⟩
#align with_top.has_add WithTop.add

@[simp, norm_cast] lemma coe_add (a b : α) : ↑(a + b) = (a + b : WithTop α) := rfl
#align with_top.coe_add WithTop.coe_add

section deprecated
set_option linter.deprecated false

@[norm_cast, deprecated]
theorem coe_bit0 : ((bit0 x : α) : WithTop α) = (bit0 x : WithTop α) :=
  rfl
#align with_top.coe_bit0 WithTop.coe_bit0

@[norm_cast, deprecated]
theorem coe_bit1 [One α] {a : α} : ((bit1 a : α) : WithTop α) = (bit1 a : WithTop α) :=
  rfl
#align with_top.coe_bit1 WithTop.coe_bit1

end deprecated

@[simp]
theorem top_add (a : WithTop α) : ⊤ + a = ⊤ :=
  rfl
#align with_top.top_add WithTop.top_add

@[simp]
theorem add_top (a : WithTop α) : a + ⊤ = ⊤ := by cases a <;> rfl
#align with_top.add_top WithTop.add_top

@[simp]
theorem add_eq_top : a + b = ⊤ ↔ a = ⊤ ∨ b = ⊤ := by
  match a, b with
  | ⊤, _ => simp
  | _, ⊤ => simp
  | (a : α), (b : α) => simp only [← coe_add, coe_ne_top, or_false]
#align with_top.add_eq_top WithTop.add_eq_top

theorem add_ne_top : a + b ≠ ⊤ ↔ a ≠ ⊤ ∧ b ≠ ⊤ :=
  add_eq_top.not.trans not_or
#align with_top.add_ne_top WithTop.add_ne_top

theorem add_lt_top [LT α] {a b : WithTop α} : a + b < ⊤ ↔ a < ⊤ ∧ b < ⊤ := by
  simp_rw [WithTop.lt_top_iff_ne_top, add_ne_top]
#align with_top.add_lt_top WithTop.add_lt_top

theorem add_eq_coe :
    ∀ {a b : WithTop α} {c : α}, a + b = c ↔ ∃ a' b' : α, ↑a' = a ∧ ↑b' = b ∧ a' + b' = c
  | ⊤, b, c => by simp
  | some a, ⊤, c => by simp
  | some a, some b, c => by norm_cast; simp
#align with_top.add_eq_coe WithTop.add_eq_coe

-- Porting note (#10618): simp can already prove this.
-- @[simp]
theorem add_coe_eq_top_iff {x : WithTop α} {y : α} : x + y = ⊤ ↔ x = ⊤ := by simp
#align with_top.add_coe_eq_top_iff WithTop.add_coe_eq_top_iff

-- Porting note (#10618): simp can already prove this.
-- @[simp]
theorem coe_add_eq_top_iff {y : WithTop α} : ↑x + y = ⊤ ↔ y = ⊤ := by simp
#align with_top.coe_add_eq_top_iff WithTop.coe_add_eq_top_iff

theorem add_right_cancel_iff [IsRightCancelAdd α] (ha : a ≠ ⊤) : b + a = c + a ↔ b = c := by
  lift a to α using ha
  obtain rfl | hb := eq_or_ne b ⊤
  · rw [top_add, eq_comm, WithTop.add_coe_eq_top_iff, eq_comm]
  lift b to α using hb
  simp_rw [← WithTop.coe_add, eq_comm, WithTop.add_eq_coe, coe_eq_coe, exists_and_left,
    exists_eq_left, add_left_inj, exists_eq_right, eq_comm]

theorem add_right_cancel [IsRightCancelAdd α] (ha : a ≠ ⊤) (h : b + a = c + a) : b = c :=
  (WithTop.add_right_cancel_iff ha).1 h

theorem add_left_cancel_iff [IsLeftCancelAdd α] (ha : a ≠ ⊤) : a + b = a + c ↔ b = c := by
  lift a to α using ha
  obtain rfl | hb := eq_or_ne b ⊤
  · rw [add_top, eq_comm, WithTop.coe_add_eq_top_iff, eq_comm]
  lift b to α using hb
  simp_rw [← WithTop.coe_add, eq_comm, WithTop.add_eq_coe, eq_comm, coe_eq_coe,
    exists_and_left, exists_eq_left', add_right_inj, exists_eq_right']

theorem add_left_cancel [IsLeftCancelAdd α] (ha : a ≠ ⊤) (h : a + b = a + c) : b = c :=
  (WithTop.add_left_cancel_iff ha).1 h

instance covariantClass_add_le [LE α] [CovariantClass α α (· + ·) (· ≤ ·)] :
    CovariantClass (WithTop α) (WithTop α) (· + ·) (· ≤ ·) :=
  ⟨fun a b c h => by
    cases a <;> cases c <;> try exact le_top
    rcases le_coe_iff.1 h with ⟨b, rfl, _⟩
    exact coe_le_coe.2 (add_le_add_left (coe_le_coe.1 h) _)⟩
#align with_top.covariant_class_add_le WithTop.covariantClass_add_le

instance covariantClass_swap_add_le [LE α] [CovariantClass α α (swap (· + ·)) (· ≤ ·)] :
    CovariantClass (WithTop α) (WithTop α) (swap (· + ·)) (· ≤ ·) :=
  ⟨fun a b c h => by
    cases a <;> cases c <;> try exact le_top
    rcases le_coe_iff.1 h with ⟨b, rfl, _⟩
    exact coe_le_coe.2 (add_le_add_right (coe_le_coe.1 h) _)⟩
#align with_top.covariant_class_swap_add_le WithTop.covariantClass_swap_add_le

instance contravariantClass_add_lt [LT α] [ContravariantClass α α (· + ·) (· < ·)] :
    ContravariantClass (WithTop α) (WithTop α) (· + ·) (· < ·) :=
  ⟨fun a b c h => by
    induction a; · exact (WithTop.not_top_lt _ h).elim
    induction b; · exact (WithTop.not_top_lt _ h).elim
    induction c
    · exact coe_lt_top _
    · exact coe_lt_coe.2 (lt_of_add_lt_add_left <| coe_lt_coe.1 h)⟩
#align with_top.contravariant_class_add_lt WithTop.contravariantClass_add_lt

instance contravariantClass_swap_add_lt [LT α] [ContravariantClass α α (swap (· + ·)) (· < ·)] :
    ContravariantClass (WithTop α) (WithTop α) (swap (· + ·)) (· < ·) :=
  ⟨fun a b c h => by
    cases a <;> cases b <;> try exact (WithTop.not_top_lt _ h).elim
    cases c
    · exact coe_lt_top _
    · exact coe_lt_coe.2 (lt_of_add_lt_add_right <| coe_lt_coe.1 h)⟩
#align with_top.contravariant_class_swap_add_lt WithTop.contravariantClass_swap_add_lt

protected theorem le_of_add_le_add_left [LE α] [ContravariantClass α α (· + ·) (· ≤ ·)] (ha : a ≠ ⊤)
    (h : a + b ≤ a + c) : b ≤ c := by
  lift a to α using ha
  induction c
  · exact le_top
  · induction b
    · exact (not_top_le_coe _ h).elim
    · simp only [← coe_add, coe_le_coe] at h ⊢
      exact le_of_add_le_add_left h
#align with_top.le_of_add_le_add_left WithTop.le_of_add_le_add_left

protected theorem le_of_add_le_add_right [LE α] [ContravariantClass α α (swap (· + ·)) (· ≤ ·)]
    (ha : a ≠ ⊤) (h : b + a ≤ c + a) : b ≤ c := by
  lift a to α using ha
  cases c
  · exact le_top
  · cases b
    · exact (not_top_le_coe _ h).elim
    · exact coe_le_coe.2 (le_of_add_le_add_right <| coe_le_coe.1 h)
#align with_top.le_of_add_le_add_right WithTop.le_of_add_le_add_right

protected theorem add_lt_add_left [LT α] [CovariantClass α α (· + ·) (· < ·)] (ha : a ≠ ⊤)
    (h : b < c) : a + b < a + c := by
  lift a to α using ha
  rcases lt_iff_exists_coe.1 h with ⟨b, rfl, h'⟩
  cases c
  · exact coe_lt_top _
  · exact coe_lt_coe.2 (add_lt_add_left (coe_lt_coe.1 h) _)
#align with_top.add_lt_add_left WithTop.add_lt_add_left

protected theorem add_lt_add_right [LT α] [CovariantClass α α (swap (· + ·)) (· < ·)] (ha : a ≠ ⊤)
    (h : b < c) : b + a < c + a := by
  lift a to α using ha
  rcases lt_iff_exists_coe.1 h with ⟨b, rfl, h'⟩
  cases c
  · exact coe_lt_top _
  · exact coe_lt_coe.2 (add_lt_add_right (coe_lt_coe.1 h) _)
#align with_top.add_lt_add_right WithTop.add_lt_add_right

protected theorem add_le_add_iff_left [LE α] [CovariantClass α α (· + ·) (· ≤ ·)]
    [ContravariantClass α α (· + ·) (· ≤ ·)] (ha : a ≠ ⊤) : a + b ≤ a + c ↔ b ≤ c :=
  ⟨WithTop.le_of_add_le_add_left ha, fun h => add_le_add_left h a⟩
#align with_top.add_le_add_iff_left WithTop.add_le_add_iff_left

protected theorem add_le_add_iff_right [LE α] [CovariantClass α α (swap (· + ·)) (· ≤ ·)]
    [ContravariantClass α α (swap (· + ·)) (· ≤ ·)] (ha : a ≠ ⊤) : b + a ≤ c + a ↔ b ≤ c :=
  ⟨WithTop.le_of_add_le_add_right ha, fun h => add_le_add_right h a⟩
#align with_top.add_le_add_iff_right WithTop.add_le_add_iff_right

protected theorem add_lt_add_iff_left [LT α] [CovariantClass α α (· + ·) (· < ·)]
    [ContravariantClass α α (· + ·) (· < ·)] (ha : a ≠ ⊤) : a + b < a + c ↔ b < c :=
  ⟨lt_of_add_lt_add_left, WithTop.add_lt_add_left ha⟩
#align with_top.add_lt_add_iff_left WithTop.add_lt_add_iff_left

protected theorem add_lt_add_iff_right [LT α] [CovariantClass α α (swap (· + ·)) (· < ·)]
    [ContravariantClass α α (swap (· + ·)) (· < ·)] (ha : a ≠ ⊤) : b + a < c + a ↔ b < c :=
  ⟨lt_of_add_lt_add_right, WithTop.add_lt_add_right ha⟩
#align with_top.add_lt_add_iff_right WithTop.add_lt_add_iff_right

protected theorem add_lt_add_of_le_of_lt [Preorder α] [CovariantClass α α (· + ·) (· < ·)]
    [CovariantClass α α (swap (· + ·)) (· ≤ ·)] (ha : a ≠ ⊤) (hab : a ≤ b) (hcd : c < d) :
    a + c < b + d :=
  (WithTop.add_lt_add_left ha hcd).trans_le <| add_le_add_right hab _
#align with_top.add_lt_add_of_le_of_lt WithTop.add_lt_add_of_le_of_lt

protected theorem add_lt_add_of_lt_of_le [Preorder α] [CovariantClass α α (· + ·) (· ≤ ·)]
    [CovariantClass α α (swap (· + ·)) (· < ·)] (hc : c ≠ ⊤) (hab : a < b) (hcd : c ≤ d) :
    a + c < b + d :=
  (WithTop.add_lt_add_right hc hab).trans_le <| add_le_add_left hcd _
#align with_top.add_lt_add_of_lt_of_le WithTop.add_lt_add_of_lt_of_le

--  There is no `WithTop.map_mul_of_mulHom`, since `WithTop` does not have a multiplication.
@[simp]
protected theorem map_add {F} [Add β] [FunLike F α β] [AddHomClass F α β]
    (f : F) (a b : WithTop α) :
    (a + b).map f = a.map f + b.map f := by
  induction a
  · exact (top_add _).symm
  · induction b
    · exact (add_top _).symm
    · rw [map_coe, map_coe, ← coe_add, ← coe_add, ← map_add]
      rfl
#align with_top.map_add WithTop.map_add

end Add

instance addSemigroup [AddSemigroup α] : AddSemigroup (WithTop α) :=
  { WithTop.add with
    add_assoc := fun _ _ _ => Option.map₂_assoc add_assoc }

instance addCommSemigroup [AddCommSemigroup α] : AddCommSemigroup (WithTop α) :=
  { WithTop.addSemigroup with
    add_comm := fun _ _ => Option.map₂_comm add_comm }

instance addZeroClass [AddZeroClass α] : AddZeroClass (WithTop α) :=
  { WithTop.zero, WithTop.add with
    zero_add := Option.map₂_left_identity zero_add
    add_zero := Option.map₂_right_identity add_zero }

section AddMonoid
variable [AddMonoid α]

instance addMonoid : AddMonoid (WithTop α) where
  __ := WithTop.addSemigroup
  __ := WithTop.addZeroClass
  nsmul n a := match a, n with
    | (a : α), n => ↑(n • a)
    | ⊤, 0 => 0
    | ⊤, _n + 1 => ⊤
  nsmul_zero a := by cases a <;> simp [zero_nsmul]
  nsmul_succ n a := by cases a <;> cases n <;> simp [succ_nsmul, coe_add]

@[simp, norm_cast] lemma coe_nsmul (a : α) (n : ℕ) : ↑(n • a) = n • (a : WithTop α) := rfl

/-- Coercion from `α` to `WithTop α` as an `AddMonoidHom`. -/
def addHom : α →+ WithTop α where
  toFun := WithTop.some
  map_zero' := rfl
  map_add' _ _ := rfl
#align with_top.coe_add_hom WithTop.addHom

@[simp, norm_cast] lemma coe_addHom : ⇑(addHom : α →+ WithTop α) = WithTop.some := rfl
#align with_top.coe_coe_add_hom WithTop.coe_addHom

end AddMonoid

instance addCommMonoid [AddCommMonoid α] : AddCommMonoid (WithTop α) :=
  { WithTop.addMonoid, WithTop.addCommSemigroup with }

section AddMonoidWithOne
variable [AddMonoidWithOne α]

instance addMonoidWithOne : AddMonoidWithOne (WithTop α) :=
  { WithTop.one, WithTop.addMonoid with
    natCast := fun n => ↑(n : α),
    natCast_zero := by
      simp only -- Porting note: Had to add this...?
      rw [Nat.cast_zero, WithTop.coe_zero],
    natCast_succ := fun n => by
      simp only -- Porting note: Had to add this...?
      rw [Nat.cast_add_one, WithTop.coe_add, WithTop.coe_one] }

@[simp, norm_cast] lemma coe_natCast (n : ℕ) : ((n : α) : WithTop α) = n := rfl
#align with_top.coe_nat WithTop.coe_natCast

@[simp] lemma natCast_ne_top (n : ℕ) : (n : WithTop α) ≠ ⊤ := coe_ne_top
#align with_top.nat_ne_top WithTop.natCast_ne_top

@[simp] lemma top_ne_natCast (n : ℕ) : (⊤ : WithTop α) ≠ n := top_ne_coe
#align with_top.top_ne_nat WithTop.top_ne_natCast

-- 2024-04-05
@[deprecated] alias coe_nat := coe_natCast
@[deprecated] alias nat_ne_top := natCast_ne_top
@[deprecated] alias top_ne_nat := top_ne_natCast

end AddMonoidWithOne

instance charZero [AddMonoidWithOne α] [CharZero α] : CharZero (WithTop α) :=
  { cast_injective := Function.Injective.comp (f := Nat.cast (R := α))
      (fun _ _ => WithTop.coe_eq_coe.1) Nat.cast_injective}

instance addCommMonoidWithOne [AddCommMonoidWithOne α] : AddCommMonoidWithOne (WithTop α) :=
  { WithTop.addMonoidWithOne, WithTop.addCommMonoid with }

instance orderedAddCommMonoid [OrderedAddCommMonoid α] : OrderedAddCommMonoid (WithTop α) where
  add_le_add_left _ _ := add_le_add_left

instance linearOrderedAddCommMonoidWithTop [LinearOrderedAddCommMonoid α] :
    LinearOrderedAddCommMonoidWithTop (WithTop α) :=
  { WithTop.orderTop, WithTop.linearOrder, WithTop.orderedAddCommMonoid with
    top_add' := WithTop.top_add }

instance existsAddOfLE [LE α] [Add α] [ExistsAddOfLE α] : ExistsAddOfLE (WithTop α) :=
  ⟨fun {a} {b} =>
    match a, b with
    | ⊤, ⊤ => by simp
    | (a : α), ⊤ => fun _ => ⟨⊤, rfl⟩
    | (a : α), (b : α) => fun h => by
      obtain ⟨c, rfl⟩ := exists_add_of_le (WithTop.coe_le_coe.1 h)
      exact ⟨c, rfl⟩
    | ⊤, (b : α) => fun h => (not_top_le_coe _ h).elim⟩

instance canonicallyOrderedAddCommMonoid [CanonicallyOrderedAddCommMonoid α] :
    CanonicallyOrderedAddCommMonoid (WithTop α) :=
  { WithTop.orderBot, WithTop.orderedAddCommMonoid, WithTop.existsAddOfLE with
    le_self_add := fun a b =>
      match a, b with
      | ⊤, ⊤ => le_rfl
      | (a : α), ⊤ => le_top
      | (a : α), (b : α) => WithTop.coe_le_coe.2 le_self_add
      | ⊤, (b : α) => le_rfl }

instance [CanonicallyLinearOrderedAddCommMonoid α] :
    CanonicallyLinearOrderedAddCommMonoid (WithTop α) :=
  { WithTop.canonicallyOrderedAddCommMonoid, WithTop.linearOrder with }

@[simp]
theorem zero_lt_top [OrderedAddCommMonoid α] : (0 : WithTop α) < ⊤ :=
  coe_lt_top 0
#align with_top.zero_lt_top WithTop.zero_lt_top

-- Porting note (#10618): simp can already prove this.
-- @[simp]
@[norm_cast]
theorem zero_lt_coe [OrderedAddCommMonoid α] (a : α) : (0 : WithTop α) < a ↔ 0 < a :=
  coe_lt_coe
#align with_top.zero_lt_coe WithTop.zero_lt_coe

/-- A version of `WithTop.map` for `OneHom`s. -/
@[to_additive (attr := simps (config := .asFn))
  "A version of `WithTop.map` for `ZeroHom`s"]
protected def _root_.OneHom.withTopMap {M N : Type*} [One M] [One N] (f : OneHom M N) :
    OneHom (WithTop M) (WithTop N) where
  toFun := WithTop.map f
  map_one' := by rw [WithTop.map_one, map_one, coe_one]
#align one_hom.with_top_map OneHom.withTopMap
#align zero_hom.with_top_map ZeroHom.withTopMap
#align one_hom.with_top_map_apply OneHom.withTopMap_apply

/-- A version of `WithTop.map` for `AddHom`s. -/
@[simps (config := .asFn)]
protected def _root_.AddHom.withTopMap {M N : Type*} [Add M] [Add N] (f : AddHom M N) :
    AddHom (WithTop M) (WithTop N) where
  toFun := WithTop.map f
  map_add' := WithTop.map_add f
#align add_hom.with_top_map AddHom.withTopMap
#align add_hom.with_top_map_apply AddHom.withTopMap_apply

/-- A version of `WithTop.map` for `AddMonoidHom`s. -/
@[simps (config := .asFn)]
protected def _root_.AddMonoidHom.withTopMap {M N : Type*} [AddZeroClass M] [AddZeroClass N]
    (f : M →+ N) : WithTop M →+ WithTop N :=
  { ZeroHom.withTopMap f.toZeroHom, AddHom.withTopMap f.toAddHom with toFun := WithTop.map f }
#align add_monoid_hom.with_top_map AddMonoidHom.withTopMap
#align add_monoid_hom.with_top_map_apply AddMonoidHom.withTopMap_apply

end WithTop

namespace WithBot
section One
variable [One α] {a : α}

@[to_additive] instance one : One (WithBot α) := WithTop.one

@[to_additive (attr := simp, norm_cast)] lemma coe_one : ((1 : α) : WithBot α) = 1 := rfl
#align with_bot.coe_one WithBot.coe_one
#align with_bot.coe_zero WithBot.coe_zero

@[to_additive (attr := simp, norm_cast)]
lemma coe_eq_one : (a : WithBot α) = 1 ↔ a = 1 := coe_eq_coe
#align with_bot.coe_eq_one WithBot.coe_eq_one
#align with_bot.coe_eq_zero WithBot.coe_eq_zero

@[to_additive (attr := simp, norm_cast)]
lemma one_eq_coe : 1 = (a : WithBot α) ↔ a = 1 := eq_comm.trans coe_eq_one

@[to_additive (attr := simp)] lemma bot_ne_one : (⊥ : WithBot α) ≠ 1 := bot_ne_coe
@[to_additive (attr := simp)] lemma one_ne_bot : (1 : WithBot α) ≠ ⊥ := coe_ne_bot

@[to_additive (attr := simp)]
theorem unbot_one : (1 : WithBot α).unbot coe_ne_bot = 1 :=
  rfl
#align with_bot.unbot_one WithBot.unbot_one
#align with_bot.unbot_zero WithBot.unbot_zero

@[to_additive (attr := simp)]
theorem unbot_one' (d : α) : (1 : WithBot α).unbot' d = 1 :=
  rfl
#align with_bot.unbot_one' WithBot.unbot_one'
#align with_bot.unbot_zero' WithBot.unbot_zero'

@[to_additive (attr := simp, norm_cast) coe_nonneg]
theorem one_le_coe [LE α] : 1 ≤ (a : WithBot α) ↔ 1 ≤ a := coe_le_coe
#align with_bot.one_le_coe WithBot.one_le_coe
#align with_bot.coe_nonneg WithBot.coe_nonneg

@[to_additive (attr := simp, norm_cast) coe_le_zero]
theorem coe_le_one [LE α] : (a : WithBot α) ≤ 1 ↔ a ≤ 1 := coe_le_coe
#align with_bot.coe_le_one WithBot.coe_le_one
#align with_bot.coe_le_zero WithBot.coe_le_zero

@[to_additive (attr := simp, norm_cast) coe_pos]
theorem one_lt_coe [LT α] : 1 < (a : WithBot α) ↔ 1 < a := coe_lt_coe
#align with_bot.one_lt_coe WithBot.one_lt_coe
#align with_bot.coe_pos WithBot.coe_pos

@[to_additive (attr := simp, norm_cast) coe_lt_zero]
theorem coe_lt_one [LT α] : (a : WithBot α) < 1 ↔ a < 1 := coe_lt_coe
#align with_bot.coe_lt_one WithBot.coe_lt_one
#align with_bot.coe_lt_zero WithBot.coe_lt_zero

@[to_additive (attr := simp)]
protected theorem map_one {β} (f : α → β) : (1 : WithBot α).map f = (f 1 : WithBot β) :=
  rfl
#align with_bot.map_one WithBot.map_one
#align with_bot.map_zero WithBot.map_zero

instance zeroLEOneClass [Zero α] [LE α] [ZeroLEOneClass α] : ZeroLEOneClass (WithBot α) :=
  ⟨coe_le_coe.2 zero_le_one⟩

end One

instance add [Add α] : Add (WithBot α) :=
  WithTop.add

instance AddSemigroup [AddSemigroup α] : AddSemigroup (WithBot α) :=
  WithTop.addSemigroup

instance addCommSemigroup [AddCommSemigroup α] : AddCommSemigroup (WithBot α) :=
  WithTop.addCommSemigroup

instance addZeroClass [AddZeroClass α] : AddZeroClass (WithBot α) :=
  WithTop.addZeroClass

section AddMonoid
variable [AddMonoid α]

instance addMonoid : AddMonoid (WithBot α) := WithTop.addMonoid

/-- Coercion from `α` to `WithBot α` as an `AddMonoidHom`. -/
def addHom : α →+ WithBot α where
  toFun := WithTop.some
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp, norm_cast] lemma coe_addHom : ⇑(addHom : α →+ WithBot α) = WithBot.some := rfl

@[simp, norm_cast]
lemma coe_nsmul (a : α) (n : ℕ) : ↑(n • a) = n • (a : WithBot α) :=
  (addHom : α →+ WithBot α).map_nsmul _ _
#align with_bot.coe_nsmul WithBot.coe_nsmul

end AddMonoid

instance addCommMonoid [AddCommMonoid α] : AddCommMonoid (WithBot α) :=
  WithTop.addCommMonoid

section AddMonoidWithOne
variable [AddMonoidWithOne α]

instance addMonoidWithOne : AddMonoidWithOne (WithBot α) := WithTop.addMonoidWithOne

@[norm_cast] lemma coe_natCast (n : ℕ) : ((n : α) : WithBot α) = n := rfl
#align with_bot.coe_nat WithBot.coe_natCast

@[simp] lemma natCast_ne_bot (n : ℕ) : (n : WithBot α) ≠ ⊥ := coe_ne_bot
#align with_bot.nat_ne_bot WithBot.natCast_ne_bot

@[simp] lemma bot_ne_natCast (n : ℕ) : (⊥ : WithBot α) ≠ n := bot_ne_coe
#align with_bot.bot_ne_nat WithBot.bot_ne_natCast

-- 2024-04-05
@[deprecated] alias coe_nat := coe_natCast
@[deprecated] alias nat_ne_bot := natCast_ne_bot
@[deprecated] alias bot_ne_nat := bot_ne_natCast

end AddMonoidWithOne

instance charZero [AddMonoidWithOne α] [CharZero α] : CharZero (WithBot α) :=
  WithTop.charZero

instance addCommMonoidWithOne [AddCommMonoidWithOne α] : AddCommMonoidWithOne (WithBot α) :=
  WithTop.addCommMonoidWithOne

section Add

variable [Add α] {a b c d : WithBot α} {x y : α}

@[simp, norm_cast]
theorem coe_add (a b : α) : ((a + b : α) : WithBot α) = a + b :=
  rfl
#align with_bot.coe_add WithBot.coe_add

section deprecated
set_option linter.deprecated false

-- Porting note: added norm_cast
@[norm_cast, deprecated]
theorem coe_bit0 : ((bit0 x : α) : WithBot α) = (bit0 x : WithBot α) :=
  rfl
#align with_bot.coe_bit0 WithBot.coe_bit0

-- Porting note: added norm_cast
@[norm_cast, deprecated]
theorem coe_bit1 [One α] {a : α} : ((bit1 a : α) : WithBot α) = (bit1 a : WithBot α) :=
  rfl
#align with_bot.coe_bit1 WithBot.coe_bit1

end deprecated

@[simp]
theorem bot_add (a : WithBot α) : ⊥ + a = ⊥ :=
  rfl
#align with_bot.bot_add WithBot.bot_add

@[simp]
theorem add_bot (a : WithBot α) : a + ⊥ = ⊥ := by cases a <;> rfl
#align with_bot.add_bot WithBot.add_bot

@[simp]
theorem add_eq_bot : a + b = ⊥ ↔ a = ⊥ ∨ b = ⊥ :=
  WithTop.add_eq_top
#align with_bot.add_eq_bot WithBot.add_eq_bot

theorem add_ne_bot : a + b ≠ ⊥ ↔ a ≠ ⊥ ∧ b ≠ ⊥ :=
  WithTop.add_ne_top
#align with_bot.add_ne_bot WithBot.add_ne_bot

theorem bot_lt_add [LT α] {a b : WithBot α} : ⊥ < a + b ↔ ⊥ < a ∧ ⊥ < b :=
  WithTop.add_lt_top (α := αᵒᵈ)
#align with_bot.bot_lt_add WithBot.bot_lt_add

theorem add_eq_coe : a + b = x ↔ ∃ a' b' : α, ↑a' = a ∧ ↑b' = b ∧ a' + b' = x :=
  WithTop.add_eq_coe
#align with_bot.add_eq_coe WithBot.add_eq_coe

-- Porting note (#10618): simp can already prove this.
-- @[simp]
theorem add_coe_eq_bot_iff : a + y = ⊥ ↔ a = ⊥ :=
  WithTop.add_coe_eq_top_iff
#align with_bot.add_coe_eq_bot_iff WithBot.add_coe_eq_bot_iff

-- Porting note (#10618): simp can already prove this.
-- @[simp]
theorem coe_add_eq_bot_iff : ↑x + b = ⊥ ↔ b = ⊥ :=
  WithTop.coe_add_eq_top_iff
#align with_bot.coe_add_eq_bot_iff WithBot.coe_add_eq_bot_iff

theorem add_right_cancel_iff [IsRightCancelAdd α] (ha : a ≠ ⊥) : b + a = c + a ↔ b = c :=
  WithTop.add_right_cancel_iff ha

theorem add_right_cancel [IsRightCancelAdd α] (ha : a ≠ ⊥) (h : b + a = c + a) : b = c :=
  WithTop.add_right_cancel ha h

theorem add_left_cancel_iff [IsLeftCancelAdd α] (ha : a ≠ ⊥) : a + b = a + c ↔ b = c :=
  WithTop.add_left_cancel_iff ha

theorem add_left_cancel [IsLeftCancelAdd α] (ha : a ≠ ⊥) (h : a + b = a + c) : b = c :=
  WithTop.add_left_cancel ha h

-- There is no `WithBot.map_mul_of_mulHom`, since `WithBot` does not have a multiplication.
@[simp]
protected theorem map_add {F} [Add β] [FunLike F α β] [AddHomClass F α β]
    (f : F) (a b : WithBot α) :
    (a + b).map f = a.map f + b.map f :=
  WithTop.map_add f a b
#align with_bot.map_add WithBot.map_add

/-- A version of `WithBot.map` for `OneHom`s. -/
@[to_additive (attr := simps (config := .asFn))
  "A version of `WithBot.map` for `ZeroHom`s"]
protected def _root_.OneHom.withBotMap {M N : Type*} [One M] [One N] (f : OneHom M N) :
    OneHom (WithBot M) (WithBot N) where
  toFun := WithBot.map f
  map_one' := by rw [WithBot.map_one, map_one, coe_one]
#align one_hom.with_bot_map OneHom.withBotMap
#align zero_hom.with_bot_map ZeroHom.withBotMap
#align one_hom.with_bot_map_apply OneHom.withBotMap_apply
#align zero_hom.with_bot_map_apply ZeroHom.withBotMap_apply

/-- A version of `WithBot.map` for `AddHom`s. -/
@[simps (config := .asFn)]
protected def _root_.AddHom.withBotMap {M N : Type*} [Add M] [Add N] (f : AddHom M N) :
    AddHom (WithBot M) (WithBot N) where
  toFun := WithBot.map f
  map_add' := WithBot.map_add f
#align add_hom.with_bot_map AddHom.withBotMap
#align add_hom.with_bot_map_apply AddHom.withBotMap_apply

/-- A version of `WithBot.map` for `AddMonoidHom`s. -/
@[simps (config := .asFn)]
protected def _root_.AddMonoidHom.withBotMap {M N : Type*} [AddZeroClass M] [AddZeroClass N]
    (f : M →+ N) : WithBot M →+ WithBot N :=
  { ZeroHom.withBotMap f.toZeroHom, AddHom.withBotMap f.toAddHom with toFun := WithBot.map f }
#align add_monoid_hom.with_bot_map AddMonoidHom.withBotMap
#align add_monoid_hom.with_bot_map_apply AddMonoidHom.withBotMap_apply

variable [Preorder α]

instance covariantClass_add_le [CovariantClass α α (· + ·) (· ≤ ·)] :
    CovariantClass (WithBot α) (WithBot α) (· + ·) (· ≤ ·) :=
  OrderDual.covariantClass_add_le (α := WithTop αᵒᵈ)
#align with_bot.covariant_class_add_le WithBot.covariantClass_add_le

instance covariantClass_swap_add_le [CovariantClass α α (swap (· + ·)) (· ≤ ·)] :
    CovariantClass (WithBot α) (WithBot α) (swap (· + ·)) (· ≤ ·) :=
  OrderDual.covariantClass_swap_add_le (α := WithTop αᵒᵈ)
#align with_bot.covariant_class_swap_add_le WithBot.covariantClass_swap_add_le

instance contravariantClass_add_lt [ContravariantClass α α (· + ·) (· < ·)] :
    ContravariantClass (WithBot α) (WithBot α) (· + ·) (· < ·) :=
  OrderDual.contravariantClass_add_lt (α := WithTop αᵒᵈ)
#align with_bot.contravariant_class_add_lt WithBot.contravariantClass_add_lt

instance contravariantClass_swap_add_lt [ContravariantClass α α (swap (· + ·)) (· < ·)] :
    ContravariantClass (WithBot α) (WithBot α) (swap (· + ·)) (· < ·) :=
  OrderDual.contravariantClass_swap_add_lt (α := WithTop αᵒᵈ)
#align with_bot.contravariant_class_swap_add_lt WithBot.contravariantClass_swap_add_lt

protected theorem le_of_add_le_add_left [ContravariantClass α α (· + ·) (· ≤ ·)] (ha : a ≠ ⊥)
    (h : a + b ≤ a + c) : b ≤ c :=
  WithTop.le_of_add_le_add_left (α := αᵒᵈ) ha h
#align with_bot.le_of_add_le_add_left WithBot.le_of_add_le_add_left

protected theorem le_of_add_le_add_right [ContravariantClass α α (swap (· + ·)) (· ≤ ·)]
    (ha : a ≠ ⊥) (h : b + a ≤ c + a) : b ≤ c :=
  WithTop.le_of_add_le_add_right (α := αᵒᵈ) ha h
#align with_bot.le_of_add_le_add_right WithBot.le_of_add_le_add_right

protected theorem add_lt_add_left [CovariantClass α α (· + ·) (· < ·)] (ha : a ≠ ⊥) (h : b < c) :
    a + b < a + c :=
  WithTop.add_lt_add_left (α := αᵒᵈ) ha h
#align with_bot.add_lt_add_left WithBot.add_lt_add_left

protected theorem add_lt_add_right [CovariantClass α α (swap (· + ·)) (· < ·)] (ha : a ≠ ⊥)
    (h : b < c) : b + a < c + a :=
  WithTop.add_lt_add_right (α := αᵒᵈ) ha h
#align with_bot.add_lt_add_right WithBot.add_lt_add_right

protected theorem add_le_add_iff_left [CovariantClass α α (· + ·) (· ≤ ·)]
    [ContravariantClass α α (· + ·) (· ≤ ·)] (ha : a ≠ ⊥) : a + b ≤ a + c ↔ b ≤ c :=
  ⟨WithBot.le_of_add_le_add_left ha, fun h => add_le_add_left h a⟩
#align with_bot.add_le_add_iff_left WithBot.add_le_add_iff_left

protected theorem add_le_add_iff_right [CovariantClass α α (swap (· + ·)) (· ≤ ·)]
    [ContravariantClass α α (swap (· + ·)) (· ≤ ·)] (ha : a ≠ ⊥) : b + a ≤ c + a ↔ b ≤ c :=
  ⟨WithBot.le_of_add_le_add_right ha, fun h => add_le_add_right h a⟩
#align with_bot.add_le_add_iff_right WithBot.add_le_add_iff_right

protected theorem add_lt_add_iff_left [CovariantClass α α (· + ·) (· < ·)]
    [ContravariantClass α α (· + ·) (· < ·)] (ha : a ≠ ⊥) : a + b < a + c ↔ b < c :=
  ⟨lt_of_add_lt_add_left, WithBot.add_lt_add_left ha⟩
#align with_bot.add_lt_add_iff_left WithBot.add_lt_add_iff_left

protected theorem add_lt_add_iff_right [CovariantClass α α (swap (· + ·)) (· < ·)]
    [ContravariantClass α α (swap (· + ·)) (· < ·)] (ha : a ≠ ⊥) : b + a < c + a ↔ b < c :=
  ⟨lt_of_add_lt_add_right, WithBot.add_lt_add_right ha⟩
#align with_bot.add_lt_add_iff_right WithBot.add_lt_add_iff_right

protected theorem add_lt_add_of_le_of_lt [CovariantClass α α (· + ·) (· < ·)]
    [CovariantClass α α (swap (· + ·)) (· ≤ ·)] (hb : b ≠ ⊥) (hab : a ≤ b) (hcd : c < d) :
    a + c < b + d :=
  WithTop.add_lt_add_of_le_of_lt (α := αᵒᵈ) hb hab hcd
#align with_bot.add_lt_add_of_le_of_lt WithBot.add_lt_add_of_le_of_lt

protected theorem add_lt_add_of_lt_of_le [CovariantClass α α (· + ·) (· ≤ ·)]
    [CovariantClass α α (swap (· + ·)) (· < ·)] (hd : d ≠ ⊥) (hab : a < b) (hcd : c ≤ d) :
    a + c < b + d :=
  WithTop.add_lt_add_of_lt_of_le (α := αᵒᵈ) hd hab hcd
#align with_bot.add_lt_add_of_lt_of_le WithBot.add_lt_add_of_lt_of_le

end Add

instance orderedAddCommMonoid [OrderedAddCommMonoid α] : OrderedAddCommMonoid (WithBot α) :=
  { WithBot.partialOrder, WithBot.addCommMonoid with
    add_le_add_left := fun _ _ h c => add_le_add_left h c }

instance linearOrderedAddCommMonoid [LinearOrderedAddCommMonoid α] :
    LinearOrderedAddCommMonoid (WithBot α) :=
  { WithBot.linearOrder, WithBot.orderedAddCommMonoid with }

end WithBot
