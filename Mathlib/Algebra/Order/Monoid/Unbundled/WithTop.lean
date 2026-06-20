/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
public import Mathlib.Order.WithBot

/-! # Adjoining top/bottom elements to ordered monoids.
-/

@[expose] public section

universe u v

variable {α : Type u} {β : Type v}

open Function

namespace WithTop

section One

variable [One α] {a : α}

@[to_additive]
instance one : One (WithTop α) :=
  ⟨(1 : α)⟩

@[to_additive (attr := simp, norm_cast)]
theorem coe_one : ((1 : α) : WithTop α) = 1 :=
  rfl

@[to_additive (attr := simp, norm_cast)]
lemma coe_eq_one : (a : WithTop α) = 1 ↔ a = 1 := coe_eq_coe

@[to_additive] lemma coe_ne_one : (a : WithTop α) ≠ 1 ↔ a ≠ 1 := coe_eq_one.ne

@[to_additive (attr := simp, norm_cast)]
lemma one_eq_coe : 1 = (a : WithTop α) ↔ a = 1 := eq_comm.trans coe_eq_one

@[to_additive (attr := simp)] lemma top_ne_one : (⊤ : WithTop α) ≠ 1 := top_ne_coe

@[to_additive (attr := simp)] lemma one_ne_top : (1 : WithTop α) ≠ ⊤ := coe_ne_top

@[to_additive (attr := simp)]
theorem untop_one : (1 : WithTop α).untop coe_ne_top = 1 :=
  rfl

@[to_additive (attr := simp)]
theorem untopD_one (d : α) : (1 : WithTop α).untopD d = 1 :=
  rfl

@[to_additive (attr := simp, norm_cast) coe_nonneg]
theorem one_le_coe [LE α] {a : α} : 1 ≤ (a : WithTop α) ↔ 1 ≤ a :=
  coe_le_coe

@[to_additive (attr := simp, norm_cast) coe_le_zero]
theorem coe_le_one [LE α] {a : α} : (a : WithTop α) ≤ 1 ↔ a ≤ 1 :=
  coe_le_coe

@[to_additive (attr := simp, norm_cast) coe_pos]
theorem one_lt_coe [LT α] {a : α} : 1 < (a : WithTop α) ↔ 1 < a :=
  coe_lt_coe

@[to_additive (attr := simp, norm_cast) coe_lt_zero]
theorem coe_lt_one [LT α] {a : α} : (a : WithTop α) < 1 ↔ a < 1 :=
  coe_lt_coe

@[to_additive (attr := simp)]
protected theorem map_one {β} (f : α → β) : (1 : WithTop α).map f = (f 1 : WithTop β) :=
  rfl

@[to_additive]
theorem map_eq_one_iff {α} {f : α → β} {v : WithTop α} [One β] :
    WithTop.map f v = 1 ↔ ∃ x, v = .some x ∧ f x = 1 := map_eq_some_iff

@[to_additive]
theorem one_eq_map_iff {α} {f : α → β} {v : WithTop α} [One β] :
    1 = WithTop.map f v ↔ ∃ x, v = .some x ∧ f x = 1 := some_eq_map_iff

instance zeroLEOneClass [Zero α] [LE α] [ZeroLEOneClass α] : ZeroLEOneClass (WithTop α) :=
  ⟨coe_le_coe.2 zero_le_one⟩

@[to_additive]
instance [LE α] [IsBotOneClass α] : IsBotOneClass (WithTop α) where
  isBot_one x := by cases x <;> simp

end One

section Add

variable [Add α] {w x y z : WithTop α} {a b : α}

instance add : Add (WithTop α) :=
  ⟨WithTop.map₂ (· + ·)⟩

@[simp, norm_cast] lemma coe_add (a b : α) : ↑(a + b) = (a + b : WithTop α) := rfl

@[simp] lemma top_add (x : WithTop α) : ⊤ + x = ⊤ := rfl
@[simp] lemma add_top (x : WithTop α) : x + ⊤ = ⊤ := by cases x <;> rfl

@[simp] lemma add_eq_top : x + y = ⊤ ↔ x = ⊤ ∨ y = ⊤ := by cases x <;> cases y <;> simp [← coe_add]

lemma add_ne_top : x + y ≠ ⊤ ↔ x ≠ ⊤ ∧ y ≠ ⊤ := by cases x <;> cases y <;> simp [← coe_add]

@[simp]
lemma add_lt_top [LT α] : x + y < ⊤ ↔ x < ⊤ ∧ y < ⊤ := by
  simp_rw [WithTop.lt_top_iff_ne_top, add_ne_top]

theorem add_eq_coe :
    ∀ {a b : WithTop α} {c : α}, a + b = c ↔ ∃ a' b' : α, ↑a' = a ∧ ↑b' = b ∧ a' + b' = c
  | ⊤, b, c => by simp
  | some a, ⊤, c => by simp
  | some a, some b, c => by norm_cast; simp

lemma add_coe_eq_top_iff : x + b = ⊤ ↔ x = ⊤ := by simp
lemma coe_add_eq_top_iff : a + y = ⊤ ↔ y = ⊤ := by simp

lemma _root_.IsAddLeftRegular.withTop (ha : IsAddLeftRegular a) :
    IsAddLeftRegular (a : WithTop α) := by
  rintro (_ | b) (_ | c) <;> simp [none_eq_top, some_eq_coe, ← coe_add, ha.eq_iff]

lemma _root_.IsAddRightRegular.withTop (ha : IsAddRightRegular a) :
    IsAddRightRegular (a : WithTop α) := by
  rintro (_ | b) (_ | c) <;> simp [none_eq_top, some_eq_coe, ← coe_add, ha.eq_iff]

lemma _root_.AddLECancellable.withTop [LE α] (ha : AddLECancellable a) :
    AddLECancellable (a : WithTop α) := by
  rintro (_ | b) (_ | c)
  · simp [none_eq_top]
  · simp [none_eq_top]
  · simp [some_eq_coe, ← coe_add, none_eq_top]
  · simpa [none_eq_top, some_eq_coe, ← coe_add] using fun a ↦ ha a

lemma add_right_inj [IsRightCancelAdd α] (hz : z ≠ ⊤) : x + z = y + z ↔ x = y := by
  lift z to α using hz; exact (IsAddRightRegular.all _).withTop.eq_iff

lemma add_right_cancel [IsRightCancelAdd α] (hz : z ≠ ⊤) (h : x + z = y + z) : x = y :=
  (WithTop.add_right_inj hz).1 h

lemma add_left_inj [IsLeftCancelAdd α] (hx : x ≠ ⊤) : x + y = x + z ↔ y = z := by
  lift x to α using hx; exact (IsAddLeftRegular.all _).withTop.eq_iff

lemma add_left_cancel [IsLeftCancelAdd α] (hx : x ≠ ⊤) (h : x + y = x + z) : y = z :=
  (WithTop.add_left_inj hx).1 h

instance addLeftMono [LE α] [AddLeftMono α] : AddLeftMono (WithTop α) where
  elim x y z := by
    cases x <;> cases y <;> cases z <;> simp [← coe_add]; simpa using fun _ ↦ by gcongr

instance addRightMono [LE α] [AddRightMono α] : AddRightMono (WithTop α) where
  elim x y z := by
    cases x <;> cases y <;> cases z <;> simp [← coe_add, swap]; simpa using fun _ ↦ by gcongr

instance addLeftReflectLT [LT α] [AddLeftReflectLT α] : AddLeftReflectLT (WithTop α) where
  elim x y z := by
    cases x <;> cases y <;> cases z <;> simp [← coe_add]; simpa using lt_of_add_lt_add_left

instance addRightReflectLT [LT α] [AddRightReflectLT α] : AddRightReflectLT (WithTop α) where
  elim x y z := by
    cases x <;> cases y <;> cases z <;> simp [← coe_add, swap]; simpa using lt_of_add_lt_add_right

protected lemma le_of_add_le_add_left [LE α] [AddLeftReflectLE α] (hx : x ≠ ⊤) :
    x + y ≤ x + z → y ≤ z := by
  lift x to α using hx; cases y <;> cases z <;> simp [← coe_add]; simpa using le_of_add_le_add_left

protected lemma le_of_add_le_add_right [LE α] [AddRightReflectLE α] (hz : z ≠ ⊤) :
    x + z ≤ y + z → x ≤ y := by
  lift z to α using hz; cases x <;> cases y <;> simp [← coe_add]; simpa using le_of_add_le_add_right

protected lemma add_lt_add_left [LT α] [AddLeftStrictMono α] (hx : x ≠ ⊤) :
    y < z → x + y < x + z := by
  lift x to α using hx; cases y <;> cases z <;> simp [← coe_add]; simpa using fun _ ↦ by gcongr

protected lemma add_lt_add_right [LT α] [AddRightStrictMono α] (hz : z ≠ ⊤) :
    x < y → x + z < y + z := by
  lift z to α using hz; cases x <;> cases y <;> simp [← coe_add]; simpa using fun _ ↦ by gcongr

@[gcongr]
protected theorem add_lt_add [Preorder α] [AddLeftStrictMono α] [AddRightStrictMono α]
    (xz : x < z) (yw : y < w) : x + y < z + w := by
  apply (WithTop.add_lt_add_left xz.ne_top yw).trans_le
  cases w
  · simp
  · exact (WithTop.add_lt_add_right coe_ne_top xz).le

protected lemma add_le_add_iff_left [LE α] [AddLeftMono α] [AddLeftReflectLE α] (hx : x ≠ ⊤) :
    x + y ≤ x + z ↔ y ≤ z := ⟨WithTop.le_of_add_le_add_left hx, fun _ ↦ by gcongr⟩

protected lemma add_le_add_iff_right [LE α] [AddRightMono α] [AddRightReflectLE α] (hz : z ≠ ⊤) :
    x + z ≤ y + z ↔ x ≤ y := ⟨WithTop.le_of_add_le_add_right hz, fun _ ↦ by gcongr⟩

protected lemma add_lt_add_iff_left [LT α] [AddLeftStrictMono α] [AddLeftReflectLT α] (hx : x ≠ ⊤) :
    x + y < x + z ↔ y < z := ⟨lt_of_add_lt_add_left, WithTop.add_lt_add_left hx⟩

protected lemma add_lt_add_iff_right [LT α] [AddRightStrictMono α] [AddRightReflectLT α]
    (hz : z ≠ ⊤) : x + z < y + z ↔ x < y := ⟨lt_of_add_lt_add_right, WithTop.add_lt_add_right hz⟩

protected theorem add_lt_add_of_le_of_lt [Preorder α] [AddLeftStrictMono α]
    [AddRightMono α] (hw : w ≠ ⊤) (hwy : w ≤ y) (hxz : x < z) :
    w + x < y + z :=
  (WithTop.add_lt_add_left hw hxz).trans_le <| by gcongr

protected theorem add_lt_add_of_lt_of_le [Preorder α] [AddLeftMono α]
    [AddRightStrictMono α] (hx : x ≠ ⊤) (hwy : w < y) (hxz : x ≤ z) :
    w + x < y + z :=
  (WithTop.add_lt_add_right hx hwy).trans_le <| by gcongr

lemma addLECancellable_of_ne_top [LE α] [AddLeftReflectLE α]
    (hx : x ≠ ⊤) : AddLECancellable x := fun _b _c ↦ WithTop.le_of_add_le_add_left hx

lemma addLECancellable_of_lt_top [Preorder α] [AddLeftReflectLE α]
    (hx : x < ⊤) : AddLECancellable x := addLECancellable_of_ne_top hx.ne

lemma addLECancellable_coe [LE α] [AddLeftReflectLE α] (a : α) :
    AddLECancellable (a : WithTop α) := addLECancellable_of_ne_top coe_ne_top

lemma addLECancellable_iff_ne_top [Nonempty α] [Preorder α]
    [AddLeftReflectLE α] : AddLECancellable x ↔ x ≠ ⊤ where
  mp := by rintro h rfl; exact (coe_lt_top <| Classical.arbitrary _).not_ge <| h <| by simp
  mpr := addLECancellable_of_ne_top

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

@[simp, norm_cast] lemma coe_addHom : ⇑(addHom : α →+ WithTop α) = WithTop.some := rfl

end AddMonoid

instance addCommMonoid [AddCommMonoid α] : AddCommMonoid (WithTop α) :=
  { WithTop.addMonoid, WithTop.addCommSemigroup with }

instance natCast [NatCast α] : NatCast (WithTop α) :=
  ⟨fun n => ↑(n : α)⟩

section AddMonoidWithOne
variable [AddMonoidWithOne α]

instance addMonoidWithOne : AddMonoidWithOne (WithTop α) where
  natCast_zero := by simp [NatCast.natCast]
  natCast_succ := fun n => by simp [NatCast.natCast]

@[simp, norm_cast] lemma coe_natCast (n : ℕ) : ((n : α) : WithTop α) = n := rfl

@[simp] lemma top_ne_natCast (n : ℕ) : (⊤ : WithTop α) ≠ n := top_ne_coe
@[simp] lemma natCast_ne_top (n : ℕ) : (n : WithTop α) ≠ ⊤ := coe_ne_top
@[simp] lemma natCast_lt_top [LT α] (n : ℕ) : (n : WithTop α) < ⊤ := coe_lt_top _

@[simp] lemma coe_ofNat (n : ℕ) [n.AtLeastTwo] :
    ((ofNat(n) : α) : WithTop α) = ofNat(n) := rfl
@[simp] lemma coe_eq_ofNat (n : ℕ) [n.AtLeastTwo] (m : α) :
    (m : WithTop α) = ofNat(n) ↔ m = ofNat(n) :=
  coe_eq_coe
@[simp] lemma ofNat_eq_coe (n : ℕ) [n.AtLeastTwo] (m : α) :
    ofNat(n) = (m : WithTop α) ↔ ofNat(n) = m :=
  coe_eq_coe
@[simp] lemma ofNat_ne_top (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : WithTop α) ≠ ⊤ :=
  natCast_ne_top n
@[simp] lemma top_ne_ofNat (n : ℕ) [n.AtLeastTwo] : (⊤ : WithTop α) ≠ ofNat(n) :=
  top_ne_natCast n

@[simp] lemma map_ofNat {f : α → β} (n : ℕ) [n.AtLeastTwo] :
    WithTop.map f (ofNat(n) : WithTop α) = f (ofNat(n)) := map_coe f n

@[simp] lemma map_natCast {f : α → β} (n : ℕ) :
    WithTop.map f (n : WithTop α) = f n := map_coe f n

lemma map_eq_ofNat_iff {f : β → α} {n : ℕ} [n.AtLeastTwo] {a : WithTop β} :
    a.map f = ofNat(n) ↔ ∃ x, a = .some x ∧ f x = n := map_eq_some_iff

lemma ofNat_eq_map_iff {f : β → α} {n : ℕ} [n.AtLeastTwo] {a : WithTop β} :
    ofNat(n) = a.map f ↔ ∃ x, a = .some x ∧ f x = n := some_eq_map_iff

lemma map_eq_natCast_iff {f : β → α} {n : ℕ} {a : WithTop β} :
    a.map f = n ↔ ∃ x, a = .some x ∧ f x = n := map_eq_some_iff

lemma natCast_eq_map_iff {f : β → α} {n : ℕ} {a : WithTop β} :
    n = a.map f ↔ ∃ x, a = .some x ∧ f x = n := some_eq_map_iff

end AddMonoidWithOne

instance charZero [AddMonoidWithOne α] [CharZero α] : CharZero (WithTop α) :=
  { cast_injective := Function.Injective.comp (f := Nat.cast (R := α))
      (fun _ _ => WithTop.coe_eq_coe.1) Nat.cast_injective }

instance addCommMonoidWithOne [AddCommMonoidWithOne α] : AddCommMonoidWithOne (WithTop α) :=
  { WithTop.addMonoidWithOne, WithTop.addCommMonoid with }

-- instance orderedAddCommMonoid [OrderedAddCommMonoid α] : OrderedAddCommMonoid (WithTop α) where
--   add_le_add_left _ _ := add_le_add_left
--
-- instance linearOrderedAddCommMonoidWithTop [LinearOrderedAddCommMonoid α] :
--     LinearOrderedAddCommMonoidWithTop (WithTop α) :=
--   { WithTop.orderTop, WithTop.linearOrder, WithTop.orderedAddCommMonoid with
--     top_add' := WithTop.top_add }
--
instance existsAddOfLE [LE α] [Add α] [ExistsAddOfLE α] : ExistsAddOfLE (WithTop α) :=
  ⟨fun {a} {b} =>
    match a, b with
    | ⊤, ⊤ => by simp
    | (a : α), ⊤ => fun _ => ⟨⊤, rfl⟩
    | (a : α), (b : α) => fun h => by
      obtain ⟨c, rfl⟩ := exists_add_of_le (WithTop.coe_le_coe.1 h)
      exact ⟨c, rfl⟩
    | ⊤, (b : α) => fun h => (not_top_le_coe _ h).elim⟩

-- instance canonicallyOrderedAddCommMonoid [CanonicallyOrderedAddCommMonoid α] :
--     CanonicallyOrderedAddCommMonoid (WithTop α) :=
--   { WithTop.orderBot, WithTop.orderedAddCommMonoid, WithTop.existsAddOfLE with
--     le_self_add := fun a b =>
--       match a, b with
--       | ⊤, ⊤ => le_rfl
--       | (a : α), ⊤ => le_top
--       | (a : α), (b : α) => WithTop.coe_le_coe.2 le_self_add
--       | ⊤, (b : α) => le_rfl }
--
-- instance [CanonicallyLinearOrderedAddCommMonoid α] :
--     CanonicallyLinearOrderedAddCommMonoid (WithTop α) :=
--   { WithTop.canonicallyOrderedAddCommMonoid, WithTop.linearOrder with }

@[to_additive (attr := simp) top_pos]
theorem one_lt_top [One α] [LT α] : (1 : WithTop α) < ⊤ := coe_lt_top _

/-- A version of `WithTop.map` for `OneHom`s. -/
@[to_additive (attr := simps -fullyApplied)
  /-- A version of `WithTop.map` for `ZeroHom`s -/]
protected def _root_.OneHom.withTopMap {M N : Type*} [One M] [One N] (f : OneHom M N) :
    OneHom (WithTop M) (WithTop N) where
  toFun := WithTop.map f
  map_one' := by rw [WithTop.map_one, map_one, coe_one]

/-- A version of `WithTop.map` for `AddHom`s. -/
@[simps -fullyApplied]
protected def _root_.AddHom.withTopMap {M N : Type*} [Add M] [Add N] (f : AddHom M N) :
    AddHom (WithTop M) (WithTop N) where
  toFun := WithTop.map f
  map_add' := WithTop.map_add f

/-- A version of `WithTop.map` for `AddMonoidHom`s. -/
@[simps -fullyApplied]
protected def _root_.AddMonoidHom.withTopMap {M N : Type*} [AddZeroClass M] [AddZeroClass N]
    (f : M →+ N) : WithTop M →+ WithTop N :=
  { ZeroHom.withTopMap f.toZeroHom, AddHom.withTopMap f.toAddHom with toFun := WithTop.map f }

end WithTop

namespace WithBot
section One
variable [One α] {a : α}

@[to_additive] instance one : One (WithBot α) := ⟨(1 : α)⟩

@[to_additive (attr := simp, norm_cast)] lemma coe_one : ((1 : α) : WithBot α) = 1 := rfl

@[to_additive (attr := simp, norm_cast)]
lemma coe_eq_one : (a : WithBot α) = 1 ↔ a = 1 := coe_eq_coe

@[to_additive (attr := simp, norm_cast)]
lemma one_eq_coe : 1 = (a : WithBot α) ↔ a = 1 := eq_comm.trans coe_eq_one

@[to_additive (attr := simp)] lemma bot_ne_one : (⊥ : WithBot α) ≠ 1 := bot_ne_coe
@[to_additive (attr := simp)] lemma one_ne_bot : (1 : WithBot α) ≠ ⊥ := coe_ne_bot

@[to_additive (attr := simp)]
theorem unbot_one : (1 : WithBot α).unbot coe_ne_bot = 1 :=
  rfl

@[to_additive (attr := simp)]
theorem unbotD_one (d : α) : (1 : WithBot α).unbotD d = 1 :=
  rfl

@[to_additive (attr := simp, norm_cast) coe_nonneg]
theorem one_le_coe [LE α] : 1 ≤ (a : WithBot α) ↔ 1 ≤ a := coe_le_coe

@[to_additive (attr := simp, norm_cast) coe_le_zero]
theorem coe_le_one [LE α] : (a : WithBot α) ≤ 1 ↔ a ≤ 1 := coe_le_coe

@[to_additive (attr := simp, norm_cast) coe_pos]
theorem one_lt_coe [LT α] : 1 < (a : WithBot α) ↔ 1 < a := coe_lt_coe

@[to_additive (attr := simp, norm_cast) coe_lt_zero]
theorem coe_lt_one [LT α] : (a : WithBot α) < 1 ↔ a < 1 := coe_lt_coe

@[to_additive (attr := simp)]
theorem bot_lt_one [LT α] : ⊥ < (1 : WithBot α) := bot_lt_coe _

@[to_additive (attr := simp)]
protected theorem map_one {β} (f : α → β) : (1 : WithBot α).map f = (f 1 : WithBot β) :=
  rfl

@[to_additive]
theorem map_eq_one_iff {α} {f : α → β} {v : WithBot α} [One β] :
    WithBot.map f v = 1 ↔ ∃ x, v = .some x ∧ f x = 1 := map_eq_some_iff

@[to_additive]
theorem one_eq_map_iff {α} {f : α → β} {v : WithBot α} [One β] :
    1 = WithBot.map f v ↔ ∃ x, v = .some x ∧ f x = 1 := some_eq_map_iff

instance zeroLEOneClass [Zero α] [LE α] [ZeroLEOneClass α] : ZeroLEOneClass (WithBot α) :=
  ⟨coe_le_coe.2 zero_le_one⟩

end One

section Add
variable [Add α] {w x y z : WithBot α} {a b : α}

instance add : Add (WithBot α) :=
  ⟨WithBot.map₂ (· + ·)⟩

@[simp, norm_cast] lemma coe_add (a b : α) : ↑(a + b) = (a + b : WithBot α) := rfl

@[simp] lemma bot_add (x : WithBot α) : ⊥ + x = ⊥ := rfl
@[simp] lemma add_bot (x : WithBot α) : x + ⊥ = ⊥ := by cases x <;> rfl

@[simp] lemma add_eq_bot : x + y = ⊥ ↔ x = ⊥ ∨ y = ⊥ := by cases x <;> cases y <;> simp [← coe_add]

lemma add_ne_bot : x + y ≠ ⊥ ↔ x ≠ ⊥ ∧ y ≠ ⊥ := by cases x <;> cases y <;> simp [← coe_add]

@[simp]
lemma bot_lt_add [LT α] : ⊥ < x + y ↔ ⊥ < x ∧ ⊥ < y := by
  simp_rw [WithBot.bot_lt_iff_ne_bot, add_ne_bot]

theorem add_eq_coe :
    ∀ {a b : WithBot α} {c : α}, a + b = c ↔ ∃ a' b' : α, ↑a' = a ∧ ↑b' = b ∧ a' + b' = c
  | ⊥, b, c => by simp
  | some a, ⊥, c => by simp
  | some a, some b, c => by norm_cast; simp

lemma add_coe_eq_bot_iff : x + b = ⊥ ↔ x = ⊥ := by simp
lemma coe_add_eq_bot_iff : a + y = ⊥ ↔ y = ⊥ := by simp

lemma _root_.IsAddLeftRegular.withBot (ha : IsAddLeftRegular a) :
    IsAddLeftRegular (a : WithBot α) := by
  rintro (_ | b) (_ | c) <;> simp [none_eq_bot, some_eq_coe, ← coe_add]; simpa using @ha _ _

lemma _root_.IsAddRightRegular.withBot (ha : IsAddRightRegular a) :
    IsAddRightRegular (a : WithBot α) := by
  rintro (_ | b) (_ | c) <;> simp [none_eq_bot, some_eq_coe, ← coe_add]; simpa using @ha _ _

lemma _root_.AddLECancellable.withBot [LE α] (ha : AddLECancellable a) :
    AddLECancellable (a : WithBot α) := by
  rintro (_ | b) (_ | c)
  · simp [none_eq_bot]
  · simp [none_eq_bot]
  · simp [some_eq_coe, ← coe_add, none_eq_bot]
  · simpa [none_eq_bot, some_eq_coe, ← coe_add] using fun a ↦ ha a

lemma add_right_inj [IsRightCancelAdd α] (hz : z ≠ ⊥) : x + z = y + z ↔ x = y := by
  lift z to α using hz; cases x <;> cases y <;> simp [← coe_add]

lemma add_right_cancel [IsRightCancelAdd α] (hz : z ≠ ⊥) (h : x + z = y + z) : x = y :=
  (WithBot.add_right_inj hz).1 h

lemma add_left_inj [IsLeftCancelAdd α] (hx : x ≠ ⊥) : x + y = x + z ↔ y = z := by
  lift x to α using hx; cases y <;> cases z <;> simp [← coe_add]

lemma add_left_cancel [IsLeftCancelAdd α] (hx : x ≠ ⊥) (h : x + y = x + z) : y = z :=
  (WithBot.add_left_inj hx).1 h

instance addLeftMono [LE α] [AddLeftMono α] : AddLeftMono (WithBot α) where
  elim x y z := by
    cases x <;> cases y <;> cases z <;> simp [← coe_add]; simpa using fun _ ↦ by gcongr

instance addRightMono [LE α] [AddRightMono α] : AddRightMono (WithBot α) where
  elim x y z := by
    cases x <;> cases y <;> cases z <;> simp [← coe_add, swap]; simpa using fun _ ↦ by gcongr

instance addLeftReflectLT [LT α] [AddLeftReflectLT α] : AddLeftReflectLT (WithBot α) where
  elim x y z := by
    cases x <;> cases y <;> cases z <;> simp [← coe_add]; simpa using lt_of_add_lt_add_left

instance addRightReflectLT [LT α] [AddRightReflectLT α] : AddRightReflectLT (WithBot α) where
  elim x y z := by
    cases x <;> cases y <;> cases z <;> simp [← coe_add, swap]; simpa using lt_of_add_lt_add_right

protected lemma le_of_add_le_add_left [LE α] [AddLeftReflectLE α] (hx : x ≠ ⊥) :
    x + y ≤ x + z → y ≤ z := by
  lift x to α using hx; cases y <;> cases z <;> simp [← coe_add]; simpa using le_of_add_le_add_left

protected lemma le_of_add_le_add_right [LE α] [AddRightReflectLE α] (hz : z ≠ ⊥) :
    x + z ≤ y + z → x ≤ y := by
  lift z to α using hz; cases x <;> cases y <;> simp [← coe_add]; simpa using le_of_add_le_add_right

protected lemma add_lt_add_left [LT α] [AddLeftStrictMono α] (hx : x ≠ ⊥) :
    y < z → x + y < x + z := by
  lift x to α using hx; cases y <;> cases z <;> simp [← coe_add]; simpa using fun _ ↦ by gcongr

protected lemma add_lt_add_right [LT α] [AddRightStrictMono α] (hz : z ≠ ⊥) :
    x < y → x + z < y + z := by
  lift z to α using hz; cases x <;> cases y <;> simp [← coe_add]; simpa using fun _ ↦ by gcongr

protected lemma add_le_add_iff_left [LE α] [AddLeftMono α] [AddLeftReflectLE α] (hx : x ≠ ⊥) :
    x + y ≤ x + z ↔ y ≤ z := ⟨WithBot.le_of_add_le_add_left hx, fun _ ↦ by gcongr⟩

protected lemma add_le_add_iff_right [LE α] [AddRightMono α] [AddRightReflectLE α] (hz : z ≠ ⊥) :
    x + z ≤ y + z ↔ x ≤ y := ⟨WithBot.le_of_add_le_add_right hz, fun _ ↦ by gcongr⟩

protected lemma add_lt_add_iff_left [LT α] [AddLeftStrictMono α] [AddLeftReflectLT α] (hx : x ≠ ⊥) :
    x + y < x + z ↔ y < z := ⟨lt_of_add_lt_add_left, WithBot.add_lt_add_left hx⟩

protected lemma add_lt_add_iff_right [LT α] [AddRightStrictMono α] [AddRightReflectLT α]
    (hz : z ≠ ⊥) : x + z < y + z ↔ x < y := ⟨lt_of_add_lt_add_right, WithBot.add_lt_add_right hz⟩

protected theorem add_lt_add_of_le_of_lt [Preorder α] [AddLeftStrictMono α]
    [AddRightMono α] (hw : w ≠ ⊥) (hwy : w ≤ y) (hxz : x < z) :
    w + x < y + z :=
  (WithBot.add_lt_add_left hw hxz).trans_le <| by gcongr

protected theorem add_lt_add_of_lt_of_le [Preorder α] [AddLeftMono α]
    [AddRightStrictMono α] (hx : x ≠ ⊥) (hwy : w < y) (hxz : x ≤ z) :
    w + x < y + z :=
  (WithBot.add_lt_add_right hx hwy).trans_le <| by gcongr

lemma addLECancellable_of_ne_bot [LE α] [AddLeftReflectLE α]
    (hx : x ≠ ⊥) : AddLECancellable x := fun _b _c ↦ WithBot.le_of_add_le_add_left hx

lemma addLECancellable_of_lt_bot [Preorder α] [AddLeftReflectLE α]
    (hx : x < ⊥) : AddLECancellable x := addLECancellable_of_ne_bot hx.ne

lemma addLECancellable_coe [LE α] [AddLeftReflectLE α] (a : α) :
    AddLECancellable (a : WithBot α) := addLECancellable_of_ne_bot coe_ne_bot

lemma addLECancellable_iff_ne_bot [Nonempty α] [Preorder α]
    [AddLeftReflectLE α] : AddLECancellable x ↔ x ≠ ⊥ where
  mp := by rintro h rfl; exact (bot_lt_coe <| Classical.arbitrary _).not_ge <| h <| by simp
  mpr := addLECancellable_of_ne_bot

/--
Addition in `WithBot (WithTop α)` is right cancellative provided the element
being cancelled is not `⊤` or `⊥`.
-/
lemma add_le_add_iff_right' {α : Type*} [Add α] [LE α]
    [AddRightMono α] [AddRightReflectLE α]
    {a b c : WithBot (WithTop α)} (hc : c ≠ ⊥) (hc' : c ≠ ⊤) :
    a + c ≤ b + c ↔ a ≤ b := by
  induction a <;> induction b <;> induction c <;> norm_cast at * <;>
    aesop (add simp WithTop.add_le_add_iff_right)

--  There is no `WithBot.map_mul_of_mulHom`, since `WithBot` does not have a multiplication.
@[simp]
protected theorem map_add {F} [Add β] [FunLike F α β] [AddHomClass F α β]
    (f : F) (a b : WithBot α) :
    (a + b).map f = a.map f + b.map f := by
  induction a
  · exact (bot_add _).symm
  · induction b
    · exact (add_bot _).symm
    · rw [map_coe, map_coe, ← coe_add, ← coe_add, ← map_add]
      rfl

end Add

instance addSemigroup [AddSemigroup α] : AddSemigroup (WithBot α) :=
  inferInstanceAs <| AddSemigroup (WithTop α)

instance addCommSemigroup [AddCommSemigroup α] : AddCommSemigroup (WithBot α) :=
  inferInstanceAs <| AddCommSemigroup (WithTop α)

instance addZeroClass [AddZeroClass α] : AddZeroClass (WithBot α) :=
  inferInstanceAs <| AddZeroClass (WithTop α)

section AddMonoid
variable [AddMonoid α]

instance addMonoid : AddMonoid (WithBot α) :=
  inferInstanceAs <| AddMonoid (WithTop α)

/-- Coercion from `α` to `WithBot α` as an `AddMonoidHom`. -/
def addHom : α →+ WithBot α where
  toFun := WithTop.some
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp, norm_cast] lemma coe_addHom : ⇑(addHom : α →+ WithBot α) = WithBot.some := rfl

@[simp, norm_cast]
lemma coe_nsmul (a : α) (n : ℕ) : ↑(n • a) = n • (a : WithBot α) :=
  (addHom : α →+ WithBot α).map_nsmul _ _

end AddMonoid

instance addCommMonoid [AddCommMonoid α] : AddCommMonoid (WithBot α) :=
  inferInstanceAs <| AddCommMonoid (WithTop α)

section NatCast
variable [NatCast α]

instance : NatCast (WithBot α) where natCast n := (n : α)

@[to_dual (attr := simp)] lemma unbotD_natCast (d : α) (n : ℕ) : unbotD d n = n := rfl

@[to_dual (attr := simp)]
lemma unbotD_ofNat (d : α) (n : ℕ) [n.AtLeastTwo] : unbotD d ofNat(n) = ofNat(n) := rfl

end NatCast

section AddMonoidWithOne
variable [AddMonoidWithOne α]

instance addMonoidWithOne : AddMonoidWithOne (WithBot α) :=
  inferInstanceAs <| AddMonoidWithOne (WithTop α)

@[norm_cast] lemma coe_natCast (n : ℕ) : ((n : α) : WithBot α) = n := rfl

@[simp] lemma natCast_ne_bot (n : ℕ) : (n : WithBot α) ≠ ⊥ := coe_ne_bot

@[simp] lemma bot_ne_natCast (n : ℕ) : (⊥ : WithBot α) ≠ n := bot_ne_coe

@[simp] lemma coe_ofNat (n : ℕ) [n.AtLeastTwo] :
    ((ofNat(n) : α) : WithBot α) = ofNat(n) := rfl
@[simp] lemma coe_eq_ofNat (n : ℕ) [n.AtLeastTwo] (m : α) :
    (m : WithBot α) = ofNat(n) ↔ m = ofNat(n) :=
  coe_eq_coe
@[simp] lemma ofNat_eq_coe (n : ℕ) [n.AtLeastTwo] (m : α) :
    ofNat(n) = (m : WithBot α) ↔ ofNat(n) = m :=
  coe_eq_coe
@[simp] lemma ofNat_ne_bot (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : WithBot α) ≠ ⊥ :=
  natCast_ne_bot n
@[simp] lemma bot_ne_ofNat (n : ℕ) [n.AtLeastTwo] : (⊥ : WithBot α) ≠ ofNat(n) :=
  bot_ne_natCast n

@[simp] lemma map_ofNat {f : α → β} (n : ℕ) [n.AtLeastTwo] :
    WithBot.map f (ofNat(n) : WithBot α) = f ofNat(n) := map_coe f n

@[simp] lemma map_natCast {f : α → β} (n : ℕ) :
    WithBot.map f (n : WithBot α) = f n := map_coe f n

lemma map_eq_ofNat_iff {f : β → α} {n : ℕ} [n.AtLeastTwo] {a : WithBot β} :
    a.map f = ofNat(n) ↔ ∃ x, a = .some x ∧ f x = n := map_eq_some_iff

lemma ofNat_eq_map_iff {f : β → α} {n : ℕ} [n.AtLeastTwo] {a : WithBot β} :
    ofNat(n) = a.map f ↔ ∃ x, a = .some x ∧ f x = n := some_eq_map_iff

lemma map_eq_natCast_iff {f : β → α} {n : ℕ} {a : WithBot β} :
    a.map f = n ↔ ∃ x, a = .some x ∧ f x = n := map_eq_some_iff

lemma natCast_eq_map_iff {f : β → α} {n : ℕ} {a : WithBot β} :
    n = a.map f ↔ ∃ x, a = .some x ∧ f x = n := some_eq_map_iff

@[simp] lemma bot_lt_natCast [LT α] (n : ℕ) : (⊥ : WithBot α) < n :=
  WithBot.bot_lt_coe _

end AddMonoidWithOne

instance charZero [AddMonoidWithOne α] [CharZero α] : CharZero (WithBot α) :=
  inferInstanceAs <| CharZero (WithTop α)

instance addCommMonoidWithOne [AddCommMonoidWithOne α] : AddCommMonoidWithOne (WithBot α) :=
  inferInstanceAs <| AddCommMonoidWithOne (WithTop α)

/-- A version of `WithBot.map` for `OneHom`s. -/
@[to_additive (attr := simps -fullyApplied)
  /-- A version of `WithBot.map` for `ZeroHom`s -/]
protected def _root_.OneHom.withBotMap {M N : Type*} [One M] [One N] (f : OneHom M N) :
    OneHom (WithBot M) (WithBot N) where
  toFun := WithBot.map f
  map_one' := by rw [WithBot.map_one, map_one, coe_one]

/-- A version of `WithBot.map` for `AddHom`s. -/
@[simps -fullyApplied]
protected def _root_.AddHom.withBotMap {M N : Type*} [Add M] [Add N] (f : AddHom M N) :
    AddHom (WithBot M) (WithBot N) where
  toFun := WithBot.map f
  map_add' := WithBot.map_add f

/-- A version of `WithBot.map` for `AddMonoidHom`s. -/
@[simps -fullyApplied]
protected def _root_.AddMonoidHom.withBotMap {M N : Type*} [AddZeroClass M] [AddZeroClass N]
    (f : M →+ N) : WithBot M →+ WithBot N :=
  { ZeroHom.withBotMap f.toZeroHom, AddHom.withBotMap f.toAddHom with toFun := WithBot.map f }

end WithBot

namespace AddEquiv

variable {γ : Type*} [Add α] [Add β] [Add γ] (e e₁ : α ≃+ β) (e₂ : β ≃+ γ)

/-- A `AddEquiv` version of `Equiv.withBotCongr`. -/
@[to_dual (attr := simps! apply) /-- A `AddEquiv` version of `Equiv.withTopCongr`. -/]
def withBotCongr : WithBot α ≃+ WithBot β where
  __ := e.toEquiv.withBotCongr
  map_add' := e.toAddHom.withBotMap.map_add'

@[to_dual (attr := simp)]
lemma coe_withBotCongr : e.withBotCongr = WithBot.map e := rfl

@[to_dual (attr := simp)]
lemma withBotCongr_toEquiv : e.withBotCongr = (e : α ≃ β).withBotCongr := rfl

@[to_dual (attr := simp)]
lemma withBotCongr_toAddHom : e.withBotCongr = (e : AddHom α β).withBotMap := rfl

@[to_dual (attr := simp)]
lemma withBotCongr_refl : (AddEquiv.refl α).withBotCongr = AddEquiv.refl _ :=
  AddEquiv.ext <| congr_fun WithBot.map_id

@[to_dual (attr := simp)]
theorem withBotCongr_symm : e.withBotCongr.symm = e.symm.withBotCongr := rfl

@[to_dual (attr := simp)]
theorem withBotCongr_trans :
    (e₁.trans e₂).withBotCongr = e₁.withBotCongr.trans e₂.withBotCongr := by
  ext x
  simp

end AddEquiv
