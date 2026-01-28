/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Order.Monoid.WithTop
public import Mathlib.Algebra.Regular.Basic


/-!
# Linearly ordered commutative additive groups and monoids with a top element adjoined

This file sets up a special class of linearly ordered commutative additive monoids
that show up as the target of so-called “valuations” in algebraic number theory.

Usually, in the informal literature, these objects are constructed
by taking a linearly ordered commutative additive group Γ and formally adjoining a
top element: Γ ∪ {⊤}.

The disadvantage is that a type such as `ENNReal` is not of that form,
whereas it is a very common target for valuations.
The solutions is to use a typeclass, and that is exactly what we do in this file.
-/

@[expose] public section

variable {G α : Type*}

/-- A linearly ordered commutative monoid with an additively absorbing `⊤` element.
  Instances should include number systems with an infinite element adjoined. -/
class LinearOrderedAddCommMonoidWithTop (α : Type*) extends
    AddCommMonoid α, LinearOrder α, IsOrderedAddMonoid α, OrderTop α where
  /-- In a `LinearOrderedAddCommMonoidWithTop`, the `⊤` element is invariant under addition. -/
  protected top_add' : ∀ x : α, ⊤ + x = ⊤
  protected isAddLeftRegular_of_ne_top ⦃x : α⦄ : x ≠ ⊤ → IsAddLeftRegular x

/-- A linearly ordered commutative group with an additively absorbing `⊤` element.
  Instances should include number systems with an infinite element adjoined. -/
-- We do not extend `LinearOrderedAddCommMonoidWithTop` as that would bring in the unnecessary
-- `isAddLeftRegular_of_ne_top` field.
class LinearOrderedAddCommGroupWithTop (α : Type*)
    extends AddCommMonoid α, LinearOrder α, IsOrderedAddMonoid α, OrderTop α, SubNegMonoid α,
    Nontrivial α where
  /-- In a `LinearOrderedAddCommMonoidWithTop`, the `⊤` element is invariant under addition. -/
  protected top_add' (x : α) : ⊤ + x = ⊤
  neg_top : -(⊤ : α) = ⊤
  add_neg_cancel_of_ne_top ⦃x : α⦄ : x ≠ ⊤ → x + -x = 0

section LinearOrderedAddCommMonoidWithTop
variable [LinearOrderedAddCommMonoidWithTop α] {a b c : α}

@[simp]
theorem top_add (a : α) : ⊤ + a = ⊤ :=
  LinearOrderedAddCommMonoidWithTop.top_add' a

@[simp]
theorem add_top (a : α) : a + ⊤ = ⊤ :=
  Trans.trans (add_comm _ _) (top_add _)

@[simp] lemma IsAddRegular.of_ne_top (ha : a ≠ ⊤) : IsAddRegular a := by
  simpa using LinearOrderedAddCommMonoidWithTop.isAddLeftRegular_of_ne_top ha

lemma add_left_injective_of_ne_top (b : α) (h : b ≠ ⊤) : Function.Injective (fun x ↦ x + b) :=
  (IsAddRegular.of_ne_top h).2

lemma add_right_injective_of_ne_top (b : α) (h : b ≠ ⊤) : Function.Injective (fun x ↦ b + x) :=
  (IsAddRegular.of_ne_top h).1

@[simp]
lemma add_left_inj_of_ne_top (h : a ≠ ⊤) : b + a = c + a ↔ b = c :=
  (add_left_injective_of_ne_top _ h).eq_iff

@[simp]
lemma add_right_inj_of_ne_top (h : a ≠ ⊤) : a + b = a + c ↔ b = c :=
  (add_right_injective_of_ne_top _ h).eq_iff

lemma add_left_strictMono_of_ne_top (h : b ≠ ⊤) : StrictMono (fun x ↦ x + b) :=
  add_left_mono.strictMono_of_injective <| add_left_injective_of_ne_top _ h

lemma add_right_strictMono_of_ne_top (h : b ≠ ⊤) : StrictMono (fun x ↦ b + x) :=
  add_right_mono.strictMono_of_injective <| add_right_injective_of_ne_top _ h

@[simp]
lemma add_le_add_iff_left_of_ne_top (h : a ≠ ⊤) : b + a ≤ c + a ↔ b ≤ c :=
  (add_left_strictMono_of_ne_top h).le_iff_le

@[simp]
lemma add_le_add_iff_right_of_ne_top (h : a ≠ ⊤) : a + b ≤ a + c ↔ b ≤ c :=
  (add_right_strictMono_of_ne_top h).le_iff_le

@[simp]
lemma add_lt_add_iff_left_of_ne_top (h : a ≠ ⊤) : b + a < c + a ↔ b < c :=
  (add_left_strictMono_of_ne_top h).lt_iff_lt

@[simp]
lemma add_lt_add_iff_right_of_ne_top (h : a ≠ ⊤) : a + b < a + c ↔ b < c :=
  (add_right_strictMono_of_ne_top h).lt_iff_lt

end LinearOrderedAddCommMonoidWithTop

namespace LinearOrderedAddCommGroupWithTop

variable [LinearOrderedAddCommGroupWithTop α] {a b c : α}

attribute [simp] neg_top

@[deprecated (since := "2025-12-14")] protected alias add_neg_cancel := add_neg_cancel_of_ne_top

/-! Note: The following lemmas are special cases of the corresponding `IsAddUnit` lemmas. -/

lemma neg_add_cancel_of_ne_top (ha : a ≠ ⊤) : -a + a = 0 := by
  simp [add_comm, add_neg_cancel_of_ne_top ha]

lemma add_neg_cancel_left_of_ne_top (ha : a ≠ ⊤) (b : α) : a + (-a + b) = b := by
  simp [← add_assoc, add_neg_cancel_of_ne_top ha]

lemma neg_add_cancel_left_of_ne_top (ha : a ≠ ⊤) (b : α) : -a + (a + b) = b := by
  simp [← add_assoc, neg_add_cancel_of_ne_top ha]

lemma add_neg_cancel_right_of_ne_top (hb : b ≠ ⊤) (a : α) : a + b + -b = a := by
  simp [add_assoc, add_neg_cancel_of_ne_top hb]

lemma neg_add_cancel_right_of_ne_top (hb : b ≠ ⊤) (a : α) : a + -b + b = a := by
  simp [add_assoc, neg_add_cancel_of_ne_top hb]

@[simp] lemma top_ne_zero : (⊤ : α) ≠ 0 := by
  intro h
  obtain ⟨a, ha⟩ := exists_ne (0 : α)
  rw [← zero_add a] at ha
  simp [LinearOrderedAddCommGroupWithTop.top_add', -zero_add, ← h] at ha

@[simp] lemma zero_ne_top : 0 ≠ (⊤ : α) := top_ne_zero.symm

@[simp] lemma top_pos : (0 : α) < ⊤ := lt_top_iff_ne_top.2 top_ne_zero.symm

@[simp] lemma isAddUnit_iff : IsAddUnit a ↔ a ≠ ⊤ where
  mp := by rintro ⟨⟨b, c, hbc, -⟩, rfl⟩ rfl; simp [LinearOrderedAddCommGroupWithTop.top_add'] at hbc
  mpr ha := .of_add_eq_zero (-a) <| by simp [ha, add_neg_cancel_of_ne_top]

instance : LinearOrderedAddCommMonoidWithTop α where
  top_add' := LinearOrderedAddCommGroupWithTop.top_add'
  isAddLeftRegular_of_ne_top _a ha := (isAddUnit_iff.2 ha).isAddRegular.1

lemma add_ne_top : a + b ≠ ⊤ ↔ a ≠ ⊤ ∧ b ≠ ⊤ := by simp [← isAddUnit_iff]

@[simp] lemma add_eq_top : a + b = ⊤ ↔ a = ⊤ ∨ b = ⊤ := by
  rw [← not_iff_not, not_or]; exact add_ne_top

@[simp] lemma add_lt_top : a + b < ⊤ ↔ a < ⊤ ∧ b < ⊤ := by simp [lt_top_iff_ne_top]

@[simp] lemma neg_eq_top : -a = ⊤ ↔ a = ⊤ where
  mp h := by simpa [h] using add_neg_cancel_of_ne_top (x := a)
  mpr h := by simp [h]

@[simp] lemma sub_top : a - ⊤ = ⊤ := by simp [sub_eq_add_neg]

instance (priority := 100) toSubtractionMonoid : SubtractionMonoid α where
  neg_neg a := by
    obtain rfl | ha := eq_or_ne a ⊤
    · simp
    · apply left_neg_eq_right_neg (a := -a) <;> simp [add_comm, add_neg_cancel_of_ne_top, ha]
  neg_add_rev a b := by
    obtain rfl | ha := eq_or_ne a ⊤
    · simp
    obtain rfl | hb := eq_or_ne b ⊤
    · simp
    · exact left_neg_eq_right_neg (a := a + b) (by simp [neg_add_cancel_of_ne_top, *])
        (by simp [add_assoc, add_neg_cancel_of_ne_top, add_neg_cancel_left_of_ne_top, *])
  neg_eq_of_add a b h := by
    have ha : a ≠ ⊤ := by rintro rfl; simp at h
    exact left_neg_eq_right_neg (a := a) (by simp [neg_add_cancel_of_ne_top, *]) h

@[deprecated (since := "2025-12-27")]
alias injective_add_left_of_ne_top := add_left_injective_of_ne_top

@[deprecated (since := "2025-12-27")]
alias injective_add_right_of_ne_top := add_right_injective_of_ne_top

lemma sub_left_injective_of_ne_top (h : b ≠ ⊤) : Function.Injective fun x ↦ x - b := by
  simpa [sub_eq_add_neg] using add_left_injective_of_ne_top (-b) (by simpa)

lemma sub_right_injective_of_ne_top (h : b ≠ ⊤) : Function.Injective fun x ↦ b - x := by
  simpa [sub_eq_add_neg] using (add_right_injective_of_ne_top b h).comp neg_injective

@[simp]
lemma sub_left_inj_of_ne_top (h : a ≠ ⊤) : b - a = c - a ↔ b = c :=
  (sub_left_injective_of_ne_top h).eq_iff

@[simp]
lemma sub_right_inj_of_ne_top (h : a ≠ ⊤) : a - b = a - c ↔ b = c :=
  (sub_right_injective_of_ne_top h).eq_iff

@[deprecated (since := "2025-12-27")]
alias strictMono_add_left_of_ne_top := add_left_strictMono_of_ne_top

@[deprecated (since := "2025-12-27")]
alias strictMono_add_right_of_ne_top := add_right_strictMono_of_ne_top

lemma sub_left_strictMono_of_ne_top (h : b ≠ ⊤) : StrictMono fun x ↦ x - b := by
  simpa [sub_eq_add_neg] using add_left_strictMono_of_ne_top (b := -b) (by simpa)

@[simp]
lemma sub_le_sub_iff_left_of_ne_top (h : a ≠ ⊤) : b - a ≤ c - a ↔ b ≤ c :=
  (sub_left_strictMono_of_ne_top h).le_iff_le

@[simp]
lemma sub_lt_sub_iff_left_of_ne_top (h : a ≠ ⊤) : b - a < c - a ↔ b < c :=
  (sub_left_strictMono_of_ne_top h).lt_iff_lt

@[simp]
lemma add_neg_cancel_iff_ne_top : a + -a = 0 ↔ a ≠ ⊤ where
  mp := by contrapose; simp +contextual
  mpr h := add_neg_cancel_of_ne_top h

@[simp]
lemma sub_self_eq_zero_iff_ne_top : a - a = 0 ↔ a ≠ ⊤ := by
  rw [sub_eq_add_neg, add_neg_cancel_iff_ne_top]

alias ⟨_, sub_self_eq_zero_of_ne_top⟩ := sub_self_eq_zero_iff_ne_top

lemma sub_pos : 0 < a - b ↔ b < a ∨ b = ⊤ := by
  obtain rfl | hb := eq_or_ne b ⊤
  · simp
  · simp [← sub_self_eq_zero_of_ne_top hb, hb]

@[simp]
lemma neg_pos : 0 < -a ↔ a < 0 ∨ a = ⊤ := by
  simpa using sub_pos (a := 0) (b := a)

@[simp]
lemma sub_self_nonneg : 0 ≤ a - a := by
  obtain rfl | ha := eq_or_ne a ⊤
  · simp
  · rw [sub_self_eq_zero_of_ne_top ha]

@[simp]
lemma sub_eq_zero (ha : a ≠ ⊤) : b - a = 0 ↔ b = a := by
  rw [← sub_self_eq_zero_of_ne_top ha, sub_left_inj_of_ne_top ha]

end LinearOrderedAddCommGroupWithTop

namespace WithTop

instance linearOrderedAddCommMonoidWithTop [AddCancelCommMonoid α] [LinearOrder α]
    [IsOrderedAddMonoid α] : LinearOrderedAddCommMonoidWithTop (WithTop α) where
  top_add' := WithTop.top_add
  isAddLeftRegular_of_ne_top _a ha _b _c := WithTop.add_left_cancel ha

namespace LinearOrderedAddCommGroup
variable [AddCommGroup G] {x y : WithTop G}

instance instNeg : Neg (WithTop G) where
  neg := .map fun a ↦ -a

/-- If `G` has subtraction, we can extend the subtraction to `WithTop G`, by setting `x - ⊤ = ⊤` and
`⊤ - x = ⊤`. This definition is only registered as an instance on additive commutative groups, to
avoid conflicting with the instance `WithTop.instSub` on types with a bottom element. -/
instance instSub : Sub (WithTop G) where
  sub
  | _, ⊤ => ⊤
  | ⊤, (b : G) => ⊤
  | (a : G), (b : G) => (a - b : G)

@[simp, norm_cast] lemma coe_neg (a : G) : (↑(-a) : WithTop G) = -a := rfl
@[simp, norm_cast] lemma coe_sub (a b : G) : (↑(a - b) : WithTop G) = ↑a - ↑b := rfl

@[simp] lemma neg_top : -(⊤ : WithTop G) = ⊤ := rfl

@[simp] lemma top_sub (x : WithTop G) : ⊤ - x = ⊤ := by cases x <;> rfl
@[simp] lemma sub_top (x : WithTop G) : x - ⊤ = ⊤ := by cases x <;> rfl

@[simp] lemma sub_eq_top_iff : x - y = ⊤ ↔ x = ⊤ ∨ y = ⊤ := by
  cases x <;> cases y <;> simp [← coe_sub]

instance [LinearOrder G] [IsOrderedAddMonoid G] : LinearOrderedAddCommGroupWithTop (WithTop G) where
  __ := WithTop.linearOrderedAddCommMonoidWithTop
  sub_eq_add_neg a b := by cases a <;> cases b <;> simp [← coe_sub, ← coe_neg, sub_eq_add_neg]
  neg_top := WithTop.map_top _
  zsmul := zsmulRec
  add_neg_cancel_of_ne_top | (a : G), _ => mod_cast add_neg_cancel a

end WithTop.LinearOrderedAddCommGroup
