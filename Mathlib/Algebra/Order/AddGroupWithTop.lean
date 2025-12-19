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

import Mathlib.Tactic.TermCongr

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

/-- A linearly ordered commutative group with an additively absorbing `⊤` element.
  Instances should include number systems with an infinite element adjoined. -/
class LinearOrderedAddCommGroupWithTop (α : Type*) extends LinearOrderedAddCommMonoidWithTop α,
  SubNegMonoid α, Nontrivial α where
  neg_top : -(⊤ : α) = ⊤
  add_neg_cancel_of_ne_top ⦃x : α⦄ : x ≠ ⊤ → x + -x = 0

section LinearOrderedAddCommMonoidWithTop
variable [LinearOrderedAddCommMonoidWithTop α]

@[simp]
theorem top_add (a : α) : ⊤ + a = ⊤ :=
  LinearOrderedAddCommMonoidWithTop.top_add' a

@[simp]
theorem add_top (a : α) : a + ⊤ = ⊤ :=
  Trans.trans (add_comm _ _) (top_add _)

end LinearOrderedAddCommMonoidWithTop

namespace LinearOrderedAddCommGroupWithTop

variable [LinearOrderedAddCommGroupWithTop α] {a b : α}

attribute [simp] LinearOrderedAddCommGroupWithTop.neg_top

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
  simp [top_add, -zero_add, ← h] at ha

@[simp] lemma zero_ne_top : 0 ≠ (⊤ : α) := top_ne_zero.symm

@[simp] lemma top_pos : (0 : α) < ⊤ := lt_top_iff_ne_top.2 top_ne_zero.symm

@[simp]
lemma add_neg_cancel_iff_ne_top : a + -a = 0 ↔ a ≠ ⊤ where
  mp := by contrapose; simp +contextual
  mpr h := add_neg_cancel_of_ne_top h

@[simp]
lemma sub_self_eq_zero_iff_ne_top : a - a = 0 ↔ a ≠ ⊤ := by
  rw [sub_eq_add_neg, add_neg_cancel_iff_ne_top]

alias ⟨_, sub_self_eq_zero_of_ne_top⟩ := sub_self_eq_zero_iff_ne_top

@[simp] lemma isAddUnit_iff : IsAddUnit a ↔ a ≠ ⊤ where
  mp := by rintro ⟨⟨b, c, hbc, -⟩, rfl⟩ rfl; simp [top_add] at hbc
  mpr ha := .of_add_eq_zero (-a) <| by simp [ha, add_neg_cancel_of_ne_top]

instance : LinearOrderedAddCommMonoidWithTop α where
  top_add' := top_add

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

lemma injective_add_left_of_ne_top (b : α) (h : b ≠ ⊤) : Function.Injective (fun x ↦ x + b) :=
  fun x y hxy ↦ by simpa [h] using congr($hxy - b)

lemma injective_add_right_of_ne_top (b : α) (h : b ≠ ⊤) : Function.Injective (fun x ↦ b + x) := by
  simpa [add_comm] using injective_add_left_of_ne_top b h

lemma strictMono_add_left_of_ne_top (b : α) (h : b ≠ ⊤) : StrictMono (fun x ↦ x + b) := by
  apply Monotone.strictMono_of_injective
  · apply Monotone.add_const monotone_id
  · apply injective_add_left_of_ne_top _ h

lemma strictMono_add_right_of_ne_top (b : α) (h : b ≠ ⊤) : StrictMono (fun x ↦ b + x) := by
  simpa [add_comm] using strictMono_add_left_of_ne_top b h

lemma sub_pos (a b : α) : 0 < a - b ↔ b < a ∨ b = ⊤ where
  mp h := or_iff_not_imp_right.mpr fun hb ↦ by
    simpa [sub_eq_add_neg, add_assoc, hb] using strictMono_add_left_of_ne_top _ hb h
  mpr := by
    rintro (h | rfl)
    · simpa [sub_eq_add_neg, h.ne_top]
        using strictMono_add_left_of_ne_top (-b) (by simp [h.ne_top]) h
    · simp

end LinearOrderedAddCommGroupWithTop

namespace WithTop

instance linearOrderedAddCommMonoidWithTop [AddCommMonoid α] [LinearOrder α]
    [IsOrderedAddMonoid α] : LinearOrderedAddCommMonoidWithTop (WithTop α) where
  top_add' := WithTop.top_add

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
  sub_eq_add_neg a b := by cases a <;> cases b <;> simp [← coe_sub, ← coe_neg, sub_eq_add_neg]
  neg_top := WithTop.map_top _
  zsmul := zsmulRec
  add_neg_cancel_of_ne_top | (a : G), _ => mod_cast add_neg_cancel a

end WithTop.LinearOrderedAddCommGroup
