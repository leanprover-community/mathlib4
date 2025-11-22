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
public import Mathlib.Tactic.ByContra

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

variable {α : Type*}

/-- A linearly ordered commutative monoid with an additively absorbing `⊤` element.
  Instances should include number systems with an infinite element adjoined. -/
class LinearOrderedAddCommMonoidWithTop (α : Type*) extends
    AddCommMonoid α, LinearOrder α, IsOrderedAddMonoid α, OrderTop α where
  /-- In a `LinearOrderedAddCommMonoidWithTop`, the `⊤` element is invariant under addition. -/
  protected top_add' : ∀ x : α, ⊤ + x = ⊤
  protected isAddLeftRegular_of_ne_top ⦃x : α⦄ : x ≠ ⊤ → IsAddLeftRegular x

/-- A linearly ordered commutative group with an additively absorbing `⊤` element.
  Instances should include number systems with an infinite element adjoined. -/
class LinearOrderedAddCommGroupWithTop (α : Type*)
    extends AddCommMonoid α, LinearOrder α, IsOrderedAddMonoid α, OrderTop α, SubNegMonoid α,
    Nontrivial α where
  /-- In a `LinearOrderedAddCommMonoidWithTop`, the `⊤` element is invariant under addition. -/
  protected top_add' (x : α) : ⊤ + x = ⊤
  neg_top : -(⊤ : α) = ⊤
  add_neg_cancel_of_ne_top ⦃x : α⦄ : x ≠ ⊤ → x + -x = 0

section LinearOrderedAddCommMonoidWithTop
variable [LinearOrderedAddCommMonoidWithTop α] {a : α}

@[simp]
theorem top_add (a : α) : ⊤ + a = ⊤ :=
  LinearOrderedAddCommMonoidWithTop.top_add' a

@[simp]
theorem add_top (a : α) : a + ⊤ = ⊤ :=
  Trans.trans (add_comm _ _) (top_add _)

@[simp] lemma IsAddRegular.of_ne_top (ha : a ≠ ⊤) : IsAddRegular a := by
  simpa using LinearOrderedAddCommMonoidWithTop.isAddLeftRegular_of_ne_top ha

lemma injective_add_left_of_ne_top (b : α) (h : b ≠ ⊤) : Function.Injective (fun x ↦ x + b) :=
  (IsAddRegular.of_ne_top h).2

lemma injective_add_right_of_ne_top (b : α) (h : b ≠ ⊤) : Function.Injective (fun x ↦ b + x) :=
  (IsAddRegular.of_ne_top h).1

lemma strictMono_add_left_of_ne_top (b : α) (h : b ≠ ⊤) : StrictMono (fun x ↦ x + b) :=
  add_left_mono.strictMono_of_injective <| injective_add_left_of_ne_top _ h

lemma strictMono_add_right_of_ne_top (b : α) (h : b ≠ ⊤) : StrictMono (fun x ↦ b + x) :=
  add_right_mono.strictMono_of_injective <| injective_add_right_of_ne_top _ h

end LinearOrderedAddCommMonoidWithTop

namespace LinearOrderedAddCommGroupWithTop

variable [LinearOrderedAddCommGroupWithTop α] {a b : α}

attribute [simp] neg_top

@[simp] lemma top_ne_zero : (⊤ : α) ≠ 0 := by
  intro h
  obtain ⟨a, ha⟩ := exists_ne (0 : α)
  rw [← zero_add a] at ha
  simp [LinearOrderedAddCommGroupWithTop.top_add', -zero_add, ← h] at ha

@[simp] lemma isAddUnit_iff : IsAddUnit a ↔ a ≠ ⊤ where
  mp := by rintro ⟨⟨b, c, hbc, -⟩, rfl⟩ rfl; simp [LinearOrderedAddCommGroupWithTop.top_add'] at hbc
  mpr ha := .of_add_eq_zero (-a) <| by simp [ha, add_neg_cancel_of_ne_top]

instance [LinearOrderedAddCommGroupWithTop α] : LinearOrderedAddCommMonoidWithTop α where
  top_add' := LinearOrderedAddCommGroupWithTop.top_add'
  isAddLeftRegular_of_ne_top _a ha := (isAddUnit_iff.2 ha).isAddRegular.1

lemma add_ne_top : a + b ≠ ⊤ ↔ a ≠ ⊤ ∧ b ≠ ⊤ := by simp [← isAddUnit_iff]

@[simp] lemma add_eq_top : a + b = ⊤ ↔ a = ⊤ ∨ b = ⊤ := by
  rw [← not_iff_not, not_or]; exact add_ne_top

@[simp] lemma neg_eq_top : -a = ⊤ ↔ a = ⊤ where
  mp h := by simpa [h] using add_neg_cancel_of_ne_top (x := a)
  mpr h := by simp [h]

instance (priority := 100) toSubtractionMonoid : SubtractionMonoid α where
  neg_neg a := by
    by_cases h : a = ⊤
    · simp [h]
    · have h2 : ¬ -a = ⊤ := fun nh ↦ h <| neg_eq_top.mp nh
      replace h2 : a + (-a + - -a) = a + 0 := congrArg (a + ·) (add_neg_cancel_of_ne_top h2)
      rw [← add_assoc, add_neg_cancel_of_ne_top h] at h2
      simp only [zero_add, add_zero] at h2
      exact h2
  neg_add_rev a b := by
    by_cases ha : a = ⊤
    · simp [ha]
    by_cases hb : b = ⊤
    · simp [hb]
    apply (_ : Function.Injective (a + b + ·))
    · dsimp
      rw [add_neg_cancel_of_ne_top, ← add_assoc, add_assoc a,
        add_neg_cancel_of_ne_top hb, add_zero,
        add_neg_cancel_of_ne_top ha]
      simp [ha, hb]
    · apply Function.LeftInverse.injective (g := (-(a + b) + ·))
      intro x
      dsimp only
      rw [← add_assoc, add_comm (-(a + b)), add_neg_cancel_of_ne_top, zero_add]
      simp [ha, hb]
  neg_eq_of_add a b h := by
    have oh := congrArg (-a + ·) h
    dsimp only at oh
    rw [add_zero, ← add_assoc, add_comm (-a), add_neg_cancel_of_ne_top, zero_add] at oh
    · exact oh.symm
    intro v
    simp [v] at h

lemma sub_pos (a b : α) : 0 < a - b ↔ b < a ∨ b = ⊤ where
  mp h := by
    refine or_iff_not_imp_right.mpr fun h2 ↦ ?_
    replace h := strictMono_add_left_of_ne_top _ h2 h
    simp only [zero_add] at h
    rw [sub_eq_add_neg, add_assoc, add_comm (-b),
      add_neg_cancel_of_ne_top h2, add_zero] at h
    exact h
  mpr h := by
    rcases h with h | h
    · convert strictMono_add_left_of_ne_top (-b) (by simp [h.ne_top]) h using 1
      · simp [add_neg_cancel_of_ne_top h.ne_top]
      · simp [sub_eq_add_neg]
    · rw [h]
      simp only [sub_eq_add_neg, LinearOrderedAddCommGroupWithTop.neg_top, add_top]
      apply lt_of_le_of_ne le_top
      exact Ne.symm top_ne_zero

end LinearOrderedAddCommGroupWithTop

namespace WithTop

instance linearOrderedAddCommMonoidWithTop [AddCancelCommMonoid α] [LinearOrder α]
    [IsOrderedAddMonoid α] : LinearOrderedAddCommMonoidWithTop (WithTop α) where
  top_add' := WithTop.top_add
  isAddLeftRegular_of_ne_top _a ha _b _c := WithTop.add_left_cancel ha

namespace LinearOrderedAddCommGroup

instance instNeg [AddCommGroup α] : Neg (WithTop α) where
  neg := WithTop.map fun a ↦ -a

/-- If `α` has subtraction, we can extend the subtraction to `WithTop α`, by setting `x - ⊤ = ⊤` and
`⊤ - x = ⊤`. This definition is only registered as an instance on additive commutative groups, to
avoid conflicting with the instance `WithTop.instSub` on types with a bottom element. -/
protected def sub [AddCommGroup α] : WithTop α → WithTop α → WithTop α
  | _, ⊤ => ⊤
  | ⊤, (x : α) => ⊤
  | (x : α), (y : α) => (x - y : α)

instance instSub [AddCommGroup α] : Sub (WithTop α) where
  sub := WithTop.LinearOrderedAddCommGroup.sub

variable [AddCommGroup α]

@[simp, norm_cast] lemma coe_neg (a : α) : (↑(-a) : WithTop α) = -a := rfl
@[simp, norm_cast] lemma coe_sub {a b : α} : (↑(a - b) : WithTop α) = ↑a - ↑b := rfl

@[simp] lemma neg_top : -(⊤ : WithTop α) = ⊤ := rfl

@[simp] lemma top_sub (x : WithTop α) : ⊤ - x = ⊤ := by cases x <;> rfl
@[simp] lemma sub_top (x : WithTop α) : x - ⊤ = ⊤ := by cases x <;> rfl

@[simp] lemma sub_eq_top_iff {a b : WithTop α} : a - b = ⊤ ↔ a = ⊤ ∨ b = ⊤ := by
  cases a <;> cases b <;> simp [← coe_sub]

instance [LinearOrder α] [IsOrderedAddMonoid α] : LinearOrderedAddCommGroupWithTop (WithTop α) where
  __ := WithTop.linearOrderedAddCommMonoidWithTop
  sub_eq_add_neg a b := by cases a <;> cases b <;> simp [← coe_sub, ← coe_neg, sub_eq_add_neg]
  neg_top := WithTop.map_top _
  zsmul := zsmulRec
  add_neg_cancel_of_ne_top | (a : α), _ => mod_cast add_neg_cancel a

end LinearOrderedAddCommGroup

end WithTop
