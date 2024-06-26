/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Order.Zorn

#align_import order.extension.linear from "leanprover-community/mathlib"@"9830a300340708eaa85d477c3fb96dd25f9468a5"

/-!
# Extend a partial order to a linear order

This file constructs a linear order which is an extension of the given partial order, using Zorn's
lemma.
-/


universe u

open Set Classical

open scoped Classical

/-- Any partial order can be extended to a linear order.
-/
theorem extend_partialOrder {α : Type u} (r : α → α → Prop) [IsPartialOrder α r] :
    ∃ s : α → α → Prop, IsLinearOrder α s ∧ r ≤ s := by
  let S := { s | IsPartialOrder α s }
  have hS : ∀ c, c ⊆ S → IsChain (· ≤ ·) c → ∀ y ∈ c, ∃ ub ∈ S, ∀ z ∈ c, z ≤ ub := by
    rintro c hc₁ hc₂ s hs
    haveI := (hc₁ hs).1
    refine ⟨sSup c, ?_, fun z hz => le_sSup hz⟩
    refine
        { refl := ?_
          trans := ?_
          antisymm := ?_ } <;>
      simp_rw [binary_relation_sSup_iff]
    · intro x
      exact ⟨s, hs, refl x⟩
    · rintro x y z ⟨s₁, h₁s₁, h₂s₁⟩ ⟨s₂, h₁s₂, h₂s₂⟩
      haveI : IsPartialOrder _ _ := hc₁ h₁s₁
      haveI : IsPartialOrder _ _ := hc₁ h₁s₂
      cases' hc₂.total h₁s₁ h₁s₂ with h h
      · exact ⟨s₂, h₁s₂, _root_.trans (h _ _ h₂s₁) h₂s₂⟩
      · exact ⟨s₁, h₁s₁, _root_.trans h₂s₁ (h _ _ h₂s₂)⟩
    · rintro x y ⟨s₁, h₁s₁, h₂s₁⟩ ⟨s₂, h₁s₂, h₂s₂⟩
      haveI : IsPartialOrder _ _ := hc₁ h₁s₁
      haveI : IsPartialOrder _ _ := hc₁ h₁s₂
      cases' hc₂.total h₁s₁ h₁s₂ with h h
      · exact antisymm (h _ _ h₂s₁) h₂s₂
      · apply antisymm h₂s₁ (h _ _ h₂s₂)
  obtain ⟨s, hs₁ : IsPartialOrder _ _, rs, hs₂⟩ := zorn_nonempty_partialOrder₀ S hS r ‹_›
  haveI : IsPartialOrder α s := hs₁
  refine ⟨s, { total := ?_, refl := hs₁.refl, trans := hs₁.trans, antisymm := hs₁.antisymm } , rs⟩
  intro x y
  by_contra! h
  let s' x' y' := s x' y' ∨ s x' x ∧ s y y'
  rw [← hs₂ s' _ fun _ _ ↦ Or.inl] at h
  · apply h.1 (Or.inr ⟨refl _, refl _⟩)
  · refine
    { refl := fun x ↦ Or.inl (refl _)
      trans := ?_
      antisymm := ?_ }
    · rintro a b c (ab | ⟨ax : s a x, yb : s y b⟩) (bc | ⟨bx : s b x, yc : s y c⟩)
      · exact Or.inl (_root_.trans ab bc)
      · exact Or.inr ⟨_root_.trans ab bx, yc⟩
      · exact Or.inr ⟨ax, _root_.trans yb bc⟩
      · exact Or.inr ⟨ax, yc⟩
    rintro a b (ab | ⟨ax : s a x, yb : s y b⟩) (ba | ⟨bx : s b x, ya : s y a⟩)
    · exact antisymm ab ba
    · exact (h.2 (_root_.trans ya (_root_.trans ab bx))).elim
    · exact (h.2 (_root_.trans yb (_root_.trans ba ax))).elim
    · exact (h.2 (_root_.trans yb bx)).elim
#align extend_partial_order extend_partialOrder

/-- A type alias for `α`, intended to extend a partial order on `α` to a linear order. -/
def LinearExtension (α : Type u) : Type u :=
  α
#align linear_extension LinearExtension

noncomputable instance {α : Type u} [PartialOrder α] : LinearOrder (LinearExtension α) where
  le := (extend_partialOrder ((· ≤ ·) : α → α → Prop)).choose
  le_refl := (extend_partialOrder ((· ≤ ·) : α → α → Prop)).choose_spec.1.1.1.1.1
  le_trans := (extend_partialOrder ((· ≤ ·) : α → α → Prop)).choose_spec.1.1.1.2.1
  le_antisymm := (extend_partialOrder ((· ≤ ·) : α → α → Prop)).choose_spec.1.1.2.1
  le_total := (extend_partialOrder ((· ≤ ·) : α → α → Prop)).choose_spec.1.2.1
  decidableLE := Classical.decRel _

/-- The embedding of `α` into `LinearExtension α` as an order homomorphism. -/
def toLinearExtension {α : Type u} [PartialOrder α] : α →o LinearExtension α where
  toFun x := x
  monotone' := (extend_partialOrder ((· ≤ ·) : α → α → Prop)).choose_spec.2
#align to_linear_extension toLinearExtension

instance {α : Type u} [Inhabited α] : Inhabited (LinearExtension α) :=
  ⟨(default : α)⟩
