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

open Classical

/-- Any partial order can be extended to a linear order.
-/
theorem extend_partialOrder {α : Type u} (r : α → α → Prop) [IsPartialOrder α r] :
    ∃ (s : α → α → Prop) (_ : IsLinearOrder α s), r ≤ s := by
  let S := { s | IsPartialOrder α s }
  -- ⊢ ∃ s x, r ≤ s
  have hS : ∀ c, c ⊆ S → IsChain (· ≤ ·) c → ∀ y ∈ c, ∃ ub ∈ S, ∀ z ∈ c, z ≤ ub := by
    rintro c hc₁ hc₂ s hs
    haveI := (hc₁ hs).1
    refine' ⟨sSup c, _, fun z hz => le_sSup hz⟩
    refine'
        { refl := _
          trans := _
          antisymm := _ } <;>
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
  -- ⊢ ∃ s x, r ≤ s
  haveI : IsPartialOrder α s := hs₁
  -- ⊢ ∃ s x, r ≤ s
  refine ⟨s, { total := ?_, refl := hs₁.refl, trans := hs₁.trans, antisymm := hs₁.antisymm } , rs⟩
  -- ⊢ ∀ (a b : α), s a b ∨ s b a
  intro x y
  -- ⊢ s x y ∨ s y x
  by_contra' h
  -- ⊢ False
  let s' x' y' := s x' y' ∨ s x' x ∧ s y y'
  -- ⊢ False
  rw [← hs₂ s' _ fun _ _ ↦ Or.inl] at h
  -- ⊢ False
  · apply h.1 (Or.inr ⟨refl _, refl _⟩)
    -- 🎉 no goals
  · refine'
    { refl := fun x ↦ Or.inl (refl _)
      trans := _
      antisymm := _ }
    rintro a b c (ab | ⟨ax : s a x, yb : s y b⟩) (bc | ⟨bx : s b x, yc : s y c⟩)
    · exact Or.inl (_root_.trans ab bc)
      -- 🎉 no goals
    · exact Or.inr ⟨_root_.trans ab bx, yc⟩
      -- 🎉 no goals
    · exact Or.inr ⟨ax, _root_.trans yb bc⟩
      -- 🎉 no goals
    · exact Or.inr ⟨ax, yc⟩
      -- 🎉 no goals
    rintro a b (ab | ⟨ax : s a x, yb : s y b⟩) (ba | ⟨bx : s b x, ya : s y a⟩)
    · exact antisymm ab ba
      -- 🎉 no goals
    · exact (h.2 (_root_.trans ya (_root_.trans ab bx))).elim
      -- 🎉 no goals
    · exact (h.2 (_root_.trans yb (_root_.trans ba ax))).elim
      -- 🎉 no goals
    · exact (h.2 (_root_.trans yb bx)).elim
      -- 🎉 no goals
#align extend_partial_order extend_partialOrder

/-- A type alias for `α`, intended to extend a partial order on `α` to a linear order. -/
def LinearExtension (α : Type u) : Type u :=
  α
#align linear_extension LinearExtension

noncomputable instance {α : Type u} [PartialOrder α] : LinearOrder (LinearExtension α) where
  le := (extend_partialOrder ((· ≤ ·) : α → α → Prop)).choose
  le_refl := (extend_partialOrder ((· ≤ ·) : α → α → Prop)).choose_spec.choose.1.1.1.1
  le_trans := (extend_partialOrder ((· ≤ ·) : α → α → Prop)).choose_spec.choose.1.1.2.1
  le_antisymm := (extend_partialOrder ((· ≤ ·) : α → α → Prop)).choose_spec.choose.1.2.1
  le_total := (extend_partialOrder ((· ≤ ·) : α → α → Prop)).choose_spec.choose.2.1
  decidableLE := Classical.decRel _

/-- The embedding of `α` into `LinearExtension α` as a relation homomorphism. -/
def toLinearExtension {α : Type u} [PartialOrder α] :
    ((· ≤ ·) : α → α → Prop) →r ((· ≤ ·) : LinearExtension α → LinearExtension α → Prop)
    where
  toFun x := x
  map_rel' := (extend_partialOrder ((· ≤ ·) : α → α → Prop)).choose_spec.choose_spec _ _
#align to_linear_extension toLinearExtension

instance {α : Type u} [Inhabited α] : Inhabited (LinearExtension α) :=
  ⟨(default : α)⟩
