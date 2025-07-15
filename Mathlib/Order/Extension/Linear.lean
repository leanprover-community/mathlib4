/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Order.Zorn
import Mathlib.Order.SuccPred.LinearLocallyFinite

/-!
# Extend a partial order to a linear order

This file constructs a linear order which is an extension of the given partial order, using Zorn's
lemma. It then uses this construction to show that every preorder is an extension of a partial
order, and every total preorder is an extension of a linear order.

Using this fact about total preorders, we show that certain types can be enumerated in a way that
is consistent with an ordering.

## Main results

- `extend_partialOrder`: Every partial order can be extended to a linear order.

- `exists_eq_extend_partialOrder`: Every preorder is an extension of a partial order.

- `exists_eq_extend_partialOrder`: Every total preorder is an extension of a linear order.

- `exists_nat_equiv_monotone`: For every lower-bounded, total, locally finite preorder on
  an infinite type `α`, there is a `Monotone` equivalence `e : ℕ ≃ α`.
-/


universe u

open Set

section PartialOrder

/-- **Szpilrajn extension theorem**: any partial order can be extended to a linear order. -/
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
      rcases hc₂.total h₁s₁ h₁s₂ with h | h
      · exact ⟨s₂, h₁s₂, _root_.trans (h _ _ h₂s₁) h₂s₂⟩
      · exact ⟨s₁, h₁s₁, _root_.trans h₂s₁ (h _ _ h₂s₂)⟩
    · rintro x y ⟨s₁, h₁s₁, h₂s₁⟩ ⟨s₂, h₁s₂, h₂s₂⟩
      haveI : IsPartialOrder _ _ := hc₁ h₁s₁
      haveI : IsPartialOrder _ _ := hc₁ h₁s₂
      rcases hc₂.total h₁s₁ h₁s₂ with h | h
      · exact antisymm (h _ _ h₂s₁) h₂s₂
      · apply antisymm h₂s₁ (h _ _ h₂s₂)
  obtain ⟨s, hrs, hs⟩ := zorn_le_nonempty₀ S hS r ‹_›
  haveI : IsPartialOrder α s := hs.prop
  refine ⟨s,
    { total := ?_, refl := hs.1.refl, trans := hs.1.trans, antisymm := hs.1.antisymm }, hrs⟩
  intro x y
  by_contra! h
  let s' x' y' := s x' y' ∨ s x' x ∧ s y y'
  rw [hs.eq_of_le (y := s') ?_ fun _ _ ↦ Or.inl] at h
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

/-- A type alias for `α`, intended to extend a partial order on `α` to a linear order. -/
def LinearExtension (α : Type u) : Type u :=
  α

noncomputable instance {α : Type u} [PartialOrder α] : LinearOrder (LinearExtension α) where
  le := (extend_partialOrder ((· ≤ ·) : α → α → Prop)).choose
  le_refl := (extend_partialOrder ((· ≤ ·) : α → α → Prop)).choose_spec.1.1.1.1.1
  le_trans := (extend_partialOrder ((· ≤ ·) : α → α → Prop)).choose_spec.1.1.1.2.1
  le_antisymm := (extend_partialOrder ((· ≤ ·) : α → α → Prop)).choose_spec.1.1.2.1
  le_total := (extend_partialOrder ((· ≤ ·) : α → α → Prop)).choose_spec.1.2.1
  toDecidableLE := Classical.decRel _

/-- The embedding of `α` into `LinearExtension α` as an order homomorphism. -/
noncomputable def toLinearExtension {α : Type u} [PartialOrder α] : α →o LinearExtension α where
  toFun x := x
  monotone' := (extend_partialOrder ((· ≤ ·) : α → α → Prop)).choose_spec.2

instance {α : Type u} [Inhabited α] : Inhabited (LinearExtension α) :=
  ⟨(default : α)⟩

end PartialOrder

section Preorder

variable {α : Type*}

/-- Given two orderings `r` and `s`, the ordering that first compares two elements using `r`,
  then breaks ties with `s`. Most reasonable when `r` is a preorder and `s` is a linear order. -/
def RefineBy (r s : α → α → Prop) (a b : α) :=
    (r a b) ∧ (r b a → s a b)

instance {α : Type*} (r s : α → α → Prop) [IsPreorder α r] [IsLinearOrder α s] :
    IsPartialOrder α (RefineBy r s) where
  refl _ := ⟨refl _, fun _ ↦ refl _⟩
  trans _ _ _ h h' := ⟨trans_of _ h.1 h'.1,
    fun hca ↦ trans_of _ (h.2 (trans_of _ h'.1 hca)) (h'.2 (trans_of _ hca h.1))⟩
  antisymm _ _ h h' := antisymm_of _ (h.2 h'.1) (h'.2 h.1)

instance {α : Type*} (r s : α → α → Prop) [IsTotalPreorder α r] [IsLinearOrder α s] :
    IsLinearOrder α (RefineBy r s) where
  total a b := by
    simp_rw [RefineBy]
    have hr := total_of r a b
    have hs := total_of s a b
    tauto

/-- Using choice, every preorder is an extension of some partial order. -/
theorem exists_eq_extend_partialOrder (r : α → α → Prop) [IsPreorder α r] :
    ∃ (s : α → α → Prop), IsPartialOrder α s ∧ s ≤ r := by
  obtain ⟨s, hs, -⟩ := extend_partialOrder (@Eq α)
  exact ⟨RefineBy r s, inferInstance, fun _ _ h ↦ h.1⟩

/-- Using choice, every total preorder is an extension of some linear order. -/
theorem exists_eq_extend_linearOrder (r : α → α → Prop) [IsTotalPreorder α r] :
    ∃ (s : α → α → Prop), IsLinearOrder α s ∧ s ≤ r := by
  obtain ⟨s, hs, -⟩ := extend_partialOrder (@Eq α)
  exact ⟨RefineBy r s, inferInstance, fun _ _ h ↦ h.1⟩

/-- A type synonym for some partial order on `α` refining a given preorder on `α`. -/
def PartialOrderRefinement (α : Type*) := α

instance [Preorder α] : PartialOrder (PartialOrderRefinement α) where
  le := Classical.choose (exists_eq_extend_partialOrder (α := α) (· ≤ ·))
  le_refl := (exists_eq_extend_partialOrder (α := α) (· ≤ ·)).choose_spec.1.refl
  le_trans := (exists_eq_extend_partialOrder (α := α) (· ≤ ·)).choose_spec.1.trans
  le_antisymm := (exists_eq_extend_partialOrder (α := α) (· ≤ ·)).choose_spec.1.antisymm

/-- The order homomorphism from `PartialOrderRefinement α` to `α` -/
def partialOrderRefinement_orderHom (α : Type*) [Preorder α] : PartialOrderRefinement α →o α where
  toFun a := a
  monotone' := (exists_eq_extend_partialOrder (α := α) (· ≤ ·)).choose_spec.2

/-- A type synonym for some linear order on `α` refining a given total preorder on `α`. -/
def LinearOrderRefinement (α : Type*) := α

instance [Preorder α] [IsTotal α (· ≤ ·)] : IsTotalPreorder α (· ≤ ·) where
  total := total_of _

noncomputable instance [Preorder α] [IsTotal α (· ≤ ·)] :
    LinearOrder (LinearOrderRefinement α) where
  le := Classical.choose (exists_eq_extend_linearOrder (α := α) (· ≤ ·))
  le_refl := (exists_eq_extend_linearOrder (α := α) (· ≤ ·)).choose_spec.1.refl
  le_trans := (exists_eq_extend_linearOrder (α := α) (· ≤ ·)).choose_spec.1.trans
  le_antisymm := (exists_eq_extend_linearOrder (α := α) (· ≤ ·)).choose_spec.1.antisymm
  le_total := (exists_eq_extend_linearOrder (α := α) (· ≤ ·)).choose_spec.1.total
  decidableLE := Classical.decRel _

/-- The order homomorphism from `LinearOrderRefinement α` to `α` -/
def linearOrderRefinement_orderHom (α : Type*) [Preorder α] [IsTotal α (· ≤ ·)] :
    LinearOrderRefinement α →o α where
  toFun a := a
  monotone' := (exists_eq_extend_linearOrder (α := α) (· ≤ ·)).choose_spec.2

end Preorder

section Enumeration

/-- For every total, lower-bounded, locally finite preorder on an infinite type, there is a monotone
  bijection from `ℕ`. -/
theorem exists_nat_equiv_monotone (α : Type*) [Infinite α] [Preorder α] [LocallyFiniteOrderBot α]
    [IsTotal α (· ≤ ·)] : ∃ (e : ℕ ≃ α), Monotone e := by
  have hfin : ∀ (a : LinearOrderRefinement α), (Iic a).Finite := fun (a : α) ↦
    (finite_Iic a).subset (fun b h ↦ (linearOrderRefinement_orderHom α).mono h)
  have h' : Infinite (LinearOrderRefinement α) := ‹_›
  have _ := LocallyFiniteOrder.ofFiniteIcc (fun a b ↦ (hfin b).subset Icc_subset_Iic_self)
  have _ := LocallyFiniteOrderBot.ofIic _ (fun a ↦ (hfin a).toFinset) (by simp)
  have _ := LocallyFiniteOrderBot.orderBot (LinearOrderRefinement α)
  have _ : NoMaxOrder (LinearOrderRefinement α) := {
    exists_gt := fun a ↦ by simpa using (hfin a).exists_not_mem }
  set e := (orderIsoNatOfLinearSuccPredArch (ι := LinearOrderRefinement α)).symm
  exact ⟨e.toEquiv, fun _ _ h ↦ (linearOrderRefinement_orderHom α).monotone (e.monotone h)⟩

/-- If `α` is infinite, `β` is a locally finite preorder, and `r : α → β` has finite fibers,
    then we can find a bijection `e : ℕ ≃ α` so that `i ≤ j → r (e i) ≤ r (e j)`.-/
theorem exists_nat_equiv_monotone_comp {α β : Type*} [Infinite α] [Preorder β]
    [LocallyFiniteOrderBot β] [IsTotal β (· ≤ ·)] (r : α → β) (hr : ∀ b, (r ⁻¹' {b}).Finite) :
    ∃ (e : ℕ ≃ α), Monotone (r ∘ e) := by
  classical
  set p : Preorder α := {
    le := fun x y ↦ r x ≤ r y
    le_refl := by simp
    le_trans := fun _ _ _ (h : r _ ≤ r _) ↦ h.trans }
  set ht : IsTotal α (· ≤ ·) := {
    total := fun a b ↦ total_of (· ≤ ·) (r a) (r b) }

  have hIicβ : ∀ b, (r ⁻¹' (Iic b)).Finite := fun b ↦
    ((finite_Iic b).biUnion (fun i _ ↦ hr i)).subset fun x (hx : r x ≤ b) ↦ mem_biUnion hx rfl

  have hIic : ∀ a : α, (Iic a).Finite := fun a ↦ (hIicβ (r a)).subset (fun _ ↦ id)

  have _ := LocallyFiniteOrderBot.ofIic' _ (fun x ↦ (hIic x).toFinset) (by simp)
  exact exists_nat_equiv_monotone α

end Enumeration
