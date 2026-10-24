/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.Bounds.OrderIso
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.ConditionallyCompleteLattice.Multiset
public import Mathlib.RingTheory.UniqueFactorizationDomain.MulEquiv

/-!
# The complete lattice of associates

The associates of a unique factorization monoid form a complete (co)Heyting algebra, with `inf` the
gcd, `sup` the lcm and `⊤ = 0`. We deduce this from the order isomorphism
`Associates α ≃o WithTop (Multiset (IrreducibleAssociates α))` of
`UniqueFactorizationMonoid.associatesOrderIso`.

## Main declarations

* `Associates.instCompleteLattice`: `Associates α` is a complete lattice.
* `Associates.instCoframe`: `Associates α` is a coframe.

Note that `Associates α` is not a frame in general (hence not a `CompleteDistribLattice`): in
`Associates ℕ`, we have `2 ⊓ sSup {p | p prime, 3 ≤ p} = 2 ⊓ 0 = 2` while `2 ⊓ p = 1` for each `p`.
-/

@[expose] public section

namespace Associates
open UniqueFactorizationMonoid

variable {α : Type*} [CommMonoidWithZero α] [UniqueFactorizationMonoid α]

open scoped Classical in
/-- The infimum of a set of associates is the greatest common divisor of its elements.

It is transferred from `WithTop (Multiset _)` along `associatesOrderIso`. -/
noncomputable instance : InfSet (Associates α) where
  sInf S := if h : Nontrivial α then
      haveI := h
      (OrderIso.completeLattice
        (β := WithTop (Multiset (IrreducibleAssociates α))) (associatesOrderIso (α := α))).sInf S
    else 0

open scoped Classical in
lemma isGLB_sInf_associates (S : Set (Associates α)) : IsGLB S (sInf S) := by
  by_cases h : Nontrivial α
  · have := h
    simp only [sInf, h, ↓reduceDIte]
    exact (OrderIso.completeLattice
      (β := WithTop (Multiset (IrreducibleAssociates α))) (associatesOrderIso (α := α))).isGLB_sInf
        S
  · rw [not_nontrivial_iff_subsingleton] at h
    exact ⟨fun _ _ ↦ (Subsingleton.elim _ _).le, fun _ _ ↦ (Subsingleton.elim _ _).le⟩

/-- Associates in a unique factorization monoid form a complete lattice, with `sInf` the gcd and
`sSup` the lcm (which is `0` when the set is not bounded above by a nonzero element). -/
noncomputable instance : CompleteLattice (Associates α) where
  __ : Lattice (Associates α) := inferInstance
  __ : BoundedOrder (Associates α) := inferInstance
  __ := completeLatticeOfInf (Associates α) isGLB_sInf_associates

open scoped Classical in
/-- Associates in a unique factorization monoid form a coframe: `a ⊔ ⨅ s = ⨅ b ∈ s, a ⊔ b`.

This is not a frame: `2 ⊓ ⨆ {p | p prime, 3 ≤ p} = 2` in `Associates ℕ`. -/
noncomputable instance : Order.Coframe (Associates α) :=
  Order.Coframe.ofMinimalAxioms
    { iInf_sup_le_sup_sInf := fun a s ↦ by
        by_cases h : Nontrivial α
        · have := h
          exact (associatesOrderIso (α := α)).coframeMinimalAxioms.iInf_sup_le_sup_sInf a s
        · rw [not_nontrivial_iff_subsingleton] at h
          exact (Subsingleton.elim _ _).le }

end Associates
