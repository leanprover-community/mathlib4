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
`Associates α ≃o FactorSet α` of `UniqueFactorizationMonoid.associatesOrderIso`.

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

It is transferred from `FactorSet α` along `associatesOrderIso`. -/
noncomputable instance : InfSet (Associates α) where
  sInf S := if _ : Nontrivial α then associatesOrderIso.completeLattice.sInf S else 0

/-- Associates in a unique factorization monoid form a complete lattice, with `sInf` the gcd and
`sSup` the lcm (which is `0` when the set is not bounded above by a nonzero element). -/
noncomputable instance : CompleteLattice (Associates α) where
  __ : Lattice (Associates α) := inferInstance
  __ : BoundedOrder (Associates α) := inferInstance
  __ := completeLatticeOfInf (Associates α) fun S ↦ by
    classical
    nontriviality α
    simpa [sInf, *] using associatesOrderIso.completeLattice.isGLB_sInf S

open scoped Classical in
/-- Associates in a unique factorization monoid form a coframe: `a ⊔ ⨅ s = ⨅ b ∈ s, a ⊔ b`.

This is not a frame: `2 ⊓ ⨆ {p | p prime, 3 ≤ p} = 2` in `Associates ℕ`. -/
noncomputable instance : Order.Coframe (Associates α) :=
  .ofMinimalAxioms
    { iInf_sup_le_sup_sInf a s :=by
        by_cases h : Nontrivial α
        · have := h
          exact (associatesOrderIso (α := α)).coframeMinimalAxioms.iInf_sup_le_sup_sInf a s
        · rw [not_nontrivial_iff_subsingleton] at h
          exact (Subsingleton.elim _ _).le }

end Associates
