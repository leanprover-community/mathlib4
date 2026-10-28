/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.ConditionallyCompleteLattice.Finsupp
public import Mathlib.Order.Lattice.Nat

/-!
# Multisets form a conditionally complete lattice

We transfer the conditionally complete lattice structure on `α →₀ ℕ` along the order isomorphism
`Finsupp.orderIsoMultiset`.
-/

public section

open WithTop

namespace Multiset
variable {α : Type*} [DecidableEq α]

noncomputable instance : ConditionallyCompleteLattice (Multiset α) :=
  Finsupp.orderIsoMultiset.symm.conditionallyCompleteLattice

noncomputable instance : Order.Coframe (WithTop (Multiset α)) :=
  .ofMinimalAxioms {
    iInf_sup_le_sup_sInf y S := by
      have hz := isGLB_sInf S
      have h d (hd : d ∈ S) : ⨅ b ∈ S, y ⊔ b ≤ y ⊔ d := iInf₂_le d hd
      generalize ⨅ b ∈ S, y ⊔ b = x at h ⊢
      generalize sInf S = z at hz
      induction y using recTopCoe with
      | top => simp
      | coe m =>
      induction x using recTopCoe with
      | top =>
        simp at h
        simp [top_le_iff.1 <| hz.2 (by rw [h · ·])]
      | coe k =>
      induction z using recTopCoe with
      | top => simp
      | coe n =>
      rw [← coe_sup, coe_le_coe, le_iff_count]
      intro p
      rw [sup_eq_union, count_union]
      by_contra! hp
      rw [max_lt_iff] at hp
      suffices replicate (k.count p) p ≤ n by apply hp.2.not_ge; grw [← this]; simp
      refine coe_le_coe.1 <| hz.2 fun b hb ↦ ?_
      induction b using recTopCoe with
      | top => exact le_top
      | coe b =>
      have : k ≤ m ⊔ b := coe_le_coe.1 (by simpa [← coe_sup] using h _ hb)
      rw [sup_eq_union, le_iff_count] at this
      have := (this p).trans_eq (count_union ..)
      obtain h' | h' := le_max_iff.1 this
      · exact absurd h' hp.1.not_ge
      · exact mod_cast le_count_iff_replicate_le.1 h'
  }

end Multiset
