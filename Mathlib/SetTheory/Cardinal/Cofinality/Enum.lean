/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.SetTheory.Cardinal.Cofinality.Basic
public import Mathlib.SetTheory.Ordinal.Family
public import Mathlib.SetTheory.Ordinal.Univ

/-!
# Enumerating a cofinal set

We define a typeclass `IsRegularCardinalOrder` for well-ordered types, whose order type equals (the
initial ordinal of) their cofinality. This notion does not appear in the literature, but intends to
generalize the properties of intervals `Iio c.ord`, wherever `c` is a regular cardinal. Other
instances of this typeclass include `ℕ`, `Ordinal`, and `Cardinal`.

If `s` is a cofinal subset of a regular cardinal order `α`, there exists a unique order isomorphism
`α ≃o s`, which we call `Order.enum`. When `α = Ordinal`, this is referred to as the enumerator
function of the set. Note that if `α = ℕ`, then this definition matches `Nat.nth`.

## Todo

- Deprecate `Ordinal.enumOrd` in favor of `Order.enum`.
- Prove that `Order.enum` on the naturals coincides with `Nat.nth`.
-/

public section

universe u

open Cardinal Order Ordinal Set

variable {α : Type*}

/-- A typeclass which expresses that the order type of a well-order equals (the initial ordinal of)
its cofinality.

If `α` is infinite, this implies that `α` is order isomorphic to `Iio c.ord` for some regular
cardinal `c`. In the informal literature, one often says that `α` is a regular cardinal, by abuse
of notation. -/
class IsRegularCardinalOrder (α : Type*) [LinearOrder α] [WellFoundedLT α] where
  type_le_ord_cof : typeLT α ≤ (cof α).ord

instance : IsRegularCardinalOrder ℕ := ⟨by simp⟩

instance (priority := low) [LinearOrder α] [WellFoundedLT α] [Subsingleton α] :
    IsRegularCardinalOrder α where
  type_le_ord_cof := by
    cases isEmpty_or_nonempty α
    · simpa
    · cases nonempty_unique α
      have := BoundedOrder.ofUnique α
      simp

instance : IsRegularCardinalOrder Ordinal where
  type_le_ord_cof := by
    rw [type_lt_ordinal, ← ord_univ, ord_le_ord, le_cof_iff]
    intro s hs
    contrapose! hs
    rw [← Cardinal.lift_id (#s), ← small_iff_lift_mk_lt_univ] at hs
    rw [not_isCofinal_iff_bddAbove]
    exact Ordinal.bddAbove_of_small

namespace Order
variable [LinearOrder α] [WellFoundedLT α] [IsRegularCardinalOrder α]

theorem ord_cof_eq_type_lt : (cof α).ord = typeLT α := by
  apply IsRegularCardinalOrder.type_le_ord_cof.antisymm'
  rw [ord_le, card_type]
  exact cof_le_cardinalMk α

@[simp]
theorem cof_eq_card : cof α = #α := by
  rw [← card_type LT.lt, ← ord_cof_eq_type_lt, card_ord]

@[simp]
theorem _root_.Cardinal.ord_cardinalMk : ord (#α) = typeLT α := by
  rw [← ord_cof_eq_type_lt, cof_eq_card]

@[simp]
theorem cof_ordinal : cof Ordinal.{u} = Cardinal.univ.{u, u + 1} := by
  simp [← Cardinal.univ_id]

theorem ordinalType_eq_of_isCofinal {s : Set α} (hs : IsCofinal s) : typeLT s = typeLT α := by
  apply (RelEmbedding.ofMonotone Subtype.val (by simp)).ordinal_type_le.antisymm
  rw [← ord_cardinalMk, ord_le, card_type, ← cof_eq_card]
  exact cof_le hs

/-- Enumerate the elements of a cofinal subset of `α` by `α` itself. This is a generalization of
`Nat.nth`. -/
noncomputable def enum (s : Set α) (hs : IsCofinal s) : α ≃o s :=
  .ofRelIsoLT (type_eq.1 (ordinalType_eq_of_isCofinal hs).symm).some

theorem enum_le_of_forall_lt {a o : α} {s : Set α} {hs : IsCofinal s} (ho : o ∈ s)
    (H : ∀ b < a, enum s hs b < o) : enum s hs a ≤ o := by
  rw [← Subtype.coe_mk o ho, Subtype.coe_le_coe, ← OrderIso.le_symm_apply]
  apply le_of_forall_lt
  simpa [OrderIso.lt_symm_apply]

theorem enum_succ_le_of_lt [SuccOrder α] {a o : α} {s : Set α} {hs : IsCofinal s} (ha : o ∈ s)
    (H : enum s hs a < o) : enum s hs (succ a) ≤ o := by
  refine enum_le_of_forall_lt ha fun b hb ↦ H.trans_le' ?_
  simpa using le_of_lt_succ hb

@[simp]
theorem enum_univ (x : α) : enum univ .univ x = ⟨x, mem_univ x⟩ := by
  rw [← Subsingleton.allEq OrderIso.Set.univ.symm (enum univ .univ)]
  rfl

end Order
