module

public import Mathlib.Tactic.Transport.Core
/-!
## haha
-/

public section

/-
How to transfer from `Set` to `Finset`?
- In a `∀ s : Finset α`, we set `s' := (↑s : Set α)`, so `s'` relates to `s`
- In `_ = _`, `_ ⊆ _`, `_ ⊂ _`, `_.Nonempty`, `_.card`, `x ∈ _`, rewrite with the relevant theorem,
  to generate a goal `_ ~ ?_`
- Fill in `{a} ~ {a}`, `∅ ~ ∅`, `s.insert a ~ s.insert a`, `s.image f ~ s.image f`,
  union, intersection, set difference

-/

variable {α : Type*} (s t : Finset α) (s' t' : Set α)

def Finset.IsSet : Prop := s = s'

@[transport]
theorem Finset.transport_eq (hs : s.IsSet s') (ht : t.IsSet t') : (s = t) = (s' = t') := by
  subst hs ht; simp

@[transport]
theorem Finset.transport_ne (hs : s.IsSet s') (ht : t.IsSet t') : (s ≠ t) = (s' ≠ t') := by
  subst hs ht; simp

@[transport]
theorem Finset.transport_subset (hs : s.IsSet s') (ht : t.IsSet t') : (s ⊆ t) = (s' ⊆ t') := by
  subst hs ht; simp

@[transport]
theorem Finset.transport_ssubset (hs : s.IsSet s') (ht : t.IsSet t') : (s ⊂ t) = (s' ⊂ t') := by
  subst hs ht; simp

-- TODO: Nonempty, membership, cardinality.

@[transport]
theorem Finset.transport_empty : (∅ : Finset α).IsSet ∅ := by simp [IsSet]

@[transport]
theorem Finset.transport_singleton (a : α) : ({a} : Finset α).IsSet {a} := by simp [IsSet]

@[transport]
theorem Finset.transport_insert [DecidableEq α] (a : α) (hs : s.IsSet s') :
    (insert a s).IsSet (insert a s') := by
  simp_all [IsSet]

@[transport]
theorem Finset.transport_union [DecidableEq α] (hs : s.IsSet s') (ht : t.IsSet t') :
    (s ∪ t).IsSet (s' ∪ t') := by
  simp_all [IsSet]

@[transport]
theorem Finset.transport_inter [DecidableEq α] (hs : s.IsSet s') (ht : t.IsSet t') :
    (s ∩ t).IsSet (s' ∩ t') := by
  simp_all [IsSet]

attribute [transport] mt Or.imp And.imp

@[transport]
def Finset.forall_transfer {p : Set α → Sort*} {q : Finset α → Sort*}
    (h : ∀ (s : Finset α) (s' : Set α), s.IsSet s' → p s' → q s) :
    (∀ s, p s) → (∀ s, q s) :=
  fun h' b ↦ h b b rfl (h' _)

example [DecidableEq α] (s : Finset α) (a : α) : insert a (∅ : Finset α) = {a} := by
  transport
  sorry

example [DecidableEq α] (a : α) : ∀ s : Finset α, insert a ∅ = s := by
  transport
  sorry

example [DecidableEq α] (a : α) : ¬ ∀ s : Set α, insert a ∅ = s := by
  transport
  sorry
