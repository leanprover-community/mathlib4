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
  fun h' b ↦ h b ↑b rfl (h' _)

inductive Option.IsOption {α β : Type*} (r : α → β → Prop) : Option α → Option β → Prop where
  | some (a b) : r a b → (some a).IsOption r (some b)
  | none : none.IsOption r none

def Option.forall_transfer {α β : Type*} {p : Option α → Sort*} {q : Option β → Sort*}
    (r : β → α → Prop) (f : β → α) (hf : ∀ b, r b (f b))
    (h : ∀ (s : Option β) (s' : Option α), s.IsOption r s' → p s' → q s) :
    (∀ s, p s) → (∀ s, q s) :=
  fun h' b ↦ by
    apply h b (b.map f) _ (h' _)
    cases b with
      | none => apply Option.IsOption.none
      | some s => ?_
    apply Option.IsOption.some
    apply hf

inductive Prod.IsProd {α α' β β' : Type*} (r : α → β → Prop) (r' : α' → β' → Prop) :
    α × α' → β × β' → Prop where
  | mk (a a' b b') : r a b → r' a' b' → (a, a').IsProd r r' (b, b')


def Prod.forall_transfer {α α' β β' : Type*}
    {p : α × α' → Sort*} {q : β × β' → Sort*}
    (r : β → α → Prop) (f : β → α) (hf : ∀ b, r b (f b))
    (r' : β' → α' → Prop) (f' : β' → α') (hf' : ∀ b, r' b (f' b))
    (h : ∀ (s : β × β') (s' : α × α'), s.IsProd r r' s' → p s' → q s) :
    (∀ s, p s) → (∀ s, q s) :=
  fun h' b ↦ by
    apply h b (b.map f f') _ (h' _)
    cases b with | mk b₁ b₂ => ?_
    apply IsProd.mk
    · apply hf
    · apply hf'

@[transport]
def Finset.forall_option_transfer {p : Option (Set α) → Sort*} {q : Option (Finset α) → Sort*}
    (h : ∀ (s : Option (Finset α)) (s' : Option (Set α)), s.IsOption Finset.IsSet s' → p s' → q s) :
    (∀ s, p s) → (∀ s, q s) :=
  fun h' b ↦ by
    apply h b (b.map SetLike.coe)
    · cases b with
      | none => apply Option.IsOption.none
      | some s =>
        apply Option.IsOption.some
        rfl
    apply h'

example [DecidableEq α] (s : Finset α) (a : α) : insert a (∅ : Finset α) = {a} := by
  transport
  sorry

example [DecidableEq α] (a : α) : ∀ s : Finset α, insert a ∅ = s := by
  transport
  sorry

example [DecidableEq α] (a : α) : ¬ ∀ s : Set α, insert a ∅ = s := by
  transport
  sorry

example [DecidableEq α] (a : α) (s : Option (Finset α)) : s.elim {a} (·.erase a) = ∅ := by
  revert s a
  transport
