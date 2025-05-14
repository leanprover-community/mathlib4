import Mathlib.Data.Fintype.Card

variable {α : Type*} {a : α} (f : Set α → Set α)

def cardOf (s : Set α) [Fintype (f s)] : ℕ := Fintype.card (f s)

lemma cardOf_set (s : Set α) (h : a ∈ s) [Fintype (f s)] : cardOf f s = Fintype.card (f s) := rfl

lemma cardOf_finset (s : Finset α) [Fintype (f s)] (h : a ∈ s) : cardOf f s = Fintype.card (f s) :=
  cardOf_set f _ h -- failed to synthesize Fintype ↑(f (Membership.mem s.val))
-- cardOf_set f s h -- works
-- cardOf_set f _ (by exact h) -- works
-- rfl -- works
variable {t : Finset α}
#check (t : Set α)
#check (t.val : Multiset α)
