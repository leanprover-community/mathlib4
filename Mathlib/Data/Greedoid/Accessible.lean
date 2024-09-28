import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Init.Data.Nat.Basic

namespace Greedoid

open Nat Finset

variable {α : Type*}

def AccessibleProperty (Sys : Finset α → Prop) : Prop :=
  ⦃s : Finset α⦄ → Sys s → s.Nonempty → ∃ t, t ⊆ s ∧ t.card + 1 = s.card ∧ Sys t

class Accessible (Sys : Finset α → Prop) : Prop :=
  accessible :
    ⦃s : Finset α⦄ → Sys s → s.Nonempty → ∃ t, t ⊆ s ∧ t.card + 1 = s.card ∧ Sys t

namespace Accessible

variable {Sys : Finset α → Prop} [Accessible Sys]

-- TODO: Add doc.
theorem nonempty_contains_emptyset'
    {s : Finset α} (hs : Sys s) {n : ℕ} (hn : n = s.card) :
    Sys ∅ := by
  induction n generalizing s with
  | zero => exact card_eq_zero.mp hn.symm ▸ hs
  | succ _ ih =>
    rcases Accessible.accessible hs (by rw[← card_ne_zero]; omega) with ⟨t, _, _, ht⟩
    exact ih ht (by omega)

theorem nonempty_contains_emptyset
    {s : Finset α} (hs : Sys s) :
    Sys ∅ :=
  nonempty_contains_emptyset' hs rfl



end Accessible

end Greedoid

