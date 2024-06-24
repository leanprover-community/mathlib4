import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Lattice
import Mathlib.Data.Greedoid.Basic

namespace Greedoid

variable {α : Type*}

open Finset

-- def base {α : Type*} [DecidableEq α] (S : Finset (Finset α)) : Finset (Finset α) :=
--   S.filter λ s ↦ ∀ t ∈ S, s ⊆ t → s.card + 1 ≠ t.card

def base (G : Greedoid α) : Finset (Finset α) :=
  let rk : ℕ := (G.feasible_set.image λ s ↦ s.card).max' (image_nonempty.mpr greedoid_nonempty)
  G.feasible_set.filter λ s ↦ s.card = rk

end Greedoid

#lint
