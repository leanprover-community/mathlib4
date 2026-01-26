
/-!
# Pairwise relations on a multiset

This file provides basic results about `Multiset.Pairwise` (definitions are in
`Mathlib/Data/Multiset/Defs.lean`).
-/

public section

namespace Multiset

variable {α : Type*} {r : α → α → Prop} {s : Multiset α}

theorem Pairwise.forall (H : Symmetric r) (hs : Pairwise r s) :
    ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → a ≠ b → r a b :=
  let ⟨_, hl₁, hl₂⟩ := hs
  hl₁.symm ▸ hl₂.forall H

end Multiset
