/-
Copyright (c) 2024 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.GroupTheory.Sylow

/-!
# Z-Groups

A Z-group is a group whose Sylow subgroups are all cyclic.

## Main definitions

* `IsZGroup G`: A predicate stating that Sylow subgroups of `G` are cyclic.

TODO: Show that if `G` is a Z-group with commutator subgroup `G'`, then `G = G' ⋊ G/G'` where `G'`
and `G/G'` are cyclic of coprime orders.

-/

variable (G G' : Type*) [Group G] [Group G'] (f : G →* G')

class IsZGroup : Prop where
  isZGroup : ∀ p : ℕ, p.Prime → ∀ P : Sylow p G, IsCyclic P

variable {G G' f}

theorem IsZGroup_iff : IsZGroup G ↔ ∀ p : ℕ, p.Prime → ∀ P : Sylow p G, IsCyclic P :=
  ⟨fun h ↦ h.1, fun h ↦ ⟨h⟩⟩

namespace IsZGroup

theorem of_injective [hG' : IsZGroup G'] (hf : Function.Injective f) : IsZGroup G := by
  rw [IsZGroup_iff] at hG' ⊢
  intro p hp P
  obtain ⟨Q, hQ⟩ := P.exists_comap_eq_of_injective hf
  specialize hG' p hp Q
  have h : Subgroup.map f P ≤ Q := hQ ▸ Subgroup.map_comap_le f ↑Q
  have := isCyclic_of_surjective _ (Subgroup.subgroupOfEquivOfLe h).surjective
  exact isCyclic_of_surjective _ (Subgroup.equivMapOfInjective P f hf).symm.surjective

instance [IsZGroup G] (H : Subgroup G) : IsZGroup H := of_injective H.subtype_injective

end IsZGroup
