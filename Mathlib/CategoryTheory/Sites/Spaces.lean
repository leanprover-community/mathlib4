/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Sites.Pretopology
import Mathlib.CategoryTheory.Limits.Lattice
import Mathlib.Topology.Sets.Opens

#align_import category_theory.sites.spaces from "leanprover-community/mathlib"@"b6fa3beb29f035598cf0434d919694c5e98091eb"

/-!
# Grothendieck topology on a topological space

Define the Grothendieck topology and the pretopology associated to a topological space, and show
that the pretopology induces the topology.

The covering (pre)sieves on `X` are those for which the union of domains contains `X`.

## Tags

site, Grothendieck topology, space

## References

* [nLab, *Grothendieck topology*](https://ncatlab.org/nlab/show/Grothendieck+topology)
* [S. MacLane, I. Moerdijk, *Sheaves in Geometry and Logic*][MM92]

## Implementation notes

We define the two separately, rather than defining the Grothendieck topology as that generated
by the pretopology for the purpose of having nice definitional properties for the sieves.
-/


universe u

namespace Opens

variable (T : Type u) [TopologicalSpace T]

open CategoryTheory TopologicalSpace CategoryTheory.Limits

/-- The Grothendieck topology associated to a topological space. -/
def grothendieckTopology : GrothendieckTopology (Opens T)
    where
  sieves X S := ∀ x ∈ X, ∃ (U : _) (f : U ⟶ X), S f ∧ x ∈ U
  top_mem' X x hx := ⟨_, 𝟙 _, trivial, hx⟩
  pullback_stable' X Y S f hf y hy := by
    rcases hf y (f.le hy) with ⟨U, g, hg, hU⟩
    -- ⊢ ∃ U f_1, (Sieve.pullback f S).arrows f_1 ∧ y ∈ U
    refine' ⟨U ⊓ Y, homOfLE inf_le_right, _, hU, hy⟩
    -- ⊢ (Sieve.pullback f S).arrows (homOfLE (_ : U ⊓ Y ≤ Y))
    apply S.downward_closed hg (homOfLE inf_le_left)
    -- 🎉 no goals
  transitive' X S hS R hR x hx := by
    rcases hS x hx with ⟨U, f, hf, hU⟩
    -- ⊢ ∃ U f, R.arrows f ∧ x ∈ U
    rcases hR hf _ hU with ⟨V, g, hg, hV⟩
    -- ⊢ ∃ U f, R.arrows f ∧ x ∈ U
    exact ⟨_, g ≫ f, hg, hV⟩
    -- 🎉 no goals
#align opens.grothendieck_topology Opens.grothendieckTopology

/-- The Grothendieck pretopology associated to a topological space. -/
def pretopology : Pretopology (Opens T)
    where
  coverings X R := ∀ x ∈ X, ∃ (U : _) (f : U ⟶ X), R f ∧ x ∈ U
  has_isos X Y f i x hx := ⟨_, _, Presieve.singleton_self _, (inv f).le hx⟩
  pullbacks X Y f S hS x hx := by
    rcases hS _ (f.le hx) with ⟨U, g, hg, hU⟩
    -- ⊢ ∃ U f_1, Presieve.pullbackArrows f S f_1 ∧ x ∈ U
    refine' ⟨_, _, Presieve.pullbackArrows.mk _ _ hg, _⟩
    -- ⊢ x ∈ pullback g f
    have : U ⊓ Y ≤ pullback g f
    -- ⊢ U ⊓ Y ≤ pullback g f
    refine' leOfHom (pullback.lift (homOfLE inf_le_left) (homOfLE inf_le_right) rfl)
    -- ⊢ x ∈ pullback g f
    apply this ⟨hU, hx⟩
    -- 🎉 no goals
  Transitive X S Ti hS hTi x hx := by
    rcases hS x hx with ⟨U, f, hf, hU⟩
    -- ⊢ ∃ U f, Presieve.bind S Ti f ∧ x ∈ U
    rcases hTi f hf x hU with ⟨V, g, hg, hV⟩
    -- ⊢ ∃ U f, Presieve.bind S Ti f ∧ x ∈ U
    exact ⟨_, _, ⟨_, g, f, hf, hg, rfl⟩, hV⟩
    -- 🎉 no goals
#align opens.pretopology Opens.pretopology

/-- The pretopology associated to a space is the largest pretopology that
    generates the Grothendieck topology associated to the space. -/
@[simp]
theorem pretopology_ofGrothendieck :
    Pretopology.ofGrothendieck _ (Opens.grothendieckTopology T) = Opens.pretopology T := by
  apply le_antisymm
  -- ⊢ Pretopology.ofGrothendieck (Opens T) (grothendieckTopology T) ≤ pretopology T
  · intro X R hR x hx
    -- ⊢ ∃ U f, R f ∧ x ∈ U
    rcases hR x hx with ⟨U, f, ⟨V, g₁, g₂, hg₂, _⟩, hU⟩
    -- ⊢ ∃ U f, R f ∧ x ∈ U
    exact ⟨V, g₂, hg₂, g₁.le hU⟩
    -- 🎉 no goals
  · intro X R hR x hx
    -- ⊢ ∃ U f, (Sieve.generate R).arrows f ∧ x ∈ U
    rcases hR x hx with ⟨U, f, hf, hU⟩
    -- ⊢ ∃ U f, (Sieve.generate R).arrows f ∧ x ∈ U
    exact ⟨U, f, Sieve.le_generate R U hf, hU⟩
    -- 🎉 no goals
#align opens.pretopology_of_grothendieck Opens.pretopology_ofGrothendieck

/-- The pretopology associated to a space induces the Grothendieck topology associated to the space.
-/
@[simp]
theorem pretopology_toGrothendieck :
    Pretopology.toGrothendieck _ (Opens.pretopology T) = Opens.grothendieckTopology T := by
  rw [← pretopology_ofGrothendieck]
  -- ⊢ Pretopology.toGrothendieck (Opens T) (Pretopology.ofGrothendieck (Opens T) ( …
  apply (Pretopology.gi (Opens T)).l_u_eq
  -- 🎉 no goals
#align opens.pretopology_to_grothendieck Opens.pretopology_toGrothendieck

end Opens
