/-
Copyright (c) 2024 Emilie Burgun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emilie Burgun
-/

import Mathlib.Topology.Basic
import Mathlib.GroupTheory.Commutator

/-!
# Group-theoretical condition for the disjointness of `(fixedBy α g)ᶜ` sets

This module describes a somewhat mysterious condition for two group elements to have disjoint
`(fixedBy α g)ᶜ` sets, assuming the group action is locally dense.

TODO: link to locally dense

This is a key construction in the proof of Rubin's theorem, as the `(fixedBy α g)ᶜ` sets can be used
to describe a topological basis of the acted-upon topological space.
-/

namespace Rubin

variable {G : Type*} [Group G] {g h : G}
variable {α : Type*} [TopologicalSpace α]

/--
A bundled pair `(fst, snd)` such that `fst`, `snd` and `⁅fst, ⁅snd, h⁆⁆` are elements
of the centralizer of `g` and `⁅fst, ⁅snd, h⁆⁆` is nontrivial.
-/
structure AlgDisjointElem (g h : G) :=
  /-- The first element of the pair -/
  fst : G
  /-- The second element of the pair -/
  snd : G
  /-- `fst` must be an element of the centralizer of `g` -/
  fst_comm : Commute fst g
  /-- `snd` must be an element of the centralizer of `g` -/
  snd_comm : Commute snd g
  /-- `comm_elem` must be an element of the centralizer of `g` -/
  comm_elem_commute' : Commute ⁅fst, ⁅snd, h⁆⁆ g
  /-- `comm_elem` must not be trivial -/
  comm_elem_nontrivial' : ⁅fst, ⁅snd, h⁆⁆ ≠ 1

def AlgDisjointElem.comm_elem (elem : AlgDisjointElem g h) : G :=
  ⁅elem.fst, ⁅elem.snd, h⁆⁆

theorem AlgDisjointElem.comm_elem_commute (elem : AlgDisjointElem g h) :
    Commute elem.comm_elem g := elem.comm_elem_commute'

theorem AlgDisjointElem.comm_elem_nontrivial (elem : AlgDisjointElem g h) :
    elem.comm_elem ≠ 1 := elem.comm_elem_nontrivial'

def AlgDisjointElem.conj (elem : AlgDisjointElem g h) (i : G) :
    AlgDisjointElem (i * g * i⁻¹) (i * h * i⁻¹) where
  fst := i * elem.fst * i⁻¹
  snd := i * elem.snd * i⁻¹
  fst_comm := by
    rw [Commute.conj_iff]
    exact elem.fst_comm
  snd_comm := by
    rw [Commute.conj_iff]
    exact elem.snd_comm
  comm_elem_commute' := by
    rw [← conjugate_commutatorElement, ← conjugate_commutatorElement, Commute.conj_iff]
    exact elem.comm_elem_commute'
  comm_elem_nontrivial' := by
    rw [← conjugate_commutatorElement, ← conjugate_commutatorElement, ne_eq, conj_eq_one_iff]
    exact elem.comm_elem_nontrivial'

/--
`f` is said to be algebraically disjoint with `g` if for all element `h` that doesn't commute with `f`,
one can construct `AlgDisjointElem g h`.
-/
def IsAlgDisjoint (f g : G) : Prop := ∀ h : G, ¬Commute f h → Nonempty (AlgDisjointElem g h)

theorem IsAlgDisjoint.conj {f g : G} (disj : IsAlgDisjoint f g) (h : G) :
    IsAlgDisjoint (h * f * h⁻¹) (h * g * h⁻¹) := by
  intro i nc
  rw [← Commute.conj_iff h⁻¹] at nc
  group at nc
  refine (disj _ nc).elim (fun elem => ⟨?elem⟩)
  have res := elem.conj h
  group at res
  rwa [zpow_neg_one] at res

-- lemma IsAlgDisjoint.of_disjoint_movedBy [h_lm : LocallyMoving G α] [T2Space α] {f g : G}
--     (disj : Disjoint (fixedBy α f)ᶜ (fixedBy α g)ᶜ) : IsAlgDisjoint f g := by
--   refine ⟨fun i nc => ⟨?elem⟩⟩


/--
The algebraic centralizer of `g` contains all the elements `h` that commute with `f^12`,
such that `f` is some group element that is algebraically disjoint with `g`.

If the group action is locally moving and faithful on a topological space,
then `algCentralizer g = fixingSubgroup (interior (closure (fixedBy α g)))`.
-/
def algCentralizer (g : G) : Subgroup G :=
  Subgroup.centralizer { f^12 | (f : G) (_: IsAlgDisjoint f g) }

end Rubin
