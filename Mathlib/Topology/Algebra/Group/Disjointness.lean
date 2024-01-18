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


variable {G : Type*} [Group G] {g h : G}

/--
A bundled pair `(fst, snd)` such that `fst`, `snd` and `⁅fst, ⁅snd, h⁆⁆` are elements
of the centralizer of `g` and `⁅fst, ⁅snd, h⁆⁆` is nontrivial.
-/
structure Rubin.AlgDisjointElem (g h : G) :=
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

def Rubin.AlgDisjointElem.comm_elem (elem : Rubin.AlgDisjointElem g h) : G :=
  ⁅elem.fst, ⁅elem.snd, h⁆⁆

theorem Rubin.AlgDisjointElem.comm_elem_commute (elem : Rubin.AlgDisjointElem g h) :
    Commute elem.comm_elem g := elem.comm_elem_commute'

theorem Rubin.AlgDisjointElem.comm_elem_nontrivial (elem : Rubin.AlgDisjointElem g h) :
    elem.comm_elem ≠ 1 := elem.comm_elem_nontrivial'

def Rubin.AlgDisjointElem.conj (elem : Rubin.AlgDisjointElem g h) (i : G) :
    Rubin.AlgDisjointElem (i * g * i⁻¹) (i * h * i⁻¹) where
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

def Rubin.IsAlgDisjoint (f g : G) : Prop := ∀ h : G, ¬Commute f h → ∃ elem: AlgDisjointElem g h, True
