/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.SetTheory.ZFC.Basic

#align_import set_theory.zfc.ordinal from "leanprover-community/mathlib"@"98bbc3526516bca903bff09ea10c4206bf079e6b"

/-!
# Von Neumann ordinals

This file works towards the development of von Neumann ordinals, i.e. transitive sets, well-ordered
under `∈`. We currently only have an initial development of transitive sets.

Further development can be found on the branch `von_neumann_v2`.

## Definitions

- `ZFSet.IsTransitive` means that every element of a set is a subset.

## Todo

- Define von Neumann ordinals.
- Define the basic arithmetic operations on ordinals from a purely set-theoretic perspective.
- Prove the equivalences between these definitions and those provided in
  `SetTheory/Ordinal/Arithmetic.lean`.
-/


universe u

variable {x y z : ZFSet.{u}}

namespace ZFSet

set_option linter.uppercaseLean3 false

/-- A transitive set is one where every element is a subset. -/
def IsTransitive (x : ZFSet) : Prop :=
  ∀ y ∈ x, y ⊆ x
#align Set.is_transitive ZFSet.IsTransitive

@[simp]
theorem empty_isTransitive : IsTransitive ∅ := fun y hy => (not_mem_empty y hy).elim
#align Set.empty_is_transitive ZFSet.empty_isTransitive

theorem IsTransitive.subset_of_mem (h : x.IsTransitive) : y ∈ x → y ⊆ x :=
  h y
#align Set.is_transitive.subset_of_mem ZFSet.IsTransitive.subset_of_mem

theorem isTransitive_iff_mem_trans : z.IsTransitive ↔ ∀ {x y : ZFSet}, x ∈ y → y ∈ z → x ∈ z :=
  ⟨fun h _ _ hx hy => h.subset_of_mem hy hx, fun H _ hx _ hy => H hy hx⟩
#align Set.is_transitive_iff_mem_trans ZFSet.isTransitive_iff_mem_trans

alias ⟨IsTransitive.mem_trans, _⟩ := isTransitive_iff_mem_trans
#align Set.is_transitive.mem_trans ZFSet.IsTransitive.mem_trans

protected theorem IsTransitive.inter (hx : x.IsTransitive) (hy : y.IsTransitive) :
    (x ∩ y).IsTransitive := fun z hz w hw => by
  rw [mem_inter] at hz ⊢
  exact ⟨hx.mem_trans hw hz.1, hy.mem_trans hw hz.2⟩
#align Set.is_transitive.inter ZFSet.IsTransitive.inter

protected theorem IsTransitive.sUnion (h : x.IsTransitive) :
    (⋃₀ x : ZFSet).IsTransitive := fun y hy z hz => by
  rcases mem_sUnion.1 hy with ⟨w, hw, hw'⟩
  exact mem_sUnion_of_mem hz (h.mem_trans hw' hw)
#align Set.is_transitive.sUnion ZFSet.IsTransitive.sUnion

theorem IsTransitive.sUnion' (H : ∀ y ∈ x, IsTransitive y) :
    (⋃₀ x : ZFSet).IsTransitive := fun y hy z hz => by
  rcases mem_sUnion.1 hy with ⟨w, hw, hw'⟩
  exact mem_sUnion_of_mem ((H w hw).mem_trans hz hw') hw
#align Set.is_transitive.sUnion' ZFSet.IsTransitive.sUnion'

protected theorem IsTransitive.union (hx : x.IsTransitive) (hy : y.IsTransitive) :
    (x ∪ y).IsTransitive := by
  rw [← sUnion_pair]
  apply IsTransitive.sUnion' fun z => _
  intro
  rw [mem_pair]
  rintro (rfl | rfl)
  assumption'
#align Set.is_transitive.union ZFSet.IsTransitive.union

protected theorem IsTransitive.powerset (h : x.IsTransitive) : (powerset x).IsTransitive :=
  fun y hy z hz => by
  rw [mem_powerset] at hy ⊢
  exact h.subset_of_mem (hy hz)
#align Set.is_transitive.powerset ZFSet.IsTransitive.powerset

theorem isTransitive_iff_sUnion_subset : x.IsTransitive ↔ (⋃₀ x : ZFSet) ⊆ x :=
  ⟨fun h y hy => by
    rcases mem_sUnion.1 hy with ⟨z, hz, hz'⟩
    exact h.mem_trans hz' hz, fun H y hy z hz => H <| mem_sUnion_of_mem hz hy⟩
#align Set.is_transitive_iff_sUnion_subset ZFSet.isTransitive_iff_sUnion_subset

alias ⟨IsTransitive.sUnion_subset, _⟩ := isTransitive_iff_sUnion_subset
#align Set.is_transitive.sUnion_subset ZFSet.IsTransitive.sUnion_subset

theorem isTransitive_iff_subset_powerset : x.IsTransitive ↔ x ⊆ powerset x :=
  ⟨fun h _ hy => mem_powerset.2 <| h.subset_of_mem hy, fun H _ hy _ hz => mem_powerset.1 (H hy) hz⟩
#align Set.is_transitive_iff_subset_powerset ZFSet.isTransitive_iff_subset_powerset

alias ⟨IsTransitive.subset_powerset, _⟩ := isTransitive_iff_subset_powerset
#align Set.is_transitive.subset_powerset ZFSet.IsTransitive.subset_powerset

end ZFSet
