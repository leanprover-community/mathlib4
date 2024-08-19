/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Order.RelIso.Set
import Mathlib.SetTheory.ZFC.Basic

/-!
# Von Neumann ordinals

This file works towards the development of von Neumann ordinals, i.e. transitive sets, well-ordered
under `∈`.

We currently only have an initial development of transitive sets and ordinals. Further development
can be found on the Mathlib 3 branch `von_neumann_v2`.

## Definitions

- `ZFSet.IsTransitive` means that every element of a set is a subset.
- `ZFSet.IsOrdinal` means that the set is transitive and well-ordered under `∈`.

## TODO

- Define von Neumann ordinals and the von Neumann hierarchy.
- Build correspondences between these notions and those of the standard `Ordinal` type.
-/


universe u

variable {x y z w : ZFSet.{u}}

namespace ZFSet


/-- A transitive set is one where every element is a subset. -/
def IsTransitive (x : ZFSet) : Prop :=
  ∀ y ∈ x, y ⊆ x

@[simp]
theorem empty_isTransitive : IsTransitive ∅ :=
  fun y hy => (not_mem_empty y hy).elim

theorem IsTransitive.subset_of_mem (h : x.IsTransitive) : y ∈ x → y ⊆ x :=
  h y

theorem isTransitive_iff_mem_trans : z.IsTransitive ↔ ∀ {x y : ZFSet}, x ∈ y → y ∈ z → x ∈ z := by
  constructor
  · intro h _ _ hx hy
    exact h.subset_of_mem hy hx
  · intro h _ hx _ hy
    exact h hy hx

alias ⟨IsTransitive.mem_trans, _⟩ := isTransitive_iff_mem_trans

protected theorem IsTransitive.inter (hx : x.IsTransitive) (hy : y.IsTransitive) :
    (x ∩ y).IsTransitive := by
  intro z hz w hw
  rw [mem_inter] at hz ⊢
  exact ⟨hx.mem_trans hw hz.1, hy.mem_trans hw hz.2⟩

protected theorem IsTransitive.sUnion (h : x.IsTransitive) :
    (⋃₀ x : ZFSet).IsTransitive := by
  intro y hy z hz
  rcases mem_sUnion.1 hy with ⟨w, hw, hw'⟩
  exact mem_sUnion_of_mem hz (h.mem_trans hw' hw)

theorem IsTransitive.sUnion' (H : ∀ y ∈ x, IsTransitive y) :
    (⋃₀ x : ZFSet).IsTransitive := by
  intro y hy z hz
  rcases mem_sUnion.1 hy with ⟨w, hw, hw'⟩
  exact mem_sUnion_of_mem ((H w hw).mem_trans hz hw') hw

protected theorem IsTransitive.union (hx : x.IsTransitive) (hy : y.IsTransitive) :
    (x ∪ y).IsTransitive := by
  rw [← sUnion_pair]
  apply IsTransitive.sUnion'
  intro
  rw [mem_pair]
  rintro (rfl | rfl)
  assumption'

protected theorem IsTransitive.powerset (h : x.IsTransitive) : (powerset x).IsTransitive := by
  intro y hy z hz
  rw [mem_powerset] at hy ⊢
  exact h.subset_of_mem (hy hz)

theorem isTransitive_iff_sUnion_subset : x.IsTransitive ↔ (⋃₀ x : ZFSet) ⊆ x := by
  constructor <;>
  intro h y hy
  · rcases mem_sUnion.1 hy with ⟨z, hz, hz'⟩
    exact h.mem_trans hz' hz
  · intro z hz
    exact h <| mem_sUnion_of_mem hz hy

alias ⟨IsTransitive.sUnion_subset, _⟩ := isTransitive_iff_sUnion_subset

theorem isTransitive_iff_subset_powerset : x.IsTransitive ↔ x ⊆ powerset x := by
  constructor <;>
  intro h y hy
  · exact mem_powerset.2 <| h.subset_of_mem hy
  · intro z hz
    exact mem_powerset.1 (h hy) hz

alias ⟨IsTransitive.subset_powerset, _⟩ := isTransitive_iff_subset_powerset

/-- A set `x` is a von Neumann ordinal when it's a transitive set, that's transitive under `∈`. We
will prove that this further implies that `x` is well-ordered under `∈`.

The transitivity condition is written in an even weaker form, where `a ∈ b` and `b ∈ c` imply
`a ∈ c` when only `c ∈ x` and not `a ∈ x` or `b ∈ x` are known a priori. -/
def IsOrdinal (x : ZFSet) : Prop :=
  x.IsTransitive ∧ ∀ a b c : ZFSet, a ∈ b → b ∈ c → c ∈ x → a ∈ c

namespace IsOrdinal

protected theorem isTransitive (h : x.IsOrdinal) : x.IsTransitive :=
  h.1

theorem subset_of_mem (h : x.IsOrdinal) : y ∈ x → y ⊆ x :=
  h.isTransitive.subset_of_mem

theorem mem_trans (h : z.IsOrdinal) : x ∈ y → y ∈ z → x ∈ z :=
  h.isTransitive.mem_trans

theorem mem_trans' (hx : x.IsOrdinal) : y ∈ z → z ∈ w → w ∈ x → y ∈ w :=
  hx.2 y z w

protected theorem isTrans (h : x.IsOrdinal) : IsTrans x.toSet (Subrel (· ∈ ·) _) :=
  ⟨fun _ _ c hab hbc => h.mem_trans' hab hbc c.2⟩

end IsOrdinal

/-- The simplified form of transitivity used within `IsOrdinal` yields an equivalent definition to
the standard one. -/
theorem isOrdinal_iff_isTrans :
    x.IsOrdinal ↔ x.IsTransitive ∧ IsTrans x.toSet (Subrel (· ∈ ·) _) := by
  constructor
  · intro h
    exact ⟨h.isTransitive, h.isTrans⟩
  · rintro ⟨h₁, ⟨h₂⟩⟩
    use h₁
    intro y z w hyz hzw hwx
    let hzx := h₁.mem_trans hzw hwx
    exact h₂ ⟨y, h₁.mem_trans hyz hzx⟩ ⟨z, hzx⟩ ⟨w, hwx⟩ hyz hzw

end ZFSet
