/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
import Mathlib.Order.Filter.Basic
import Mathlib.Order.PFilter

/-!
# Filters and Ideals

This file sets up the complement equivalence between filters and ideals on a type.

## Main definitions

* `Filter.complIdeal`
* `Order.Ideal.complFilter`
* `Filter.complIdealIso`

## Tags

filter, ideal
-/

variable {α : Type*}

section

open Order OrderDual Set

/--
The complement of a filter, as an order ideal of sets.
-/
def Filter.toPFilter (f : Filter α) : PFilter (Set α) where
  dual := {
    carrier := ofDual ⁻¹' f.sets
    lower' a b hab ha := f.mem_of_superset ha (monotone_id.dual_left hab)
    nonempty' := ⟨toDual univ, by simp⟩
    directed' a ha b hb :=
      ⟨toDual (ofDual a ∩ ofDual b), by simp_all, inter_subset_left, inter_subset_right⟩
  }

@[simp]
theorem Filter.mem_complIdeal (f : Filter α) (s : Set α) :
    s ∈ f.toPFilter ↔ s ∈ f := Iff.rfl

/--
The complement of an order ideal of sets, as a filter.
-/
def Order.PFilter.toFilter (i : PFilter (Set α)) : Filter α where
  sets := i
  univ_sets := by simpa using i.top_mem
  sets_of_superset hx hxy := i.mem_of_le (monotone_id.dual_left hxy) hx
  inter_sets hx hy := by simpa [compl_inter] using i.inf_mem hx hy

@[simp]
theorem Order.PFilter.mem_complFilter (i : PFilter (Set α)) (s : Set α) :
    s ∈ i.toFilter ↔ s ∈ i := Iff.rfl

@[simp]
theorem Filter.complFilter_complIdeal (f : Filter α) : f.toPFilter.toFilter = f := by
  ext; simp
@[simp]
theorem Order.Ideal.complFilter_complIdeal (i : PFilter (Set α)) : i.toFilter.toPFilter = i := by
  ext; simp

theorem Filter.toPFilter_anti : Antitone (@Filter.toPFilter α) :=
  fun _ _ hab _ hb ↦ hab hb
theorem Order.PFilter.toFilter_anti : Antitone (@Order.PFilter.toFilter α) :=
  fun _ _ hab _ hb ↦ hab hb

/--
Filters and ideals are complement to each other.
-/
@[simps! apply symm_apply]
def Filter.complIdealIso : Filter α ≃o (PFilter (Set α))ᵒᵈ :=
  OrderIso.ofHomInv
    (OrderHom.mk _ Filter.toPFilter_anti.dual_right)
    (OrderHom.mk _ PFilter.toFilter_anti.dual_left)
    (by ext; simp) (by ext; simp)

end
