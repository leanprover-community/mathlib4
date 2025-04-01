/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Ideal

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
def Filter.complIdeal (f : Filter α) : Ideal (Set α) where
  carrier := compl ⁻¹' f.sets
  lower' a b hab ha := f.mem_of_superset ha (compl_anti hab)
  nonempty' := ⟨∅, by simp⟩
  directed' a ha b hb := ⟨a ∪ b, by simp_all, subset_union_left, subset_union_right⟩

@[simp]
theorem Filter.mem_complIdeal (f : Filter α) (s : Set α) :
    s ∈ f.complIdeal ↔ sᶜ ∈ f := Iff.rfl

/--
The complement of an order ideal of sets, as a filter.
-/
def Order.Ideal.complFilter (i : Ideal (Set α)) : Filter α where
  sets := compl ⁻¹' i
  univ_sets := by simpa using i.bot_mem
  sets_of_superset hx hxy := i.lower (compl_anti hxy) hx
  inter_sets hx hy := by simpa [compl_inter] using i.sup_mem hx hy

@[simp]
theorem Order.Ideal.mem_complFilter (i : Ideal (Set α)) (s : Set α) :
    s ∈ i.complFilter ↔ sᶜ ∈ i := Iff.rfl

@[simp]
theorem Filter.complFilter_complIdeal (f : Filter α) : f.complIdeal.complFilter = f := by
  ext; simp
@[simp]
theorem Order.Ideal.complFilter_complIdeal (i : Ideal (Set α)) : i.complFilter.complIdeal = i := by
  ext; simp

theorem Filter.complIdeal_anti : Antitone (@Filter.complIdeal α) :=
  fun _ _ hab _ hb ↦ hab hb
theorem Order.Ideal.complFilter_anti : Antitone (@Ideal.complFilter α) :=
  fun _ _ hab _ hb ↦ hab hb

/--
Filters and ideals are complement to each other.
-/
@[simps! apply symm_apply]
def Filter.complIdealIso : Filter α ≃o (Ideal (Set α))ᵒᵈ :=
  OrderIso.ofHomInv
    (OrderHom.mk _ Filter.complIdeal_anti.dual_right)
    (OrderHom.mk _ Ideal.complFilter_anti.dual_left)
    (by ext; simp) (by ext; simp)

end
