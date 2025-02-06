/-
Copyright (c) 2025 Pim Otte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pim Otte
-/

import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Data.Set.Card

/-!
# Representation of components by a set of vertices

## Main definition

* `SimpleGraph.ConnectedComponent.Represents` says that a set of vertices represents a set of components if it contains exactly
  one vertex from each component.
-/

universe u

variable {V : Type u}
variable {G : SimpleGraph V}

namespace SimpleGraph

namespace ConnectedComponent

/-- A set of vertices represents a set of components if it contains exactly one vertex from
each component. -/
def Represents (s : Set V) (C : Set G.ConnectedComponent) : Prop :=
    Set.BijOn G.connectedComponentMk s C

lemma out_image_represents {G : SimpleGraph V} (C : Set G.ConnectedComponent) :
    Represents (Quot.out '' C) C :=
  Set.BijOn.mk (by rintro c ⟨x, ⟨hx, rfl⟩⟩; simp_all [connectedComponentMk]) (by
    rintro x ⟨c, ⟨hc, rfl⟩⟩ y ⟨d, ⟨hd, rfl⟩⟩ hxy
    simp only [connectedComponentMk] at hxy
    aesop) (fun _ _ ↦ by simpa [connectedComponentMk])

namespace Represents

variable {C : Set G.ConnectedComponent} {s : Set V} {c : G.ConnectedComponent}

lemma existsUnique_rep (hrep : Represents s C) (h : c ∈ C) : ∃! x, x ∈ s ∩ c.supp := by
  obtain ⟨x, ⟨hx, rfl⟩⟩ := hrep.2.2 h
  use x
  simp only [Set.mem_inter_iff, hx, SetLike.mem_coe, mem_supp_iff, and_self, and_imp, true_and]
  exact fun y hy hyx ↦ hrep.2.1 hy hx hyx

lemma disjoint_supp_of_not_mem (hrep : Represents s C) (h : c ∉ C) : Disjoint s c.supp := by
  rw [Set.disjoint_left]
  intro a ha hc
  simp only [mem_supp_iff] at hc
  subst hc
  exact h (hrep.1 ha)

lemma ncard_inter (hrep : Represents s C) (h : c ∈ C) : (s ∩ c.supp).ncard = 1 := by
  rw [Set.ncard_eq_one]
  obtain ⟨a, ha⟩ := hrep.unique_rep h
  aesop

lemma ncard_sdiff_of_mem [Fintype V] (hrep : Represents s C) (h : c ∈ C) :
    (c.supp \ s).ncard = c.supp.ncard - 1 := by
  simp [← Set.ncard_inter_add_ncard_diff_eq_ncard c.supp s (Set.toFinite _), Set.inter_comm,
    ncard_inter hrep h]

lemma ncard_sdiff_of_not_mem [Fintype V] (hrep : Represents s C) (h : c ∉ C) :
    (c.supp \ s).ncard = c.supp.ncard := by
  simp [← Set.ncard_inter_add_ncard_diff_eq_ncard c.supp s (Set.toFinite _), Set.inter_comm,
    Set.disjoint_iff_inter_eq_empty.mp (hrep.exact h)]

end Represents

end ConnectedComponent

end SimpleGraph
