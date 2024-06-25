/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Data.Set.Lattice

#align_import data.set.intervals.ord_connected_component from "leanprover-community/mathlib"@"92ca63f0fb391a9ca5f22d2409a6080e786d99f7"

/-!
# Order connected components of a set

In this file we define `Set.ordConnectedComponent s x` to be the set of `y` such that
`Set.uIcc x y ⊆ s` and prove some basic facts about this definition. At the moment of writing,
this construction is used only to prove that any linear order with order topology is a T₅ space,
so we only add API needed for this lemma.
-/


open Interval Function OrderDual

namespace Set

variable {α : Type*} [LinearOrder α] {s t : Set α} {x y z : α}

/-- Order-connected component of a point `x` in a set `s`. It is defined as the set of `y` such that
`Set.uIcc x y ⊆ s`. Note that it is empty if and only if `x ∉ s`. -/
def ordConnectedComponent (s : Set α) (x : α) : Set α :=
  { y | [[x, y]] ⊆ s }
#align set.ord_connected_component Set.ordConnectedComponent

theorem mem_ordConnectedComponent : y ∈ ordConnectedComponent s x ↔ [[x, y]] ⊆ s :=
  Iff.rfl
#align set.mem_ord_connected_component Set.mem_ordConnectedComponent

theorem dual_ordConnectedComponent :
    ordConnectedComponent (ofDual ⁻¹' s) (toDual x) = ofDual ⁻¹' ordConnectedComponent s x :=
  ext <| (Surjective.forall toDual.surjective).2 fun x => by
    rw [mem_ordConnectedComponent, dual_uIcc]
    rfl
#align set.dual_ord_connected_component Set.dual_ordConnectedComponent

theorem ordConnectedComponent_subset : ordConnectedComponent s x ⊆ s := fun _ hy =>
  hy right_mem_uIcc
#align set.ord_connected_component_subset Set.ordConnectedComponent_subset

theorem subset_ordConnectedComponent {t} [h : OrdConnected s] (hs : x ∈ s) (ht : s ⊆ t) :
    s ⊆ ordConnectedComponent t x := fun _ hy => (h.uIcc_subset hs hy).trans ht
#align set.subset_ord_connected_component Set.subset_ordConnectedComponent

@[simp]
theorem self_mem_ordConnectedComponent : x ∈ ordConnectedComponent s x ↔ x ∈ s := by
  rw [mem_ordConnectedComponent, uIcc_self, singleton_subset_iff]
#align set.self_mem_ord_connected_component Set.self_mem_ordConnectedComponent

@[simp]
theorem nonempty_ordConnectedComponent : (ordConnectedComponent s x).Nonempty ↔ x ∈ s :=
  ⟨fun ⟨_, hy⟩ => hy <| left_mem_uIcc, fun h => ⟨x, self_mem_ordConnectedComponent.2 h⟩⟩
#align set.nonempty_ord_connected_component Set.nonempty_ordConnectedComponent

@[simp]
theorem ordConnectedComponent_eq_empty : ordConnectedComponent s x = ∅ ↔ x ∉ s := by
  rw [← not_nonempty_iff_eq_empty, nonempty_ordConnectedComponent]
#align set.ord_connected_component_eq_empty Set.ordConnectedComponent_eq_empty

@[simp]
theorem ordConnectedComponent_empty : ordConnectedComponent ∅ x = ∅ :=
  ordConnectedComponent_eq_empty.2 (not_mem_empty x)
#align set.ord_connected_component_empty Set.ordConnectedComponent_empty

@[simp]
theorem ordConnectedComponent_univ : ordConnectedComponent univ x = univ := by
  simp [ordConnectedComponent]
#align set.ord_connected_component_univ Set.ordConnectedComponent_univ

theorem ordConnectedComponent_inter (s t : Set α) (x : α) :
    ordConnectedComponent (s ∩ t) x = ordConnectedComponent s x ∩ ordConnectedComponent t x := by
  simp [ordConnectedComponent, setOf_and]
#align set.ord_connected_component_inter Set.ordConnectedComponent_inter

theorem mem_ordConnectedComponent_comm :
    y ∈ ordConnectedComponent s x ↔ x ∈ ordConnectedComponent s y := by
  rw [mem_ordConnectedComponent, mem_ordConnectedComponent, uIcc_comm]
#align set.mem_ord_connected_component_comm Set.mem_ordConnectedComponent_comm

theorem mem_ordConnectedComponent_trans (hxy : y ∈ ordConnectedComponent s x)
    (hyz : z ∈ ordConnectedComponent s y) : z ∈ ordConnectedComponent s x :=
  calc
    [[x, z]] ⊆ [[x, y]] ∪ [[y, z]] := uIcc_subset_uIcc_union_uIcc
    _ ⊆ s := union_subset hxy hyz
#align set.mem_ord_connected_component_trans Set.mem_ordConnectedComponent_trans

theorem ordConnectedComponent_eq (h : [[x, y]] ⊆ s) :
    ordConnectedComponent s x = ordConnectedComponent s y :=
  ext fun _ =>
    ⟨mem_ordConnectedComponent_trans (mem_ordConnectedComponent_comm.2 h),
      mem_ordConnectedComponent_trans h⟩
#align set.ord_connected_component_eq Set.ordConnectedComponent_eq

instance : OrdConnected (ordConnectedComponent s x) :=
  ordConnected_of_uIcc_subset_left fun _ hy _ hz => (uIcc_subset_uIcc_left hz).trans hy

/-- Projection from `s : Set α` to `α` sending each order connected component of `s` to a single
point of this component. -/
noncomputable def ordConnectedProj (s : Set α) : s → α := fun x : s =>
  (nonempty_ordConnectedComponent.2 x.2).some
#align set.ord_connected_proj Set.ordConnectedProj

theorem ordConnectedProj_mem_ordConnectedComponent (s : Set α) (x : s) :
    ordConnectedProj s x ∈ ordConnectedComponent s x :=
  Nonempty.some_mem _
#align set.ord_connected_proj_mem_ord_connected_component Set.ordConnectedProj_mem_ordConnectedComponent

theorem mem_ordConnectedComponent_ordConnectedProj (s : Set α) (x : s) :
    ↑x ∈ ordConnectedComponent s (ordConnectedProj s x) :=
  mem_ordConnectedComponent_comm.2 <| ordConnectedProj_mem_ordConnectedComponent s x
#align set.mem_ord_connected_component_ord_connected_proj Set.mem_ordConnectedComponent_ordConnectedProj

@[simp]
theorem ordConnectedComponent_ordConnectedProj (s : Set α) (x : s) :
    ordConnectedComponent s (ordConnectedProj s x) = ordConnectedComponent s x :=
  ordConnectedComponent_eq <| mem_ordConnectedComponent_ordConnectedProj _ _
#align set.ord_connected_component_ord_connected_proj Set.ordConnectedComponent_ordConnectedProj

@[simp]
theorem ordConnectedProj_eq {x y : s} :
    ordConnectedProj s x = ordConnectedProj s y ↔ [[(x : α), y]] ⊆ s := by
  constructor <;> intro h
  · rw [← mem_ordConnectedComponent, ← ordConnectedComponent_ordConnectedProj, h,
      ordConnectedComponent_ordConnectedProj, self_mem_ordConnectedComponent]
    exact y.2
  · simp only [ordConnectedProj, ordConnectedComponent_eq h]
#align set.ord_connected_proj_eq Set.ordConnectedProj_eq

/-- A set that intersects each order connected component of a set by a single point. Defined as the
range of `Set.ordConnectedProj s`. -/
def ordConnectedSection (s : Set α) : Set α :=
  range <| ordConnectedProj s
#align set.ord_connected_section Set.ordConnectedSection

theorem dual_ordConnectedSection (s : Set α) :
    ordConnectedSection (ofDual ⁻¹' s) = ofDual ⁻¹' ordConnectedSection s := by
  simp only [ordConnectedSection]
  simp (config := { unfoldPartialApp := true }) only [ordConnectedProj]
  ext x
  simp only [mem_range, Subtype.exists, mem_preimage, OrderDual.exists, dual_ordConnectedComponent,
    ofDual_toDual]
  tauto
#align set.dual_ord_connected_section Set.dual_ordConnectedSection

theorem ordConnectedSection_subset : ordConnectedSection s ⊆ s :=
  range_subset_iff.2 fun _ => ordConnectedComponent_subset <| Nonempty.some_mem _
#align set.ord_connected_section_subset Set.ordConnectedSection_subset

theorem eq_of_mem_ordConnectedSection_of_uIcc_subset (hx : x ∈ ordConnectedSection s)
    (hy : y ∈ ordConnectedSection s) (h : [[x, y]] ⊆ s) : x = y := by
  rcases hx with ⟨x, rfl⟩; rcases hy with ⟨y, rfl⟩
  exact
    ordConnectedProj_eq.2
      (mem_ordConnectedComponent_trans
        (mem_ordConnectedComponent_trans (ordConnectedProj_mem_ordConnectedComponent _ _) h)
        (mem_ordConnectedComponent_ordConnectedProj _ _))
#align set.eq_of_mem_ord_connected_section_of_uIcc_subset Set.eq_of_mem_ordConnectedSection_of_uIcc_subset

/-- Given two sets `s t : Set α`, the set `Set.orderSeparatingSet s t` is the set of points that
belong both to some `Set.ordConnectedComponent tᶜ x`, `x ∈ s`, and to some
`Set.ordConnectedComponent sᶜ x`, `x ∈ t`. In the case of two disjoint closed sets, this is the
union of all open intervals $(a, b)$ such that their endpoints belong to different sets. -/
def ordSeparatingSet (s t : Set α) : Set α :=
  (⋃ x ∈ s, ordConnectedComponent tᶜ x) ∩ ⋃ x ∈ t, ordConnectedComponent sᶜ x
#align set.ord_separating_set Set.ordSeparatingSet

theorem ordSeparatingSet_comm (s t : Set α) : ordSeparatingSet s t = ordSeparatingSet t s :=
  inter_comm _ _
#align set.ord_separating_set_comm Set.ordSeparatingSet_comm

theorem disjoint_left_ordSeparatingSet : Disjoint s (ordSeparatingSet s t) :=
  Disjoint.inter_right' _ <|
    disjoint_iUnion₂_right.2 fun _ _ =>
      disjoint_compl_right.mono_right <| ordConnectedComponent_subset
#align set.disjoint_left_ord_separating_set Set.disjoint_left_ordSeparatingSet

theorem disjoint_right_ordSeparatingSet : Disjoint t (ordSeparatingSet s t) :=
  ordSeparatingSet_comm t s ▸ disjoint_left_ordSeparatingSet
#align set.disjoint_right_ord_separating_set Set.disjoint_right_ordSeparatingSet

theorem dual_ordSeparatingSet :
    ordSeparatingSet (ofDual ⁻¹' s) (ofDual ⁻¹' t) = ofDual ⁻¹' ordSeparatingSet s t := by
  simp only [ordSeparatingSet, mem_preimage, ← toDual.surjective.iUnion_comp, ofDual_toDual,
    dual_ordConnectedComponent, ← preimage_compl, preimage_inter, preimage_iUnion]
#align set.dual_ord_separating_set Set.dual_ordSeparatingSet

/-- An auxiliary neighborhood that will be used in the proof of
    `OrderTopology.CompletelyNormalSpace`. -/
def ordT5Nhd (s t : Set α) : Set α :=
  ⋃ x ∈ s, ordConnectedComponent (tᶜ ∩ (ordConnectedSection <| ordSeparatingSet s t)ᶜ) x
#align set.ord_t5_nhd Set.ordT5Nhd

theorem disjoint_ordT5Nhd : Disjoint (ordT5Nhd s t) (ordT5Nhd t s) := by
  rw [disjoint_iff_inf_le]
  rintro x ⟨hx₁, hx₂⟩
  rcases mem_iUnion₂.1 hx₁ with ⟨a, has, ha⟩
  clear hx₁
  rcases mem_iUnion₂.1 hx₂ with ⟨b, hbt, hb⟩
  clear hx₂
  rw [mem_ordConnectedComponent, subset_inter_iff] at ha hb
  wlog hab : a ≤ b with H
  · exact H (x := x) (y := y) (z := z) b hbt hb a has ha (le_of_not_le hab)
  cases' ha with ha ha'
  cases' hb with hb hb'
  have hsub : [[a, b]] ⊆ (ordSeparatingSet s t).ordConnectedSectionᶜ := by
    rw [ordSeparatingSet_comm, uIcc_comm] at hb'
    calc
      [[a, b]] ⊆ [[a, x]] ∪ [[x, b]] := uIcc_subset_uIcc_union_uIcc
      _ ⊆ (ordSeparatingSet s t).ordConnectedSectionᶜ := union_subset ha' hb'
  clear ha' hb'
  rcases le_total x a with hxa | hax
  · exact hb (Icc_subset_uIcc' ⟨hxa, hab⟩) has
  rcases le_total b x with hbx | hxb
  · exact ha (Icc_subset_uIcc ⟨hab, hbx⟩) hbt
  have h' : x ∈ ordSeparatingSet s t := ⟨mem_iUnion₂.2 ⟨a, has, ha⟩, mem_iUnion₂.2 ⟨b, hbt, hb⟩⟩
  lift x to ordSeparatingSet s t using h'
  suffices ordConnectedComponent (ordSeparatingSet s t) x ⊆ [[a, b]] from
    hsub (this <| ordConnectedProj_mem_ordConnectedComponent _ x) (mem_range_self _)
  rintro y hy
  rw [uIcc_of_le hab, mem_Icc, ← not_lt, ← not_lt]
  have sol1 := fun (hya : y < a) =>
      (disjoint_left (t := ordSeparatingSet s t)).1 disjoint_left_ordSeparatingSet has
        (hy <| Icc_subset_uIcc' ⟨hya.le, hax⟩)
  have sol2 := fun (hby : b < y) =>
      (disjoint_left (t := ordSeparatingSet s t)).1 disjoint_right_ordSeparatingSet hbt
        (hy <| Icc_subset_uIcc ⟨hxb, hby.le⟩)
  exact ⟨sol1, sol2⟩
#align set.disjoint_ord_t5_nhd Set.disjoint_ordT5Nhd
