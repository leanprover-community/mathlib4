/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
module

public import Mathlib.Topology.Separation.CompletelyRegular

import Mathlib.Topology.UniformSpace.OfCompactT2
import Mathlib.Topology.UrysohnsLemma

/-!
# Uniformizable Spaces

A topological space is uniformizable (there exists a uniformity that
generates the same topology) iff it is completely regular.

## Main Results

* `UniformSpace.toCompletelyRegularSpace`: Uniform spaces are completely regular
* `CompletelyRegularSpace.exists_uniformSpace`: Completely regular spaces are uniformizable
* `CompletelyRegularSpace.of_exists_uniformSpace`: Uniformizable spaces are completely regular
* `completelyRegularSpace_iff_exists_uniformSpace`: A space is completely regular
  iff it is uniformizable

## Implementation Details

Urysohn's lemma is reused in the proof of `UniformSpace.completelyRegularSpace`.

## References

* <https://www.math.wm.edu/~vinroot/PadicGroups/519probset1.pdf>
-/

variable {α : Type*}

open Filter Set Uniformity UniformSpace SetRel

section UniformSpace
variable [UniformSpace α]

/-- To construct a real-valued function separating a point `x` from a closed set in a uniform
space, we recursively construct pairs of a closed set `c` contained in an open set `u`
satisfying the following predicate: the closed set is the closure of the ball centered
at `x` associated to some open entourage `uc`, the open set is the ball centered at `x`
associated to some entourage `uu`, such that `uu` is a thickening of `uc` by some entourage `s`
in the sense that the composition `s ○ uc ○ s` is contained in `uu`. -/
def P (c u : Set α) :=
  ∃ (x : α) (uc uu s : SetRel α α),
    IsOpen uc ∧ uc ∈ 𝓤 α ∧ c = closure (ball x uc) ∧
    u = ball x uu ∧ s ○ uc ○ s ⊆ uu ∧ s ∈ 𝓤 α

/-- Given a pair consisting of a closed set `c` contained in an open set `u` satisfying the
predicate `P`, it is always possible to refine it to two pairs `c ⊆ v` and `closure v ⊆ u`
satisfying `P`. We can then use the general `Urysohns.CU` construction to obtain the
desired real-valued function. -/
theorem urysohns_main {c u : Set α} (Pcu : P c u) :
    ∃ (v : Set α), IsOpen v ∧ c ⊆ v ∧ closure v ⊆ u ∧ P c v ∧ P (closure v) u := by
  obtain ⟨x, uc, uu, s, huc, ucu, rfl, rfl, hn, hs⟩ := Pcu
  obtain ⟨(ds : SetRel α α), hdsu, hdso, -, hdsd⟩ := comp_open_symm_mem_uniformity_sets hs
  have ho : IsOpen (ds ○ uc ○ ds) := (hdso.relComp huc).relComp hdso
  have hsub := calc ds ○ (ds ○ uc ○ ds) ○ ds
    _ = (ds ○ ds) ○ uc ○ (ds ○ ds) := by simp [comp_assoc]
    _ ⊆ s ○ uc ○ s := comp_subset_comp (comp_subset_comp_left hdsd) hdsd
    _ ⊆ uu := hn
  have : ds.IsRefl := id_subset_iff.1 (refl_le_uniformity hdsu)
  refine ⟨ball x (ds ○ uc ○ ds), isOpen_ball x ho, ?_, subset_trans ?_ (ball_mono hsub x),
      ⟨x, uc, ds ○ uc ○ ds, ds, huc, ucu, rfl, rfl, le_rfl, hdsu⟩, x, ds ○ uc ○ ds, uu, ds, ho,
      mem_of_superset ucu (right_subset_comp.trans left_subset_comp), rfl, rfl, hsub, hdsu⟩ <;>
  · refine closure_ball_subset.trans (ball_mono ?_ x)
    rw [closure_eq_inter_uniformity]
    exact iInter₂_subset_of_subset ds hdsu (by simp [comp_assoc])

public instance UniformSpace.toCompletelyRegularSpace : CompletelyRegularSpace α where
  completely_regular x K hK hx :=
    have ⟨O, hOu, hOo, hbO⟩ := isOpen_iff_isOpen_ball_subset.mp hK.isOpen_compl x hx
    have ⟨(u3 : SetRel α α), hu3u, _, hu3O⟩ := comp_comp_symm_mem_uniformity_sets hOu
    have hu3O := ((comp_subset_comp_left (comp_subset_comp_right interior_subset))).trans hu3O
    let c : Urysohns.CU P := {
      C := closure (ball x (interior u3))
      U := ball x O
      closed_C := isClosed_closure
      open_U := isOpen_ball x hOo
      subset := closure_ball_subset.trans <| (ball_mono · x) <| by
        simp_rw [closure_eq_inter_uniformity, ← comp_assoc]
        exact (iInter₂_subset u3 hu3u).trans hu3O
      hP _ Pcu _ _ := urysohns_main Pcu
      P_C_U := ⟨x, interior u3, O, u3,
        isOpen_interior, interior_mem_uniformity hu3u, rfl, rfl, hu3O, hu3u⟩
    }
    ⟨fun x ↦ ⟨c.lim x, c.lim_mem_Icc x⟩, c.continuous_lim.subtype_mk c.lim_mem_Icc,
      Subtype.ext (c.lim_of_mem_C x <| subset_closure (refl_mem_uniformity <|
        interior_mem_uniformity hu3u)), fun y hy ↦ Subtype.ext (c.lim_of_notMem_U y (hbO · hy))⟩

end UniformSpace

section TopologicalSpace
variable [t : TopologicalSpace α]

public theorem CompletelyRegularSpace.of_exists_uniformSpace
    (h : ∃ u : UniformSpace α, u.toTopologicalSpace = t) :
    CompletelyRegularSpace α := by
  obtain ⟨u, rfl⟩ := h
  infer_instance

public theorem CompletelyRegularSpace.exists_uniformSpace [CompletelyRegularSpace α] :
    ∃ u : UniformSpace α, u.toTopologicalSpace = t :=
  ⟨uniformSpaceOfCompactR1.comap stoneCechUnit, isInducing_stoneCechUnit.eq_induced.symm⟩

public theorem completelyRegularSpace_iff_exists_uniformSpace :
    CompletelyRegularSpace α ↔ ∃ u : UniformSpace α, u.toTopologicalSpace = t :=
  ⟨(·.exists_uniformSpace), .of_exists_uniformSpace⟩

end TopologicalSpace
