/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
module

public import Mathlib.Topology.Separation.CompletelyRegular

import Mathlib.Topology.UniformSpace.OfCompactT2

/-!
# Uniformizable Spaces

A topological space is uniformizable (there exists a uniformity that
generates the same topology) iff it is completely regular.

TODO: Explain proofs

## Main Results

* `UniformSpace.completelyRegularSpace`: Uniform spaces are completely regular
* `CompletelyRegularSpace.exists_uniformSpace`: Completely regular spaces are uniformizable
* `CompletelyRegularSpace.of_exists_uniformSpace`: Uniformizable spaces are completely regular
* `completelyRegularSpace_iff_exists_uniformSpace`: A space is completely regular
  iff it is uniformizable

## Implementation Details

Urysohn's lemma is reused in the proof of `UniformSpace.completelyRegularSpace`.

## References

* <https://www.math.wm.edu/~vinroot/PadicGroups/519probset1.pdf>
* [S. Willard, *General Topology*][zbMATH02107988]
-/

variable {α : Type*}

open Filter Set Uniformity SetRel

section UniformSpace
variable [UniformSpace α]

noncomputable def descend (s : { s : SetRel α α // s ∈ 𝓤 α }) :
    { s : SetRel α α // s ∈ 𝓤 α } :=
  ⟨_, (comp_open_symm_mem_uniformity_sets (mem_uniformity_isClosed
    (comp_open_symm_mem_uniformity_sets s.2).choose_spec.1).choose_spec.1).choose_spec.1⟩

theorem descend_open (s : { s : SetRel α α // s ∈ 𝓤 α }) :
    IsOpen (descend s).1 :=
  (comp_open_symm_mem_uniformity_sets (mem_uniformity_isClosed
    (comp_open_symm_mem_uniformity_sets s.2).choose_spec.1).choose_spec.1).choose_spec.2.1

theorem descend_symm (s : { s : SetRel α α // s ∈ 𝓤 α }) :
    (descend s).1.IsSymm :=
  (comp_open_symm_mem_uniformity_sets (mem_uniformity_isClosed
    (comp_open_symm_mem_uniformity_sets s.2).choose_spec.1).choose_spec.1).choose_spec.2.2.1

theorem descend_descends (s : { s : SetRel α α // s ∈ 𝓤 α }) :
    (descend s).1 ○ (descend s).1 ⊆ s := by
  dsimp [descend]
  generalize_proofs o₁ c o₂
  have hoc : o₂.choose ⊆ c.choose := by
    trans o₂.choose ○ o₂.choose
    · suffices _ : o₂.choose.IsRefl from left_subset_comp
      rw [← id_subset_iff]
      exact refl_le_uniformity o₂.choose_spec.1
    · exact o₂.choose_spec.2.2.2
  calc o₂.choose ○ o₂.choose
    _ ⊆ c.choose ○ c.choose := comp_subset_comp hoc hoc
    _ ⊆ o₁.choose ○ o₁.choose := comp_subset_comp c.choose_spec.2.2 c.choose_spec.2.2
    _ ⊆ s.1 := o₁.choose_spec.2.2.2

def P (c : Set α) (u : Set α) :=
  ∃ (x : α) (uc uu : SetRel α α) (s : { s : SetRel α α // s ∈ 𝓤 α }),
    IsOpen uc ∧ uc.IsSymm ∧ uc ∈ 𝓤 α ∧ c = closure (Prod.mk x ⁻¹' uc) ∧
    IsOpen uu ∧ u = Prod.mk x ⁻¹' uu ∧ s ○ uc ○ s ⊆ uu

theorem descend_spec {c u : Set α} (Pcu : P c u) :
    ∃ (v : Set α), IsOpen v ∧ c ⊆ v ∧ closure v ⊆ u ∧ P c v ∧ P (closure v) u := by
  obtain ⟨x, uc, uu, s, huc, symmuc, ucu, rfl, huu, rfl, hn⟩ := Pcu
  have ho : IsOpen ((descend s).1 ○ uc ○ (descend s).1) :=
    ((descend_open s).relComp huc).relComp (descend_open s)
  use Prod.mk x ⁻¹' (descend s ○ uc ○ descend s), ho.preimage (Continuous.prodMk_right x)
  constructor
  · apply ((Continuous.prodMk_right x).closure_preimage_subset _).trans
    apply Set.preimage_mono
    rw [closure_eq_inter_uniformity, comp_assoc]
    exact iInter₂_subset (descend s).1 (descend s).2
  constructor
  · apply ((Continuous.prodMk_right x).closure_preimage_subset _).trans
    apply Set.preimage_mono
    apply hn.trans'
    rw [closure_eq_inter_uniformity]
    apply iInter₂_subset_of_subset (descend s).1 (descend s).2
    exact Eq.trans_subset (by simp_rw [comp_assoc])
      (comp_subset_comp (comp_subset_comp (descend_descends s) subset_rfl) (descend_descends s))
  have : (descend s).1.IsRefl := id_subset_iff.1 (refl_le_uniformity (descend s).2)
  have hucd : descend s ○ uc ○ descend s ∈ 𝓤 α :=
    mem_of_superset ucu (right_subset_comp.trans left_subset_comp)
  constructor
  · exact ⟨x, uc, _, _, huc, symmuc, ucu, rfl, ho, rfl, subset_rfl⟩
  · have hos : ((descend s).1 ○ uc ○ (descend s).1).IsSymm := by
      sorry
    refine ⟨x, _, uu, descend s, ho, hos, hucd, rfl, huu, rfl, ?_⟩
    calc (descend s).1 ○ ((descend s).1 ○ uc ○ (descend s).1) ○ (descend s).1
      _ = ((descend s).1 ○ (descend s).1) ○ uc ○ ((descend s).1 ○ (descend s).1) := by
        simp [comp_assoc]
      _ ⊆ s ○ uc ○ s :=
        comp_subset_comp (comp_subset_comp (descend_descends s) subset_rfl) (descend_descends s)
      _ ⊆ uu := hn

public instance UniformSpace.toCompletelyRegularSpace : CompletelyRegularSpace α where
  completely_regular x K hK hx := by
    obtain ⟨O, hOu, hOo, hbO⟩ := isOpen_iff_isOpen_ball_subset.mp hK.isOpen_compl x hx
    have hcu := (descend (descend ⟨O, hOu⟩)).2
    have hccccO :=
      (SetRel.comp_subset_comp
        (descend_descends (descend ⟨O, hOu⟩))
        (descend_descends (descend ⟨O, hOu⟩))).trans
      (descend_descends ⟨O, hOu⟩)
    obtain ⟨C, hCu, hC, hCc⟩ := mem_uniformity_isClosed hcu
    have hCO := calc
      _ ⊆ _ := hCc
      _ ⊆ _ := subset_comp_self_of_mem_uniformity hcu
      _ ⊆ _ := subset_comp_self_of_mem_uniformity
        (mem_of_superset hcu (subset_comp_self_of_mem_uniformity hcu))
      _ ⊆ _ := hccccO
    have hou := (descend ⟨C, hCu⟩).2
    have hoo := descend_open ⟨C, hCu⟩
    have hosymm := descend_symm ⟨C, hCu⟩
    have hooC := descend_descends ⟨C, hCu⟩
    have hoC := (subset_comp_self_of_mem_uniformity hou).trans hooC
    have hxo : x ∈ closure (Prod.mk x ⁻¹' (descend ⟨C, hCu⟩).1) :=
      subset_closure (mem_ball_self x hou)
    have hyo : K ⊆ (Prod.mk x ⁻¹' O)ᶜ := subset_compl_comm.mp hbO
    set c : Urysohns.CU P := {
      C := closure (Prod.mk x ⁻¹' (descend ⟨C, hCu⟩).1)
      U := Prod.mk x ⁻¹' O
      closed_C := isClosed_closure
      open_U := hOo.preimage (Continuous.prodMk_right x)
      subset :=
        (closure_minimal (Set.preimage_mono hoC) (isClosed_ball x hC)).trans (preimage_mono hCO)
      hP _ Pcu _ _ := descend_spec Pcu
      P_C_U :=
        ⟨x, descend ⟨C, hCu⟩, O, _, hoo, hosymm, hou, rfl, hOo, rfl,
          (SetRel.comp_subset_comp (SetRel.comp_subset_comp subset_rfl (hoC.trans hCc))
            (subset_comp_self_of_mem_uniformity (descend (descend ⟨O, hOu⟩)).2)).trans hccccO⟩
    }
    exact ⟨fun x => ⟨c.lim x, c.lim_mem_Icc x⟩, c.continuous_lim.subtype_mk c.lim_mem_Icc,
      Subtype.ext (c.lim_of_mem_C x hxo), fun y hy => Subtype.ext (c.lim_of_notMem_U y (hyo hy))⟩

end UniformSpace

variable [t : TopologicalSpace α] [CompletelyRegularSpace α]

public theorem CompletelyRegularSpace.exists_uniformSpace :
    ∃ (u : UniformSpace α), u.toTopologicalSpace = t :=
  ⟨uniformSpaceOfCompactR1.comap stoneCechUnit, isInducing_stoneCechUnit.eq_induced.symm⟩

public theorem CompletelyRegularSpace.of_exists_uniformSpace
    (h : ∃ (u : UniformSpace α), u.toTopologicalSpace = t) :
    CompletelyRegularSpace α := by
  obtain ⟨u, rfl⟩ := h
  infer_instance

public theorem completelyRegularSpace_iff_exists_uniformSpace :
    CompletelyRegularSpace α ↔ ∃ (u : UniformSpace α), u.toTopologicalSpace = t :=
  ⟨@CompletelyRegularSpace.exists_uniformSpace α t, CompletelyRegularSpace.of_exists_uniformSpace⟩
