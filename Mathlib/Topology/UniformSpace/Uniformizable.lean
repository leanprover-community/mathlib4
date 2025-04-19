/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
import Mathlib.Topology.Separation.CompletelyRegular

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

-- how do I cite this
* <https://www.math.wm.edu/~vinroot/PadicGroups/519probset1.pdf>
* [S. Willard, *General Topology*][Wil04]
-/

variable {α : Type*}

open Filter Set

section UniformSpace
variable [UniformSpace α]

private noncomputable def descend (s : { s : Set (α × α) // s ∈ uniformity α }) :
    { s : Set (α × α) // s ∈ uniformity α} :=
  ⟨_, (comp_open_symm_mem_uniformity_sets (mem_uniformity_isClosed
    (comp_open_symm_mem_uniformity_sets s.2).choose_spec.1).choose_spec.1).choose_spec.1⟩

private theorem descend_open (s : { s : Set (α × α) // s ∈ uniformity α }):
    IsOpen (descend s).1 :=
  (comp_open_symm_mem_uniformity_sets (mem_uniformity_isClosed
    (comp_open_symm_mem_uniformity_sets s.2).choose_spec.1).choose_spec.1).choose_spec.2.1

private theorem descend_symm (s : { s : Set (α × α) // s ∈ uniformity α }) :
    IsSymmetricRel (descend s).1 :=
  (comp_open_symm_mem_uniformity_sets (mem_uniformity_isClosed
    (comp_open_symm_mem_uniformity_sets s.2).choose_spec.1).choose_spec.1).choose_spec.2.2.1

private theorem descend_descends (s : { s : Set (α × α) // s ∈ uniformity α }) :
    compRel (descend s).1 (descend s).1 ⊆ s := by
  dsimp [descend]
  generalize_proofs o₁ c o₂
  have hoc : o₂.choose ⊆ c.choose := by
    trans compRel o₂.choose o₂.choose
    · apply subset_comp_self
      rw [← Filter.mem_principal]
      exact refl_le_uniformity o₂.choose_spec.1
    · exact o₂.choose_spec.2.2.2
  calc compRel o₂.choose o₂.choose
    _ ⊆ compRel c.choose c.choose := compRel_mono hoc hoc
    _ ⊆ compRel o₁.choose o₁.choose := compRel_mono c.choose_spec.2.2 c.choose_spec.2.2
    _ ⊆ s.1 := o₁.choose_spec.2.2.2

private def P (c : Set α) (u : Set α) :=
  ∃ (x : α) (uc uu : Set (α × α)) (s : { s : Set (α × α) // s ∈ uniformity α }),
    IsOpen uc ∧ IsSymmetricRel uc ∧ uc ∈ uniformity α ∧ c = closure (Prod.mk x ⁻¹' uc) ∧
    IsOpen uu ∧ u = Prod.mk x ⁻¹' uu ∧ compRel s (compRel uc s) ⊆ uu

private theorem descend_spec {c u : Set α}
    (Pcu : P c u) (hcu : c ⊆ u) :
    ∃ (v : Set α), IsOpen v ∧ c ⊆ v ∧ closure v ⊆ u ∧ P c v ∧ P (closure v) u := by
  obtain ⟨x, uc, uu, s, huc, symmuc, ucu, rfl, huu, rfl, hn⟩ := Pcu
  have ho : IsOpen (compRel (descend s) (compRel uc (descend s))) :=
    (descend_open s).compRel (huc.compRel (descend_open s))
  use Prod.mk x ⁻¹' compRel (descend s) (compRel uc (descend s)),
    ho.preimage (Continuous.prodMk_right x)
  constructor
  · apply ((Continuous.prodMk_right x).closure_preimage_subset _).trans
    apply preimage_mono
    rw [closure_eq_inter_uniformity]
    exact iInter₂_subset (descend s).1 (descend s).2
  constructor
  · apply ((Continuous.prodMk_right x).closure_preimage_subset _).trans
    apply preimage_mono
    apply hn.trans'
    rw [closure_eq_inter_uniformity]
    apply iInter₂_subset_of_subset (descend s).1 (descend s).2
    conv_lhs =>
      equals compRel (compRel (descend s) (descend s))
        (compRel uc (compRel (descend s) (descend s))) =>
          simp [compRel_assoc]
    exact compRel_mono (descend_descends s) (compRel_mono subset_rfl (descend_descends s))
  have hucd : compRel (descend s) (compRel uc (descend s)) ∈ uniformity α :=
    mem_of_superset ucu
      ((left_subset_compRel (refl_le_uniformity (descend s).2)).trans
        (right_subset_compRel (refl_le_uniformity (descend s).2)))
  constructor
  · exact ⟨x, uc, _, _, huc, symmuc, ucu, rfl, ho, rfl, subset_rfl⟩
  · have hos : IsSymmetricRel (compRel (descend s) (compRel uc (descend s))) := by
      simp [IsSymmetricRel, compRel_assoc, prodSwap_preimage_compRel,
        symmuc.eq, (descend_symm s).eq]
    refine ⟨x, _, uu, descend s, ho, hos, hucd, rfl, huu, rfl, ?_⟩
    rw [compRel_assoc]
    apply hn.trans'
    rw [← compRel_assoc]
    apply compRel_mono (descend_descends s)
    rw [compRel_assoc]
    exact compRel_mono subset_rfl (descend_descends s)

instance UniformSpace.completelyRegularSpace : CompletelyRegularSpace α where
  completely_regular x K hK hx := by
    obtain ⟨O, hOu, hOo, hbO⟩ := isOpen_iff_isOpen_ball_subset.mp hK.isOpen_compl x hx
    have hcu := (descend (descend ⟨O, hOu⟩)).2
    have hccccO :=
      (compRel_mono
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
      subset := (closure_minimal (preimage_mono hoC) (isClosed_ball x hC)).trans (preimage_mono hCO)
      hP _ Pcu _ hcu := descend_spec Pcu hcu
      P_C_U := by
        exact ⟨x, descend ⟨C, hCu⟩, O, _, hoo, hosymm, hou, rfl, hOo, rfl,
          (compRel_mono (subset_comp_self_of_mem_uniformity (descend (descend ⟨O, hOu⟩)).2)
            (compRel_mono (hoC.trans hCc) subset_rfl)).trans hccccO⟩
    }
    exact ⟨fun x => ⟨c.lim x, c.lim_mem_Icc x⟩, c.continuous_lim.subtype_mk c.lim_mem_Icc,
      Subtype.ext (c.lim_of_mem_C x hxo), fun y hy => Subtype.ext (c.lim_of_nmem_U y (hyo hy))⟩

end UniformSpace

section TopologicalSpace
variable [TopologicalSpace α]
open Real

variable (α) in
/-
This definition could be useful in other places, but I've not seen a use yet
so this is private for now (mainly so I don't have to write api).
-/
private def inducedUniformity : UniformSpace α :=
  UniformSpace.ofCore {
    uniformity := ⨅ (f : C(α, ℝ)) (ε : ℝ) (_ : ε > 0),
      principal ((fun p => dist (f p.fst) (f p.snd)) ⁻¹' Iio ε)
    refl := by
      simp_rw [le_iInf_iff]
      simp +contextual
    symm := by
      rw [tendsto_iff_comap]
      apply le_of_eq
      simp_rw [Filter.comap_iInf, comap_principal, preimage_preimage,
        Prod.fst_swap, Prod.snd_swap, dist_comm]
    -- this proof takes four seconds to elaborate on my machine
    -- TODO: speed this up
    comp := by
      intro s hs
      simp_rw [mem_iInf, iInf_eq_if] at hs
      obtain ⟨I, hI, U, hs, rfl⟩ := hs
      have := hI.to_subtype
      choose J hJ V hs hU using hs
      have := fun i => (hJ i).to_subtype
      replace hU : U = fun i => ⋂ j, V i j := funext hU
      subst hU
      suffices h : ((fun s => compRel s s) <| ⋂ (i : I) (j : J i) (_ : j.val > 0),
          (fun p ↦ dist (i.val p.fst) (i.val p.snd)) ⁻¹' Iio (j / 2)) ⊆ ⋂ (i) (j), V i j by
        refine mem_of_superset ?_ h
        apply mem_lift'
        simp_rw [mem_iInf, iInf_eq_if, mem_ite, mem_principal, mem_top]
        refine ⟨I, hI, _, fun i => ?_, rfl⟩
        refine ⟨(· / 2) '' J i, (hJ i).image (· / 2),
          fun j => ⋂ (_ : j.val > 0), (fun p ↦ dist (i.val p.fst) (i.val p.snd)) ⁻¹' Iio j,
            fun j => ⟨fun hj => ?_, fun hj => by simp [hj]⟩, ?_⟩
        · simp_rw [iInter_eq_if, if_pos hj, subset_rfl]
        · apply iInter_congr_of_surjective _ surjective_onto_image
          intro j
          simp only [imageFactorization]
          exact iInter_congr_Prop (by simp) fun _ => rfl
      simp_rw [subset_iInter_iff]
      intro i j
      specialize hs i j
      split_ifs at hs with hj
      · intro x hx
        apply hs
        rw [mem_compRel] at hx
        obtain ⟨z, hxz, hzx⟩ := hx
        simp_rw [mem_iInter] at hxz hzx
        apply (dist_triangle (i.val x.fst) (i.val z) (i.val x.snd)).trans_lt
        rw [← add_halves j.val]
        exact add_lt_add (hxz i j hj) (hzx i j hj)
      · rw [mem_top] at hs
        simp [hs]
  }

private theorem le_u_l :
    ‹TopologicalSpace α› ≤ (inducedUniformity α).toTopologicalSpace := by
  intro s hs
  rw [isOpen_iff_forall_mem_open]
  rw [@isOpen_iff_ball_subset] at hs
  intro x hx
  obtain ⟨V, hV, hVs⟩ := hs x hx
  change V ∈ iInf _ at hV
  simp_rw [mem_iInf] at hV
  obtain ⟨I, hI, U, hU, rfl⟩ := hV
  have := hI.to_subtype
  choose J hJ V hV hU using hU
  have := fun i => (hJ i).to_subtype
  replace hU : U = fun i => ⋂ j, V i j := funext hU
  subst hU
  refine ⟨⋂ (i : I) (j : J i) (_ : j.val > 0), (fun y => dist (i.val x) (i.val y)) ⁻¹' Iio j,
    ?_, ?_, ?_⟩
  · apply hVs.trans'
    simp_rw [UniformSpace.ball, preimage_iInter]
    apply iInter₂_mono
    intro i j
    simp_rw [iInf_eq_if, mem_ite, mem_principal, mem_top] at hV
    rw [iInter_eq_if]
    split_ifs with hj
    · apply (preimage_mono ((hV i j).left hj)).trans'
      intro y hy
      simpa using hy
    · simp [(hV i j).right hj]
  · exact isOpen_iInter_of_finite fun i =>
      isOpen_iInter_of_finite fun j =>
        isOpen_iInter_of_finite fun hj =>
          isOpen_Iio.preimage (continuous_const.dist i.val.continuous)
  · simp_rw [mem_iInter]
    intro i j hj
    simp [hj]

section CompletelyRegularSpace
variable [CompletelyRegularSpace α]

private theorem u_l_le :
    (inducedUniformity α).toTopologicalSpace ≤ ‹TopologicalSpace α› := by
  intro s hs
  rw [@isOpen_iff_ball_subset]
  intro x hx
  obtain ⟨f, hf, hf0, hf1⟩ :=
    CompletelyRegularSpace.completely_regular x sᶜ hs.isClosed_compl (not_mem_compl_iff.mpr hx)
  use ((fun p : α × α => dist (f p.fst : ℝ) (f p.snd)) ⁻¹' Iio 2⁻¹)
  constructor
  · have hf' : Continuous (fun i => (f i : ℝ)) := continuous_subtype_val.comp hf
    suffices h : (_ : Filter _) ≤ _ from h (mem_principal_self _)
    apply iInf₂_le_of_le ⟨_, hf'⟩ 2⁻¹
    exact iInf_le _ (by norm_num)
  · rw [UniformSpace.ball]
    intro a ha
    by_contra has
    norm_num [hf0, hf1 has] at ha

theorem CompletelyRegularSpace.exists_uniformSpace :
    ∃ (u : UniformSpace α), u.toTopologicalSpace = ‹TopologicalSpace α› :=
  ⟨inducedUniformity α, u_l_le.antisymm le_u_l⟩

end CompletelyRegularSpace

theorem CompletelyRegularSpace.of_exists_uniformSpace
    (h : ∃ (u : UniformSpace α), u.toTopologicalSpace = ‹TopologicalSpace α›) :
    CompletelyRegularSpace α := by
  obtain ⟨u, rfl⟩ := h
  infer_instance

theorem completelyRegularSpace_iff_exists_uniformSpace :
    CompletelyRegularSpace α ↔
    ∃ (u : UniformSpace α), u.toTopologicalSpace = ‹TopologicalSpace α› :=
  ⟨@CompletelyRegularSpace.exists_uniformSpace α _, CompletelyRegularSpace.of_exists_uniformSpace⟩

end TopologicalSpace
