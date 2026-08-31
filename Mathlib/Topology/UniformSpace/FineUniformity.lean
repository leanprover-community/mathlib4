/-
Copyright (c) 2026 Tian Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tian Chen
-/
module

public import Mathlib.Topology.UniformSpace.Uniformizable

/-!
# The fine uniformity

The *fine uniformity* of a (uniformizable) topological space is the finest uniformity compatible
with the topology. A uniform space with such a uniformity is called a *fine space*.

## Main results

* `FineSpace.uniformContinuous_of_continuous`: a continuous function on a fine space is uniformly
  continuous

## TODO

* the entourages of the fine uniformity on a paracompact Hausdorff space are exactly the
  neighborhoods of the diagonal
* the fine uniformity on a paracompact Hausdorff space is complete

## References

* [Willard's *General Topology*][zbMATH02107988]
-/

open Filter Set Uniformity UniformSpace SetRel

public section

section Defs

variable (X : Type*)

/-- The fine uniformity of a (uniformizable) topological space is the finest uniformity compatible
with the topology. -/
@[instance_reducible]
def fineUniformity [t : TopologicalSpace X] : UniformSpace X :=
  sInf { u | t ≤ u.toTopologicalSpace }

/-- A basis for the fine uniformity. In the uniform cover definition of a uniform space,
this corresponds to the normally open covers. -/
def fineUniformityBasis [t : TopologicalSpace X] : FilterBasis (X × X) where
  sets := { U | ∃ s : ℕ → Set (X × X), s 0 = U ∧
    ∀ i, diagonal X ⊆ s i ∧ IsOpen (s i) ∧ s (i + 1) ○ s (i + 1) ≤ s i }
  nonempty := ⟨univ, fun _ ↦ univ, by simp⟩
  inter_sets := by
    rintro _ _ ⟨s₁, rfl, hs₁⟩ ⟨s₂, rfl, hs₂⟩
    refine ⟨s₁ 0 ∩ s₂ 0, ⟨fun i ↦ s₁ i ∩ s₂ i, rfl, fun i ↦ ?_⟩, subset_rfl⟩
    repeat rw [subset_inter_iff]
    exact ⟨⟨(hs₁ i).1, (hs₂ i).1⟩, (hs₁ i).2.1.inter (hs₂ i).2.1,
      comp_subset_comp inter_subset_left inter_subset_left |>.trans (hs₁ i).2.2,
      comp_subset_comp inter_subset_right inter_subset_right |>.trans (hs₂ i).2.2⟩

/-- A uniform space is a fine space if its uniformity is the fine uniformity. -/
class FineSpace [u : UniformSpace X] : Prop where
  eq_fineUniformity' : u = fineUniformity X

end Defs

variable {X : Type*}

section UniformSpace

variable [UniformSpace X]

private lemma exist_comp_of_mem_uniformity (s : Set (X × X)) (hs : s ∈ 𝓤 X) :
    ∃ s', s' ○ s' ⊆ s ∧ s' ∈ 𝓤 X ∧ IsOpen s':= by
  obtain ⟨t, ht, hts⟩ := comp_mem_uniformity_sets hs
  rw [uniformity_hasBasis_open.mem_iff] at ht
  obtain ⟨s', hs', hs't⟩ := ht
  exact ⟨s', (comp_subset_comp hs't hs't).trans hts, hs'.1, hs'.2⟩

lemma IsOpen.mem_fineUniformityBasis_of_mem_uniformity {s : Set (X × X)}
  (hsOpen : IsOpen s) (hs : s ∈ 𝓤 X) : s ∈ fineUniformityBasis X := by
  choose f hf using @exist_comp_of_mem_uniformity X
  let g (t : { s // s ∈ 𝓤 X }) : { s // s ∈ 𝓤 X } := ⟨f t.1 t.2, (hf t.1 t.2).2.1⟩
  refine ⟨fun i ↦ g^[i] ⟨s, hs⟩, rfl, fun i ↦ ?_⟩
  rcases i with _ | i
  · exact ⟨subset_of_mem_nhdsSet <| nhdsSet_diagonal_le_uniformity hs, hsOpen, (hf s hs).1⟩
  · simp_rw [Function.iterate_succ']
    exact ⟨subset_of_mem_nhdsSet <| nhdsSet_diagonal_le_uniformity (hf _ _).2.1,
      (hf _ _).2.2, (hf _ _).1⟩

end UniformSpace

section Uniformizable

variable [t : TopologicalSpace X] [CompletelyRegularSpace X]

lemma toTopologicalSpace_fineUniformity : (fineUniformity X).toTopologicalSpace = t := by
  rw [toTopologicalSpace_sInf]
  refine le_antisymm ?_ <| le_iInf₂ fun _ h ↦ h
  simp only [mem_ofPred_eq, iInf_le_iff, le_iInf_iff]
  intro _ h
  obtain ⟨u, rfl⟩ := CompletelyRegularSpace.exists_uniformSpace (X := X) (t := t)
  exact h u le_rfl

lemma isFineSpace_fineUniformity : @FineSpace X (fineUniformity X) :=
  @FineSpace.mk X (fineUniformity X) <| by rw [toTopologicalSpace_fineUniformity]

end Uniformizable

namespace IsFineSpace

variable [u : UniformSpace X]

instance [CompactSpace X] : FineSpace X :=
  ⟨unique_uniformity_of_compact rfl toTopologicalSpace_fineUniformity⟩

instance [DiscreteUniformity X] : FineSpace X :=
  ⟨by unfold fineUniformity; rw [@DiscreteUniformity.eq_bot X u, toTopologicalSpace_bot]; simp⟩

variable [FineSpace X]

variable (X) in
lemma eq_fineUniformity : u = fineUniformity X := FineSpace.eq_fineUniformity'

lemma uniformity_eq_fineUniformityBasis_filter : 𝓤 X = (fineUniformityBasis X).filter := by
  ext S
  constructor
  · intro hS
    rw [uniformity_hasBasis_open.mem_uniformity_iff] at hS
    obtain ⟨s, ⟨hsU, hso⟩, hs⟩ := hS
    exact ⟨s, hso.mem_fineUniformityBasis_of_mem_uniformity hsU, fun ⟨a, b⟩ h ↦ hs a b h⟩
  · intro ⟨v, hv, hvS⟩
    rw [eq_fineUniformity X]
    obtain ⟨s, rfl, hs⟩ := hv
    let u' := ofCore <| .mkOfBasis
      { sets := range (fun i ↦ s i ∩ Prod.swap ⁻¹' s i)
        nonempty := range_nonempty _
        inter_sets := by
          rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
          refine ⟨_, ⟨i + j, rfl⟩, ?_⟩
          rw [inter_inter_inter_comm]
          have hs' : Antitone s := antitone_of_add_one_le fun i _ a ha ↦
            (hs i).2.2 ⟨a.2, ha, (hs _).1 <| mem_diagonal a.2⟩
          have : s (i + j) ⊆ s i ∩ s j := subset_inter (hs' (self_le_add_right _ _))
            (hs' (self_le_add_left _ _))
          apply inter_subset_inter this
          rw [← preimage_inter]
          exact preimage_mono this }
      (by
        rintro _ ⟨i, rfl⟩ x
        have h := (hs i).1 (mem_diagonal x)
        exact ⟨h, h⟩)
      (by
        rintro _ ⟨i, rfl⟩
        refine ⟨_, ⟨i, ?_⟩, subset_rfl⟩
        rw [preimage_inter, preimage_preimage, inter_comm]
        congr)
      (by
        rintro _ ⟨i, rfl⟩
        have h := (hs i).2.2
        refine ⟨_, ⟨i + 1, rfl⟩, subset_inter
          (subset_trans (comp_subset_comp inter_subset_left inter_subset_left) h)
          (subset_trans ?_ <| preimage_mono h)⟩
        change _ ⊆ inv _
        rw [inv_comp]
        exact comp_subset_comp inter_subset_right inter_subset_right)
    have hu : u.toTopologicalSpace ≤ u'.toTopologicalSpace := le_of_nhds_le_nhds fun x ↦ by
      rw [nhds_eq_comap_uniformity]
      intro a ha
      obtain ⟨t, ⟨_, ⟨i, rfl⟩, hi⟩, ha⟩ := ha
      clear u'
      rw [_root_.mem_nhds_iff]
      refine ⟨Prod.mk x ⁻¹' s i ∩ (Prod.mk · x) ⁻¹' s i, fun y hy ↦ ha (hi hy),
        (Continuous.prodMk_right x).isOpen_preimage _ (hs i).2.1 |>.inter
          <| (Continuous.prodMk_left x).isOpen_preimage _ (hs i).2.1, ?_⟩
      have h := (hs i).1 (mem_diagonal x)
      exact ⟨h, h⟩
    unfold fineUniformity
    rw [sInf_eq_iInf', iInf_uniformity]
    apply mem_iInf_of_mem ⟨u', hu⟩
    exact ⟨s 0 ∩ Prod.swap ⁻¹' s 0, mem_range_self 0, inter_subset_left.trans hvS⟩

lemma hasBasis : (𝓤 X).HasBasis (· ∈ fineUniformityBasis X) id := by
  rw [uniformity_eq_fineUniformityBasis_filter]
  exact (fineUniformityBasis X).hasBasis

variable {Y : Type*} [UniformSpace Y]

/-- A continuous function on fine space is uniformly continuous. -/
theorem uniformContinuous_of_continuous {f : X → Y} (hf : Continuous f) : UniformContinuous f := by
  rw [hasBasis.uniformContinuous_iff uniformity_hasBasis_open]
  intro r ⟨hr, hro⟩
  obtain ⟨s, rfl, hs⟩ := hro.mem_fineUniformityBasis_of_mem_uniformity hr
  refine ⟨Prod.map f f ⁻¹' s 0, ⟨(Prod.map f f ⁻¹' s ·), rfl, ?_⟩, fun _ _ h ↦ h⟩
  intro i
  refine ⟨subset_trans ?_ <| preimage_mono (hs i).1, (hf.prodMap hf).isOpen_preimage _ (hs i).2.1,
    subset_trans (fun _ ↦ by aesop) <| preimage_mono (hs i).2.2⟩
  simp [diagonal_subset_iff]

end IsFineSpace

#lint
