/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Data.Real.Archimedean
import Mathlib.Topology.UniformSpace.Ultra.Basic

/-!
# Ultrametric (nonarchimedean) uniform spaces induced by pseudometrics

Ultrametric (nonarchimedean) uniform spaces are such that they are induces by systems
of pseudometrics
having a uniformity based on equivalence relations.

## Main results

* `TopologicalSpace.isTopologicalBasis_clopens`: a uniform space with a nonarchimedean uniformity
  has a topological basis of clopen sets in the topology, meaning that it is topologically
  zero-dimensional.

## Implementation notes

-/

open scoped Uniformity

variable {X : Type*} (M : Set (X → X → ℝ))

variable (X) in
@[ext]
structure PseudoMetricFun where
  toFun : X → X → ℝ
  refl' x : toFun x x = 0
  symm' x y : toFun x y = toFun y x
  triangle' x y z : toFun x z ≤ toFun x y + toFun y z

namespace PseudoMetricFun

instance : FunLike (PseudoMetricFun X) X (X → ℝ) where
  coe := PseudoMetricFun.toFun
  coe_injective' := by
    intro a
    aesop

variable (d : PseudoMetricFun X)

@[simp]
protected lemma refl (x : X) : d x x = 0 := d.refl' x
protected lemma symm (x y : X) : d x y = d y x := d.symm' x y
protected lemma triangle (x y z : X) : d x z ≤ d x y + d y z := d.triangle' x y z
protected lemma nonneg (x y : X) : 0 ≤ d x y := by
  by_contra! H
  have : d x x < 0 := by
    calc d x x ≤ d x y + d y x := d.triangle' x y x
      _ < 0 + 0 := by refine add_lt_add H (d.symm x y ▸ H)
      _ = 0 := by simp
  exact this.not_le (d.refl' x).ge

@[simp]
protected def sup (d' : PseudoMetricFun X) : PseudoMetricFun X where
  toFun := fun x y ↦ (d x y) ⊔ (d' x y)
  refl' _ := by simp
  symm' x y := by simp [d.symm, d'.symm]
  triangle' := by
    intro x y z
    simp only [sup_le_iff]
    refine ⟨(d.triangle x y z).trans ?_, (d'.triangle x y z).trans ?_⟩ <;>
    apply add_le_add <;> simp

instance : Max (PseudoMetricFun X) where
  max := PseudoMetricFun.sup

@[simp]
protected lemma sup_apply (d' : PseudoMetricFun X) (x y : X) :
    (d ⊔ d') x y = (d x y) ⊔ (d' x y) := rfl

end PseudoMetricFun

lemma Filter.generate_image_preimage_le_comap {α β : Type*} (X : Set (Set α)) (f : β → α) :
  .generate ((f ⁻¹' ·) '' X) ≤ Filter.comap f (.generate X) := by
  intro s
  simp only [Filter.mem_comap, Filter.mem_generate_iff, Set.exists_subset_image_iff,
    Set.sInter_image]
  rintro ⟨t, ⟨u, hu, huf, hut⟩, hts⟩
  refine ⟨u, hu, huf.image _, subset_trans ?_ hts⟩
  rw [← Set.preimage_sInter]
  exact Set.preimage_mono hut

def UniformSpace.Core.ofPseudoMetricSystem (M : Set (PseudoMetricFun X)) :
    UniformSpace.Core X where
  uniformity := .generate <| (fun εd ↦ {xy | εd.2 xy.1 xy.2 < εd.1}) '' ((Set.Ioi 0 : Set ℝ) ×ˢ M)
  refl := by
    simp only [Filter.principal, idRel_subset, Filter.le_generate_iff, Set.image_subset_iff,
      Set.preimage_setOf_eq, Set.mem_setOf_eq, PseudoMetricFun.refl]
    intro
    aesop
  symm := by
    rw [Filter.tendsto_iff_comap]
    refine (Filter.generate_image_preimage_le_comap _ _).trans' ?_
    rw [← Set.image_swap_eq_preimage_swap, Set.image_image, Set.image_swap_eq_preimage_swap]
    simp [PseudoMetricFun.symm]
  comp := by
    rw [Filter.le_generate_iff]
    intro s
    simp only [Set.mem_image, Set.mem_prod, Set.mem_Ioi, Prod.exists, Filter.mem_sets,
      forall_exists_index, and_imp]
    rintro ε d εpos hd rfl
    rw [Filter.mem_lift'_sets (Monotone.compRel _ _)]
    · refine ⟨{xy | d xy.1 xy.2 < ε / 2}, Filter.mem_generate_of_mem ?_, ?_⟩
      · simp only [Set.mem_image, Set.mem_prod, Set.mem_Ioi, Prod.exists]
        exact ⟨ε / 2, d, ⟨by simp [εpos], hd⟩, rfl⟩
      · intro ⟨a, b⟩
        rw [mem_compRel]
        simp only [Set.mem_setOf_eq, forall_exists_index, and_imp]
        intro c hac hcb
        refine (d.triangle _ _ _).trans_lt ((add_lt_add hac hcb).trans_le ?_)
        simp
    · exact monotone_id
    · exact monotone_id

lemma IsUltraUniformity.ofPseudoMetricSystem_of_ultrametric {M : Set (PseudoMetricFun X)}
    (hM : ∀ d ∈ M, ∀ x y z, d x y ≤ d x z ⊔ d y z) :
    @IsUltraUniformity _ (.ofCore <| .ofPseudoMetricSystem M) := by
  letI : UniformSpace X := .ofCore <| .ofPseudoMetricSystem M
  refine .mk_of_hasBasis (Filter.hasBasis_generate _) ?_ ?_
  · intro s
    simp only [and_imp]
    intro hs hs'
    suffices ∀ t ∈ s, IsSymmetricRel t by -- TODO
      ext ⟨a, b⟩
      simp only [Set.preimage_sInter, Set.mem_iInter, Set.mem_preimage, Prod.swap_prod_mk,
        Set.mem_sInter]
      refine forall₂_congr ?_
      intro t ht
      simp [(this t ht).mk_mem_comm]
    intro t ht
    specialize hs' ht
    simp only [Set.mem_image, Set.mem_prod, Set.mem_Ioi, Prod.exists] at hs'
    obtain ⟨ε, d, ⟨εpos, hd⟩, rfl⟩ := hs'
    ext
    simp [d.symm]
  · intro s
    simp only [and_imp]
    intro hs hs'
    suffices ∀ t ∈ s, IsTransitiveRel t by -- TODO
      intro x y z
      simp only [Set.mem_sInter]
      intro hxy hyz t ht
      exact this t ht (hxy t ht) (hyz t ht)
    intro t ht
    specialize hs' ht
    simp only [Set.mem_image, Set.mem_prod, Set.mem_Ioi, Prod.exists] at hs'
    obtain ⟨ε, d, ⟨εpos, hd⟩, rfl⟩ := hs'
    intro x y z hxy hyz
    refine (hM d hd x z y).trans_lt ?_
    simpa using And.intro hxy (d.symm _ _ ▸ hyz)
