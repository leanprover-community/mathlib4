/-
Copyright (c) 2025 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen, Oliver Nash
-/
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!

# One-point compactification of Euclidean space is homeomorphic to the sphere.

-/

open Function Metric Module Set Submodule

noncomputable section

variable {n : ℕ} {v : EuclideanSpace ℝ (Fin n.succ)} (hv : ‖v‖ = 1)

/-- The orthogonal complement of the span of a point on the sphere
is homeomorphic to a Euclidean space of codimension 1. -/
noncomputable def Submodule_homeo_Euclidean {n : ℕ}
    (v : sphere (0 : (EuclideanSpace ℝ (Fin n.succ))) 1) :
    Homeomorph ((span ℝ {v.1})ᗮ) (EuclideanSpace ℝ (Fin n)) :=
  letI fact {n : ℕ} : Fact (finrank ℝ (EuclideanSpace ℝ (Fin n.succ)) = n + 1) := ⟨by simp⟩
  (OrthonormalBasis.fromOrthogonalSpanSingleton n (ne_zero_of_mem_unit_sphere v)).repr.toHomeomorph

/-- The one-point compactification of ℝⁿ, in the form of a codimension 1 subspace,
 is homeomorphic to the n-sphere. -/
def onePointHyperplaneHomeoUnitSphere :
    OnePoint (ℝ ∙ v)ᗮ ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin n.succ)) 1 := by
  have hv' : v ∈ sphere 0 (1:ℝ) := by simpa
  apply OnePoint.equivOfIsEmbeddingOfRangeEq (f := (stereographic hv).symm)
  · constructor
    · apply (Topology.isInducing_iff _).mpr
      ext s
      constructor
      · exact fun h => isOpen_mk.mpr <| by
          use (stereographic hv).symm '' s
          constructor
          · obtain ⟨b,hb⟩ := (
              (stereographic hv).isOpenEmbedding_restrict.continuous).isOpen_preimage s h
            have hh : (stereographic hv) ⁻¹' s ∩ {⟨v, hv'⟩}ᶜ = b ∩ {⟨v, hv'⟩}ᶜ := ext <| fun x =>
              ⟨fun h => ⟨(congrFun hb.2 ⟨x, h.2⟩).mpr h.1, h.2⟩,
               fun h => ⟨(congrFun hb.2 ⟨x, h.2⟩).mp  h.1, h.2⟩⟩
            exact (stereographic hv).isOpen_image_symm_of_subset_target h <| by simp
          · exact (injective_stereographic_symm hv).preimage_image s
      · intro ⟨t,ht⟩
        rw [isOpen_mk] at ht
        exact ht.2 ▸ ((stereographic hv).continuousOn_invFun.mono
                     fun _ _ ↦ trivial).isOpen_preimage
          ((continuous_stereographic_symm hv).isOpen_preimage t ht.1) (fun ⦃a⦄ a ↦ a) ht.1
    · exact injective_stereographic_symm hv
  · exact ext <| fun x =>
      ⟨fun ⟨y,hy⟩ => hy ▸ (fun _ => (stereographic hv).map_target) y (by trivial),
      fun h => ⟨(stereographic hv).toFun' x, (stereographic hv).left_inv h⟩⟩

/-- The one-point compactification of Euclidean space is homeomorphic to the sphere. -/
noncomputable def OnePointEuclidean_homeo_sphere : Homeomorph
    (OnePoint (EuclideanSpace ℝ (Fin n))) ((sphere (0 : EuclideanSpace ℝ (Fin n.succ)) 1)) := by
  have hv' : v ∈ sphere 0 (1:ℝ) := by simpa
  exact ((Submodule_homeo_Euclidean ⟨v,hv'⟩).symm.onePointCongr).trans
    <| onePointHyperplaneHomeoUnitSphere hv
