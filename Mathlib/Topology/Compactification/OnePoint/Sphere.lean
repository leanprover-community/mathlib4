/-
Copyright (c) 2025 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen, Oliver Nash
-/
-- import Mathlib.Analysis.Calculus.Deriv.Inv
-- import Mathlib.Analysis.Complex.Circle
-- import Mathlib.Analysis.NormedSpace.BallAction
-- import Mathlib.Analysis.SpecialFunctions.ExpDeriv
-- import Mathlib.Analysis.InnerProductSpace.Calculus
-- import Mathlib.Analysis.InnerProductSpace.PiL2
-- import Mathlib.Data.Complex.FiniteDimensional
-- import Mathlib.Geometry.Manifold.Algebra.LieGroup
-- import Mathlib.Geometry.Manifold.Instances.Real
-- import Mathlib.Geometry.Manifold.MFDeriv.Basic
-- import Mathlib.Tactic.Module
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.PartialHomeomorph

import Mathlib.Geometry.Manifold.Instances.Sphere

/-!

# One-point compactification of Euclidean space is homeomorphic to the sphere.

-/

open Metric Module Function

noncomputable section OnePoint

variable {n : ℕ}
variable {v : EuclideanSpace ℝ (Fin n.succ)}
variable (hv : ‖v‖ = 1)
variable (hv' : v ∈ sphere 0 (1:ℝ))
/-
    For example, `v` could be
    `(EuclideanSpace.single (0:Fin n.succ) (1:ℝ))`
-/

open Set Submodule

/-- The orthogonal complement of the span of a point on the sphere
is homeomorphic to a Euclidean space of codimension 1. -/
noncomputable def Submodule_homeo_Euclidean {n : ℕ}
    (v : sphere (0 : (EuclideanSpace ℝ (Fin n.succ))) 1) :
    Homeomorph ((span ℝ {v.1})ᗮ) (EuclideanSpace ℝ (Fin n)) :=
  letI fact {n : ℕ} : Fact (finrank ℝ (EuclideanSpace ℝ (Fin n.succ)) = n + 1) := ⟨by simp⟩
  (OrthonormalBasis.fromOrthogonalSpanSingleton n (ne_zero_of_mem_unit_sphere v)).repr.toHomeomorph

/-- `stereoInvFun` agrees with the inverse image of
 stereographic projection on the `source`.
 (This is nonredundant since the inverse image may
 include the anchor of the stereographic projection, which is not in the `source`.) -/
lemma image_source (s : Set ↥(span ℝ {v})ᗮ) : stereoInvFun hv '' s =
    (stereographic hv).toPartialEquiv ⁻¹' s ∩ (stereographic hv).source := ext <| fun x =>
    ⟨fun h => by
      obtain ⟨y,hy⟩ := h
      have : (stereographic hv) x = y := hy.2 ▸ (stereographic hv).right_inv' trivial
      simp only [PartialHomeomorph.toFun_eq_coe, mem_inter_iff, mem_preimage]
      exact ⟨this ▸ hy.1, hy.2 ▸ stereoInvFun_ne_north_pole hv y⟩,
    fun h => ⟨(stereographic hv) x, h.1, (stereographic hv).left_inv' <| mem_of_mem_inter_right h⟩⟩

/-- The one-point compactification of ℝⁿ, in the form of a codimension 1 subspace,
 is homeomorphic to the n-sphere. -/
def onePointHyperplaneHomeoUnitSphere :
    OnePoint (ℝ ∙ v)ᗮ ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin n.succ)) 1 := by
  apply OnePoint.equivOfIsEmbeddingOfRangeEq (f := stereoInvFun hv)
  · constructor
    · apply (Topology.isInducing_iff _).mpr
      ext s
      constructor
      · exact fun h => isOpen_mk.mpr <| by
          use stereoInvFun hv '' s
          constructor
          · obtain ⟨b,hb⟩ := (
              (stereographic hv).isOpenEmbedding_restrict.continuous).isOpen_preimage s h
            have hh : (stereographic hv) ⁻¹' s ∩ {⟨v, hv'⟩}ᶜ = b ∩ {⟨v, hv'⟩}ᶜ := ext <| fun x =>
              ⟨fun h => ⟨(congrFun hb.2 ⟨x, h.2⟩).mpr h.1, h.2⟩,
               fun h => ⟨(congrFun hb.2 ⟨x, h.2⟩).mp  h.1, h.2⟩⟩
            exact image_source hv s ▸ hh ▸ hb.1.inter isOpen_compl_singleton
          · exact (injective_stereographic_symm hv).preimage_image s
      · intro ⟨t,ht⟩
        rw [isOpen_mk] at ht
        exact ht.2 ▸ ((stereographic hv).continuousOn_invFun.mono
                     fun _ _ ↦ trivial).isOpen_preimage
          ((continuous_stereoInvFun hv).isOpen_preimage t ht.1) (fun ⦃a⦄ a ↦ a) ht.1
    · exact injective_stereographic_symm hv
  · exact ext <| fun x =>
      ⟨fun ⟨y,hy⟩ => hy ▸ (fun _ => (stereographic hv).map_target) y (by trivial),
      fun h => ⟨(stereographic hv).toFun' x, (stereographic hv).left_inv h⟩⟩


/-- The one-point compactification of Euclidean space is homeomorphic to the sphere. -/
noncomputable def OnePointEuclidean_homeo_sphere : Homeomorph
    (OnePoint (EuclideanSpace ℝ (Fin n))) ((sphere (0 : EuclideanSpace ℝ (Fin n.succ)) 1)) :=
  ((Submodule_homeo_Euclidean ⟨v,hv'⟩).symm.onePointCongr).trans
    <| onePointHyperplaneHomeoUnitSphere hv hv'

end OnePoint
