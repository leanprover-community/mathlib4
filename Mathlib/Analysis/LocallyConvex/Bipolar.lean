/-
Copyright (c) 2025 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/

import Mathlib.Analysis.LocallyConvex.Polar
import Mathlib.Analysis.LocallyConvex.AbsConvex
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Topology.Algebra.Module.StrongTopology

/-!

# Bipolar Theorem

-/

variable {𝕜 E F : Type*}

namespace LinearMap

section

variable {𝕜 E F : Type*}
variable [NormedField 𝕜] [AddCommMonoid E] [AddCommMonoid F]
variable [Module 𝕜 E] [Module 𝕜 F]

variable {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜}

-- #check (WeakBilin.eval B : F →ₗ[𝕜] WeakBilin B →L[𝕜] 𝕜)

-- TODO unify this and NormedAddGroupHom.coe_ker
theorem coe_ker (f : E →ₗ[𝕜] 𝕜) :
    (ker f : Set E) = (f : E → 𝕜) ⁻¹' {0} :=
  rfl

-- Let f be in the topological dual of `E` equipped with the weak topology induced by `B`. Then the
-- kernel of `f` is closed.
-- c.f. Mathlib/Analysis/Normed/Group/Hom.lean:theorem isClosed_ker
theorem isClosed_ker (f : WeakBilin B →L[𝕜] 𝕜) :
    IsClosed (ker f : Set (WeakBilin B)) :=
  f.coe_ker ▸ IsClosed.preimage f.continuous (T1Space.t1 0)

-- Kreyszig  2.7-9 continuous iff bounded, continuous iff continuous at a point

-- Conway Theorem V1.3 p125 dual of dual - if `e` is in the topological dual of the topological dual
-- of `E` then `e` is in `E`. Uses A 1.4 (intersection of kernels)
-- I think A 1.4 is mem_span_of_iInf_ker_le_ker

end


section NormedField

variable {𝕜 E F : Type*}
variable [NormedField 𝕜] [NormedSpace ℝ 𝕜] [AddCommMonoid E] [AddCommMonoid F]
variable [Module 𝕜 E] [Module 𝕜 F]

variable {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜} (s : Set E)

variable [Module ℝ F] [IsScalarTower ℝ 𝕜 F] [IsScalarTower ℝ 𝕜 𝕜]

theorem polar_AbsConvex : AbsConvex 𝕜 (B.polar s) := by
  rw [polar_eq_biInter_preimage]
  exact AbsConvex.iInter₂ fun i hi =>
    ⟨balanced_closedBall_zero.mulActionHom_preimage (f := (B i : (F →ₑ[(RingHom.id 𝕜)] 𝕜))),
      (convex_closedBall _ _).linear_preimage (B i)⟩

end NormedField


-- `RCLike 𝕜` and `IsScalarTower ℝ 𝕜 E` needed for `RCLike.geometric_hahn_banach_closed_point`
variable [RCLike 𝕜] [AddCommGroup E] [AddCommGroup F]
variable [Module 𝕜 E] [Module 𝕜 F]

variable (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)

-- See `LinearMap.dualPairing_nondegenerate` in Mathlib/LinearAlgebra/Dual
-- `WeakBilin B` is `E` with the σ(E,F)-topology`
-- `((WeakBilin B) →L[𝕜] 𝕜)` is the topological dual of `E` with the σ(E,F)-topology, from
--   Topology/Algebra/Module/WeadDual
-- `WeakBilin.isEmbedding` - topological

variable (f : WeakBilin B →L[𝕜] 𝕜)

lemma test4 :
    ∃ (s : Finset F) (r : ℝ) (_ : 0 < r),
    Seminorm.ball (s.sup (B.toSeminormFamily)) (0 : E) r ⊆ (f ⁻¹' (Metric.ball 0 1)) := by
  obtain ⟨V, hV1 , hV2⟩ := (Filter.HasBasis.mem_iff (LinearMap.hasBasis_weakBilin B)).mp
    (mem_nhds_iff.mpr ⟨f ⁻¹' (Metric.ball 0 1), ⟨subset_refl _,
    ⟨IsOpen.preimage (ContinuousLinearMap.continuous f) Metric.isOpen_ball, by
      rw [Set.mem_preimage, map_zero]
      exact Metric.mem_ball_self Real.zero_lt_one⟩⟩⟩)
  obtain ⟨sE, hsE1, hsE2⟩ := hV1
  obtain ⟨F, hF⟩ := Set.mem_range.mp hsE1
  use F
  simp_rw [← hF, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop] at hsE2
  obtain ⟨w, h1, h2⟩ := hsE2
  exact ⟨w, h1, h2.symm.trans_subset hV2⟩

--def mL (s : Finset F) : s → WeakBilin B →ₗ[𝕜] 𝕜 := fun (f : s) => (WeakBilin.eval B) f.val

-- Try to rephrase this in terms of `Analysis/LocallyConvex/WithSeminorms`

--#check Seminorm.IsBounded
-- def IsBounded (p : ι → Seminorm 𝕜 E) (q : ι' → Seminorm 𝕜₂ F) (f : E →ₛₗ[σ₁₂] F) : Prop :=
--  ∀ i, ∃ s : Finset ι, ∃ C : ℝ≥0, (q i).comp f ≤ C • s.sup p



-- ι = F
-- E = WeakBilin B
-- F = 𝕜
-- (f : WeakBilin B →L[𝕜] 𝕜)
-- p : B.toSeminormFamily
-- q : Fin 1 => normSeminorm 𝕜 𝕜

-- A linear map between two bornological spaces is continuous if and only if it is bounded
-- (with respect to the usual bornologies).
-- https://en.wikipedia.org/wiki/Bornology#Bornology_of_a_topological_vector_space

-- Bourbaki TVS III.12 Proposition 1(iii') Let E be a LCS with its canonical Bornology and let F be
-- a LCS a linear mapping u:E->F is continuous iff u(X) is bounded in F for every X bounded in E.
-- (Here I think E and F over ℝ or ℂ)
-- Continuous implies bounded is III.4 Corol 1
-- We have LinearMap.continuous_of_locally_bounded for `E` is first countable

/-
#check WithSeminorms.isVonNBounded_iff_finset_seminorm_bounded
#check WithSeminorms.image_isVonNBounded_iff_finset_seminorm_bounded

#check NormedSpace.isVonNBounded_ball

#check Metric.isBounded_ball

#check LinearMap.continuous_of_locally_bounded
-/

open Bornology in
lemma cont_maps_bd : ∀ s, IsVonNBounded 𝕜 s → IsVonNBounded 𝕜 (f '' s) := by
  exact fun s a ↦ IsVonNBounded.image a f

open Bornology in
lemma test {s : Set (WeakBilin B)} (h : IsVonNBounded 𝕜 s) : IsVonNBounded 𝕜 (f '' s) := by
  apply IsVonNBounded.image h

open Bornology in
lemma testb2 {s : Set (WeakBilin B)} (h : IsVonNBounded 𝕜 s) : IsVonNBounded 𝕜 (f '' s) := by
  apply IsVonNBounded.image h

--#check Seminorm.absorbent_ball_zero

variable {s : Finset F} (r : ℝ)

--#check ((s.sup B.toSeminormFamily).ball 0 r)


--#check PseudoMetricSpace.toBornology

--#check Set.Ioi

--#check Pointwise

open Pointwise

variable (t : Set E) (a : 𝕜) (c : ℝ)

/-
#check a • t

#check (c :𝕜) • t

#check PseudoMetricSpace.cobounded_sets

#check Balanced
-/

lemma bal {s : Finset F} : Balanced 𝕜 ((s.sup B.toSeminormFamily).ball 0 r) := by
  exact Seminorm.balanced_ball_zero (s.sup B.toSeminormFamily) r



-- c.f. LinearMap.continuous_of_locally_bounded
lemma isBounded_of_Continuous :
    Seminorm.IsBounded B.toSeminormFamily (fun _ : Fin 1 => normSeminorm 𝕜 𝕜) f.toLinearMap := by
  obtain ⟨s,C, hC1, hC2⟩ :=
    Seminorm.bound_of_continuous B.weakBilin_withSeminorms
      f.toSeminorm (continuous_norm.comp f.continuous)
  rw [Seminorm.IsBounded, forall_const]
  exact ⟨s, ⟨C, hC2⟩⟩

lemma test5 : ∃ (s₁ : Finset F),
    ↑f ∈ Submodule.span 𝕜 (Set.range (ContinuousLinearMap.toLinearMap₁₂
      (WeakBilin.eval B) ∘ Subtype.val : s₁ → WeakBilin B →ₗ[𝕜] 𝕜)) := by
  obtain ⟨s,hS⟩ := isBounded_of_Continuous B f (Fin.last 0)
  --simp at hs
  exact ⟨s, functional_mem_span_iff.mpr hS⟩

/-
See
- Conway V Theorem 1.3 on p108
     - III 2.1 on p68 - continuous iff cont at 0 iff cont at a point iff scalar bound
     - III 5.3 on p54 - a linear funtional is continuous iff the kernel is closed (a iff d in 3.1)
     - Mathlib/Analysis/Normed/Group/Hom.lean:theorem isClosed_ker
- Bourbaki TVS II.43
- Rudin Theorem 3.10
-/
lemma dualEmbedding_isSurjective : Function.Surjective (WeakBilin.eval B) := by
  rw [Function.Surjective]
  intro f₁
  --obtain ⟨s, hS⟩ := isBounded_of_Continuous B f₁ (Fin.last 0)
  --let hs := functional_mem_span_iff'.mpr hS
  obtain ⟨s, hs⟩ := test5 B f₁
  rw [← Set.image_univ, Finsupp.mem_span_image_iff_linearCombination] at hs
  obtain ⟨l, hl1, hl2⟩ := hs
  let f := Finsupp.linearCombination 𝕜 Subtype.val l
  use f
  rw [Finsupp.supported_univ] at hl1
  simp only [Submodule.mem_top] at hl1
  simp only [f]
  rw [←ContinuousLinearMap.coe_inj]
  rw [← hl2]
  rw [WeakBilin.eval]
  simp
  rw [ContinuousLinearMap.toLinearMap₁₂]
  rw [ContinuousLinearMap.coeLMₛₗ]
  rw [Finsupp.linearCombination_apply]
  rw [Finsupp.linearCombination_apply]
  simp
  rw [map_finsuppSum]
  aesop



/-
def dualEquiv : F ≃ₗ[𝕜] (WeakBilin B) →L[𝕜] 𝕜 where
  toLinearMap := WeakBilin.eval B


def strictEquiv2 : E ≃ₗ[𝕜] (WeakBilin B.flip) →L[𝕜] 𝕜 where
  toLinearMap := B
-/

/-
variable [Module ℝ E]
variable [IsScalarTower ℝ 𝕜 E]

open scoped ComplexOrder
theorem Bipolar {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜} {s : Set E} [Nonempty s] (h : B.Nondegenerate):
    B.flip.polar (B.polar s) = closedAbsConvexHull (E := WeakBilin B) 𝕜 s := by
  apply le_antisymm
  · simp only [Set.le_eq_subset]
    rw [← Set.compl_subset_compl]
    intro x hx
    rw [Set.mem_compl_iff] at hx
    obtain ⟨f,⟨u,⟨hf₁,hf₂⟩⟩⟩ :=
      RCLike.geometric_hahn_banach_closed_point (𝕜 := 𝕜) (E := WeakBilin B)
        absConvex_convexClosedHull.2 isClosed_closedAbsConvexHull hx
    have e3 : RCLike.re (f 0) < u :=
      (hf₁ 0) (absConvexHull_subset_closedAbsConvexHull zero_mem_absConvexHull)
    rw [map_zero, map_zero] at e3
    let g := (1/u : ℝ) • f
    have fg : g = (1/u : ℝ) • f := rfl
    have hg₁ : ∀ a ∈ (closedAbsConvexHull (E := WeakBilin B) 𝕜) s, RCLike.re (g a) < 1 := by
      intro a ha
      rw [fg]
      simp only [ ContinuousLinearMap.coe_smul', Pi.smul_apply]
      rw [RCLike.smul_re]
      have t1 : RCLike.re (f a) < u := hf₁ a ha
      simp [t1]
      rw [← (inv_mul_cancel₀ (lt_iff_le_and_ne.mp e3).2.symm)]
      exact mul_lt_mul_of_pos_left ((hf₁ a) ha) (inv_pos_of_pos e3)
    --have hg₃ : g ∈ B.polar (E := WeakBilin B) s := sorry
    sorry

  · exact closedAbsConvexHull_min (subset_bipolar B s) (polar_AbsConvex _) (polar_isClosed B.flip _)
-/

end LinearMap
