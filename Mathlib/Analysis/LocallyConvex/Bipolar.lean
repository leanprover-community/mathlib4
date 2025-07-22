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

lemma test1 : IsOpen (f ⁻¹' (Metric.ball 0 1)) :=
  IsOpen.preimage (ContinuousLinearMap.continuous f) Metric.isOpen_ball

lemma test2a : 0 ∈ (f ⁻¹' (Metric.ball 0 1)) := by
  simp_all only [Set.mem_preimage, map_zero, Metric.mem_ball, dist_self, zero_lt_one]

lemma test2b : 0 ∈ (f ⁻¹' (Metric.ball 0 1)) ∧ IsOpen (f ⁻¹' (Metric.ball 0 1)) := by
  constructor
  · exact test2a B f
  · exact test1 B f

lemma test2 : (f ⁻¹' (Metric.ball 0 1))  ∈ (nhds 0) := by
  rw [mem_nhds_iff]
  use f ⁻¹' (Metric.ball 0 1)
  constructor
  · exact fun ⦃a⦄ a ↦ a
  · exact And.symm (test2b B f)

--#check (Filter.HasBasis.mem_iff (LinearMap.hasBasis_weakBilin B)).mp (test2 B f)

lemma test3 : ∃ V ∈ B.toSeminormFamily.basisSets, V ⊆ (f ⁻¹' (Metric.ball 0 1)) := by
  obtain ⟨V, hV1, hV2⟩ := (Filter.HasBasis.mem_iff (LinearMap.hasBasis_weakBilin B)).mp (test2 B f)
  use V
  constructor
  · apply hV1
  · apply hV2

lemma test4 :
    ∃ (s : Finset F) (r : ℝ) (_ : 0 < r),
    Seminorm.ball (s.sup (B.toSeminormFamily)) (0 : E) r ⊆ (f ⁻¹' (Metric.ball 0 1)) := by
  obtain ⟨V, hV1 , hV2⟩ := test3 B f
  obtain ⟨sE,hsE1, hsE2⟩ := hV1
  simp at hsE1
  obtain ⟨F, hF⟩ := hsE1
  use F
  have e1 : (0 : ℝ ) < (1 : ℝ) := by exact Real.zero_lt_one
  rw [Set.iUnion, iSup] at hF
  subst hF
  simp_all only [zero_lt_one, Set.sSup_eq_sUnion, Set.sUnion_range, Set.mem_iUnion,
    Set.mem_singleton_iff,
    exists_prop]
  obtain ⟨w, h⟩ := hsE2
  obtain ⟨left, right⟩ := h
  subst right
  use w

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

lemma isBounded_of_Continuous :
    Seminorm.IsBounded B.toSeminormFamily (fun _ : Fin 1 => normSeminorm 𝕜 𝕜) f.toLinearMap := by
  rw [Seminorm.isBounded_const]
  obtain ⟨s₁, hs⟩ := test4 B f
  use s₁
  obtain ⟨r, hr1, hr2⟩ := hs
  have e1 : 0 < r⁻¹ := by exact Right.inv_pos.mpr hr1
  use ⟨r⁻¹, le_of_lt e1⟩
  intro x
  have e1 (z : WeakBilin B) (h : z ∈ ((s₁.sup B.toSeminormFamily).ball 0 r)) : ‖f z‖ < 1 := by
    have e2 : z ∈ f ⁻¹' Metric.ball 0 1 := by
      exact hr2 h
    aesop
  have e2 (z : WeakBilin B) :
      z ∈ (s₁.sup B.toSeminormFamily).ball 0 r  ↔ (s₁.sup B.toSeminormFamily) z < r := by
    aesop
  simp_rw [e2] at e1
  have i1 {a : ℝ} (ha : 0 < a) : 0 < (s₁.sup B.toSeminormFamily) x + a := by
    have i2 : 0 ≤ (s₁.sup B.toSeminormFamily) x := apply_nonneg _ _
    have i3 : a ≤ (s₁.sup B.toSeminormFamily) x + a := by exact le_add_of_nonneg_left i2
    --have i0 : (0 : ℝ)  < (1 : ℝ)  := by exact Real.zero_lt_one
    exact  lt_of_lt_of_le ha i3
  have i2 {a : ℝ} (ha : 0 < a) : 0 < ((s₁.sup B.toSeminormFamily) x + a)⁻¹ := by
    exact Right.inv_pos.mpr (i1 ha)
  have e3 {a : ℝ} (ha : 0 < a) :
      (s₁.sup B.toSeminormFamily) (((r * ((s₁.sup B.toSeminormFamily) x + a)⁻¹) : 𝕜) • x) < r := by
    rw [SeminormClass.map_smul_eq_mul]
    rw [norm_mul]
    rw [norm_algebraMap', Real.norm_eq_abs]
    rw [abs_eq_self.mpr (le_of_lt hr1)]
    rw [norm_algebraMap', norm_inv]
    rw [mul_assoc]
    conv_rhs => rw [← mul_one r]
    rw [mul_lt_mul_left hr1]
    rw [inv_mul_lt_one₀]
    rw [Real.norm_eq_abs]
    rw [abs_eq_self.mpr (le_of_lt (i1 ha))]
    rw [lt_add_iff_pos_right]
    exact ha
    rw [Real.norm_eq_abs, abs_pos]
    apply (ne_of_lt _).symm
    exact i1 ha
  have e4 {a : ℝ} (ha : 0 < a) :
      ‖f (((r * ((s₁.sup B.toSeminormFamily) x + a)⁻¹) : 𝕜) • x)‖ < 1 := by
    apply e1
    exact e3 ha
  have e5 {a : ℝ} (ha : 0 < a) : ‖f x‖ < r⁻¹ * ((s₁.sup B.toSeminormFamily) x + a) := by
    --unfold y at e4
    simp_rw [map_smul, norm_smul, norm_mul] at e4
    rw [norm_algebraMap'] at e4
    --simp_rw [norm_inv] at e4
    simp_rw [norm_algebraMap', Real.norm_eq_abs] at e4
    rw [abs_eq_self.mpr (le_of_lt hr1)] at e4
    --rw [abs_eq_self.mpr (le_of_lt (i2 ha))] at e4
    --
    rw [← inv_mul_lt_iff₀]
    simp
    rw [← inv_mul_lt_one₀]
    rw [← mul_assoc]
    rw [mul_comm _ r]
    --simp_rw [Real.norm_eq_abs] at e4
    --rw [abs_eq_self.mpr (le_of_lt i1)] at e4
    rw [← abs_eq_self.mpr (le_of_lt (i2 ha))]
    apply e4 ha
    exact i1 ha
    exact Right.inv_pos.mpr hr1
  have e6 {a : ℝ} (ha : 0 < a) : r * ‖f x‖ < (s₁.sup B.toSeminormFamily) x + a := by
    exact (lt_inv_mul_iff₀ hr1).mp (e5 ha)
  have e7 : r * ‖f x‖ ≤ (s₁.sup B.toSeminormFamily) x := by
    apply le_of_forall_pos_lt_add'
    exact fun ε a ↦ e6 a
  have e8 : ‖f x‖ ≤ r⁻¹ * ((s₁.sup B.toSeminormFamily) x) := by
    exact (le_inv_mul_iff₀' hr1).mpr e7
  exact e8

lemma test5 : ∃ (s₁ : Finset F),
    ↑f ∈ Submodule.span 𝕜 (Set.range (ContinuousLinearMap.toLinearMap₁₂
      (WeakBilin.eval B) ∘ Subtype.val : s₁ → WeakBilin B →ₗ[𝕜] 𝕜)) := by
  obtain ⟨s,hS⟩ := isBounded_of_Continuous B f (Fin.last 0)
  --simp at hs
  exact ⟨s, functional_mem_span_iff'.mpr hS⟩

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
