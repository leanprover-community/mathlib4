/-
Copyright (c) 2025 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/

import Mathlib.Analysis.LocallyConvex.Polar
import Mathlib.Analysis.LocallyConvex.AbsConvex
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.LinearAlgebra.Dual.Lemmas

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

theorem functional_mem_span_iff (s : Finset F) (f : E →ₗ[𝕜] 𝕜) :
    f ∈ Submodule.span 𝕜 (Set.range (B.flip ∘ Subtype.val : s → E →ₗ[𝕜] 𝕜)) ↔
    ∃ γ, ∀ (x : E), ‖f x‖ ≤ γ * ((s.sup B.toSeminormFamily) x) := by
  constructor
  · intro h
    rw [← Set.image_univ, Finsupp.mem_span_image_iff_linearCombination] at h
    obtain ⟨l, hl1, hl2⟩ := h
    use (l.sum fun i d ↦ ‖d‖)
    intro x
    rw [← hl2, Finsupp.linearCombination_apply, finsupp_sum_apply,
      (Finsupp.sum_mul ((s.sup B.toSeminormFamily) x) l)]
    have e4' (i : s) : (B.toSeminormFamily i) x ≤ (s.sup B.toSeminormFamily) x :=
      Seminorm.le_finset_sup_apply (Finset.coe_mem i)
    have e4 (d : 𝕜) (i : s) :
        ‖d * ((B.flip ∘ Subtype.val) i) x‖ ≤ ‖d‖ * ((s.sup B.toSeminormFamily) x) := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (e4' i) (norm_nonneg d)
    have e6 : (l.sum fun i d ↦ ‖d * ((B.flip ∘ Subtype.val) i) x‖) ≤
        (l.sum fun i d ↦ (‖d‖ * ((s.sup B.toSeminormFamily) x))) :=
      Finsupp.sum_le_sum (α := 𝕜) (β := ℝ) (fun i _ => e4 (l i) i)
    apply le_trans (norm_sum_le _ _)
    exact (le_trans e6 (Preorder.le_refl (l.sum fun i d ↦ ‖d‖ * (s.sup B.toSeminormFamily) x)))
  · intro ⟨γ, hγ⟩
    apply mem_span_of_iInf_ker_le_ker
    intro x hx
    rw [mem_ker, ← norm_le_zero_iff]
    convert (hγ x)
    rw [Submodule.mem_iInf, Subtype.forall] at hx
    have e1 : (s.sup B.toSeminormFamily) x = 0 := by
      rw [le_antisymm_iff]
      constructor
      · apply Seminorm.finset_sup_apply_le (Preorder.le_refl 0)
        intro i his
        rw [toSeminormFamily_apply, norm_le_zero_iff]
        exact hx _ his
      · exact apply_nonneg (s.sup B.toSeminormFamily) x
    simp_all only [mul_zero]

/-

lemma test5 : ∃ (s₁ : Finset F), ↑f ∈ Submodule.span 𝕜 (Set.range (B.mL s₁)) := by
  obtain ⟨s₁, hs⟩ := test4 B f
  use s₁
  apply mem_span_of_iInf_ker_le_ker (ι := s₁) (L := (mL B s₁)) (K := f.toLinearMap)
  intro x hx
  simp at hx
  simp at hs
  obtain ⟨r, hr1, hr2⟩ := hs
  have hr : 0 ≤ r := by exact le_of_lt hr1

  --have ex : x ∈

  have e1 : ‖f x‖ ≤ r • ((s₁.sup B.toSeminormFamily) x) := by
    --simp_all only [one_div]
    let a := (r+1) * ((s₁.sup B.toSeminormFamily) x)

    have c1 : a = 0 ∨ a ≠ 0 := eq_or_ne a 0

    rcases c1 with h1 | h2
    · have c2 : (s₁.sup B.toSeminormFamily) x = 0 := by
        by_contra hn
        simp at hn
        simp [a] at h1
        have rz : 0 < r + 1  := by
          rw [← zero_add 0]
          apply add_lt_add hr1
          exact Real.zero_lt_one
        have rz2 : 0 ≠ r + 1 := by
          exact ne_of_lt rz
        aesop
      rw [c2]
      simp
      have ex1 : x ∈ (s₁.sup B.toSeminormFamily).ball 0 r := by
        rw [Seminorm.mem_ball, sub_zero]
        rw [← c2] at hr1
        exact hr1
      have ex2 (k : 𝕜) : k • x ∈ (s₁.sup B.toSeminormFamily).ball 0 r := by
        rw [Seminorm.mem_ball, sub_zero]
        rw [SeminormClass.map_smul_eq_mul]
        have fibble : ‖k‖ * (s₁.sup B.toSeminormFamily) x = ‖k‖ * 0 := by
          rw [c2]
        rw [mul_zero] at fibble
        rw [← fibble] at hr1
        exact hr1
      --simp_all
      --have ex3 (k : 𝕜) : f k • x



    let y := a⁻¹ • x
    /-
    have i1 (fi : s₁) : (⟨‖(WeakBilin.eval B) fi x‖, norm_nonneg _⟩ : NNReal) ≤
        s₁.sup (α := NNReal)  (fun fi  => ⟨‖(WeakBilin.eval B) fi x‖, norm_nonneg _⟩) := by
      --norm_cast
      apply Finset.le_sup
        (f := (fun fi  => (⟨‖(WeakBilin.eval B) fi x‖, norm_nonneg _⟩): : NNReal)) fi.prop
    -/

    have e2 : y ∈ (s₁.sup B.toSeminormFamily).ball 0 r⁻¹ := by
      rw [Seminorm.mem_ball, sub_zero]
      simp only [y]
      have a1 : 0 ≤ a⁻¹ := by
        simp_all only [mul_inv_rev, a]
        rw [mul_nonneg_iff_left_nonneg_of_pos]
        rw [inv_nonneg]
        exact apply_nonneg (s₁.sup fun fi ↦ (B.flip fi).toSeminorm) x
        rw [inv_pos]



        sorry
      simp_all only [mul_inv_rev, Seminorm.mem_ball, sub_zero, y, a]
      sorry
      --simp_all only [NNReal.coe_inv, Seminorm.mem_ball, sub_zero, y]





      sorry


    sorry



-/




/-
See
- Conway V Theorem 1.3 on p108
     - III 2.1 on p68 - continuous iff cont at 0 iff cont at a point iff scalar bound
     - III 5.3 on p54 - a linear funtional is continuous iff the kernel is closed (a iff d in 3.1)
     - Mathlib/Analysis/Normed/Group/Hom.lean:theorem isClosed_ker
- Bourbaki TVS II.43
- Rudin Theorem 3.10
lemma dualEmbedding_isSurjective : Function.Surjective (WeakBilin.eval B) := by
  rw [Function.Surjective]
  intro f₁
  sorry
-/

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
