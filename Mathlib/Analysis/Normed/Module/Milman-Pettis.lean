/-
Copyright (c) 2025 Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio
-/

import Mathlib.Analysis.Convex.Uniform
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Group.Pointwise
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.Dual

open scoped Topology NNReal

section opNorm

namespace ContinuousLinearMap

variable {𝕜 𝕜' E F : Type*}
variable [NormedAddCommGroup E] [SeminormedAddCommGroup F]
variable [DenselyNormedField 𝕜] [NormedAlgebra ℝ 𝕜] [NontriviallyNormedField 𝕜']
variable [NormedSpace 𝕜 E] [NormedSpace 𝕜' F] {σ₁₂ : 𝕜 →+* 𝕜'} [RingHomIsometric σ₁₂]

theorem exists_nnorm_eq_one_lt_apply_of_lt_opNorm (f : E →SL[σ₁₂] F) {r : ℝ≥0} (hr : r < ‖f‖) :
    ∃ x : E, ‖x‖ = 1 ∧ r < ‖f x‖ := by
  obtain ⟨x, hlt, hr⟩ := exists_lt_apply_of_lt_opNorm f hr
  obtain rfl | hx0 := eq_zero_or_norm_pos x
  · simp only [map_zero, norm_zero] at hr
    exact (not_lt_of_ge r.2 hr).elim
  use algebraMap ℝ 𝕜 ‖x‖⁻¹ • x
  suffices r < ‖x‖⁻¹ * ‖f x‖ by simpa [norm_smul, inv_mul_cancel₀ hx0.ne'] using this
  calc
    r < 1⁻¹ * ‖f x‖ := by simpa
    _ < ‖x‖⁻¹ * ‖f x‖ := by
      gcongr; exact lt_of_le_of_lt r.2 hr

theorem exists_nnorm_eq_one_lt_apply_of_lt_opNorm' [Nontrivial E]
    (f : E →SL[σ₁₂] F) {r : ℝ} (hr : r < ‖f‖) :
    ∃ x : E, ‖x‖ = 1 ∧ r < ‖f x‖ := by
  by_cases hr₀ : r < 0
  · obtain ⟨y, hy⟩ : ∃ x : E, x ≠ 0 := exists_ne 0
    refine ⟨algebraMap ℝ 𝕜 ‖y‖⁻¹ • y, ?_, lt_of_lt_of_le hr₀ <| norm_nonneg _⟩
    calc ‖algebraMap ℝ 𝕜 ‖y‖⁻¹ • y‖ = ‖algebraMap ℝ 𝕜 ‖y‖⁻¹‖ * ‖y‖ := by rw [norm_smul]
                                  _ = ‖y‖⁻¹ * ‖y‖ := by simp_all [norm_inv]
                                  _ = 1 := by rw [inv_mul_cancel₀]; rwa [norm_ne_zero_iff]
  obtain ⟨x, hlt, hr⟩ := exists_lt_apply_of_lt_opNorm f hr
  obtain rfl | hx0 := eq_zero_or_norm_pos x
  · simp only [map_zero, norm_zero] at hr
    exact (hr₀ hr).elim
  use algebraMap ℝ 𝕜 ‖x‖⁻¹ • x
  suffices r < ‖x‖⁻¹ * ‖f x‖ by simpa [norm_smul, inv_mul_cancel₀ hx0.ne'] using this
  calc
    r < 1⁻¹ * ‖f x‖ := by simpa
    _ < ‖x‖⁻¹ * ‖f x‖ := by
      gcongr; exact lt_of_le_of_lt (le_of_not_gt hr₀) hr

instance [Nontrivial E] : Nontrivial (StrongDual 𝕜 E) := sorry

end ContinuousLinearMap

end opNorm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Metric NormedSpace Function ContinuousLinearMap Pointwise

local notation3 "E**" => StrongDual ℝ (StrongDual ℝ E)
local notation3 "𝒰" => (inclusionInDoubleDual ℝ E) '' closedBall 0 1

/- Goldstine lemma (see Brezis, Chapter § 3.5, Lemma 3.4) says that the unit ball in the double
dual of a Banach space (**FAE: I suspect completeness is not needed) ** is the closure, with respect
to the weak topology `σ(E**, E*)` induced by the canonical pairing `E** × E* → ℝ`, of the image of
the unit ball in  `E`. Observe that, for any topological `𝕜`-module `M`, `strongDualPairing 𝕜 M` is
the pairing whose *first* variable is in `M*` and the second is in `M`. -/
lemma goldstine : closure (X := (WeakBilin (strongDualPairing ℝ (StrongDual ℝ E))))
  (inclusionInDoubleDual ℝ E '' (closedBall 0 1)) = closedBall (0 : E**) 1 := by sorry

lemma surjective_iff_ball_le_range {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E →L[ℝ] F) : Surjective f ↔ ∃ s : Set F, ∃ ρ > 0, sphere 0 ρ ≤ Set.range f := by
  refine ⟨fun _ ↦ ⟨Set.univ, 1, by simp_all⟩, fun ⟨s, ρ, ρ_pos, sphere_le⟩ z ↦ ?_⟩
  by_cases hz : z = 0
  · exact ⟨0, by simp_all⟩
  set α := ‖z‖ with hα_def
  have hα : α ≠ 0 := by
    rwa [norm_ne_zero_iff]
  set y := (ρ * α⁻¹) • z with hy_def
  have hy : y ∈ sphere 0 ρ := by
    simp
    calc ‖y‖ = ‖(ρ * α⁻¹) • z‖  := by rw [hy_def]
           _ = |ρ * α⁻¹| * ‖z‖ := by rw [norm_smul, Real.norm_eq_abs]
           _ = |ρ * α⁻¹| * |α| := by simp [hα_def]
           _ = ρ := by
            simpa [← abs_mul, mul_assoc, inv_mul_cancel₀ hα] using le_of_lt ρ_pos
  obtain ⟨x, hx⟩ := sphere_le hy
  use (ρ⁻¹ * α) • x
  rw [map_smul, hx, hy_def, ← smul_assoc, smul_eq_mul, show (ρ⁻¹ * α * (ρ * α⁻¹)) = 1 by grind,
    one_smul]

lemma exists_sub_one_lt [Nontrivial E] {ξ : E**} {δ : ℝ} (hδ : 0 < δ) (h : ‖ξ‖ = 1) :
    ∃ φ : StrongDual ℝ E, ‖φ‖ = 1 ∧ |ξ φ - 1| < δ := by
  obtain ⟨φ, hφ_eq, hφ_lt⟩ := exists_nnorm_eq_one_lt_apply_of_lt_opNorm'
    (f := ξ) (r := 1 - δ) (by grind)
  replace hφ_lt : 1 - δ < |ξ φ| := by rwa [Real.norm_eq_abs] at hφ_lt
  wlog h_pos : 0 ≤ ξ φ generalizing φ
  · exact this (-φ) (by rw [opNorm_neg, hφ_eq]) (by simpa)
      (by simpa only [map_neg, Left.nonneg_neg_iff] using le_of_not_ge h_pos)
  have : ξ φ ≤ 1 := by
    apply le_of_abs_le
    grw [← Real.norm_eq_abs, le_opNorm ξ φ, h, hφ_eq, one_mul]
  refine ⟨φ, hφ_eq, ?_⟩
  rw [← abs_neg, neg_sub]
  rw [abs_eq_self.mpr (by grind)] at ⊢ hφ_lt
  rwa [sub_lt_comm]

set_option linter.style.commandStart false

example (A : Type*) [TopologicalSpace A] (s : Set A) (a : A) :
    a ∈ closure s ↔ ∀ t, s ⊆ t ∧ IsClosed t → a ∈ t := by
  dsimp [closure]
  aesop

/- Milman-Pettis theorem: every uniformly convex Banach (**FAE: Complete Needed?**) space is\
reflexive. For the time being, we state this property as the surjectivity of
`inclusionInDoubleDual`,
but it must be proven that for normed space this is equivalent to `includionInDoubleDual` being
a homeomorphism. -/
theorem surjective_of_uniformConvexSpace [UniformConvexSpace E] :
    Surjective (inclusionInDoubleDual ℝ E) := by
  by_cases hE : ¬ Nontrivial E
  · rw [not_nontrivial_iff_subsingleton] at hE
    apply surjective_to_subsingleton
  simp at hE
  let X := WeakDual ℝ (StrongDual ℝ E) -- `E**` with the weak topology
  let 𝒯 : TopologicalSpace X := inferInstance -- the weak topology on `E**`: can use IsOpen[T] **FAE: Choose!**
  rw [surjective_iff_ball_le_range]
  refine ⟨sphere 0 1, _, zero_lt_one, ?_⟩
  intro ξ hξ
  have hξ_norm : ‖ξ‖ = 1 := by rwa [← mem_sphere_zero_iff_norm]
  have hξ_mem {V : Set _} (hV_mem : ξ ∈ V) (hV : IsOpen[𝒯] V) : ξ ∈ closure[𝒯] (V ∩ 𝒰) := by
    apply hV.inter_closure <| Set.mem_inter hV_mem _
    rw [goldstine]
    apply sphere_subset_closedBall hξ
  set ε := infDist ξ 𝒰 with ε_def
  by_cases ε_pos : 0 = ε
  · sorry
  replace ε_pos : 0 < ε := lt_of_le_of_ne infDist_nonneg ε_pos
  obtain ⟨δ, hδ_pos, hδ_dist⟩ := exists_forall_closed_ball_dist_add_le_two_sub E ε_pos
  obtain ⟨φ, hφ_norm, hφ_lt⟩ := exists_sub_one_lt (half_pos hδ_pos) hξ_norm
  set V := {x : E** | |x φ - 1| < δ/2} with hV_def
  have hV_dist {x x' : E**} (hx : x ∈ V ∩ 𝒰) (hx' : x' ∈ V ∩ 𝒰) : ‖x - x'‖ < ε/2 := sorry
  have hV_open : IsOpen[𝒯] V := by
    rw [hV_def]
    convert @Continuous.isOpen_preimage (X := X) (Y := ℝ) _ _ (fun x : E** ↦ |x φ - 1|)
      (s := ball 0 (δ / 2)) _ isOpen_ball
    · ext
      simp_all only [mem_sphere_iff_norm, sub_zero, Set.mem_inter_iff, Set.mem_setOf_eq,
        dist_zero_right, and_imp, Set.mem_preimage, mem_ball, Real.norm_eq_abs, abs_abs]
    · exact Continuous.comp (X := X) (f := fun x : E** ↦ x φ) (g := fun (x : ℝ) ↦ |x - 1|)
        (by fun_prop) <| WeakBilin.eval_continuous (strongDualPairing ℝ (StrongDual ℝ E)) _
  obtain ⟨y, hy⟩ : (V ∩ 𝒰).Nonempty := by
    rw [← closure_nonempty_iff (X := X)]
    exact ⟨ξ, hξ_mem hφ_lt hV_open⟩
  have subset : V ∩ 𝒰 ⊆ ({y} + closedBall 0 (ε/2) : (Set E**)) := sorry
  have clSub : IsClosed[𝒯] ({y} + closedBall 0 (ε/2) : (Set E**)) := sorry
  have trueEnd : infDist ξ (V ∩ 𝒰) ≤ ε/2 := by -- migliorare rimpiazzando` V∩𝒰₁` con 𝒰₁
    apply (infDist_le_dist_of_mem hy).trans
    specialize hξ_mem hφ_lt hV_open
    apply hξ_mem
    simp
    constructor
    · convert clSub
      simp only [singleton_add_closedBall, add_zero]
      rfl
    · convert subset
      simp
      rfl
  have := (ε_def.symm ▸ infDist_le_infDist_of_subset Set.inter_subset_right ⟨y, hy⟩).trans trueEnd
  exact not_lt_of_ge this (half_lt_self ε_pos)|>.elim

lemma exists_open_diam_inter_lt [UniformConvexSpace E] {ξ : E**} {ε : ℝ} (hε : 0 < ε)
    (hξ : ξ ∈ closedBall 0 1) :
    -- (letI 𝒯 : TopologicalSpace (WeakDual ℝ (StrongDual ℝ E)) :=
    ∃ W : Set E**, IsOpen (X := WeakDual ℝ (StrongDual ℝ E))
      W ∧ ξ ∈ W ∧ diam (W ∩ 𝒰) < ε := by sorry


example (s : Set (WeakDual ℝ (StrongDual ℝ E)))
    (hsB : s ⊆ ((closedBall (0 : E**) 1) : Set (E**))) :
    closure (X := (WeakDual ℝ (StrongDual ℝ E))) s ⊆ ((closedBall (0 : E**) 1) : Set (E**)) := by
  have h1 : s ⊆ WeakDual.toStrongDual ⁻¹' (((closedBall (0 : E**) 1) : Set (E**))) := by
    exact hsB
  have h2 : IsClosed (X := WeakDual ℝ (StrongDual ℝ E))
    (WeakDual.toStrongDual ⁻¹' (((closedBall (0 : E**) 1) : Set (E**)))) := by
    apply WeakDual.isClosed_closedBall
  apply closure_minimal hsB h2

-- (hb : IsBounded (StrongDual.toWeakDual ⁻¹' s))

example (s : Set (WeakDual ℝ (StrongDual ℝ E)))
    (hB : Bornology.IsBounded (StrongDual.toWeakDual ⁻¹' s)) :
    closure (X := (WeakDual ℝ (StrongDual ℝ E))) s ⊆ closure (X := E**) s := by sorry
  -- have h1 : s ⊆ WeakDual.toStrongDual ⁻¹' (((closedBall (0 : E**) 1) : Set (E**))) := by
  --   exact hsB
  -- have h2 : IsClosed (X := WeakDual ℝ (StrongDual ℝ E))
  --   (WeakDual.toStrongDual ⁻¹' (((closedBall (0 : E**) 1) : Set (E**)))) := by
  --   apply WeakDual.isClosed_closedBall
  -- apply closure_minimal hsB h2

lemma diam_lt_iff_subset {X : Type*} [MetricSpace X] {s : Set X} {ε : ℝ} (hε : 0 < ε) :
    diam s < ε ↔ ∃ c ρ, ρ < ε ∧ s ⊆ closedBall c ρ := by sorry
  -- refine ⟨fun h ↦ ?_, fun ⟨c, ρ, hρ₀, hρ₁, hc⟩ ↦ ?_⟩
  -- · sorry
  -- · sorry



lemma diam_WeakClosure_le_of_diam_le {s : Set E**} {ε : ℝ} (hε : 0 < ε) (hs : diam s < ε) :
    letI 𝒯 : TopologicalSpace (WeakDual ℝ (StrongDual ℝ E)) := inferInstance
    diam (WeakDual.toStrongDual '' (closure[𝒯] s)) < ε := by
  let 𝒯 : TopologicalSpace (WeakDual ℝ (StrongDual ℝ E)) := inferInstance
  obtain ⟨c, ρ, hρ, hc⟩ := (diam_lt_iff_subset hε).mp hs
  have : WeakDual.toStrongDual '' closure[𝒯] s ⊆ closedBall c ρ := by
    simp only [WeakDual.coe_toStrongDual, Set.image_id']
    refine closure_minimal hc ?_
    apply WeakDual.isClosed_closedBall
  apply lt_of_le_of_lt (diam_mono this isBounded_closedBall)
  · rw [diam_lt_iff_subset hε]
    refine ⟨c, ρ, hρ, by simp⟩

lemma WeakClosure_subset_closedBall {s : Set E**} {c : E**} {ε : ℝ} (hε : 0 < ε)
    (hs : s ⊆ closedBall c ε) :
    letI 𝒯 : TopologicalSpace (WeakDual ℝ (StrongDual ℝ E)) := inferInstance
    (WeakDual.toStrongDual '' (closure[𝒯] s)) ⊆ closedBall c ε := by sorry
  -- let 𝒯 : TopologicalSpace (WeakDual ℝ (StrongDual ℝ E)) := inferInstance
  -- obtain ⟨c, ρ, hρ, hc⟩ := (diam_lt_iff_subset hε).mp hs
  -- have : WeakDual.toStrongDual '' closure[𝒯] s ⊆ closedBall c ρ := by
  --   simp only [WeakDual.coe_toStrongDual, Set.image_id']
  --   refine closure_minimal hc ?_
  --   apply WeakDual.isClosed_closedBall
  -- apply lt_of_le_of_lt (diam_mono this isBounded_closedBall)
  -- · rw [diam_lt_iff_subset hε]
  --   refine ⟨c, ρ, hρ, by simp⟩


-- lemma closure_le_closure (s : Set E**) :
--     WeakDual.toStrongDual '' (closure (X := WeakDual ℝ (StrongDual ℝ E)) s) ⊆
--       closure (s) := by
--     let 𝒯 : TopologicalSpace (WeakDual ℝ (StrongDual ℝ E)) := inferInstance
--     have ff (K : Set (WeakDual ℝ (StrongDual ℝ E))) (h : IsClosed[𝒯] K) : Bornology.IsBounded
--       (StrongDual.toWeakDual ⁻¹' K) := sorry
--     rw [closure, closure]
--     have := Set.image_sInter_subset (f := WeakDual.toStrongDual (𝕜 := ℝ) (E := StrongDual ℝ E))
--       (S := {t | IsClosed[𝒯] t ∧ s ⊆ t})
--     apply subset_trans this
--     rw [Set.sInter_eq_biInter]
--     apply Set.iInter_mono''
--     intro S x hx
--     rw [Set.mem_iInter] at hx ⊢
--     simp only [Set.mem_setOf_eq, WeakDual.coe_toStrongDual, Set.image_id', and_imp] at hx
--     intro ⟨hS_cl, hS_s⟩
--     apply hx _ hS_s
--     specialize ff S
    -- have := @WeakDual.isClosed_image_coe_of_bounded_of_closed ℝ _ (StrongDual ℝ E) _ _
    --   S


    --
    -- intro j
    -- use j







  -- have uno := @WeakBilin.isEmbedding ℝ E** (StrongDual ℝ E) _ _ _ _ _ _
  --       (strongDualPairing ℝ (StrongDual ℝ E)) ?_
  -- have due := uno.closure_eq_preimage_closure_image s
  -- rw [due]

  --     set ι : (WeakDual ℝ (StrongDual ℝ E)) → E** := fun x ↦ x with ι_def
  --     have hι : Topology.IsEmbedding ι := by
  --       rw [ι_def]
  --       convert uno
  --       simp
        -- exact?

      -- (𝕜 := ℝ) (E := StrongDual ℝ E) (F := (StrongDual ℝ E)
      --   (B := strongDualPairing ℝ (StrongDual ℝ E))
        -- (B := strongDualPairing ℝ (StrongDual ℝ E))
      -- apply WeakSpace.closure_subset (𝕜 := ℝ) (E := E**) (V := W ∩ 𝒰)
      -- · convert hx_mem
      --   sorry
      -- ·
      -- -- have := @Convex.toWeakSpace_closure ℝ E** _ _ _ _ _ _ _ _ _ (W ∩ 𝒰) ?_
      -- have : closure ((toWeakSpace ℝ E**) '' (W ∩ 𝒰)) = closure[𝒯] (W ∩ 𝒰) := by
      --   congr
      --   · --simp [𝒯, WeakSpace, WeakBilin, TopologicalSpace.Pi]
      --     -- rfl
      --   · ext x
      --     refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
      --     · simp at hx
      --       sorry
      --     · simp at ⊢ hx
      --       sorry




lemma surjective [UniformConvexSpace E] : closure 𝒰 = closedBall 0 1 := by
  let 𝒯 : TopologicalSpace <| WeakDual ℝ (StrongDual ℝ E) := inferInstance
  -- `WeakDual (StrongDual ℝ E)` is `E**` endowed with the weak-* topology
  ext x
  rw [Metric.mem_closure_iff]
  refine ⟨fun h ↦ ?_, fun hx ↦ ?_⟩
  · rw [← closure_closedBall, Metric.mem_closure_iff] -- use a lemma saying that the image of dual is closed
    intro ε hε
    obtain ⟨b, hb_mem, hb_lt⟩ := h ε hε
    refine ⟨b, ?_, hb_lt⟩
    obtain ⟨c, hc_le, hc_eq⟩ := by simpa using hb_mem
    grw [← hc_eq, mem_closedBall, dist_zero_right, double_dual_bound, hc_le]
  · intro ε hε
    obtain ⟨W, hW, x_mem, h_diam⟩ := exists_open_diam_inter_lt hε hx
    have hx_mem : x ∈ closure[𝒯] (W ∩ 𝒰) := by
      apply hW.inter_closure <| Set.mem_inter x_mem _
      rwa [goldstine]
    obtain ⟨y, y_mem⟩ : (W ∩ 𝒰).Nonempty := by
      rw [← closure_nonempty_iff (X := WeakDual ℝ (StrongDual ℝ E))]
      use x
    -- replace hx_mem : x ∈ closure (W ∩ 𝒰) := by--closure_le_closure hx_mem
      -- have := @WeakDual.isClosed_image_coe_of_bounded_of_closed ℝ _ (StrongDual ℝ E) _ _
      --   (closure[𝒯] (W ∩ 𝒰)) ?_ isClosed_closure
      -- simp at this
      -- have also := @closure_minimal

    refine ⟨y, y_mem.2, ?_⟩
    replace h_diam := diam_WeakClosure_le_of_diam_le hε h_diam
    simp only [WeakDual.coe_toStrongDual, Set.image_id'] at h_diam
    apply lt_of_le_of_lt (dist_le_diam_of_mem _ hx_mem _) h_diam
    · rw [Metric.isBounded_iff_subset_ball]
      use 1
      -- use (0 : E**)

      -- refine ⟨1, Set.inter_subset_right.trans (fun _ ha ↦ ?_)⟩
      --apply IsCompact.isBounded (α := (StrongDual ℝ E))
      -- convert WeakDual.isCompact_of_bounded_of_closed (𝕜 := ℝ) (E := (StrongDual ℝ E))
      --   (s := closure[𝒯] (W ∩ 𝒰)) ?_ ?_

      -- apply Bornology.IsBounded.closure (α := WeakDual ℝ (StrongDual ℝ E))
      -- rw [Metric.isBounded_iff_subset_closedBall 0]
      -- refine ⟨1, Set.inter_subset_right.trans (fun _ ha ↦ ?_)⟩
      -- obtain ⟨_, hx_norm, hxa⟩ := by simpa using ha
      -- grw [← hxa, mem_closedBall_zero_iff, double_dual_bound, hx_norm]
    exact subset_closure (X := WeakDual ℝ (StrongDual ℝ E)) y_mem



    -- ·
    -- apply lt_of_le_of_lt (dist_le_diam_of_mem _ hx_mem (subset_closure y_mem))
    --   (by rwa [diam_closure])
    -- apply Bornology.IsBounded.closure
    -- rw [Metric.isBounded_iff_subset_closedBall 0]
    -- refine ⟨1, Set.inter_subset_right.trans (fun _ ha ↦ ?_)⟩
    -- obtain ⟨_, hx_norm, hxa⟩ := by simpa using ha
    -- grw [← hxa, mem_closedBall_zero_iff, double_dual_bound, hx_norm]


/- Milman-Pettis theorem: every uniformly convex Banach (**FAE: Complete Needed?**) space is\
reflexive. For the time being, we state this property as the surjectivity of
`inclusionInDoubleDual`,
but it must be proven that for normed space this is equivalent to `includionInDoubleDual` being
a homeomorphism. -/
-- theorem surjective_of_uniformConvexSpace' [UniformConvexSpace E] :
--     Surjective (inclusionInDoubleDual ℝ E) := by
