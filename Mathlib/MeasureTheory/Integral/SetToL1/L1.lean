/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov, Sébastien Gouëzel, Rémy Degenne
-/
module

public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.MeasureTheory.Integral.SetToL1.SimpleFunc

/-!
# Extension of set functions to L¹

Starting from the continuous linear map on integrable simple functions constructed in
`Mathlib.MeasureTheory.Integral.SetToL1.SimpleFunc`, this file extends a dominated
finitely-measure-additive set function to all of L¹. The main definition is
`MeasureTheory.L1.setToL1`, together with its uniqueness, algebraic and order properties, norm
bounds, and continuity.
-/

@[expose] public section

noncomputable section

open scoped Topology NNReal

open Set Filter ENNReal

namespace MeasureTheory

variable {α E F 𝕜 : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {m : MeasurableSpace α} {μ : Measure α}

namespace L1

open Lp.simpleFunc Lp

open L1.SimpleFunc

section SetToL1

attribute [local instance] Lp.simpleFunc.module

attribute [local instance] Lp.simpleFunc.normedSpace

variable (𝕜) [NormedRing 𝕜] [Module 𝕜 E] [Module 𝕜 F] [IsBoundedSMul 𝕜 E] [IsBoundedSMul 𝕜 F]
  [CompleteSpace F] {T T' T'' : Set α → E →L[ℝ] F} {C C' C'' : ℝ}

/-- Extend `Set α → (E →L[ℝ] F)` to `(α →₁[μ] E) →L[𝕜] F`. -/
def setToL1' (hT : DominatedFinMeasAdditive μ T C)
    (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x) : (α →₁[μ] E) →L[𝕜] F :=
  (setToL1SCLM' α E 𝕜 μ hT h_smul).extend (coeToLp α E 𝕜)

theorem setToL1'_eq_setToL1SCLM (hT : DominatedFinMeasAdditive μ T C)
    (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x) (f : α →₁ₛ[μ] E) :
    setToL1' 𝕜 hT h_smul f = setToL1SCLM α E μ hT f := by
  apply ContinuousLinearMap.extend_eq _ _ simpleFunc.isUniformInducing
  · exact simpleFunc.denseRange one_ne_top

@[simp]
theorem setToL1'_apply_coeToLp (hT : DominatedFinMeasAdditive μ T C)
    (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x) (f : α →₁ₛ[μ] E) :
    setToL1' 𝕜 hT h_smul (coeToLp α E ℝ f) = setToL1SCLM α E μ hT f :=
  setToL1'_eq_setToL1SCLM 𝕜 hT h_smul f

variable {𝕜}

/-- Extend `Set α → E →L[ℝ] F` to `(α →₁[μ] E) →L[ℝ] F`. -/
def setToL1 (hT : DominatedFinMeasAdditive μ T C) : (α →₁[μ] E) →L[ℝ] F :=
  (setToL1SCLM α E μ hT).extend (coeToLp α E ℝ)

theorem setToL1_eq_setToL1SCLM (hT : DominatedFinMeasAdditive μ T C) (f : α →₁ₛ[μ] E) :
    setToL1 hT f = setToL1SCLM α E μ hT f :=
  setToL1'_eq_setToL1SCLM ℝ hT (by simp) _

@[simp]
theorem setToL1_apply_coeToLp (hT : DominatedFinMeasAdditive μ T C) (f : α →₁ₛ[μ] E) :
    setToL1 hT (coeToLp α E ℝ f) = setToL1SCLM α E μ hT f :=
  setToL1_eq_setToL1SCLM hT f

theorem setToL1_unique (hT : DominatedFinMeasAdditive μ T C) {A : (α →₁[μ] E) →L[ℝ] F}
    (hA : ∀ f : α →₁ₛ[μ] E, setToL1SCLM α E μ hT f = A f) (f : α →₁[μ] E) :
    setToL1 hT f = A f := by
  suffices setToL1 hT = A by rw [this]
  apply ContinuousLinearMap.extend_unique
  · exact (simpleFunc.denseRange one_ne_top)
  · exact simpleFunc.isUniformInducing
  ext f
  rw [hA f]
  rfl

theorem setToL1_eq_setToL1' (hT : DominatedFinMeasAdditive μ T C)
    (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x) (f : α →₁[μ] E) :
    setToL1 hT f = setToL1' 𝕜 hT h_smul f := by
  have h₁ : Dense (Set.range (coeToLp α E ℝ)) := simpleFunc.denseRange (μ := μ) one_ne_top
  apply Dense.induction (P := fun f : α →₁[μ] E ↦ (setToL1 hT) f = (setToL1' 𝕜 hT h_smul) f) h₁
  · intro f ⟨f', hf⟩
    simp [← hf]
  · exact isClosed_eq (setToL1 hT).continuous (setToL1' 𝕜 hT h_smul).continuous

@[simp]
theorem setToL1_zero_left (hT : DominatedFinMeasAdditive μ (0 : Set α → E →L[ℝ] F) C)
    (f : α →₁[μ] E) : setToL1 hT f = 0 :=
  setToL1_unique hT (A := 0) (by simp) f

theorem setToL1_zero_left' (hT : DominatedFinMeasAdditive μ T C)
    (h_zero : ∀ s, MeasurableSet s → μ s < ∞ → T s = 0) (f : α →₁[μ] E) : setToL1 hT f = 0 :=
  setToL1_unique hT (A := 0) (by simp [setToL1SCLM_zero_left' hT h_zero]) f

theorem setToL1_congr_left (T T' : Set α → E →L[ℝ] F) {C C' : ℝ}
    (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C') (h : T = T')
    (f : α →₁[μ] E) : setToL1 hT f = setToL1 hT' f := by
  apply setToL1_unique hT (A := setToL1 hT') _ f
  intro f
  suffices setToL1 hT' f = setToL1SCLM α E μ hT f by rw [← this]
  rw [setToL1_eq_setToL1SCLM]
  exact setToL1SCLM_congr_left hT' hT h.symm f

theorem setToL1_congr_left' (T T' : Set α → E →L[ℝ] F) {C C' : ℝ}
    (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C')
    (h : ∀ s, MeasurableSet s → μ s < ∞ → T s = T' s) (f : α →₁[μ] E) :
    setToL1 hT f = setToL1 hT' f := by
  apply setToL1_unique hT (A := setToL1 hT') _ f
  intro f
  suffices setToL1 hT' f = setToL1SCLM α E μ hT f by rw [← this]
  rw [setToL1_eq_setToL1SCLM]
  exact (setToL1SCLM_congr_left' hT hT' h f).symm

theorem setToL1_add_left (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ T' C') (f : α →₁[μ] E) :
    setToL1 (hT.add hT') f = setToL1 hT f + setToL1 hT' f := by
  apply setToL1_unique (hT.add hT') (A := setToL1 hT + setToL1 hT') _ f
  simp [setToL1_eq_setToL1SCLM, setToL1_eq_setToL1SCLM, setToL1SCLM_add_left hT hT']

theorem setToL1_add_left' (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ T' C') (hT'' : DominatedFinMeasAdditive μ T'' C'')
    (h_add : ∀ s, MeasurableSet s → μ s < ∞ → T'' s = T s + T' s) (f : α →₁[μ] E) :
    setToL1 hT'' f = setToL1 hT f + setToL1 hT' f := by
  apply setToL1_unique hT'' (A := setToL1 hT + setToL1 hT') _ f
  simp [setToL1_eq_setToL1SCLM, setToL1_eq_setToL1SCLM, setToL1SCLM_add_left' hT hT' hT'' h_add]

theorem setToL1_smul_left (hT : DominatedFinMeasAdditive μ T C) (c : ℝ) (f : α →₁[μ] E) :
    setToL1 (hT.smul c) f = c • setToL1 hT f := by
  apply setToL1_unique (hT.smul c) (A := c • setToL1 hT) _ f
  simp [setToL1_eq_setToL1SCLM, setToL1SCLM_smul_left c hT]

theorem setToL1_smul_left' (hT : DominatedFinMeasAdditive μ T C)
    (hT' : DominatedFinMeasAdditive μ T' C') (c : ℝ)
    (h_smul : ∀ s, MeasurableSet s → μ s < ∞ → T' s = c • T s) (f : α →₁[μ] E) :
    setToL1 hT' f = c • setToL1 hT f := by
  apply setToL1_unique hT' (A := c • setToL1 hT) _ f
  simp [setToL1_eq_setToL1SCLM, setToL1SCLM_smul_left' c hT hT' h_smul]

theorem setToL1_smul (hT : DominatedFinMeasAdditive μ T C)
    (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x) (c : 𝕜) (f : α →₁[μ] E) :
    setToL1 hT (c • f) = c • setToL1 hT f := by
  rw [setToL1_eq_setToL1' hT h_smul, setToL1_eq_setToL1' hT h_smul]
  exact map_smul _ _ _

theorem setToL1_simpleFunc_indicatorConst (hT : DominatedFinMeasAdditive μ T C) {s : Set α}
    (hs : MeasurableSet s) (hμs : μ s < ∞) (x : E) :
    setToL1 hT (simpleFunc.indicatorConst 1 hs hμs.ne x) = T s x := by
  rw [setToL1_eq_setToL1SCLM]
  exact setToL1S_indicatorConst (fun s => hT.eq_zero_of_measure_zero) hT.1 hs hμs x

theorem setToL1_indicatorConstLp (hT : DominatedFinMeasAdditive μ T C) {s : Set α}
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : E) :
    setToL1 hT (indicatorConstLp 1 hs hμs x) = T s x := by
  rw [← Lp.simpleFunc.coe_indicatorConst hs hμs x]
  exact setToL1_simpleFunc_indicatorConst hT hs hμs.lt_top x

theorem setToL1_const [IsFiniteMeasure μ] (hT : DominatedFinMeasAdditive μ T C) (x : E) :
    setToL1 hT (indicatorConstLp 1 MeasurableSet.univ (measure_ne_top _ _) x) = T univ x :=
  setToL1_indicatorConstLp hT MeasurableSet.univ (measure_ne_top _ _) x

section Order

-- Naming chosen to match the corresponding declarations in `SimpleFunc.lean`.
variable {G' G'' : Type*}
  [NormedAddCommGroup G'] [PartialOrder G'] [NormedSpace ℝ G']
  [NormedAddCommGroup G''] [PartialOrder G''] [IsOrderedAddMonoid G'']
  [NormedSpace ℝ G''] [CompleteSpace G'']

theorem setToL1_mono_left' [OrderClosedTopology G''] {T T' : Set α → E →L[ℝ] G''} {C C' : ℝ}
    (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C')
    (hTT' : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x, T s x ≤ T' s x) (f : α →₁[μ] E) :
    setToL1 hT f ≤ setToL1 hT' f := by
  induction f using Lp.induction (hp_ne_top := one_ne_top) with
  | @indicatorConst c s hs hμs =>
    rw [setToL1_simpleFunc_indicatorConst hT hs hμs, setToL1_simpleFunc_indicatorConst hT' hs hμs]
    exact hTT' s hs hμs c
  | @add f g hf hg _ hf_le hg_le =>
    rw [(setToL1 hT).map_add, (setToL1 hT').map_add]
    exact add_le_add hf_le hg_le
  | isClosed => exact isClosed_le (setToL1 hT).continuous (setToL1 hT').continuous

theorem setToL1_mono_left [OrderClosedTopology G''] {T T' : Set α → E →L[ℝ] G''} {C C' : ℝ}
    (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C')
    (hTT' : ∀ s x, T s x ≤ T' s x) (f : α →₁[μ] E) : setToL1 hT f ≤ setToL1 hT' f :=
  setToL1_mono_left' hT hT' (fun s _ _ x => hTT' s x) f

theorem setToL1_nonneg [ClosedIciTopology G''] {T : Set α → G' →L[ℝ] G''} {C : ℝ}
    (hT : DominatedFinMeasAdditive μ T C)
    (hT_nonneg : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x, 0 ≤ x → 0 ≤ T s x) {f : α →₁[μ] G'}
    (hf : 0 ≤ f) : 0 ≤ setToL1 hT f := by
  suffices ∀ f : { g : α →₁[μ] G' // 0 ≤ g }, 0 ≤ setToL1 hT f from
    this (⟨f, hf⟩ : { g : α →₁[μ] G' // 0 ≤ g })
  refine fun g =>
    @isClosed_property { g : α →₁ₛ[μ] G' // 0 ≤ g } { g : α →₁[μ] G' // 0 ≤ g } _ _
      (fun g => 0 ≤ setToL1 hT g)
      (denseRange_coeSimpleFuncNonnegToLpNonneg 1 μ G' one_ne_top) ?_ ?_ g
  · exact (isClosed_Ici (a := 0)).preimage ((setToL1 hT).continuous.comp continuous_induced_dom)
  · intro g
    have : (coeSimpleFuncNonnegToLpNonneg 1 μ G' g : α →₁[μ] G') = (g : α →₁ₛ[μ] G') := rfl
    rw [this, setToL1_eq_setToL1SCLM]
    exact setToL1S_nonneg (fun s => hT.eq_zero_of_measure_zero) hT.1 hT_nonneg g.2

theorem setToL1_mono [ClosedIciTopology G''] [IsOrderedAddMonoid G']
    {T : Set α → G' →L[ℝ] G''} {C : ℝ} (hT : DominatedFinMeasAdditive μ T C)
    (hT_nonneg : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x, 0 ≤ x → 0 ≤ T s x) {f g : α →₁[μ] G'}
    (hfg : f ≤ g) : setToL1 hT f ≤ setToL1 hT g := by
  rw [← sub_nonneg] at hfg ⊢
  rw [← (setToL1 hT).map_sub]
  exact setToL1_nonneg hT hT_nonneg hfg

end Order

theorem norm_setToL1_le_norm_setToL1SCLM (hT : DominatedFinMeasAdditive μ T C) :
    ‖setToL1 hT‖ ≤ ‖setToL1SCLM α E μ hT‖ :=
  calc
    ‖setToL1 hT‖ ≤ (1 : ℝ≥0) * ‖setToL1SCLM α E μ hT‖ := by
      refine
        ContinuousLinearMap.opNorm_extend_le (setToL1SCLM α E μ hT)
          (simpleFunc.denseRange one_ne_top) fun x => le_of_eq ?_
      rw [NNReal.coe_one, one_mul]
      simp [coeToLp]
    _ = ‖setToL1SCLM α E μ hT‖ := by rw [NNReal.coe_one, one_mul]

theorem norm_setToL1_le_mul_norm (hT : DominatedFinMeasAdditive μ T C) (hC : 0 ≤ C)
    (f : α →₁[μ] E) : ‖setToL1 hT f‖ ≤ C * ‖f‖ :=
  calc
    ‖setToL1 hT f‖ ≤ ‖setToL1SCLM α E μ hT‖ * ‖f‖ :=
      ContinuousLinearMap.le_of_opNorm_le _ (norm_setToL1_le_norm_setToL1SCLM hT) _
    _ ≤ C * ‖f‖ := mul_le_mul (norm_setToL1SCLM_le hT hC) le_rfl (norm_nonneg _) hC

theorem norm_setToL1_le_mul_norm' (hT : DominatedFinMeasAdditive μ T C) (f : α →₁[μ] E) :
    ‖setToL1 hT f‖ ≤ max C 0 * ‖f‖ :=
  calc
    ‖setToL1 hT f‖ ≤ ‖setToL1SCLM α E μ hT‖ * ‖f‖ :=
      ContinuousLinearMap.le_of_opNorm_le _ (norm_setToL1_le_norm_setToL1SCLM hT) _
    _ ≤ max C 0 * ‖f‖ :=
      mul_le_mul (norm_setToL1SCLM_le' hT) le_rfl (norm_nonneg _) (le_max_right _ _)

theorem norm_setToL1_le (hT : DominatedFinMeasAdditive μ T C) (hC : 0 ≤ C) : ‖setToL1 hT‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC (norm_setToL1_le_mul_norm hT hC)

theorem norm_setToL1_le' (hT : DominatedFinMeasAdditive μ T C) : ‖setToL1 hT‖ ≤ max C 0 :=
  ContinuousLinearMap.opNorm_le_bound _ (le_max_right _ _) (norm_setToL1_le_mul_norm' hT)

theorem setToL1_lipschitz (hT : DominatedFinMeasAdditive μ T C) :
    LipschitzWith (Real.toNNReal C) (setToL1 hT) :=
  (setToL1 hT).lipschitzWith.weaken (norm_setToL1_le' hT)

/-- If `fs i → f` in `L1`, then `setToL1 hT (fs i) → setToL1 hT f`. -/
theorem tendsto_setToL1 (hT : DominatedFinMeasAdditive μ T C) (f : α →₁[μ] E) {ι}
    (fs : ι → α →₁[μ] E) {l : Filter ι} (hfs : Tendsto fs l (𝓝 f)) :
    Tendsto (fun i => setToL1 hT (fs i)) l (𝓝 <| setToL1 hT f) :=
  ((setToL1 hT).continuous.tendsto _).comp hfs

end SetToL1

end L1

end MeasureTheory
