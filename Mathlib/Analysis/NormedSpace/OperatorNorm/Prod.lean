/-
Copyright (c) 2019 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo
-/
import Mathlib.Analysis.NormedSpace.OperatorNorm.Bilinear

/-!
# Operator norm: Cartesian products

Interaction of operator norm with Cartesian products.
-/

-- make instances connecting normed things and algebra have higher priority
open scoped AlgebraNormedInstances

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]

open Set Real Metric ContinuousLinearMap

section SemiNormed

variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [SeminormedAddCommGroup G]
variable [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [NormedSpace 𝕜 G]

namespace ContinuousLinearMap

section FirstSecond

variable (𝕜 E F)

/-- The operator norm of the first projection `E × F → E` is at most 1. (It is 0 if `E` is zero, so
the inequality cannot be improved without further assumptions.) -/
lemma norm_fst_le : ‖fst 𝕜 E F‖ ≤ 1 :=
  opNorm_le_bound _ zero_le_one (fun ⟨e, f⟩ ↦ by simpa only [one_mul] using le_max_left ‖e‖ ‖f‖)

/-- The operator norm of the second projection `E × F → F` is at most 1. (It is 0 if `F` is zero, so
the inequality cannot be improved without further assumptions.) -/
lemma norm_snd_le : ‖snd 𝕜 E F‖ ≤ 1 :=
  opNorm_le_bound _ zero_le_one (fun ⟨e, f⟩ ↦ by simpa only [one_mul] using le_max_right ‖e‖ ‖f‖)

end FirstSecond

section OpNorm

@[simp]
theorem opNorm_prod (f : E →L[𝕜] F) (g : E →L[𝕜] G) : ‖f.prod g‖ = ‖(f, g)‖ :=
  le_antisymm
      (opNorm_le_bound _ (norm_nonneg _) fun x => by
        simpa only [prod_apply, Prod.norm_def, max_mul_of_nonneg, norm_nonneg] using
          max_le_max (le_opNorm f x) (le_opNorm g x)) <|
    max_le
      (opNorm_le_bound _ (norm_nonneg _) fun x =>
        (le_max_left _ _).trans ((f.prod g).le_opNorm x))
      (opNorm_le_bound _ (norm_nonneg _) fun x =>
        (le_max_right _ _).trans ((f.prod g).le_opNorm x))
#align continuous_linear_map.op_norm_prod ContinuousLinearMap.opNorm_prod

@[deprecated] alias op_norm_prod := opNorm_prod -- deprecated on 2024-02-02

@[simp]
theorem opNNNorm_prod (f : E →L[𝕜] F) (g : E →L[𝕜] G) : ‖f.prod g‖₊ = ‖(f, g)‖₊ :=
  Subtype.ext <| opNorm_prod f g
#align continuous_linear_map.op_nnnorm_prod ContinuousLinearMap.opNNNorm_prod

@[deprecated] alias op_nnnorm_prod := opNNNorm_prod -- deprecated on 2024-02-02

/-- `ContinuousLinearMap.prod` as a `LinearIsometryEquiv`. -/
def prodₗᵢ (R : Type*) [Semiring R] [Module R F] [Module R G] [ContinuousConstSMul R F]
    [ContinuousConstSMul R G] [SMulCommClass 𝕜 R F] [SMulCommClass 𝕜 R G] :
    (E →L[𝕜] F) × (E →L[𝕜] G) ≃ₗᵢ[R] E →L[𝕜] F × G :=
  ⟨prodₗ R, fun ⟨f, g⟩ => opNorm_prod f g⟩
#align continuous_linear_map.prodₗᵢ ContinuousLinearMap.prodₗᵢ

end OpNorm

set_option linter.uppercaseLean3 false

section Prod

variable (M₁ M₂ M₃ M₄ : Type*) (𝕜)
variable
  [SeminormedAddCommGroup M₁] [NormedSpace 𝕜 M₁]
  [SeminormedAddCommGroup M₂] [NormedSpace 𝕜 M₂]
  [SeminormedAddCommGroup M₃] [NormedSpace 𝕜 M₃]
  [SeminormedAddCommGroup M₄] [NormedSpace 𝕜 M₄]

/-- `ContinuousLinearMap.prodMap` as a continuous linear map. -/
def prodMapL : (M₁ →L[𝕜] M₂) × (M₃ →L[𝕜] M₄) →L[𝕜] M₁ × M₃ →L[𝕜] M₂ × M₄ :=
  ContinuousLinearMap.copy
    (have Φ₁ : (M₁ →L[𝕜] M₂) →L[𝕜] M₁ →L[𝕜] M₂ × M₄ :=
      ContinuousLinearMap.compL 𝕜 M₁ M₂ (M₂ × M₄) (ContinuousLinearMap.inl 𝕜 M₂ M₄)
    have Φ₂ : (M₃ →L[𝕜] M₄) →L[𝕜] M₃ →L[𝕜] M₂ × M₄ :=
      ContinuousLinearMap.compL 𝕜 M₃ M₄ (M₂ × M₄) (ContinuousLinearMap.inr 𝕜 M₂ M₄)
    have Φ₁' :=
      (ContinuousLinearMap.compL 𝕜 (M₁ × M₃) M₁ (M₂ × M₄)).flip (ContinuousLinearMap.fst 𝕜 M₁ M₃)
    have Φ₂' :=
      (ContinuousLinearMap.compL 𝕜 (M₁ × M₃) M₃ (M₂ × M₄)).flip (ContinuousLinearMap.snd 𝕜 M₁ M₃)
    have Ψ₁ : (M₁ →L[𝕜] M₂) × (M₃ →L[𝕜] M₄) →L[𝕜] M₁ →L[𝕜] M₂ :=
      ContinuousLinearMap.fst 𝕜 (M₁ →L[𝕜] M₂) (M₃ →L[𝕜] M₄)
    have Ψ₂ : (M₁ →L[𝕜] M₂) × (M₃ →L[𝕜] M₄) →L[𝕜] M₃ →L[𝕜] M₄ :=
      ContinuousLinearMap.snd 𝕜 (M₁ →L[𝕜] M₂) (M₃ →L[𝕜] M₄)
    Φ₁' ∘L Φ₁ ∘L Ψ₁ + Φ₂' ∘L Φ₂ ∘L Ψ₂)
    (fun p : (M₁ →L[𝕜] M₂) × (M₃ →L[𝕜] M₄) => p.1.prodMap p.2) (by
      apply funext
      rintro ⟨φ, ψ⟩
      refine ContinuousLinearMap.ext fun ⟨x₁, x₂⟩ => ?_
      dsimp
      simp)
#align continuous_linear_map.prod_mapL ContinuousLinearMap.prodMapL

variable {M₁ M₂ M₃ M₄}

@[simp]
theorem prodMapL_apply (p : (M₁ →L[𝕜] M₂) × (M₃ →L[𝕜] M₄)) :
    ContinuousLinearMap.prodMapL 𝕜 M₁ M₂ M₃ M₄ p = p.1.prodMap p.2 :=
  rfl
#align continuous_linear_map.prod_mapL_apply ContinuousLinearMap.prodMapL_apply

variable {X : Type*} [TopologicalSpace X]

theorem _root_.Continuous.prod_mapL {f : X → M₁ →L[𝕜] M₂} {g : X → M₃ →L[𝕜] M₄} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun x => (f x).prodMap (g x) :=
  (prodMapL 𝕜 M₁ M₂ M₃ M₄).continuous.comp (hf.prod_mk hg)
#align continuous.prod_mapL Continuous.prod_mapL

theorem _root_.Continuous.prod_map_equivL {f : X → M₁ ≃L[𝕜] M₂} {g : X → M₃ ≃L[𝕜] M₄}
    (hf : Continuous fun x => (f x : M₁ →L[𝕜] M₂)) (hg : Continuous fun x => (g x : M₃ →L[𝕜] M₄)) :
    Continuous fun x => ((f x).prod (g x) : M₁ × M₃ →L[𝕜] M₂ × M₄) :=
  (prodMapL 𝕜 M₁ M₂ M₃ M₄).continuous.comp (hf.prod_mk hg)
#align continuous.prod_map_equivL Continuous.prod_map_equivL

theorem _root_.ContinuousOn.prod_mapL {f : X → M₁ →L[𝕜] M₂} {g : X → M₃ →L[𝕜] M₄} {s : Set X}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun x => (f x).prodMap (g x)) s :=
  ((prodMapL 𝕜 M₁ M₂ M₃ M₄).continuous.comp_continuousOn (hf.prod hg) : _)
#align continuous_on.prod_mapL ContinuousOn.prod_mapL

theorem _root_.ContinuousOn.prod_map_equivL {f : X → M₁ ≃L[𝕜] M₂} {g : X → M₃ ≃L[𝕜] M₄} {s : Set X}
    (hf : ContinuousOn (fun x => (f x : M₁ →L[𝕜] M₂)) s)
    (hg : ContinuousOn (fun x => (g x : M₃ →L[𝕜] M₄)) s) :
    ContinuousOn (fun x => ((f x).prod (g x) : M₁ × M₃ →L[𝕜] M₂ × M₄)) s :=
  (prodMapL 𝕜 M₁ M₂ M₃ M₄).continuous.comp_continuousOn (hf.prod hg)
#align continuous_on.prod_map_equivL ContinuousOn.prod_map_equivL

end Prod

end ContinuousLinearMap

end SemiNormed

section Normed

namespace ContinuousLinearMap

section FirstSecond

variable (𝕜 E F)

/-- The operator norm of the first projection `E × F → E` is exactly 1 if `E` is nontrivial. -/
@[simp] lemma norm_fst [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] [Nontrivial E] :
    ‖fst 𝕜 E F‖ = 1 := by
  refine le_antisymm (norm_fst_le ..) ?_
  let ⟨e, he⟩ := exists_ne (0 : E)
  have : ‖e‖ ≤ _ * max ‖e‖ ‖(0 : F)‖ := (fst 𝕜 E F).le_opNorm (e, 0)
  rw [norm_zero, max_eq_left (norm_nonneg e)] at this
  rwa [← mul_le_mul_iff_of_pos_right (norm_pos_iff.mpr he), one_mul]

/-- The operator norm of the second projection `E × F → F` is exactly 1 if `F` is nontrivial. -/
@[simp] lemma norm_snd [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [Nontrivial F]  :
    ‖snd 𝕜 E F‖ = 1 := by
  refine le_antisymm (norm_snd_le ..) ?_
  let ⟨f, hf⟩ := exists_ne (0 : F)
  have : ‖f‖ ≤ _ * max ‖(0 : E)‖ ‖f‖ := (snd 𝕜 E F).le_opNorm (0, f)
  rw [norm_zero, max_eq_right (norm_nonneg f)] at this
  rwa [← mul_le_mul_iff_of_pos_right (norm_pos_iff.mpr hf), one_mul]

end FirstSecond

end ContinuousLinearMap

end Normed
