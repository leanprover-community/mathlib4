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

--suppress_compilation

-- the `ₗ` subscript variables are because we only treat linear maps in this file, while other
-- closely related files use plain letters for semilinear maps and subscript `ₗ` for linear
variable {𝕜 E Fₗ Gₗ : Type*}

section SemiNormed

open Set Real Metric ContinuousLinearMap

variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup Fₗ] [SeminormedAddCommGroup Gₗ]

variable [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [NormedSpace 𝕜 Fₗ] [NormedSpace 𝕜 Gₗ]

namespace ContinuousLinearMap

section OpNorm

@[simp]
theorem opNorm_prod (f : E →L[𝕜] Fₗ) (g : E →L[𝕜] Gₗ) : ‖f.prod g‖ = ‖(f, g)‖ :=
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

@[deprecated]
alias op_norm_prod :=
  opNorm_prod -- deprecated on 2024-02-02

@[simp]
theorem opNNNorm_prod (f : E →L[𝕜] Fₗ) (g : E →L[𝕜] Gₗ) : ‖f.prod g‖₊ = ‖(f, g)‖₊ :=
  Subtype.ext <| opNorm_prod f g
#align continuous_linear_map.op_nnnorm_prod ContinuousLinearMap.opNNNorm_prod

@[deprecated]
alias op_nnnorm_prod :=
  opNNNorm_prod -- deprecated on 2024-02-02

/-- `ContinuousLinearMap.prod` as a `LinearIsometryEquiv`. -/
def prodₗᵢ (R : Type*) [Semiring R] [Module R Fₗ] [Module R Gₗ] [ContinuousConstSMul R Fₗ]
    [ContinuousConstSMul R Gₗ] [SMulCommClass 𝕜 R Fₗ] [SMulCommClass 𝕜 R Gₗ] :
    (E →L[𝕜] Fₗ) × (E →L[𝕜] Gₗ) ≃ₗᵢ[R] E →L[𝕜] Fₗ × Gₗ :=
  ⟨prodₗ R, fun ⟨f, g⟩ => opNorm_prod f g⟩
#align continuous_linear_map.prodₗᵢ ContinuousLinearMap.prodₗᵢ

end OpNorm

set_option linter.uppercaseLean3 false

section Prod

universe u₁ u₂ u₃ u₄

variable (M₁ : Type u₁) [SeminormedAddCommGroup M₁] [NormedSpace 𝕜 M₁] (M₂ : Type u₂)
  [SeminormedAddCommGroup M₂] [NormedSpace 𝕜 M₂] (M₃ : Type u₃) [SeminormedAddCommGroup M₃]
  [NormedSpace 𝕜 M₃] (M₄ : Type u₄) [SeminormedAddCommGroup M₄] [NormedSpace 𝕜 M₄]

variable (𝕜)

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
      refine' ContinuousLinearMap.ext fun ⟨x₁, x₂⟩ => _
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
