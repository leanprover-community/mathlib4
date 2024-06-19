/-
Copyright (c) 2019 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo
-/
import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic
import Mathlib.Analysis.NormedSpace.LinearIsometry
import Mathlib.Analysis.NormedSpace.ContinuousLinearMap

/-!
# Operator norm: bilinear maps

This file contains lemmas concerning operator norm as applied to bilinear maps `E × F → G`,
interpreted as linear maps `E → F → G` as usual (and similarly for semilinear variants).

-/

suppress_compilation

open Bornology
open Filter hiding map_smul
open scoped Classical NNReal Topology Uniformity

-- the `ₗ` subscript variables are for special cases about linear (as opposed to semilinear) maps
variable {𝕜 𝕜₂ 𝕜₃ E Eₗ F Fₗ G Gₗ 𝓕 : Type*}

section SemiNormed

open Metric ContinuousLinearMap

variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup Eₗ] [SeminormedAddCommGroup F]
  [SeminormedAddCommGroup Fₗ] [SeminormedAddCommGroup G] [SeminormedAddCommGroup Gₗ]

variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜 Eₗ] [NormedSpace 𝕜₂ F] [NormedSpace 𝕜 Fₗ] [NormedSpace 𝕜₃ G]
  [NormedSpace 𝕜 Gₗ] {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₃ : 𝕜₂ →+* 𝕜₃} {σ₁₃ : 𝕜 →+* 𝕜₃}
  [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

variable [FunLike 𝓕 E F]

namespace ContinuousLinearMap

section OpNorm

open Set Real

theorem opNorm_ext [RingHomIsometric σ₁₃] (f : E →SL[σ₁₂] F) (g : E →SL[σ₁₃] G)
    (h : ∀ x, ‖f x‖ = ‖g x‖) : ‖f‖ = ‖g‖ :=
  opNorm_eq_of_bounds (norm_nonneg _)
    (fun x => by
      rw [h x]
      exact le_opNorm _ _)
    fun c hc h₂ =>
    opNorm_le_bound _ hc fun z => by
      rw [← h z]
      exact h₂ z
#align continuous_linear_map.op_norm_ext ContinuousLinearMap.opNorm_ext

@[deprecated (since := "2024-02-02")] alias op_norm_ext := opNorm_ext

variable [RingHomIsometric σ₂₃]

theorem opNorm_le_bound₂ (f : E →SL[σ₁₃] F →SL[σ₂₃] G) {C : ℝ} (h0 : 0 ≤ C)
    (hC : ∀ x y, ‖f x y‖ ≤ C * ‖x‖ * ‖y‖) : ‖f‖ ≤ C :=
  f.opNorm_le_bound h0 fun x => (f x).opNorm_le_bound (mul_nonneg h0 (norm_nonneg _)) <| hC x
#align continuous_linear_map.op_norm_le_bound₂ ContinuousLinearMap.opNorm_le_bound₂

@[deprecated (since := "2024-02-02")] alias op_norm_le_bound₂ := opNorm_le_bound₂

theorem le_opNorm₂ [RingHomIsometric σ₁₃] (f : E →SL[σ₁₃] F →SL[σ₂₃] G) (x : E) (y : F) :
    ‖f x y‖ ≤ ‖f‖ * ‖x‖ * ‖y‖ :=
  (f x).le_of_opNorm_le (f.le_opNorm x) y
#align continuous_linear_map.le_op_norm₂ ContinuousLinearMap.le_opNorm₂

@[deprecated (since := "2024-02-02")] alias le_op_norm₂ := le_opNorm₂

-- Porting note (#10756): new theorem
theorem le_of_opNorm₂_le_of_le [RingHomIsometric σ₁₃] (f : E →SL[σ₁₃] F →SL[σ₂₃] G) {x : E} {y : F}
    {a b c : ℝ} (hf : ‖f‖ ≤ a) (hx : ‖x‖ ≤ b) (hy : ‖y‖ ≤ c) :
    ‖f x y‖ ≤ a * b * c :=
  (f x).le_of_opNorm_le_of_le (f.le_of_opNorm_le_of_le hf hx) hy

@[deprecated (since := "2024-02-02")] alias le_of_op_norm₂_le_of_le := le_of_opNorm₂_le_of_le

end OpNorm

end ContinuousLinearMap

namespace LinearMap

variable [RingHomIsometric σ₂₃]

lemma norm_mkContinuous₂_aux (f : E →ₛₗ[σ₁₃] F →ₛₗ[σ₂₃] G) (C : ℝ)
    (h : ∀ x y, ‖f x y‖ ≤ C * ‖x‖ * ‖y‖) (x : E) :
    ‖(f x).mkContinuous (C * ‖x‖) (h x)‖ ≤ max C 0 * ‖x‖ :=
  (mkContinuous_norm_le' (f x) (h x)).trans_eq <| by
    rw [max_mul_of_nonneg _ _ (norm_nonneg x), zero_mul]

/-- Create a bilinear map (represented as a map `E →L[𝕜] F →L[𝕜] G`) from the corresponding linear
map and existence of a bound on the norm of the image. The linear map can be constructed using
`LinearMap.mk₂`.

If you have an explicit bound, use `LinearMap.mkContinuous₂` instead, as a norm estimate will
follow automatically in `LinearMap.mkContinuous₂_norm_le`. -/
def mkContinuousOfExistsBound₂ (f : E →ₛₗ[σ₁₃] F →ₛₗ[σ₂₃] G)
    (h : ∃ C, ∀ x y, ‖f x y‖ ≤ C * ‖x‖ * ‖y‖) : E →SL[σ₁₃] F →SL[σ₂₃] G :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := fun x => (f x).mkContinuousOfExistsBound <| let ⟨C, hC⟩ := h; ⟨C * ‖x‖, hC x⟩
      map_add' := fun x y => by
        ext z
        simp
      map_smul' := fun c x => by
        ext z
        simp } <|
    let ⟨C, hC⟩ := h; ⟨max C 0, norm_mkContinuous₂_aux f C hC⟩

/-- Create a bilinear map (represented as a map `E →L[𝕜] F →L[𝕜] G`) from the corresponding linear
map and a bound on the norm of the image. The linear map can be constructed using
`LinearMap.mk₂`. Lemmas `LinearMap.mkContinuous₂_norm_le'` and `LinearMap.mkContinuous₂_norm_le`
provide estimates on the norm of an operator constructed using this function. -/
def mkContinuous₂ (f : E →ₛₗ[σ₁₃] F →ₛₗ[σ₂₃] G) (C : ℝ) (hC : ∀ x y, ‖f x y‖ ≤ C * ‖x‖ * ‖y‖) :
    E →SL[σ₁₃] F →SL[σ₂₃] G :=
  mkContinuousOfExistsBound₂ f ⟨C, hC⟩
#align linear_map.mk_continuous₂ LinearMap.mkContinuous₂

@[simp]
theorem mkContinuous₂_apply (f : E →ₛₗ[σ₁₃] F →ₛₗ[σ₂₃] G) {C : ℝ}
    (hC : ∀ x y, ‖f x y‖ ≤ C * ‖x‖ * ‖y‖) (x : E) (y : F) : f.mkContinuous₂ C hC x y = f x y :=
  rfl
#align linear_map.mk_continuous₂_apply LinearMap.mkContinuous₂_apply

theorem mkContinuous₂_norm_le' (f : E →ₛₗ[σ₁₃] F →ₛₗ[σ₂₃] G) {C : ℝ}
    (hC : ∀ x y, ‖f x y‖ ≤ C * ‖x‖ * ‖y‖) : ‖f.mkContinuous₂ C hC‖ ≤ max C 0 :=
  mkContinuous_norm_le _ (le_max_iff.2 <| Or.inr le_rfl) (norm_mkContinuous₂_aux f C hC)
#align linear_map.mk_continuous₂_norm_le' LinearMap.mkContinuous₂_norm_le'

theorem mkContinuous₂_norm_le (f : E →ₛₗ[σ₁₃] F →ₛₗ[σ₂₃] G) {C : ℝ} (h0 : 0 ≤ C)
    (hC : ∀ x y, ‖f x y‖ ≤ C * ‖x‖ * ‖y‖) : ‖f.mkContinuous₂ C hC‖ ≤ C :=
  (f.mkContinuous₂_norm_le' hC).trans_eq <| max_eq_left h0
#align linear_map.mk_continuous₂_norm_le LinearMap.mkContinuous₂_norm_le

end LinearMap

namespace ContinuousLinearMap

variable [RingHomIsometric σ₂₃] [RingHomIsometric σ₁₃]

/-- Flip the order of arguments of a continuous bilinear map.
For a version bundled as `LinearIsometryEquiv`, see
`ContinuousLinearMap.flipL`. -/
def flip (f : E →SL[σ₁₃] F →SL[σ₂₃] G) : F →SL[σ₂₃] E →SL[σ₁₃] G :=
  LinearMap.mkContinuous₂
    -- Porting note: the `simp only`s below used to be `rw`.
    -- Now that doesn't work as we need to do some beta reduction along the way.
    (LinearMap.mk₂'ₛₗ σ₂₃ σ₁₃ (fun y x => f x y) (fun x y z => (f z).map_add x y)
      (fun c y x => (f x).map_smulₛₗ c y) (fun z x y => by simp only [f.map_add, add_apply])
        (fun c y x => by simp only [f.map_smulₛₗ, smul_apply]))
    ‖f‖ fun y x => (f.le_opNorm₂ x y).trans_eq <| by simp only [mul_right_comm]
#align continuous_linear_map.flip ContinuousLinearMap.flip

private theorem le_norm_flip (f : E →SL[σ₁₃] F →SL[σ₂₃] G) : ‖f‖ ≤ ‖flip f‖ :=
  #adaptation_note
  /--
  After https://github.com/leanprover/lean4/pull/4119 we either need
  to specify the `f.flip` argument, or use `set_option maxSynthPendingDepth 2 in`.
  -/
  f.opNorm_le_bound₂ (norm_nonneg f.flip) fun x y => by
    rw [mul_right_comm]
    exact (flip f).le_opNorm₂ y x

@[simp]
theorem flip_apply (f : E →SL[σ₁₃] F →SL[σ₂₃] G) (x : E) (y : F) : f.flip y x = f x y :=
  rfl
#align continuous_linear_map.flip_apply ContinuousLinearMap.flip_apply

@[simp]
theorem flip_flip (f : E →SL[σ₁₃] F →SL[σ₂₃] G) : f.flip.flip = f := by
  ext
  rfl
#align continuous_linear_map.flip_flip ContinuousLinearMap.flip_flip

@[simp]
theorem opNorm_flip (f : E →SL[σ₁₃] F →SL[σ₂₃] G) : ‖f.flip‖ = ‖f‖ :=
  le_antisymm (by simpa only [flip_flip] using le_norm_flip f.flip) (le_norm_flip f)
#align continuous_linear_map.op_norm_flip ContinuousLinearMap.opNorm_flip

@[deprecated (since := "2024-02-02")] alias op_norm_flip := opNorm_flip

@[simp]
theorem flip_add (f g : E →SL[σ₁₃] F →SL[σ₂₃] G) : (f + g).flip = f.flip + g.flip :=
  rfl
#align continuous_linear_map.flip_add ContinuousLinearMap.flip_add

@[simp]
theorem flip_smul (c : 𝕜₃) (f : E →SL[σ₁₃] F →SL[σ₂₃] G) : (c • f).flip = c • f.flip :=
  rfl
#align continuous_linear_map.flip_smul ContinuousLinearMap.flip_smul

variable (E F G σ₁₃ σ₂₃)

/-- Flip the order of arguments of a continuous bilinear map.
This is a version bundled as a `LinearIsometryEquiv`.
For an unbundled version see `ContinuousLinearMap.flip`. -/
def flipₗᵢ' : (E →SL[σ₁₃] F →SL[σ₂₃] G) ≃ₗᵢ[𝕜₃] F →SL[σ₂₃] E →SL[σ₁₃] G where
  toFun := flip
  invFun := flip
  map_add' := flip_add
  map_smul' := flip_smul
  left_inv := flip_flip
  right_inv := flip_flip
  norm_map' := opNorm_flip
#align continuous_linear_map.flipₗᵢ' ContinuousLinearMap.flipₗᵢ'

variable {E F G σ₁₃ σ₂₃}

@[simp]
theorem flipₗᵢ'_symm : (flipₗᵢ' E F G σ₂₃ σ₁₃).symm = flipₗᵢ' F E G σ₁₃ σ₂₃ :=
  rfl
#align continuous_linear_map.flipₗᵢ'_symm ContinuousLinearMap.flipₗᵢ'_symm

@[simp]
theorem coe_flipₗᵢ' : ⇑(flipₗᵢ' E F G σ₂₃ σ₁₃) = flip :=
  rfl
#align continuous_linear_map.coe_flipₗᵢ' ContinuousLinearMap.coe_flipₗᵢ'

variable (𝕜 E Fₗ Gₗ)

/-- Flip the order of arguments of a continuous bilinear map.
This is a version bundled as a `LinearIsometryEquiv`.
For an unbundled version see `ContinuousLinearMap.flip`. -/
def flipₗᵢ : (E →L[𝕜] Fₗ →L[𝕜] Gₗ) ≃ₗᵢ[𝕜] Fₗ →L[𝕜] E →L[𝕜] Gₗ where
  toFun := flip
  invFun := flip
  map_add' := flip_add
  map_smul' := flip_smul
  left_inv := flip_flip
  right_inv := flip_flip
  norm_map' := opNorm_flip
#align continuous_linear_map.flipₗᵢ ContinuousLinearMap.flipₗᵢ

variable {𝕜 E Fₗ Gₗ}

@[simp]
theorem flipₗᵢ_symm : (flipₗᵢ 𝕜 E Fₗ Gₗ).symm = flipₗᵢ 𝕜 Fₗ E Gₗ :=
  rfl
#align continuous_linear_map.flipₗᵢ_symm ContinuousLinearMap.flipₗᵢ_symm

@[simp]
theorem coe_flipₗᵢ : ⇑(flipₗᵢ 𝕜 E Fₗ Gₗ) = flip :=
  rfl
#align continuous_linear_map.coe_flipₗᵢ ContinuousLinearMap.coe_flipₗᵢ

variable (F σ₁₂)
variable [RingHomIsometric σ₁₂]

/-- The continuous semilinear map obtained by applying a continuous semilinear map at a given
vector.

This is the continuous version of `LinearMap.applyₗ`. -/
def apply' : E →SL[σ₁₂] (E →SL[σ₁₂] F) →L[𝕜₂] F :=
  flip (id 𝕜₂ (E →SL[σ₁₂] F))
#align continuous_linear_map.apply' ContinuousLinearMap.apply'

variable {F σ₁₂}

@[simp]
theorem apply_apply' (v : E) (f : E →SL[σ₁₂] F) : apply' F σ₁₂ v f = f v :=
  rfl
#align continuous_linear_map.apply_apply' ContinuousLinearMap.apply_apply'

variable (𝕜 Fₗ)

/-- The continuous semilinear map obtained by applying a continuous semilinear map at a given
vector.

This is the continuous version of `LinearMap.applyₗ`. -/
def apply : E →L[𝕜] (E →L[𝕜] Fₗ) →L[𝕜] Fₗ :=
  flip (id 𝕜 (E →L[𝕜] Fₗ))
#align continuous_linear_map.apply ContinuousLinearMap.apply

variable {𝕜 Fₗ}

@[simp]
theorem apply_apply (v : E) (f : E →L[𝕜] Fₗ) : apply 𝕜 Fₗ v f = f v :=
  rfl
#align continuous_linear_map.apply_apply ContinuousLinearMap.apply_apply

variable (σ₁₂ σ₂₃ E F G)

set_option linter.uppercaseLean3 false

/-- Composition of continuous semilinear maps as a continuous semibilinear map. -/
def compSL : (F →SL[σ₂₃] G) →L[𝕜₃] (E →SL[σ₁₂] F) →SL[σ₂₃] E →SL[σ₁₃] G :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂'ₛₗ (RingHom.id 𝕜₃) σ₂₃ comp add_comp smul_comp comp_add fun c f g => by
      ext
      simp only [ContinuousLinearMap.map_smulₛₗ, coe_smul', coe_comp', Function.comp_apply,
        Pi.smul_apply])
    1 fun f g => by simpa only [one_mul] using opNorm_comp_le f g
#align continuous_linear_map.compSL ContinuousLinearMap.compSL

#adaptation_note
/--
Before https://github.com/leanprover/lean4/pull/4119 we had to create a local instance:
```
letI : Norm ((F →SL[σ₂₃] G) →L[𝕜₃] (E →SL[σ₁₂] F) →SL[σ₂₃] E →SL[σ₁₃] G) :=
  hasOpNorm (𝕜₂ := 𝕜₃) (E := F →SL[σ₂₃] G) (F := (E →SL[σ₁₂] F) →SL[σ₂₃] E →SL[σ₁₃] G)
```
-/
set_option maxSynthPendingDepth 2 in
theorem norm_compSL_le : ‖compSL E F G σ₁₂ σ₂₃‖ ≤ 1 :=
  LinearMap.mkContinuous₂_norm_le _ zero_le_one _
#align continuous_linear_map.norm_compSL_le ContinuousLinearMap.norm_compSL_le

variable {σ₁₂ σ₂₃ E F G}

@[simp]
theorem compSL_apply (f : F →SL[σ₂₃] G) (g : E →SL[σ₁₂] F) : compSL E F G σ₁₂ σ₂₃ f g = f.comp g :=
  rfl
#align continuous_linear_map.compSL_apply ContinuousLinearMap.compSL_apply

theorem _root_.Continuous.const_clm_comp {X} [TopologicalSpace X] {f : X → E →SL[σ₁₂] F}
    (hf : Continuous f) (g : F →SL[σ₂₃] G) :
    Continuous (fun x => g.comp (f x) : X → E →SL[σ₁₃] G) :=
  (compSL E F G σ₁₂ σ₂₃ g).continuous.comp hf
#align continuous.const_clm_comp Continuous.const_clm_comp

-- Giving the implicit argument speeds up elaboration significantly
theorem _root_.Continuous.clm_comp_const {X} [TopologicalSpace X] {g : X → F →SL[σ₂₃] G}
    (hg : Continuous g) (f : E →SL[σ₁₂] F) :
    Continuous (fun x => (g x).comp f : X → E →SL[σ₁₃] G) :=
  (@ContinuousLinearMap.flip _ _ _ _ _ (E →SL[σ₁₃] G) _ _ _ _ _ _ _ _ _ _ _ _ _
    (compSL E F G σ₁₂ σ₂₃) f).continuous.comp hg
#align continuous.clm_comp_const Continuous.clm_comp_const

variable (𝕜 σ₁₂ σ₂₃ E Fₗ Gₗ)

/-- Composition of continuous linear maps as a continuous bilinear map. -/
def compL : (Fₗ →L[𝕜] Gₗ) →L[𝕜] (E →L[𝕜] Fₗ) →L[𝕜] E →L[𝕜] Gₗ :=
  compSL E Fₗ Gₗ (RingHom.id 𝕜) (RingHom.id 𝕜)
#align continuous_linear_map.compL ContinuousLinearMap.compL

#adaptation_note
/--
Before https://github.com/leanprover/lean4/pull/4119 we had to create a local instance:
```
letI : Norm ((Fₗ →L[𝕜] Gₗ) →L[𝕜] (E →L[𝕜] Fₗ) →L[𝕜] E →L[𝕜] Gₗ) :=
  hasOpNorm (𝕜₂ := 𝕜) (E := Fₗ →L[𝕜] Gₗ) (F := (E →L[𝕜] Fₗ) →L[𝕜] E →L[𝕜] Gₗ)
```
-/
set_option maxSynthPendingDepth 2 in
theorem norm_compL_le : ‖compL 𝕜 E Fₗ Gₗ‖ ≤ 1 :=
  norm_compSL_le _ _ _ _ _
#align continuous_linear_map.norm_compL_le ContinuousLinearMap.norm_compL_le

@[simp]
theorem compL_apply (f : Fₗ →L[𝕜] Gₗ) (g : E →L[𝕜] Fₗ) : compL 𝕜 E Fₗ Gₗ f g = f.comp g :=
  rfl
#align continuous_linear_map.compL_apply ContinuousLinearMap.compL_apply

variable (Eₗ) {𝕜 E Fₗ Gₗ}

/-- Apply `L(x,-)` pointwise to bilinear maps, as a continuous bilinear map -/
@[simps! apply]
def precompR (L : E →L[𝕜] Fₗ →L[𝕜] Gₗ) : E →L[𝕜] (Eₗ →L[𝕜] Fₗ) →L[𝕜] Eₗ →L[𝕜] Gₗ :=
  (compL 𝕜 Eₗ Fₗ Gₗ).comp L
#align continuous_linear_map.precompR ContinuousLinearMap.precompR

/-- Apply `L(-,y)` pointwise to bilinear maps, as a continuous bilinear map -/
def precompL (L : E →L[𝕜] Fₗ →L[𝕜] Gₗ) : (Eₗ →L[𝕜] E) →L[𝕜] Fₗ →L[𝕜] Eₗ →L[𝕜] Gₗ :=
  (precompR Eₗ (flip L)).flip
#align continuous_linear_map.precompL ContinuousLinearMap.precompL

@[simp] lemma precompL_apply (L : E →L[𝕜] Fₗ →L[𝕜] Gₗ) (u : Eₗ →L[𝕜] E) (f : Fₗ) (g : Eₗ) :
    precompL Eₗ L u f g = L (u g) f := rfl

#adaptation_note
/--
Before https://github.com/leanprover/lean4/pull/4119
we had to create a local instance in the signature:
```
letI : SeminormedAddCommGroup ((Eₗ →L[𝕜] Fₗ) →L[𝕜] Eₗ →L[𝕜] Gₗ) := inferInstance
letI : NormedSpace 𝕜 ((Eₗ →L[𝕜] Fₗ) →L[𝕜] Eₗ →L[𝕜] Gₗ) := inferInstance
```
-/
set_option maxSynthPendingDepth 2 in
theorem norm_precompR_le (L : E →L[𝕜] Fₗ →L[𝕜] Gₗ) : ‖precompR Eₗ L‖ ≤ ‖L‖ :=
  calc
    ‖precompR Eₗ L‖ ≤ ‖compL 𝕜 Eₗ Fₗ Gₗ‖ * ‖L‖ := opNorm_comp_le _ _
    _ ≤ 1 * ‖L‖ := mul_le_mul_of_nonneg_right (norm_compL_le _ _ _ _) (norm_nonneg L)
    _ = ‖L‖ := by rw [one_mul]
#align continuous_linear_map.norm_precompR_le ContinuousLinearMap.norm_precompR_le

#adaptation_note
/--
Before https://github.com/leanprover/lean4/pull/4119
we had to create a local instance in the signature:
```
letI : Norm ((Eₗ →L[𝕜] E) →L[𝕜] Fₗ →L[𝕜] Eₗ →L[𝕜] Gₗ) :=
  hasOpNorm (𝕜₂ := 𝕜) (E := Eₗ →L[𝕜] E) (F := Fₗ →L[𝕜] Eₗ →L[𝕜] Gₗ)
```
-/
set_option maxSynthPendingDepth 2 in
theorem norm_precompL_le (L : E →L[𝕜] Fₗ →L[𝕜] Gₗ) : ‖precompL Eₗ L‖ ≤ ‖L‖ := by
  rw [precompL, opNorm_flip, ← opNorm_flip L]
  exact norm_precompR_le _ L.flip
#align continuous_linear_map.norm_precompL_le ContinuousLinearMap.norm_precompL_le

end ContinuousLinearMap

variable {σ₂₁ : 𝕜₂ →+* 𝕜} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]

namespace ContinuousLinearMap

variable {E' F' : Type*} [SeminormedAddCommGroup E'] [SeminormedAddCommGroup F']
variable {𝕜₁' : Type*} {𝕜₂' : Type*} [NontriviallyNormedField 𝕜₁'] [NontriviallyNormedField 𝕜₂']
  [NormedSpace 𝕜₁' E'] [NormedSpace 𝕜₂' F'] {σ₁' : 𝕜₁' →+* 𝕜} {σ₁₃' : 𝕜₁' →+* 𝕜₃} {σ₂' : 𝕜₂' →+* 𝕜₂}
  {σ₂₃' : 𝕜₂' →+* 𝕜₃} [RingHomCompTriple σ₁' σ₁₃ σ₁₃'] [RingHomCompTriple σ₂' σ₂₃ σ₂₃']
  [RingHomIsometric σ₂₃] [RingHomIsometric σ₁₃'] [RingHomIsometric σ₂₃']

/-- Compose a bilinear map `E →SL[σ₁₃] F →SL[σ₂₃] G` with two linear maps
`E' →SL[σ₁'] E` and `F' →SL[σ₂'] F`.  -/
def bilinearComp (f : E →SL[σ₁₃] F →SL[σ₂₃] G) (gE : E' →SL[σ₁'] E) (gF : F' →SL[σ₂'] F) :
    E' →SL[σ₁₃'] F' →SL[σ₂₃'] G :=
  ((f.comp gE).flip.comp gF).flip
#align continuous_linear_map.bilinear_comp ContinuousLinearMap.bilinearComp

@[simp]
theorem bilinearComp_apply (f : E →SL[σ₁₃] F →SL[σ₂₃] G) (gE : E' →SL[σ₁'] E) (gF : F' →SL[σ₂'] F)
    (x : E') (y : F') : f.bilinearComp gE gF x y = f (gE x) (gF y) :=
  rfl
#align continuous_linear_map.bilinear_comp_apply ContinuousLinearMap.bilinearComp_apply

variable [RingHomIsometric σ₁₃] [RingHomIsometric σ₁'] [RingHomIsometric σ₂']

/-- Derivative of a continuous bilinear map `f : E →L[𝕜] F →L[𝕜] G` interpreted as a map `E × F → G`
at point `p : E × F` evaluated at `q : E × F`, as a continuous bilinear map. -/
def deriv₂ (f : E →L[𝕜] Fₗ →L[𝕜] Gₗ) : E × Fₗ →L[𝕜] E × Fₗ →L[𝕜] Gₗ :=
  f.bilinearComp (fst _ _ _) (snd _ _ _) + f.flip.bilinearComp (snd _ _ _) (fst _ _ _)
#align continuous_linear_map.deriv₂ ContinuousLinearMap.deriv₂

@[simp]
theorem coe_deriv₂ (f : E →L[𝕜] Fₗ →L[𝕜] Gₗ) (p : E × Fₗ) :
    ⇑(f.deriv₂ p) = fun q : E × Fₗ => f p.1 q.2 + f q.1 p.2 :=
  rfl
#align continuous_linear_map.coe_deriv₂ ContinuousLinearMap.coe_deriv₂

theorem map_add_add (f : E →L[𝕜] Fₗ →L[𝕜] Gₗ) (x x' : E) (y y' : Fₗ) :
    f (x + x') (y + y') = f x y + f.deriv₂ (x, y) (x', y') + f x' y' := by
  simp only [map_add, add_apply, coe_deriv₂, add_assoc]
  abel
#align continuous_linear_map.map_add_add ContinuousLinearMap.map_add_add

end ContinuousLinearMap

end SemiNormed
