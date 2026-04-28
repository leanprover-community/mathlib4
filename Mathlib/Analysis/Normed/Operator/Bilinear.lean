/-
Copyright (c) 2019 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

/-!
# Operator norm: bilinear maps

This file contains lemmas concerning operator norm as applied to bilinear maps `E × F → G`,
interpreted as linear maps `E → F → G` as usual (and similarly for semilinear variants).

-/

@[expose] public section

suppress_compilation

open Bornology
open Filter hiding map_smul
open scoped NNReal Topology Uniformity

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


variable [RingHomIsometric σ₂₃]

theorem opNorm_le_bound₂ (f : E →SL[σ₁₃] F →SL[σ₂₃] G) {C : ℝ} (h0 : 0 ≤ C)
    (hC : ∀ x y, ‖f x y‖ ≤ C * ‖x‖ * ‖y‖) : ‖f‖ ≤ C :=
  f.opNorm_le_bound h0 fun x => (f x).opNorm_le_bound (by positivity) <| hC x


theorem le_opNorm₂ [RingHomIsometric σ₁₃] (f : E →SL[σ₁₃] F →SL[σ₂₃] G) (x : E) (y : F) :
    ‖f x y‖ ≤ ‖f‖ * ‖x‖ * ‖y‖ :=
  (f x).le_of_opNorm_le (f.le_opNorm x) y


theorem le_of_opNorm₂_le_of_le [RingHomIsometric σ₁₃] (f : E →SL[σ₁₃] F →SL[σ₂₃] G) {x : E} {y : F}
    {a b c : ℝ} (hf : ‖f‖ ≤ a) (hx : ‖x‖ ≤ b) (hy : ‖y‖ ≤ c) :
    ‖f x y‖ ≤ a * b * c :=
  (f x).le_of_opNorm_le_of_le (f.le_of_opNorm_le_of_le hf hx) hy


end OpNorm

end ContinuousLinearMap

namespace LinearMap

lemma norm_mkContinuous₂_aux (f : E →ₛₗ[σ₁₃] F →ₛₗ[σ₂₃] G) (C : ℝ)
    (h : ∀ x y, ‖f x y‖ ≤ C * ‖x‖ * ‖y‖) (x : E) :
    ‖(f x).mkContinuous (C * ‖x‖) (h x)‖ ≤ max C 0 * ‖x‖ :=
  (mkContinuous_norm_le' (f x) (h x)).trans_eq <| by
    rw [max_mul_of_nonneg _ _ (norm_nonneg x), zero_mul]

variable [RingHomIsometric σ₂₃]

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

@[simp]
theorem mkContinuous₂_apply (f : E →ₛₗ[σ₁₃] F →ₛₗ[σ₂₃] G) {C : ℝ}
    (hC : ∀ x y, ‖f x y‖ ≤ C * ‖x‖ * ‖y‖) (x : E) (y : F) : f.mkContinuous₂ C hC x y = f x y :=
  rfl

theorem mkContinuous₂_norm_le' (f : E →ₛₗ[σ₁₃] F →ₛₗ[σ₂₃] G) {C : ℝ}
    (hC : ∀ x y, ‖f x y‖ ≤ C * ‖x‖ * ‖y‖) : ‖f.mkContinuous₂ C hC‖ ≤ max C 0 :=
  mkContinuous_norm_le _ (le_max_iff.2 <| Or.inr le_rfl) (norm_mkContinuous₂_aux f C hC)

theorem mkContinuous₂_norm_le (f : E →ₛₗ[σ₁₃] F →ₛₗ[σ₂₃] G) {C : ℝ} (h0 : 0 ≤ C)
    (hC : ∀ x y, ‖f x y‖ ≤ C * ‖x‖ * ‖y‖) : ‖f.mkContinuous₂ C hC‖ ≤ C :=
  (f.mkContinuous₂_norm_le' hC).trans_eq <| max_eq_left h0

end LinearMap

namespace ContinuousLinearMap

variable [RingHomIsometric σ₂₃] [RingHomIsometric σ₁₃]

/-- Flip the order of arguments of a continuous bilinear map.
For a version bundled as `LinearIsometryEquiv`, see
`ContinuousLinearMap.flipL`. -/
def flip (f : E →SL[σ₁₃] F →SL[σ₂₃] G) : F →SL[σ₂₃] E →SL[σ₁₃] G :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂'ₛₗ σ₂₃ σ₁₃ (fun y x => f x y) (fun x y z => (f z).map_add x y)
      (fun c y x => (f x).map_smulₛₗ c y) (fun z x y => by simp only [f.map_add, _root_.add_apply])
        (fun c y x => by simp only [f.map_smulₛₗ, _root_.smul_apply]))
    ‖f‖ fun y x => (f.le_opNorm₂ x y).trans_eq <| by simp only [mul_right_comm]

private theorem le_norm_flip (f : E →SL[σ₁₃] F →SL[σ₂₃] G) : ‖f‖ ≤ ‖flip f‖ :=
  f.opNorm_le_bound₂ (norm_nonneg f.flip) fun x y => by
    rw [mul_right_comm]
    exact (flip f).le_opNorm₂ y x

@[simp]
theorem flip_apply (f : E →SL[σ₁₃] F →SL[σ₂₃] G) (x : E) (y : F) : f.flip y x = f x y :=
  rfl

@[simp]
theorem flip_flip (f : E →SL[σ₁₃] F →SL[σ₂₃] G) : f.flip.flip = f := by
  ext
  rfl

@[simp]
theorem opNorm_flip (f : E →SL[σ₁₃] F →SL[σ₂₃] G) : ‖f.flip‖ = ‖f‖ :=
  le_antisymm (by simpa only [flip_flip] using le_norm_flip f.flip) (le_norm_flip f)

@[simp]
lemma flip_zero : flip (0 : E →SL[σ₁₃] F →SL[σ₂₃] G) = 0 := rfl

@[simp]
theorem flip_add (f g : E →SL[σ₁₃] F →SL[σ₂₃] G) : (f + g).flip = f.flip + g.flip :=
  rfl

@[simp]
theorem flip_smul (c : 𝕜₃) (f : E →SL[σ₁₃] F →SL[σ₂₃] G) : (c • f).flip = c • f.flip :=
  rfl

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

variable {E F G σ₁₃ σ₂₃}

@[simp]
theorem flipₗᵢ'_symm : (flipₗᵢ' E F G σ₂₃ σ₁₃).symm = flipₗᵢ' F E G σ₁₃ σ₂₃ :=
  rfl

@[simp]
theorem coe_flipₗᵢ' : ⇑(flipₗᵢ' E F G σ₂₃ σ₁₃) = flip :=
  rfl

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

variable {𝕜 E Fₗ Gₗ}

@[simp]
theorem flipₗᵢ_symm : (flipₗᵢ 𝕜 E Fₗ Gₗ).symm = flipₗᵢ 𝕜 Fₗ E Gₗ :=
  rfl

@[simp]
theorem coe_flipₗᵢ : ⇑(flipₗᵢ 𝕜 E Fₗ Gₗ) = flip :=
  rfl

variable (F σ₁₂)
variable [RingHomIsometric σ₁₂]

/-- The continuous semilinear map obtained by applying a continuous semilinear map at a given
vector.

This is the continuous version of `LinearMap.applyₗ`. -/
def apply' : E →SL[σ₁₂] (E →SL[σ₁₂] F) →L[𝕜₂] F :=
  flip (.id 𝕜₂ (E →SL[σ₁₂] F))

variable {F σ₁₂}

@[simp]
theorem apply_apply' (v : E) (f : E →SL[σ₁₂] F) : apply' F σ₁₂ v f = f v :=
  rfl

variable (𝕜 Fₗ)

/-- The continuous semilinear map obtained by applying a continuous semilinear map at a given
vector.

This is the continuous version of `LinearMap.applyₗ`. -/
def apply : E →L[𝕜] (E →L[𝕜] Fₗ) →L[𝕜] Fₗ :=
  flip (.id 𝕜 (E →L[𝕜] Fₗ))

variable {𝕜 Fₗ}

@[simp]
theorem apply_apply (v : E) (f : E →L[𝕜] Fₗ) : apply 𝕜 Fₗ v f = f v :=
  rfl

variable (σ₁₂ σ₂₃ E F G)


/-- Composition of continuous semilinear maps as a continuous semibilinear map. -/
def compSL : (F →SL[σ₂₃] G) →L[𝕜₃] (E →SL[σ₁₂] F) →SL[σ₂₃] E →SL[σ₁₃] G :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂'ₛₗ (RingHom.id 𝕜₃) σ₂₃ comp add_comp smul_comp comp_add fun c f g => by
      ext; simp)
    1 fun f g => by simpa only [one_mul] using opNorm_comp_le f g

theorem norm_compSL_le : ‖compSL E F G σ₁₂ σ₂₃‖ ≤ 1 :=
  LinearMap.mkContinuous₂_norm_le _ zero_le_one _

variable {σ₁₂ σ₂₃ E F G}

@[simp]
theorem compSL_apply (f : F →SL[σ₂₃] G) (g : E →SL[σ₁₂] F) : compSL E F G σ₁₂ σ₂₃ f g = f.comp g :=
  rfl

theorem _root_.Continuous.const_clm_comp {X} [TopologicalSpace X] {f : X → E →SL[σ₁₂] F}
    (hf : Continuous f) (g : F →SL[σ₂₃] G) :
    Continuous (fun x => g.comp (f x) : X → E →SL[σ₁₃] G) :=
  (compSL E F G σ₁₂ σ₂₃ g).continuous.comp hf

-- Giving the implicit argument speeds up elaboration significantly
theorem _root_.Continuous.clm_comp_const {X} [TopologicalSpace X] {g : X → F →SL[σ₂₃] G}
    (hg : Continuous g) (f : E →SL[σ₁₂] F) :
    Continuous (fun x => (g x).comp f : X → E →SL[σ₁₃] G) :=
  (@ContinuousLinearMap.flip _ _ _ _ _ (E →SL[σ₁₃] G) _ _ _ _ _ _ _ _ _ _ _ _ _
    (compSL E F G σ₁₂ σ₂₃) f).continuous.comp hg

variable (𝕜 σ₁₂ σ₂₃ E Fₗ Gₗ)

/-- Composition of continuous linear maps as a continuous bilinear map. -/
def compL : (Fₗ →L[𝕜] Gₗ) →L[𝕜] (E →L[𝕜] Fₗ) →L[𝕜] E →L[𝕜] Gₗ :=
  compSL E Fₗ Gₗ (RingHom.id 𝕜) (RingHom.id 𝕜)

theorem norm_compL_le : ‖compL 𝕜 E Fₗ Gₗ‖ ≤ 1 :=
  norm_compSL_le _ _ _ _ _

@[simp]
theorem compL_apply (f : Fₗ →L[𝕜] Gₗ) (g : E →L[𝕜] Fₗ) : compL 𝕜 E Fₗ Gₗ f g = f.comp g :=
  rfl

variable (Eₗ) {𝕜 E Fₗ Gₗ}

/-- Apply `L(x,-)` pointwise to bilinear maps, as a continuous bilinear map -/
@[simps! apply]
def precompR (L : E →L[𝕜] Fₗ →L[𝕜] Gₗ) : E →L[𝕜] (Eₗ →L[𝕜] Fₗ) →L[𝕜] Eₗ →L[𝕜] Gₗ :=
  compL 𝕜 Eₗ Fₗ Gₗ ∘L L

/-- Apply `L(-,y)` pointwise to bilinear maps, as a continuous bilinear map -/
def precompL (L : E →L[𝕜] Fₗ →L[𝕜] Gₗ) : (Eₗ →L[𝕜] E) →L[𝕜] Fₗ →L[𝕜] Eₗ →L[𝕜] Gₗ :=
  (precompR Eₗ (flip L)).flip

@[simp] lemma precompL_apply (L : E →L[𝕜] Fₗ →L[𝕜] Gₗ) (u : Eₗ →L[𝕜] E) (f : Fₗ) (g : Eₗ) :
    precompL Eₗ L u f g = L (u g) f := rfl

theorem norm_precompR_le (L : E →L[𝕜] Fₗ →L[𝕜] Gₗ) : ‖precompR Eₗ L‖ ≤ ‖L‖ :=
  calc
    ‖precompR Eₗ L‖ ≤ ‖compL 𝕜 Eₗ Fₗ Gₗ‖ * ‖L‖ := opNorm_comp_le _ _
    _ ≤ 1 * ‖L‖ := by gcongr; apply norm_compL_le
    _ = ‖L‖ := by rw [one_mul]

theorem norm_precompL_le (L : E →L[𝕜] Fₗ →L[𝕜] Gₗ) : ‖precompL Eₗ L‖ ≤ ‖L‖ := by
  rw [precompL, opNorm_flip, ← opNorm_flip L]
  exact norm_precompR_le _ L.flip

end ContinuousLinearMap

variable {σ₂₁ : 𝕜₂ →+* 𝕜} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]

namespace ContinuousLinearMap

variable {E' F' : Type*} [SeminormedAddCommGroup E'] [SeminormedAddCommGroup F']
variable {𝕜₁' : Type*} {𝕜₂' : Type*} [NontriviallyNormedField 𝕜₁'] [NontriviallyNormedField 𝕜₂']
  [NormedSpace 𝕜₁' E'] [NormedSpace 𝕜₂' F'] {σ₁' : 𝕜₁' →+* 𝕜} {σ₁₃' : 𝕜₁' →+* 𝕜₃} {σ₂' : 𝕜₂' →+* 𝕜₂}
  {σ₂₃' : 𝕜₂' →+* 𝕜₃} [RingHomCompTriple σ₁' σ₁₃ σ₁₃'] [RingHomCompTriple σ₂' σ₂₃ σ₂₃']
  [RingHomIsometric σ₂₃] [RingHomIsometric σ₁₃'] [RingHomIsometric σ₂₃']

/-- Compose a bilinear map `E →SL[σ₁₃] F →SL[σ₂₃] G` with two linear maps
`E' →SL[σ₁'] E` and `F' →SL[σ₂'] F`. -/
def bilinearComp (f : E →SL[σ₁₃] F →SL[σ₂₃] G) (gE : E' →SL[σ₁'] E) (gF : F' →SL[σ₂'] F) :
    E' →SL[σ₁₃'] F' →SL[σ₂₃'] G :=
  ((f.comp gE).flip.comp gF).flip

@[simp]
theorem bilinearComp_apply (f : E →SL[σ₁₃] F →SL[σ₂₃] G) (gE : E' →SL[σ₁'] E) (gF : F' →SL[σ₂'] F)
    (x : E') (y : F') : f.bilinearComp gE gF x y = f (gE x) (gF y) :=
  rfl

@[simp]
lemma bilinearComp_zero {gE : E' →SL[σ₁'] E} {gF : F' →SL[σ₂'] F} :
    bilinearComp (0 : E →SL[σ₁₃] F →SL[σ₂₃] G) gE gF = 0 := rfl

@[simp]
lemma bilinearComp_zero_left {f : E →SL[σ₁₃] F →SL[σ₂₃] G} {gF : F' →SL[σ₂'] F} :
    bilinearComp f (0 : E' →SL[σ₁'] E) gF = 0 := by ext; simp

@[simp]
lemma bilinearComp_zero_right {f : E →SL[σ₁₃] F →SL[σ₂₃] G} {gE : E' →SL[σ₁'] E} :
    bilinearComp f gE (0 : F' →SL[σ₂'] F) = 0 := by ext; simp

variable [RingHomIsometric σ₁₃] [RingHomIsometric σ₁'] [RingHomIsometric σ₂']

/-- Derivative of a continuous bilinear map `f : E →L[𝕜] F →L[𝕜] G` interpreted as a map `E × F → G`
at point `p : E × F` evaluated at `q : E × F`, as a continuous bilinear map. -/
def deriv₂ (f : E →L[𝕜] Fₗ →L[𝕜] Gₗ) : E × Fₗ →L[𝕜] E × Fₗ →L[𝕜] Gₗ :=
  f.bilinearComp (fst _ _ _) (snd _ _ _) + f.flip.bilinearComp (snd _ _ _) (fst _ _ _)

@[simp]
theorem coe_deriv₂ (f : E →L[𝕜] Fₗ →L[𝕜] Gₗ) (p : E × Fₗ) :
    ⇑(f.deriv₂ p) = fun q : E × Fₗ => f p.1 q.2 + f q.1 p.2 :=
  rfl

theorem map_add_add (f : E →L[𝕜] Fₗ →L[𝕜] Gₗ) (x x' : E) (y y' : Fₗ) :
    f (x + x') (y + y') = f x y + f.deriv₂ (x, y) (x', y') + f x' y' := by
  simp only [map_add, _root_.add_apply, coe_deriv₂, add_assoc]
  abel

/-- The norm of the tensor product of a scalar linear map and of an element of a normed space
is the product of the norms. -/
@[simp]
theorem norm_smulRight_apply (c : StrongDual 𝕜 E) (f : Fₗ) : ‖smulRight c f‖ = ‖c‖ * ‖f‖ := by
  refine le_antisymm ?_ ?_
  · refine opNorm_le_bound _ (by positivity) fun x => ?_
    calc
      ‖c x • f‖ = ‖c x‖ * ‖f‖ := norm_smul _ _
      _ ≤ ‖c‖ * ‖x‖ * ‖f‖ := by gcongr; apply le_opNorm
      _ = ‖c‖ * ‖f‖ * ‖x‖ := by ring
  · obtain hf | hf := (norm_nonneg f).eq_or_lt'
    · simp [hf]
    · rw [← le_div_iff₀ hf]
      refine opNorm_le_bound _ (by positivity) fun x => ?_
      rw [div_mul_eq_mul_div, le_div_iff₀ hf]
      calc
        ‖c x‖ * ‖f‖ = ‖c x • f‖ := (norm_smul _ _).symm
        _ = ‖smulRight c f x‖ := rfl
        _ ≤ ‖smulRight c f‖ * ‖x‖ := le_opNorm _ _

/-- The non-negative norm of the tensor product of a scalar linear map and of an element of a normed
space is the product of the non-negative norms. -/
@[simp]
theorem nnnorm_smulRight_apply (c : StrongDual 𝕜 E) (f : Fₗ) : ‖smulRight c f‖₊ = ‖c‖₊ * ‖f‖₊ :=
  NNReal.eq <| c.norm_smulRight_apply f

@[simp] theorem norm_toSpanSingleton (x : E) : ‖toSpanSingleton 𝕜 x‖ = ‖x‖ := by
  simp [← smulRight_id, norm_id]

@[simp] theorem nnnorm_toSpanSingleton (x : E) : ‖toSpanSingleton 𝕜 x‖₊ = ‖x‖₊ :=
  NNReal.eq <| norm_toSpanSingleton _

variable (𝕜 E Fₗ) in
/-- `ContinuousLinearMap.smulRight` as a continuous trilinear map:
`smulRightL (c : StrongDual 𝕜 E) (f : F) (x : E) = c x • f`.

This is also known as a rank-one operator.
See also `InnerProductSpace.rankOne` for the rank-one operator on Hilbert spaces. -/
@[simps! apply_apply]
def smulRightL : StrongDual 𝕜 E →L[𝕜] Fₗ →L[𝕜] E →L[𝕜] Fₗ :=
  LinearMap.mkContinuous₂
    { toFun := smulRightₗ
      map_add' := fun c₁ c₂ => by
        ext x
        simp [add_smul]
      map_smul' := fun m c => by
        ext x
        simp [smul_smul] }
    1 fun c x => by
      simp only [coe_smulRightₗ, one_mul, norm_smulRight_apply, LinearMap.coe_mk, AddHom.coe_mk,
        le_refl]

@[deprecated norm_smulRight_apply (since := "2025-11-12")]
theorem norm_smulRightL_apply (c : StrongDual 𝕜 E) (f : Fₗ) :
    ‖smulRightL 𝕜 E Fₗ c f‖ = ‖c‖ * ‖f‖ := by
  simp

end ContinuousLinearMap

end SemiNormed

section Restrict

namespace ContinuousLinearMap

variable {𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace 𝕜' E] [IsScalarTower 𝕜 𝕜' E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace 𝕜' F] [IsScalarTower 𝕜 𝕜' F]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedSpace 𝕜' G] [IsScalarTower 𝕜 𝕜' G]

variable (𝕜) in
/-- Convenience function for restricting the linearity of a bilinear map. -/
def bilinearRestrictScalars (B : E →L[𝕜'] F →L[𝕜'] G) : E →L[𝕜] F →L[𝕜] G :=
  (restrictScalarsL 𝕜' F G 𝕜 𝕜).comp (B.restrictScalars 𝕜)

variable (B : E →L[𝕜'] F →L[𝕜'] G) (x : E) (y : F)

theorem bilinearRestrictScalars_eq_restrictScalarsL_comp_restrictScalars :
    B.bilinearRestrictScalars 𝕜 = (restrictScalarsL 𝕜' F G 𝕜 𝕜).comp (B.restrictScalars 𝕜) := rfl

theorem bilinearRestrictScalars_eq_restrictScalars_restrictScalarsL_comp :
    B.bilinearRestrictScalars 𝕜 = restrictScalars 𝕜 ((restrictScalarsL 𝕜' F G 𝕜 𝕜').comp B) := rfl

variable (𝕜) in
@[simp]
theorem bilinearRestrictScalars_apply_apply : (B.bilinearRestrictScalars 𝕜) x y = B x y := rfl

@[simp]
theorem norm_bilinearRestrictScalars : ‖B.bilinearRestrictScalars 𝕜‖ = ‖B‖ := rfl

end ContinuousLinearMap

end Restrict
