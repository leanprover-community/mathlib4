/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Zhouhang Zhou
-/
import Mathlib.Analysis.Normed.Operator.Basic

/-!

# Extension of continuous linear maps on Banach spaces

In this file we provide two different ways to extend a continuous linear map defined on a dense
subspace to the entire Banach space.

* `ContinuousLinearMap.extend`: Extend from a dense subspace using `IsUniformInducing`
* `ContinuousLinearMap.extendOfNorm`: Extend from a continuous linear map that is a dense
injection into the domain and using a norm estimate.

-/

suppress_compilation

open scoped NNReal

variable {𝕜 𝕜₂ E Eₗ F Fₗ : Type*}

namespace ContinuousLinearMap

section Extend

section Ring

variable [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E]
  [AddCommGroup F] [UniformSpace F] [IsUniformAddGroup F] [T0Space F]
  [AddCommMonoid Eₗ] [UniformSpace Eₗ] [ContinuousAdd Eₗ]
  [Semiring 𝕜] [Semiring 𝕜₂] [Module 𝕜 E] [Module 𝕜₂ F] [Module 𝕜 Eₗ]
  [ContinuousConstSMul 𝕜 Eₗ] [ContinuousConstSMul 𝕜₂ F]
  {σ₁₂ : 𝕜 →+* 𝕜₂} (f g : E →SL[σ₁₂] F) [CompleteSpace F] (e : E →L[𝕜] Eₗ)

variable (h_dense : DenseRange e) (h_e : IsUniformInducing e)

/-- Extension of a continuous linear map `f : E →SL[σ₁₂] F`, with `E` a normed space and `F` a
complete normed space, along a uniform and dense embedding `e : E →L[𝕜] Eₗ`. -/
def extend : Eₗ →SL[σ₁₂] F :=
  -- extension of `f` is continuous
  have cont := (uniformContinuous_uniformly_extend h_e h_dense f.uniformContinuous).continuous
  -- extension of `f` agrees with `f` on the domain of the embedding `e`
  have eq := uniformly_extend_of_ind h_e h_dense f.uniformContinuous
  { toFun := (h_e.isDenseInducing h_dense).extend f
    map_add' := by
      refine h_dense.induction_on₂ ?_ ?_
      · exact isClosed_eq (cont.comp continuous_add)
          ((cont.comp continuous_fst).add (cont.comp continuous_snd))
      · intro x y
        simp only [eq, ← e.map_add]
        exact f.map_add _ _
    map_smul' := fun k => by
      refine fun b => h_dense.induction_on b ?_ ?_
      · exact isClosed_eq (cont.comp (continuous_const_smul _))
          ((continuous_const_smul _).comp cont)
      · intro x
        rw [← map_smul]
        simp only [eq]
        exact ContinuousLinearMap.map_smulₛₗ _ _ _
    cont }

@[simp]
theorem extend_eq (x : E) : extend f e h_dense h_e (e x) = f x :=
  IsDenseInducing.extend_eq (h_e.isDenseInducing h_dense) f.cont _

theorem extend_unique (g : Eₗ →SL[σ₁₂] F) (H : g.comp e = f) : extend f e h_dense h_e = g :=
  ContinuousLinearMap.coeFn_injective <|
    uniformly_extend_unique h_e h_dense (ContinuousLinearMap.ext_iff.1 H) g.continuous

@[simp]
theorem extend_zero : extend (0 : E →SL[σ₁₂] F) e h_dense h_e = 0 :=
  extend_unique _ _ _ _ _ (zero_comp _)

end Ring

section NormedField

variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] {σ₁₂ : 𝕜 →+* 𝕜₂}
  [NormedAddCommGroup E] [NormedAddCommGroup Eₗ] [NormedAddCommGroup F] [NormedAddCommGroup Fₗ]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜 Eₗ] [NormedSpace 𝕜₂ F] [NormedSpace 𝕜₂ Fₗ] [CompleteSpace F]
  (f g : E →SL[σ₁₂] F) (e : E →L[𝕜] Eₗ)

variable (h_dense : DenseRange e) (h_e : IsUniformInducing e)

variable {N : ℝ≥0} (h_e : ∀ x, ‖x‖ ≤ N * ‖e x‖) [RingHomIsometric σ₁₂]

/-- If a dense embedding `e : E →L[𝕜] G` expands the norm by a constant factor `N⁻¹`, then the
norm of the extension of `f` along `e` is bounded by `N * ‖f‖`. -/
theorem opNorm_extend_le :
    ‖f.extend e h_dense (isUniformEmbedding_of_bound _ h_e).isUniformInducing‖ ≤ N * ‖f‖ := by
  -- Add `opNorm_le_of_dense`?
  refine opNorm_le_bound _ ?_ (isClosed_property h_dense (isClosed_le ?_ ?_) fun x ↦ ?_)
  · cases le_total 0 N with
    | inl hN => exact mul_nonneg hN (norm_nonneg _)
    | inr hN =>
      have : Unique E := ⟨⟨0⟩, fun x ↦ norm_le_zero_iff.mp <|
        (h_e x).trans (mul_nonpos_of_nonpos_of_nonneg hN (norm_nonneg _))⟩
      obtain rfl : f = 0 := Subsingleton.elim ..
      simp
  · exact (cont _).norm
  · exact continuous_const.mul continuous_norm
  · rw [extend_eq]
    calc
      ‖f x‖ ≤ ‖f‖ * ‖x‖ := le_opNorm _ _
      _ ≤ ‖f‖ * (N * ‖e x‖) := mul_le_mul_of_nonneg_left (h_e x) (norm_nonneg _)
      _ ≤ N * ‖f‖ * ‖e x‖ := by rw [mul_comm ↑N ‖f‖, mul_assoc]


end NormedField

end Extend

end ContinuousLinearMap

namespace LinearMap

section LeftInverse

variable [DivisionRing 𝕜] [AddCommGroup E] [AddCommGroup F] [Module 𝕜 E] [Module 𝕜 F]

variable (f : E →ₗ[𝕜] F)

open scoped Classical in
/-- The left inverse of `f : E →ₗ[𝕜] F`.

If `f` is not injective, then we use the junk value `0`. -/
def leftInverse : F →ₗ[𝕜] E :=
  if h_inj : LinearMap.ker f = ⊥ then
  Classical.choose (f.exists_leftInverse_of_injective h_inj)
  else 0

/-- If `f` is injective, then the left inverse composed with `f` is the identity. -/
@[simp]
theorem leftInverse_apply_of_inj (h_inj : LinearMap.ker f = ⊥) (x : E) :
    f.leftInverse (f x) = x := by
  have := Classical.choose_spec (f.exists_leftInverse_of_injective h_inj)
  rw [LinearMap.ext_iff] at this
  simpa [leftInverse, h_inj] using this x

end LeftInverse

section compInv

variable [DivisionRing 𝕜] [DivisionRing 𝕜₂] {σ₁₂ : 𝕜 →+* 𝕜₂}
  [AddCommGroup E] [SeminormedAddCommGroup F] [SeminormedAddCommGroup Eₗ]
  [Module 𝕜 E] [Module 𝕜₂ F] [Module 𝕜 Eₗ]

variable (f : E →ₛₗ[σ₁₂] F) (g : E →ₗ[𝕜] Eₗ)

open scoped Classical in
/-- Composition with the left inverse as a CLM. -/
def compLeftInverse :=
  if h : LinearMap.ker g = ⊥ ∧ ∃ (C : ℝ), ∀ (x : E), ‖f x‖ ≤ C * ‖g x‖ then
  (f ∘ₛₗ (g.leftInverse.domRestrict
    (LinearMap.range g))).mkContinuousOfExistsBound
  (by
    rcases h.2 with ⟨C, hC⟩
    use C
    rintro ⟨x, y, hxy⟩
    simp only [← hxy, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.domRestrict_apply, AddSubgroupClass.coe_norm]
    convert hC y
    apply g.leftInverse_apply_of_inj h.1)
  else 0

@[simp]
theorem compLeftInverse_apply_of_inj_bdd (h_inj : LinearMap.ker g = ⊥)
    (h_norm : ∃ (C : ℝ), ∀ (x : E), ‖f x‖ ≤ C * ‖g x‖) (y : LinearMap.range g) :
    f.compLeftInverse g y = (f ∘ₛₗ (g.leftInverse.domRestrict
      (LinearMap.range g))) y := by
  simp [compLeftInverse, h_inj, h_norm]

end compInv

section NormedDivisionRing

variable [NormedDivisionRing 𝕜] [NormedDivisionRing 𝕜₂] {σ₁₂ : 𝕜 →+* 𝕜₂}
  [AddCommGroup E] [SeminormedAddCommGroup Eₗ] [NormedAddCommGroup F]
  [Module 𝕜 E] [Module 𝕜₂ F] [IsBoundedSMul 𝕜₂ F] [Module 𝕜 Eₗ] [IsBoundedSMul 𝕜 Eₗ]
  [CompleteSpace F]

variable (f : E →ₛₗ[σ₁₂] F) (e : E →ₗ[𝕜] Eₗ)

open scoped Classical in
/-- Extension of a continuous linear map `f : E →SL[σ₁₂] F` to `Fₗ →SL[σ₁₂] F`,
where `E` is a normed space and `F` a complete normed space,
using an injective dense embedding `e : E →L[𝕜] Fₗ` together with a bound `‖f x‖ ≤ C * ‖e x‖`
for all `x : E`. -/
def extendOfNorm : Eₗ →SL[σ₁₂] F :=
  if h : DenseRange e then
  (f.compLeftInverse e).extend (LinearMap.range e).subtypeL (by simpa using h)
    isUniformEmbedding_subtype_val.isUniformInducing
  else 0

variable {f e}

theorem extendOfNorm_eq (h_inj : LinearMap.ker e = ⊥)
    (h_dense : DenseRange e) (h_norm : ∃ C, ∀ x, ‖f x‖ ≤ C * ‖e x‖) (x : E) :
    f.extendOfNorm e (e x) = f x := by
  simp only [extendOfNorm, h_dense, ↓reduceDIte]
  have := (f.compLeftInverse e).extend_eq (LinearMap.range e).subtypeL (by simpa using h_dense)
    isUniformEmbedding_subtype_val.isUniformInducing
  convert this ⟨e x, LinearMap.mem_range_self e x⟩
  simp only [h_inj, h_norm, compLeftInverse_apply_of_inj_bdd, LinearMap.coe_comp,
    Function.comp_apply, LinearMap.domRestrict_apply]
  congr
  apply (e.leftInverse_apply_of_inj h_inj _).symm

theorem extendOfNorm_norm_le (h_inj : LinearMap.ker e = ⊥) (h_dense : DenseRange e) (C : ℝ)
    (h_norm : ∀ (x : E), ‖f x‖ ≤ C * ‖e x‖) (x : Eₗ) :
    ‖f.extendOfNorm e x‖ ≤ C * ‖x‖ := by
  have h_mem : ∀ (x : Eₗ) (hy : x ∈ (LinearMap.range e)), ‖extendOfNorm f e x‖ ≤ C * ‖x‖ := by
    rintro x ⟨y, hxy⟩
    rw [← hxy]
    convert h_norm y
    apply extendOfNorm_eq h_inj h_dense ⟨C, h_norm⟩
  exact h_dense.induction h_mem (isClosed_le (by fun_prop) (by fun_prop)) x

end NormedDivisionRing

section NormedField

variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] {σ₁₂ : 𝕜 →+* 𝕜₂}
  [NormedAddCommGroup F] [SeminormedAddCommGroup Eₗ]
  [NormedSpace 𝕜₂ F] [NormedSpace 𝕜 Eₗ]
  [AddCommGroup E] [Module 𝕜 E] [CompleteSpace F]

variable {f : E →ₛₗ[σ₁₂] F} {e : E →ₗ[𝕜] Eₗ}

theorem extendOfNorm_opNorm_le (h_inj : LinearMap.ker e = ⊥)
    (h_dense : DenseRange e) {C : ℝ}
    (hC : 0 ≤ C) (h_norm : ∀ (x : E), ‖f x‖ ≤ C * ‖e x‖) : ‖f.extendOfNorm e‖ ≤ C :=
  (f.extendOfNorm e).opNorm_le_bound hC (extendOfNorm_norm_le h_inj h_dense C h_norm)

end NormedField

end LinearMap
