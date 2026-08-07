/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Zhouhang Zhou
-/
module

public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
public import Mathlib.Topology.Algebra.UniformFilterBasis

/-!

# Extension of continuous linear maps on locally convex spaces

In this file we provide two different ways to extend a continuous linear map defined on a dense
subspace to the entire Banach space.

* `ContinuousLinearMap.extend`: Extend `f : E →SL[σ₁₂] F` to a continuous linear map
  `Eₗ →SL[σ₁₂] F`, where `e : E →ₗ[𝕜] Eₗ` is a dense map that is `IsUniformInducing`.
* `LinearMap.extendOfIsBounded`: Extend `f : E →ₛₗ[σ₁₂] F` to a continuous linear map
  `Eₗ →SL[σ₁₂] F`, where `e : E →ₗ[𝕜] Eₗ` is a dense map and we have the norm estimate
  `‖f x‖ ≤ C * ‖e x‖` for all `x : E`.

-/

@[expose] public noncomputable section

open scoped NNReal

variable {𝕜 𝕜₂ E Eₗ F Fₗ ι ι' : Type*}

namespace ContinuousLinearMap

section Extend

section Ring

variable [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E]
  [AddCommGroup F] [UniformSpace F] [IsUniformAddGroup F] [T0Space F]
  [AddCommMonoid Eₗ] [UniformSpace Eₗ] [ContinuousAdd Eₗ]
  [Semiring 𝕜] [Semiring 𝕜₂] [Module 𝕜 E] [Module 𝕜₂ F] [Module 𝕜 Eₗ]
  [ContinuousConstSMul 𝕜 Eₗ] [ContinuousConstSMul 𝕜₂ F]
  {σ₁₂ : 𝕜 →+* 𝕜₂} (f g : E →SL[σ₁₂] F) [CompleteSpace F] (e : E →L[𝕜] Eₗ)

open scoped Classical in
/-- Extension of a continuous linear map `f : E →SL[σ₁₂] F`, with `E` a normed space and `F` a
complete normed space, along a uniform and dense embedding `e : E →L[𝕜] Eₗ`. -/
def extend : Eₗ →SL[σ₁₂] F :=
  if h : DenseRange e ∧ IsUniformInducing e then
  -- extension of `f` is continuous
  have cont := (uniformContinuous_uniformly_extend h.2 h.1 f.uniformContinuous).continuous
  -- extension of `f` agrees with `f` on the domain of the embedding `e`
  have eq := uniformly_extend_of_ind h.2 h.1 f.uniformContinuous
  { toFun := (h.2.isDenseInducing h.1).extend f
    map_add' := by
      refine h.1.induction_on₂ ?_ ?_
      · exact isClosed_eq (cont.comp continuous_add)
          ((cont.comp continuous_fst).add (cont.comp continuous_snd))
      · intro x y
        simp only [eq, ← e.map_add]
        exact f.map_add _ _
    map_smul' := fun k => by
      refine fun b => h.1.induction_on b ?_ ?_
      · exact isClosed_eq (cont.comp (continuous_const_smul _))
          ((continuous_const_smul _).comp cont)
      · intro x
        rw [← map_smul]
        simp only [eq]
        exact map_smulₛₗ _ _ _
    cont }
  else 0

variable {e}

@[simp]
theorem extend_eq (h_dense : DenseRange e) (h_e : IsUniformInducing e) (x : E) :
    extend f e (e x) = f x := by
  simp only [extend, h_dense, h_e, and_self, ↓reduceDIte, coe_mk', LinearMap.coe_mk, AddHom.coe_mk]
  exact IsDenseInducing.extend_eq (h_e.isDenseInducing h_dense) f.cont _

theorem extend_unique (h_dense : DenseRange e) (h_e : IsUniformInducing e) (g : Eₗ →SL[σ₁₂] F)
    (H : g.comp e = f) : extend f e = g := by
  simp only [extend, h_dense, h_e, and_self, ↓reduceDIte]
  exact ContinuousLinearMap.coeFn_injective <|
    uniformly_extend_unique h_e h_dense (ContinuousLinearMap.ext_iff.1 H) g.continuous

@[simp]
theorem extend_zero (h_dense : DenseRange e) (h_e : IsUniformInducing e) :
    extend (0 : E →SL[σ₁₂] F) e = 0 :=
  extend_unique _ h_dense h_e _ (zero_comp _)

end Ring

end Extend

end ContinuousLinearMap

namespace LinearMap

section compInv

variable [NormedField 𝕜] [NormedField 𝕜₂] {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂]
  [AddCommGroup E] [AddCommGroup F] [AddCommGroup Eₗ]
  [TopologicalSpace F]
  [Module 𝕜 E] [Module 𝕜₂ F] [Module 𝕜 Eₗ]

variable {p : SeminormFamily 𝕜 Eₗ ι} {q : SeminormFamily 𝕜₂ F ι'}
variable (f : E →ₛₗ[σ₁₂] F) (g : E →ₗ[𝕜] Eₗ)

theorem ker_le_ker_of_isBounded [T1Space F] (hq : WithSeminorms q)
    (h : Seminorm.IsBounded (p.comp g) q f) : g.ker ≤ f.ker := by
  intro x (hx : g x = 0)
  suffices ∀ (i : ι'), (q i) (f x) = 0 by
    have foo := hq.separating_of_T1 (f x)
    simp; grind
  intro i
  obtain ⟨s, C, hC⟩ := h i
  rw [Seminorm.le_def] at hC
  apply le_antisymm _ (by positivity)
  convert! hC x
  symm
  simp only [_root_.smul_apply, smul_eq_zero]
  right
  simp [← SeminormFamily.finset_sup_comp, hx]

variable [TopologicalSpace Eₗ]

open scoped Classical in
/-- Composition of a semilinear map `f` with the left inverse of a linear map `g` as a continuous
linear map provided that the norm estimate `‖f x‖ ≤ C * ‖g x‖` holds for all `x : E`. -/
def compLeftInverse [T2Space F] (hp : WithSeminorms p) (hq : WithSeminorms q) :
    g.range →SL[σ₁₂] F :=
  if h : Seminorm.IsBounded (p.comp g) q f then
    ⟨((g.ker.liftQ f <| ker_le_ker_of_isBounded f g hq h).comp
    g.quotKerEquivRange.symm.toLinearMap), ?_⟩
  else 0
where finally
  refine WithSeminorms.continuous_of_isBounded (p := p.comp g.range.subtype) ?_ hq _ ?_
  · apply LinearMap.withSeminorms_induced hp
  · intro i
    obtain ⟨s, C, hC⟩ := h i
    use s, C
    intro ⟨y, x, hxy⟩
    specialize hC x
    simp only [← SeminormFamily.finset_sup_comp, Seminorm.comp_apply, _root_.smul_apply] at hC
    simpa [← SeminormFamily.finset_sup_comp, ← hxy]

theorem compLeftInverse_apply_of_bdd [T2Space F] (hp : WithSeminorms p) (hq : WithSeminorms q)
    (h : Seminorm.IsBounded (p.comp g) q f)
    (x : E) (y : Eₗ) (hx : g x = y) :
    f.compLeftInverse g hp hq ⟨y, ⟨x, hx⟩⟩ = f x := by
  simp [compLeftInverse, h, ← hx]

end compInv

section Extend

variable [NormedField 𝕜] [NormedField 𝕜₂] {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂]
  [AddCommGroup E] [AddCommGroup F] [AddCommGroup Eₗ]
  [UniformSpace F] [IsUniformAddGroup F]
  [Module 𝕜 E] [Module 𝕜₂ F] [Module 𝕜 Eₗ]

variable {p : SeminormFamily 𝕜 Eₗ ι} {q : SeminormFamily 𝕜₂ F ι'}
variable (f : E →ₛₗ[σ₁₂] F) (e : E →ₗ[𝕜] Eₗ)

variable [UniformSpace Eₗ] [IsUniformAddGroup Eₗ]
  [ContinuousConstSMul 𝕜₂ F] [CompleteSpace F]

instance (S : Submodule 𝕜 Eₗ) : IsUniformAddGroup S :=
  inferInstanceAs (IsUniformAddGroup S.toAddSubgroup)

variable [ContinuousConstSMul 𝕜 Eₗ] [T2Space F]

/-- Extension of a linear map `f : E →ₛₗ[σ₁₂] F` to a continuous linear map `Eₗ →SL[σ₁₂] F`,
where `E` is a normed space and `F` a complete normed space, using a dense map `e : E →ₗ[𝕜] Eₗ`
together with a bound `‖f x‖ ≤ C * ‖e x‖` for all `x : E`. -/
def extendOfIsBounded (hp : WithSeminorms p) (hq : WithSeminorms q) : Eₗ →SL[σ₁₂] F :=
  (f.compLeftInverse e hp hq).extend e.range.subtypeL

variable {f e}

theorem extendOfIsBounded_eq (h_dense : DenseRange e) (hp : WithSeminorms p) (hq : WithSeminorms q)
    (h : Seminorm.IsBounded (p.comp e) q f)
    (x : E) : f.extendOfIsBounded e hp hq (e x) = f x := by
  have := (f.compLeftInverse e hp hq).extend_eq (e := (LinearMap.range e).subtypeL)
    (by simpa using! h_dense) isUniformEmbedding_subtype_val.isUniformInducing
  convert! this ⟨e x, LinearMap.mem_range_self e x⟩
  exact (compLeftInverse_apply_of_bdd _ _ hp hq h _ _ rfl).symm

theorem extendOfIsBounded_unique (h_dense : DenseRange e) (hp : WithSeminorms p)
    (hq : WithSeminorms q) (h : Seminorm.IsBounded (p.comp e) q f) (g : Eₗ →SL[σ₁₂] F)
    (H : g.toLinearMap.comp e = f) : f.extendOfIsBounded e hp hq = g := by
  apply ContinuousLinearMap.extend_unique
  · simpa using! h_dense
  · exact isUniformEmbedding_subtype_val.isUniformInducing
  ext ⟨y, x, hxy⟩
  rw [compLeftInverse_apply_of_bdd _ _ hp hq h x y hxy]
  simp [← hxy, ← H]

end Extend

end LinearMap
