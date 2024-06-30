/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Eric Wieser
-/
import Mathlib.Algebra.Quaternion
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Algebra

#align_import analysis.quaternion from "leanprover-community/mathlib"@"07992a1d1f7a4176c6d3f160209608be4e198566"

/-!
# Quaternions as a normed algebra

In this file we define the following structures on the space `ℍ := ℍ[ℝ]` of quaternions:

* inner product space;
* normed ring;
* normed space over `ℝ`.

We show that the norm on `ℍ[ℝ]` agrees with the euclidean norm of its components.

## Notation

The following notation is available with `open Quaternion` or `open scoped Quaternion`:

* `ℍ` : quaternions

## Tags

quaternion, normed ring, normed space, normed algebra
-/


@[inherit_doc] scoped[Quaternion] notation "ℍ" => Quaternion ℝ

open scoped RealInnerProductSpace

namespace Quaternion

instance : Inner ℝ ℍ :=
  ⟨fun a b => (a * star b).re⟩

theorem inner_self (a : ℍ) : ⟪a, a⟫ = normSq a :=
  rfl
#align quaternion.inner_self Quaternion.inner_self

theorem inner_def (a b : ℍ) : ⟪a, b⟫ = (a * star b).re :=
  rfl
#align quaternion.inner_def Quaternion.inner_def

noncomputable instance : NormedAddCommGroup ℍ :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℝ ℍ _ _ _
    { toInner := inferInstance
      conj_symm := fun x y => by simp [inner_def, mul_comm]
      nonneg_re := fun x => normSq_nonneg
      definite := fun x => normSq_eq_zero.1
      add_left := fun x y z => by simp only [inner_def, add_mul, add_re]
      smul_left := fun x y r => by simp [inner_def] }

noncomputable instance : InnerProductSpace ℝ ℍ :=
  InnerProductSpace.ofCore _

theorem normSq_eq_norm_mul_self (a : ℍ) : normSq a = ‖a‖ * ‖a‖ := by
  rw [← inner_self, real_inner_self_eq_norm_mul_norm]
#align quaternion.norm_sq_eq_norm_sq Quaternion.normSq_eq_norm_mul_self

instance : NormOneClass ℍ :=
  ⟨by rw [norm_eq_sqrt_real_inner, inner_self, normSq.map_one, Real.sqrt_one]⟩

@[simp, norm_cast]
theorem norm_coe (a : ℝ) : ‖(a : ℍ)‖ = ‖a‖ := by
  rw [norm_eq_sqrt_real_inner, inner_self, normSq_coe, Real.sqrt_sq_eq_abs, Real.norm_eq_abs]
#align quaternion.norm_coe Quaternion.norm_coe

@[simp, norm_cast]
theorem nnnorm_coe (a : ℝ) : ‖(a : ℍ)‖₊ = ‖a‖₊ :=
  Subtype.ext <| norm_coe a
#align quaternion.nnnorm_coe Quaternion.nnnorm_coe

@[simp, nolint simpNF] -- Porting note (#10959): simp cannot prove this
theorem norm_star (a : ℍ) : ‖star a‖ = ‖a‖ := by
  simp_rw [norm_eq_sqrt_real_inner, inner_self, normSq_star]
#align quaternion.norm_star Quaternion.norm_star

@[simp, nolint simpNF] -- Porting note (#10959): simp cannot prove this
theorem nnnorm_star (a : ℍ) : ‖star a‖₊ = ‖a‖₊ :=
  Subtype.ext <| norm_star a
#align quaternion.nnnorm_star Quaternion.nnnorm_star

noncomputable instance : NormedDivisionRing ℍ where
  dist_eq _ _ := rfl
  norm_mul' a b := by
    simp only [norm_eq_sqrt_real_inner, inner_self, normSq.map_mul]
    exact Real.sqrt_mul normSq_nonneg _

-- Porting note: added `noncomputable`
noncomputable instance : NormedAlgebra ℝ ℍ where
  norm_smul_le := norm_smul_le
  toAlgebra := Quaternion.algebra

instance : CstarRing ℍ where
  norm_star_mul_self {x} := (norm_mul _ _).trans <| congr_arg (· * ‖x‖) (norm_star x)

/-- Coercion from `ℂ` to `ℍ`. -/
@[coe] def coeComplex (z : ℂ) : ℍ := ⟨z.re, z.im, 0, 0⟩

instance : Coe ℂ ℍ := ⟨coeComplex⟩

@[simp, norm_cast]
theorem coeComplex_re (z : ℂ) : (z : ℍ).re = z.re :=
  rfl
#align quaternion.coe_complex_re Quaternion.coeComplex_re

@[simp, norm_cast]
theorem coeComplex_imI (z : ℂ) : (z : ℍ).imI = z.im :=
  rfl
#align quaternion.coe_complex_im_i Quaternion.coeComplex_imI

@[simp, norm_cast]
theorem coeComplex_imJ (z : ℂ) : (z : ℍ).imJ = 0 :=
  rfl
#align quaternion.coe_complex_im_j Quaternion.coeComplex_imJ

@[simp, norm_cast]
theorem coeComplex_imK (z : ℂ) : (z : ℍ).imK = 0 :=
  rfl
#align quaternion.coe_complex_im_k Quaternion.coeComplex_imK

@[simp, norm_cast]
theorem coeComplex_add (z w : ℂ) : ↑(z + w) = (z + w : ℍ) := by ext <;> simp
#align quaternion.coe_complex_add Quaternion.coeComplex_add

@[simp, norm_cast]
theorem coeComplex_mul (z w : ℂ) : ↑(z * w) = (z * w : ℍ) := by ext <;> simp
#align quaternion.coe_complex_mul Quaternion.coeComplex_mul

@[simp, norm_cast]
theorem coeComplex_zero : ((0 : ℂ) : ℍ) = 0 :=
  rfl
#align quaternion.coe_complex_zero Quaternion.coeComplex_zero

@[simp, norm_cast]
theorem coeComplex_one : ((1 : ℂ) : ℍ) = 1 :=
  rfl
#align quaternion.coe_complex_one Quaternion.coeComplex_one

@[simp, norm_cast] -- Porting note (#10959): simp cannot prove this
theorem coe_real_complex_mul (r : ℝ) (z : ℂ) : (r • z : ℍ) = ↑r * ↑z := by ext <;> simp
#align quaternion.coe_real_complex_mul Quaternion.coe_real_complex_mul

@[simp, norm_cast]
theorem coeComplex_coe (r : ℝ) : ((r : ℂ) : ℍ) = r :=
  rfl
#align quaternion.coe_complex_coe Quaternion.coeComplex_coe

/-- Coercion `ℂ →ₐ[ℝ] ℍ` as an algebra homomorphism. -/
def ofComplex : ℂ →ₐ[ℝ] ℍ where
  toFun := (↑)
  map_one' := rfl
  map_zero' := rfl
  map_add' := coeComplex_add
  map_mul' := coeComplex_mul
  commutes' _ := rfl
#align quaternion.of_complex Quaternion.ofComplex

@[simp]
theorem coe_ofComplex : ⇑ofComplex = coeComplex := rfl
#align quaternion.coe_of_complex Quaternion.coe_ofComplex

/-- The norm of the components as a euclidean vector equals the norm of the quaternion. -/
theorem norm_piLp_equiv_symm_equivTuple (x : ℍ) :
    ‖(WithLp.equiv 2 (Fin 4 → _)).symm (equivTuple ℝ x)‖ = ‖x‖ := by
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner, inner_self, normSq_def', PiLp.inner_apply,
    Fin.sum_univ_four]
  simp_rw [RCLike.inner_apply, starRingEnd_apply, star_trivial, ← sq]
  rfl
set_option linter.uppercaseLean3 false in
#align quaternion.norm_pi_Lp_equiv_symm_equiv_tuple Quaternion.norm_piLp_equiv_symm_equivTuple

/-- `QuaternionAlgebra.linearEquivTuple` as a `LinearIsometryEquiv`. -/
@[simps apply symm_apply]
noncomputable def linearIsometryEquivTuple : ℍ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4) :=
  { (QuaternionAlgebra.linearEquivTuple (-1 : ℝ) (-1 : ℝ)).trans
      (WithLp.linearEquiv 2 ℝ (Fin 4 → ℝ)).symm with
    toFun := fun a => (WithLp.equiv _ (Fin 4 → _)).symm ![a.1, a.2, a.3, a.4]
    invFun := fun a => ⟨a 0, a 1, a 2, a 3⟩
    norm_map' := norm_piLp_equiv_symm_equivTuple }
#align quaternion.linear_isometry_equiv_tuple Quaternion.linearIsometryEquivTuple

@[continuity]
theorem continuous_coe : Continuous (coe : ℝ → ℍ) :=
  continuous_algebraMap ℝ ℍ
#align quaternion.continuous_coe Quaternion.continuous_coe

@[continuity]
theorem continuous_normSq : Continuous (normSq : ℍ → ℝ) := by
  simpa [← normSq_eq_norm_mul_self] using
    (continuous_norm.mul continuous_norm : Continuous fun q : ℍ => ‖q‖ * ‖q‖)
#align quaternion.continuous_norm_sq Quaternion.continuous_normSq

@[continuity]
theorem continuous_re : Continuous fun q : ℍ => q.re :=
  (continuous_apply 0).comp linearIsometryEquivTuple.continuous
#align quaternion.continuous_re Quaternion.continuous_re

@[continuity]
theorem continuous_imI : Continuous fun q : ℍ => q.imI :=
  (continuous_apply 1).comp linearIsometryEquivTuple.continuous
#align quaternion.continuous_im_i Quaternion.continuous_imI

@[continuity]
theorem continuous_imJ : Continuous fun q : ℍ => q.imJ :=
  (continuous_apply 2).comp linearIsometryEquivTuple.continuous
#align quaternion.continuous_im_j Quaternion.continuous_imJ

@[continuity]
theorem continuous_imK : Continuous fun q : ℍ => q.imK :=
  (continuous_apply 3).comp linearIsometryEquivTuple.continuous
#align quaternion.continuous_im_k Quaternion.continuous_imK

@[continuity]
theorem continuous_im : Continuous fun q : ℍ => q.im := by
  simpa only [← sub_self_re] using continuous_id.sub (continuous_coe.comp continuous_re)
#align quaternion.continuous_im Quaternion.continuous_im

instance : CompleteSpace ℍ :=
  haveI : UniformEmbedding linearIsometryEquivTuple.toLinearEquiv.toEquiv.symm :=
    linearIsometryEquivTuple.toContinuousLinearEquiv.symm.uniformEmbedding
  (completeSpace_congr this).1 (by infer_instance)

section infinite_sum

variable {α : Type*}

@[simp, norm_cast]
theorem hasSum_coe {f : α → ℝ} {r : ℝ} : HasSum (fun a => (f a : ℍ)) (↑r : ℍ) ↔ HasSum f r :=
  ⟨fun h => by simpa only using h.map (show ℍ →ₗ[ℝ] ℝ from QuaternionAlgebra.reₗ _ _) continuous_re,
    fun h => by simpa only using h.map (algebraMap ℝ ℍ) (continuous_algebraMap _ _)⟩
#align quaternion.has_sum_coe Quaternion.hasSum_coe

@[simp, norm_cast]
theorem summable_coe {f : α → ℝ} : (Summable fun a => (f a : ℍ)) ↔ Summable f := by
  simpa only using
    Summable.map_iff_of_leftInverse (algebraMap ℝ ℍ) (show ℍ →ₗ[ℝ] ℝ from QuaternionAlgebra.reₗ _ _)
      (continuous_algebraMap _ _) continuous_re coe_re
#align quaternion.summable_coe Quaternion.summable_coe

@[norm_cast]
theorem tsum_coe (f : α → ℝ) : (∑' a, (f a : ℍ)) = ↑(∑' a, f a) := by
  by_cases hf : Summable f
  · exact (hasSum_coe.mpr hf.hasSum).tsum_eq
  · simp [tsum_eq_zero_of_not_summable hf, tsum_eq_zero_of_not_summable (summable_coe.not.mpr hf)]
#align quaternion.tsum_coe Quaternion.tsum_coe

end infinite_sum

end Quaternion
