/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Eric Wieser
-/
import Mathlib.Algebra.Quaternion
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Algebra

/-!
# Quaternions as a normed algebra

In this file we define the following structures on the space `ℍ := ℍ[ℝ]` of quaternions:

* inner product space;
* normed ring;
* normed space over `ℝ`.

We show that the norm on `ℍ[ℝ]` agrees with the Euclidean norm of its components.

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

theorem inner_def (a b : ℍ) : ⟪a, b⟫ = (a * star b).re :=
  rfl

noncomputable instance : NormedAddCommGroup ℍ :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℝ ℍ _ _ _
    { toInner := inferInstance
      conj_inner_symm := fun x y => by simp [inner_def, mul_comm]
      re_inner_nonneg := fun _ => normSq_nonneg
      definite := fun _ => normSq_eq_zero.1
      add_left := fun x y z => by simp only [inner_def, add_mul, re_add]
      smul_left := fun x y r => by simp [inner_def] }

noncomputable instance : InnerProductSpace ℝ ℍ :=
  InnerProductSpace.ofCore _

theorem normSq_eq_norm_mul_self (a : ℍ) : normSq a = ‖a‖ * ‖a‖ := by
  rw [← inner_self, real_inner_self_eq_norm_mul_norm]

instance : NormOneClass ℍ :=
  ⟨by rw [norm_eq_sqrt_real_inner, inner_self, normSq.map_one, Real.sqrt_one]⟩

@[simp, norm_cast]
theorem norm_coe (a : ℝ) : ‖(a : ℍ)‖ = ‖a‖ := by
  rw [norm_eq_sqrt_real_inner, inner_self, normSq_coe, Real.sqrt_sq_eq_abs, Real.norm_eq_abs]

@[simp, norm_cast]
theorem nnnorm_coe (a : ℝ) : ‖(a : ℍ)‖₊ = ‖a‖₊ :=
  Subtype.ext <| norm_coe a

-- This does not need to be `@[simp]`, as it is a consequence of later simp lemmas.
theorem norm_star (a : ℍ) : ‖star a‖ = ‖a‖ := by
  simp_rw [norm_eq_sqrt_real_inner, inner_self, normSq_star]

-- This does not need to be `@[simp]`, as it is a consequence of later simp lemmas.
theorem nnnorm_star (a : ℍ) : ‖star a‖₊ = ‖a‖₊ :=
  Subtype.ext <| norm_star a

noncomputable instance : NormedDivisionRing ℍ where
  dist_eq _ _ := rfl
  norm_mul _ _ := by simp [norm_eq_sqrt_real_inner, inner_self]

noncomputable instance : NormedAlgebra ℝ ℍ where
  norm_smul_le := norm_smul_le
  toAlgebra := Quaternion.algebra

instance : CStarRing ℍ where
  norm_mul_self_le x :=
    le_of_eq <| Eq.symm <| (norm_mul _ _).trans <| congr_arg (· * ‖x‖) (norm_star x)

/-- Coercion from `ℂ` to `ℍ`. -/
@[coe] def coeComplex (z : ℂ) : ℍ := ⟨z.re, z.im, 0, 0⟩

instance : Coe ℂ ℍ := ⟨coeComplex⟩

@[simp, norm_cast]
theorem re_coeComplex (z : ℂ) : (z : ℍ).re = z.re :=
  rfl

@[deprecated (since := "2025-08-31")] alias coeComplex_re := re_coeComplex

@[simp, norm_cast]
theorem imI_coeComplex (z : ℂ) : (z : ℍ).imI = z.im :=
  rfl

@[deprecated (since := "2025-08-31")] alias coeComplex_imI := imI_coeComplex

@[simp, norm_cast]
theorem imJ_coeComplex (z : ℂ) : (z : ℍ).imJ = 0 :=
  rfl

@[deprecated (since := "2025-08-31")] alias coeComplex_imJ := imJ_coeComplex

@[simp, norm_cast]
theorem imK_coeComplex (z : ℂ) : (z : ℍ).imK = 0 :=
  rfl

@[deprecated (since := "2025-08-31")] alias coeComplex_imK := imK_coeComplex

@[simp, norm_cast]
theorem coeComplex_add (z w : ℂ) : ↑(z + w) = (z + w : ℍ) := by ext <;> simp

@[simp, norm_cast]
theorem coeComplex_mul (z w : ℂ) : ↑(z * w) = (z * w : ℍ) := by ext <;> simp

@[simp, norm_cast]
theorem coeComplex_zero : ((0 : ℂ) : ℍ) = 0 :=
  rfl

@[simp, norm_cast]
theorem coeComplex_one : ((1 : ℂ) : ℍ) = 1 :=
  rfl

@[simp, norm_cast]
theorem coe_real_complex_mul (r : ℝ) (z : ℂ) : (r • z : ℍ) = ↑r * ↑z := by ext <;> simp

@[simp, norm_cast]
theorem coeComplex_coe (r : ℝ) : ((r : ℂ) : ℍ) = r :=
  rfl

/-- Coercion `ℂ →ₐ[ℝ] ℍ` as an algebra homomorphism. -/
def ofComplex : ℂ →ₐ[ℝ] ℍ where
  toFun := (↑)
  map_one' := rfl
  map_zero' := rfl
  map_add' := coeComplex_add
  map_mul' := coeComplex_mul
  commutes' _ := rfl

@[simp]
theorem coe_ofComplex : ⇑ofComplex = coeComplex := rfl

/-- The norm of the components as a Euclidean vector equals the norm of the quaternion. -/
lemma norm_toLp_equivTuple (x : ℍ) : ‖WithLp.toLp 2 (equivTuple ℝ x)‖ = ‖x‖ := by
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner, inner_self, normSq_def', PiLp.inner_apply,
    Fin.sum_univ_four]
  simp_rw [RCLike.inner_apply, starRingEnd_apply, star_trivial, ← sq]
  rfl

/-- `QuaternionAlgebra.linearEquivTuple` as a `LinearIsometryEquiv`. -/
@[simps apply symm_apply]
noncomputable def linearIsometryEquivTuple : ℍ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4) :=
  { (QuaternionAlgebra.linearEquivTuple (-1 : ℝ) (0 : ℝ) (-1 : ℝ)).trans
      (WithLp.linearEquiv 2 ℝ (Fin 4 → ℝ)).symm with
    toFun := fun a => !₂[a.1, a.2, a.3, a.4]
    invFun := fun a => ⟨a 0, a 1, a 2, a 3⟩
    norm_map' := norm_toLp_equivTuple }

@[continuity]
theorem continuous_coe : Continuous (coe : ℝ → ℍ) :=
  continuous_algebraMap ℝ ℍ

@[continuity]
theorem continuous_normSq : Continuous (normSq : ℍ → ℝ) := by
  simpa [← normSq_eq_norm_mul_self] using
    (continuous_norm.mul continuous_norm : Continuous fun q : ℍ => ‖q‖ * ‖q‖)

@[continuity]
theorem continuous_re : Continuous fun q : ℍ => q.re :=
  (continuous_apply 0).comp linearIsometryEquivTuple.continuous

@[continuity]
theorem continuous_imI : Continuous fun q : ℍ => q.imI :=
  (continuous_apply 1).comp linearIsometryEquivTuple.continuous

@[continuity]
theorem continuous_imJ : Continuous fun q : ℍ => q.imJ :=
  (continuous_apply 2).comp linearIsometryEquivTuple.continuous

@[continuity]
theorem continuous_imK : Continuous fun q : ℍ => q.imK :=
  (continuous_apply 3).comp linearIsometryEquivTuple.continuous

@[continuity]
theorem continuous_im : Continuous fun q : ℍ => q.im := by
  simpa only [← sub_re_self] using continuous_id.sub (continuous_coe.comp continuous_re)

instance : CompleteSpace ℍ :=
  haveI : IsUniformEmbedding linearIsometryEquivTuple.toLinearEquiv.toEquiv.symm :=
    linearIsometryEquivTuple.toContinuousLinearEquiv.symm.isUniformEmbedding
  (completeSpace_congr this).1 inferInstance

section infinite_sum

variable {α : Type*} {L : SummationFilter α}

@[simp, norm_cast]
theorem hasSum_coe {f : α → ℝ} {r : ℝ} : HasSum (fun a => (f a : ℍ)) (↑r : ℍ) L ↔ HasSum f r L :=
  ⟨fun h => by
    simpa only using
    h.map (show ℍ →ₗ[ℝ] ℝ from QuaternionAlgebra.reₗ _ _ _) continuous_re,
    fun h => by simpa only using h.map (algebraMap ℝ ℍ) (continuous_algebraMap _ _)⟩

@[simp, norm_cast]
theorem summable_coe {f : α → ℝ} : (Summable (fun a => (f a : ℍ)) L) ↔ Summable f L := by
  simpa only using
    Summable.map_iff_of_leftInverse (algebraMap ℝ ℍ) (show ℍ →ₗ[ℝ] ℝ from
      QuaternionAlgebra.reₗ _ _ _)
      (continuous_algebraMap _ _) continuous_re re_coe

@[norm_cast]
theorem tsum_coe (f : α → ℝ) : (∑'[L] a, (f a : ℍ)) = ↑(∑'[L] a, f a) :=
  (Function.LeftInverse.map_tsum f (continuous_algebraMap _ _) continuous_re re_coe).symm

end infinite_sum

end Quaternion
