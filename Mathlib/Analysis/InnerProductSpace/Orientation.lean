/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Heather Macbeth
-/
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.LinearAlgebra.Orientation

/-!
# Orientations of real inner product spaces.

This file provides definitions and proves lemmas about orientations of real inner product spaces.

## Main definitions

* `OrthonormalBasis.adjustToOrientation` takes an orthonormal basis and an orientation, and
  returns an orthonormal basis with that orientation: either the original orthonormal basis, or one
  constructed by negating a single (arbitrary) basis vector.
* `Orientation.finOrthonormalBasis` is an orthonormal basis, indexed by `Fin n`, with the given
  orientation.
* `Orientation.volumeForm` is a nonvanishing top-dimensional alternating form on an oriented real
  inner product space, uniquely defined by compatibility with the orientation and inner product
  structure.

## Main theorems

* `Orientation.volumeForm_apply_le` states that the result of applying the volume form to a set of
  `n` vectors, where `n` is the dimension the inner product space, is bounded by the product of the
  lengths of the vectors.
* `Orientation.abs_volumeForm_apply_of_pairwise_orthogonal` states that the result of applying the
  volume form to a set of `n` orthogonal vectors, where `n` is the dimension the inner product
  space, is equal up to sign to the product of the lengths of the vectors.

-/


noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open Module InnerProductSpace

open scoped RealInnerProductSpace

namespace OrthonormalBasis

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (e f : OrthonormalBasis ι ℝ E)
  (x : Orientation ℝ E ι)

/-- The change-of-basis matrix between two orthonormal bases with the same orientation has
determinant 1. -/
theorem det_to_matrix_orthonormalBasis_of_same_orientation
    (h : e.toBasis.orientation = f.toBasis.orientation) : e.toBasis.det f = 1 := by
  apply (e.det_to_matrix_orthonormalBasis_real f).resolve_right
  have : 0 < e.toBasis.det f := by
    rw [e.toBasis.orientation_eq_iff_det_pos] at h
    simpa using h
  linarith

/-- The change-of-basis matrix between two orthonormal bases with the opposite orientations has
determinant -1. -/
theorem det_to_matrix_orthonormalBasis_of_opposite_orientation
    (h : e.toBasis.orientation ≠ f.toBasis.orientation) : e.toBasis.det f = -1 := by
  contrapose! h
  simp [e.toBasis.orientation_eq_iff_det_pos,
    (e.det_to_matrix_orthonormalBasis_real f).resolve_right h]

variable {e f}

/-- Two orthonormal bases with the same orientation determine the same "determinant" top-dimensional
form on `E`, and conversely. -/
theorem same_orientation_iff_det_eq_det :
    e.toBasis.det = f.toBasis.det ↔ e.toBasis.orientation = f.toBasis.orientation := by
  constructor
  · intro h
    dsimp [Basis.orientation]
    congr
  · intro h
    rw [e.toBasis.det.eq_smul_basis_det f.toBasis]
    simp [e.det_to_matrix_orthonormalBasis_of_same_orientation f h]

variable (e f)

/-- Two orthonormal bases with opposite orientations determine opposite "determinant"
top-dimensional forms on `E`. -/
theorem det_eq_neg_det_of_opposite_orientation (h : e.toBasis.orientation ≠ f.toBasis.orientation) :
    e.toBasis.det = -f.toBasis.det := by
  rw [e.toBasis.det.eq_smul_basis_det f.toBasis]
  simp [e.det_to_matrix_orthonormalBasis_of_opposite_orientation f h]

variable [Nonempty ι]

section AdjustToOrientation

/-- `OrthonormalBasis.adjustToOrientation`, applied to an orthonormal basis, preserves the
property of orthonormality. -/
theorem orthonormal_adjustToOrientation : Orthonormal ℝ (e.toBasis.adjustToOrientation x) := by
  apply e.orthonormal.orthonormal_of_forall_eq_or_eq_neg
  simpa using e.toBasis.adjustToOrientation_apply_eq_or_eq_neg x

/-- Given an orthonormal basis and an orientation, return an orthonormal basis giving that
orientation: either the original basis, or one constructed by negating a single (arbitrary) basis
vector. -/
def adjustToOrientation : OrthonormalBasis ι ℝ E :=
  (e.toBasis.adjustToOrientation x).toOrthonormalBasis (e.orthonormal_adjustToOrientation x)

theorem toBasis_adjustToOrientation :
    (e.adjustToOrientation x).toBasis = e.toBasis.adjustToOrientation x :=
  (e.toBasis.adjustToOrientation x).toBasis_toOrthonormalBasis _

/-- `adjustToOrientation` gives an orthonormal basis with the required orientation. -/
@[simp]
theorem orientation_adjustToOrientation : (e.adjustToOrientation x).toBasis.orientation = x := by
  rw [e.toBasis_adjustToOrientation]
  exact e.toBasis.orientation_adjustToOrientation x

/-- Every basis vector from `adjustToOrientation` is either that from the original basis or its
negation. -/
theorem adjustToOrientation_apply_eq_or_eq_neg (i : ι) :
    e.adjustToOrientation x i = e i ∨ e.adjustToOrientation x i = -e i := by
  simpa [← e.toBasis_adjustToOrientation] using
    e.toBasis.adjustToOrientation_apply_eq_or_eq_neg x i

theorem det_adjustToOrientation :
    (e.adjustToOrientation x).toBasis.det = e.toBasis.det ∨
      (e.adjustToOrientation x).toBasis.det = -e.toBasis.det := by
  simpa using e.toBasis.det_adjustToOrientation x

theorem abs_det_adjustToOrientation (v : ι → E) :
    |(e.adjustToOrientation x).toBasis.det v| = |e.toBasis.det v| := by
  simp [toBasis_adjustToOrientation]

end AdjustToOrientation

end OrthonormalBasis

namespace Orientation

variable {n : ℕ}

open OrthonormalBasis

/-- An orthonormal basis, indexed by `Fin n`, with the given orientation. -/
protected def finOrthonormalBasis (hn : 0 < n) (h : finrank ℝ E = n) (x : Orientation ℝ E (Fin n)) :
    OrthonormalBasis (Fin n) ℝ E := by
  haveI := Fin.pos_iff_nonempty.1 hn
  haveI : FiniteDimensional ℝ E := .of_finrank_pos <| h.symm ▸ hn
  exact ((@stdOrthonormalBasis _ _ _ _ _ this).reindex <| finCongr h).adjustToOrientation x

/-- `Orientation.finOrthonormalBasis` gives a basis with the required orientation. -/
@[simp]
theorem finOrthonormalBasis_orientation (hn : 0 < n) (h : finrank ℝ E = n)
    (x : Orientation ℝ E (Fin n)) : (x.finOrthonormalBasis hn h).toBasis.orientation = x := by
  haveI := Fin.pos_iff_nonempty.1 hn
  haveI : FiniteDimensional ℝ E := .of_finrank_pos <| h.symm ▸ hn
  exact ((@stdOrthonormalBasis _ _ _ _ _ this).reindex <|
    finCongr h).orientation_adjustToOrientation x

section VolumeForm

variable [_i : Fact (finrank ℝ E = n)] (o : Orientation ℝ E (Fin n))

/-- The volume form on an oriented real inner product space, a nonvanishing top-dimensional
alternating form uniquely defined by compatibility with the orientation and inner product structure.
-/
irreducible_def volumeForm : E [⋀^Fin n]→ₗ[ℝ] ℝ := by
  classical
    cases n with
    | zero =>
      let opos : E [⋀^Fin 0]→ₗ[ℝ] ℝ := .constOfIsEmpty ℝ E (Fin 0) (1 : ℝ)
      exact o.eq_or_eq_neg_of_isEmpty.by_cases (fun _ => opos) fun _ => -opos
    | succ n => exact (o.finOrthonormalBasis n.succ_pos _i.out).toBasis.det

@[simp]
theorem volumeForm_zero_pos [_i : Fact (finrank ℝ E = 0)] :
    Orientation.volumeForm (positiveOrientation : Orientation ℝ E (Fin 0)) =
      AlternatingMap.constLinearEquivOfIsEmpty 1 := by
  simp [volumeForm, Or.by_cases]

theorem volumeForm_zero_neg [_i : Fact (finrank ℝ E = 0)] :
    Orientation.volumeForm (-positiveOrientation : Orientation ℝ E (Fin 0)) =
      -AlternatingMap.constLinearEquivOfIsEmpty 1 := by
  simp_rw [volumeForm, Or.by_cases, positiveOrientation]
  apply if_neg
  simp only [neg_rayOfNeZero]
  rw [ray_eq_iff, SameRay.sameRay_comm]
  intro h
  simpa using
    congr_arg AlternatingMap.constLinearEquivOfIsEmpty.symm (eq_zero_of_sameRay_self_neg h)

/-- The volume form on an oriented real inner product space can be evaluated as the determinant with
respect to any orthonormal basis of the space compatible with the orientation. -/
theorem volumeForm_robust (b : OrthonormalBasis (Fin n) ℝ E) (hb : b.toBasis.orientation = o) :
    o.volumeForm = b.toBasis.det := by
  cases n
  · classical
      have : o = positiveOrientation := hb.symm.trans b.toBasis.orientation_isEmpty
      simp_rw [volumeForm, Or.by_cases, dif_pos this, Nat.rec_zero, Basis.det_isEmpty]
  · simp_rw [volumeForm]
    rw [same_orientation_iff_det_eq_det, hb]
    exact o.finOrthonormalBasis_orientation _ _

/-- The volume form on an oriented real inner product space can be evaluated as the determinant with
respect to any orthonormal basis of the space compatible with the orientation. -/
theorem volumeForm_robust_neg (b : OrthonormalBasis (Fin n) ℝ E) (hb : b.toBasis.orientation ≠ o) :
    o.volumeForm = -b.toBasis.det := by
  rcases n with - | n
  · classical
      have : positiveOrientation ≠ o := by rwa [b.toBasis.orientation_isEmpty] at hb
      simp_rw [volumeForm, Or.by_cases, dif_neg this.symm, Nat.rec_zero, Basis.det_isEmpty]
  let e : OrthonormalBasis (Fin n.succ) ℝ E := o.finOrthonormalBasis n.succ_pos Fact.out
  simp_rw [volumeForm]
  apply e.det_eq_neg_det_of_opposite_orientation b
  convert hb.symm
  exact o.finOrthonormalBasis_orientation _ _

@[simp]
theorem volumeForm_neg_orientation : (-o).volumeForm = -o.volumeForm := by
  rcases n with - | n
  · refine o.eq_or_eq_neg_of_isEmpty.elim ?_ ?_ <;> rintro rfl
    · simp [volumeForm_zero_neg]
    · simp [volumeForm_zero_neg]
  let e : OrthonormalBasis (Fin n.succ) ℝ E := o.finOrthonormalBasis n.succ_pos Fact.out
  have h₁ : e.toBasis.orientation = o := o.finOrthonormalBasis_orientation _ _
  have h₂ : e.toBasis.orientation ≠ -o := by
    symm
    rw [e.toBasis.orientation_ne_iff_eq_neg, h₁]
  rw [o.volumeForm_robust e h₁, (-o).volumeForm_robust_neg e h₂]

theorem volumeForm_robust' (b : OrthonormalBasis (Fin n) ℝ E) (v : Fin n → E) :
    |o.volumeForm v| = |b.toBasis.det v| := by
  cases n
  · refine o.eq_or_eq_neg_of_isEmpty.elim ?_ ?_ <;> rintro rfl <;> simp
  · rw [o.volumeForm_robust (b.adjustToOrientation o) (b.orientation_adjustToOrientation o),
      b.abs_det_adjustToOrientation]

/-- Let `v` be an indexed family of `n` vectors in an oriented `n`-dimensional real inner
product space `E`. The output of the volume form of `E` when evaluated on `v` is bounded in absolute
value by the product of the norms of the vectors `v i`. -/
theorem abs_volumeForm_apply_le (v : Fin n → E) : |o.volumeForm v| ≤ ∏ i : Fin n, ‖v i‖ := by
  rcases n with - | n
  · refine o.eq_or_eq_neg_of_isEmpty.elim ?_ ?_ <;> rintro rfl <;> simp
  haveI : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  have : finrank ℝ E = Fintype.card (Fin n.succ) := by simpa using _i.out
  let b : OrthonormalBasis (Fin n.succ) ℝ E := gramSchmidtOrthonormalBasis this v
  have hb : b.toBasis.det v = ∏ i, ⟪b i, v i⟫ := gramSchmidtOrthonormalBasis_det this v
  rw [o.volumeForm_robust' b, hb, Finset.abs_prod]
  apply Finset.prod_le_prod
  · intro i _
    positivity
  intro i _
  convert abs_real_inner_le_norm (b i) (v i)
  simp [b.orthonormal.1 i]

theorem volumeForm_apply_le (v : Fin n → E) : o.volumeForm v ≤ ∏ i : Fin n, ‖v i‖ :=
  (le_abs_self _).trans (o.abs_volumeForm_apply_le v)

/-- Let `v` be an indexed family of `n` orthogonal vectors in an oriented `n`-dimensional
real inner product space `E`. The output of the volume form of `E` when evaluated on `v` is, up to
sign, the product of the norms of the vectors `v i`. -/
theorem abs_volumeForm_apply_of_pairwise_orthogonal {v : Fin n → E}
    (hv : Pairwise fun i j => ⟪v i, v j⟫ = 0) : |o.volumeForm v| = ∏ i : Fin n, ‖v i‖ := by
  rcases n with - | n
  · refine o.eq_or_eq_neg_of_isEmpty.elim ?_ ?_ <;> rintro rfl <;> simp
  haveI : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  have hdim : finrank ℝ E = Fintype.card (Fin n.succ) := by simpa using _i.out
  let b : OrthonormalBasis (Fin n.succ) ℝ E := gramSchmidtOrthonormalBasis hdim v
  have hb : b.toBasis.det v = ∏ i, ⟪b i, v i⟫ := gramSchmidtOrthonormalBasis_det hdim v
  rw [o.volumeForm_robust' b, hb, Finset.abs_prod]
  by_cases h : ∃ i, v i = 0
  · obtain ⟨i, hi⟩ := h
    rw [Finset.prod_eq_zero (Finset.mem_univ i), Finset.prod_eq_zero (Finset.mem_univ i)] <;>
      simp [hi]
  push_neg at h
  congr
  ext i
  have hb : b i = ‖v i‖⁻¹ • v i := gramSchmidtOrthonormalBasis_apply_of_orthogonal hdim hv (h i)
  simp only [hb, inner_smul_left, real_inner_self_eq_norm_mul_norm, RCLike.conj_to_real]
  rw [abs_of_nonneg]
  · field_simp
  · positivity

/-- The output of the volume form of an oriented real inner product space `E` when evaluated on an
orthonormal basis is ±1. -/
theorem abs_volumeForm_apply_of_orthonormal (v : OrthonormalBasis (Fin n) ℝ E) :
    |o.volumeForm v| = 1 := by
  simpa [o.volumeForm_robust' v v] using congr_arg abs v.toBasis.det_self

theorem volumeForm_map {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [Fact (finrank ℝ F = n)] (φ : E ≃ₗᵢ[ℝ] F) (x : Fin n → F) :
    (Orientation.map (Fin n) φ.toLinearEquiv o).volumeForm x = o.volumeForm (φ.symm ∘ x) := by
  rcases n with - | n
  · refine o.eq_or_eq_neg_of_isEmpty.elim ?_ ?_ <;> rintro rfl <;> simp
  let e : OrthonormalBasis (Fin n.succ) ℝ E := o.finOrthonormalBasis n.succ_pos Fact.out
  have he : e.toBasis.orientation = o :=
    o.finOrthonormalBasis_orientation n.succ_pos Fact.out
  have heφ : (e.map φ).toBasis.orientation = Orientation.map (Fin n.succ) φ.toLinearEquiv o := by
    rw [← he]
    exact e.toBasis.orientation_map φ.toLinearEquiv
  rw [(Orientation.map (Fin n.succ) φ.toLinearEquiv o).volumeForm_robust (e.map φ) heφ]
  rw [o.volumeForm_robust e he]
  simp

/-- The volume form is invariant under pullback by a positively-oriented isometric automorphism. -/
theorem volumeForm_comp_linearIsometryEquiv (φ : E ≃ₗᵢ[ℝ] E)
    (hφ : 0 < LinearMap.det (φ.toLinearEquiv : E →ₗ[ℝ] E)) (x : Fin n → E) :
    o.volumeForm (φ ∘ x) = o.volumeForm x := by
  rcases n with - | n
  · refine o.eq_or_eq_neg_of_isEmpty.elim ?_ ?_ <;> rintro rfl <;> simp
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  convert o.volumeForm_map φ (φ ∘ x)
  · symm
    rwa [← o.map_eq_iff_det_pos φ.toLinearEquiv] at hφ
    rw [_i.out, Fintype.card_fin]
  · ext
    simp

end VolumeForm

end Orientation
