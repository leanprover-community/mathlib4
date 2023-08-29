/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Heather Macbeth
-/
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.LinearAlgebra.Orientation

#align_import analysis.inner_product_space.orientation from "leanprover-community/mathlib"@"bd65478311e4dfd41f48bf38c7e3b02fb75d0163"

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

open FiniteDimensional

open scoped BigOperators RealInnerProductSpace

namespace OrthonormalBasis

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [ne : Nonempty ι] (e f : OrthonormalBasis ι ℝ E)
  (x : Orientation ℝ E ι)

/-- The change-of-basis matrix between two orthonormal bases with the same orientation has
determinant 1. -/
theorem det_to_matrix_orthonormalBasis_of_same_orientation
    (h : e.toBasis.orientation = f.toBasis.orientation) : e.toBasis.det f = 1 := by
  apply (e.det_to_matrix_orthonormalBasis_real f).resolve_right
  -- ⊢ ¬↑(Basis.det (OrthonormalBasis.toBasis e)) ↑f = -1
  have : 0 < e.toBasis.det f := by
    rw [e.toBasis.orientation_eq_iff_det_pos] at h
    simpa using h
  linarith
  -- 🎉 no goals
#align orthonormal_basis.det_to_matrix_orthonormal_basis_of_same_orientation OrthonormalBasis.det_to_matrix_orthonormalBasis_of_same_orientation

/-- The change-of-basis matrix between two orthonormal bases with the opposite orientations has
determinant -1. -/
theorem det_to_matrix_orthonormalBasis_of_opposite_orientation
    (h : e.toBasis.orientation ≠ f.toBasis.orientation) : e.toBasis.det f = -1 := by
  contrapose! h
  -- ⊢ Basis.orientation (OrthonormalBasis.toBasis e) = Basis.orientation (Orthonor …
  simp [e.toBasis.orientation_eq_iff_det_pos,
    (e.det_to_matrix_orthonormalBasis_real f).resolve_right h]
#align orthonormal_basis.det_to_matrix_orthonormal_basis_of_opposite_orientation OrthonormalBasis.det_to_matrix_orthonormalBasis_of_opposite_orientation

variable {e f}

/-- Two orthonormal bases with the same orientation determine the same "determinant" top-dimensional
form on `E`, and conversely. -/
theorem same_orientation_iff_det_eq_det :
    e.toBasis.det = f.toBasis.det ↔ e.toBasis.orientation = f.toBasis.orientation := by
  constructor
  -- ⊢ Basis.det (OrthonormalBasis.toBasis e) = Basis.det (OrthonormalBasis.toBasis …
  · intro h
    -- ⊢ Basis.orientation (OrthonormalBasis.toBasis e) = Basis.orientation (Orthonor …
    dsimp [Basis.orientation]
    -- ⊢ rayOfNeZero ℝ (Basis.det (OrthonormalBasis.toBasis e)) (_ : Basis.det (Ortho …
    congr
    -- 🎉 no goals
  · intro h
    -- ⊢ Basis.det (OrthonormalBasis.toBasis e) = Basis.det (OrthonormalBasis.toBasis …
    rw [e.toBasis.det.eq_smul_basis_det f.toBasis]
    -- ⊢ ↑(Basis.det (OrthonormalBasis.toBasis e)) ↑(OrthonormalBasis.toBasis f) • Ba …
    simp [e.det_to_matrix_orthonormalBasis_of_same_orientation f h]
    -- 🎉 no goals
#align orthonormal_basis.same_orientation_iff_det_eq_det OrthonormalBasis.same_orientation_iff_det_eq_det

variable (e f)

/-- Two orthonormal bases with opposite orientations determine opposite "determinant"
top-dimensional forms on `E`. -/
theorem det_eq_neg_det_of_opposite_orientation (h : e.toBasis.orientation ≠ f.toBasis.orientation) :
    e.toBasis.det = -f.toBasis.det := by
  rw [e.toBasis.det.eq_smul_basis_det f.toBasis]
  -- ⊢ ↑(Basis.det (OrthonormalBasis.toBasis e)) ↑(OrthonormalBasis.toBasis f) • Ba …
  -- Porting note: added `neg_one_smul` with explicit type
  simp [e.det_to_matrix_orthonormalBasis_of_opposite_orientation f h,
    neg_one_smul ℝ (M := AlternatingMap ℝ E ℝ ι)]
#align orthonormal_basis.det_eq_neg_det_of_opposite_orientation OrthonormalBasis.det_eq_neg_det_of_opposite_orientation

section AdjustToOrientation

/-- `OrthonormalBasis.adjustToOrientation`, applied to an orthonormal basis, preserves the
property of orthonormality. -/
theorem orthonormal_adjustToOrientation : Orthonormal ℝ (e.toBasis.adjustToOrientation x) := by
  apply e.orthonormal.orthonormal_of_forall_eq_or_eq_neg
  -- ⊢ ∀ (i : ι), ↑(Basis.adjustToOrientation (OrthonormalBasis.toBasis e) x) i = ↑ …
  simpa using e.toBasis.adjustToOrientation_apply_eq_or_eq_neg x
  -- 🎉 no goals
#align orthonormal_basis.orthonormal_adjust_to_orientation OrthonormalBasis.orthonormal_adjustToOrientation

/-- Given an orthonormal basis and an orientation, return an orthonormal basis giving that
orientation: either the original basis, or one constructed by negating a single (arbitrary) basis
vector. -/
def adjustToOrientation : OrthonormalBasis ι ℝ E :=
  (e.toBasis.adjustToOrientation x).toOrthonormalBasis (e.orthonormal_adjustToOrientation x)
#align orthonormal_basis.adjust_to_orientation OrthonormalBasis.adjustToOrientation

theorem toBasis_adjustToOrientation :
    (e.adjustToOrientation x).toBasis = e.toBasis.adjustToOrientation x :=
  (e.toBasis.adjustToOrientation x).toBasis_toOrthonormalBasis _
#align orthonormal_basis.to_basis_adjust_to_orientation OrthonormalBasis.toBasis_adjustToOrientation

/-- `adjustToOrientation` gives an orthonormal basis with the required orientation. -/
@[simp]
theorem orientation_adjustToOrientation : (e.adjustToOrientation x).toBasis.orientation = x := by
  rw [e.toBasis_adjustToOrientation]
  -- ⊢ Basis.orientation (Basis.adjustToOrientation (OrthonormalBasis.toBasis e) x) …
  exact e.toBasis.orientation_adjustToOrientation x
  -- 🎉 no goals
#align orthonormal_basis.orientation_adjust_to_orientation OrthonormalBasis.orientation_adjustToOrientation

/-- Every basis vector from `adjustToOrientation` is either that from the original basis or its
negation. -/
theorem adjustToOrientation_apply_eq_or_eq_neg (i : ι) :
    e.adjustToOrientation x i = e i ∨ e.adjustToOrientation x i = -e i := by
  simpa [← e.toBasis_adjustToOrientation] using
    e.toBasis.adjustToOrientation_apply_eq_or_eq_neg x i
#align orthonormal_basis.adjust_to_orientation_apply_eq_or_eq_neg OrthonormalBasis.adjustToOrientation_apply_eq_or_eq_neg

theorem det_adjustToOrientation :
    (e.adjustToOrientation x).toBasis.det = e.toBasis.det ∨
      (e.adjustToOrientation x).toBasis.det = -e.toBasis.det := by
  simpa using e.toBasis.det_adjustToOrientation x
  -- 🎉 no goals
#align orthonormal_basis.det_adjust_to_orientation OrthonormalBasis.det_adjustToOrientation

theorem abs_det_adjustToOrientation (v : ι → E) :
    |(e.adjustToOrientation x).toBasis.det v| = |e.toBasis.det v| := by
  simp [toBasis_adjustToOrientation]
  -- 🎉 no goals
#align orthonormal_basis.abs_det_adjust_to_orientation OrthonormalBasis.abs_det_adjustToOrientation

end AdjustToOrientation

end OrthonormalBasis

namespace Orientation

variable {n : ℕ}

open OrthonormalBasis

/-- An orthonormal basis, indexed by `Fin n`, with the given orientation. -/
protected def finOrthonormalBasis (hn : 0 < n) (h : finrank ℝ E = n) (x : Orientation ℝ E (Fin n)) :
    OrthonormalBasis (Fin n) ℝ E := by
  haveI := Fin.pos_iff_nonempty.1 hn
  -- ⊢ OrthonormalBasis (Fin n) ℝ E
  haveI := finiteDimensional_of_finrank (h.symm ▸ hn : 0 < finrank ℝ E)
  -- ⊢ OrthonormalBasis (Fin n) ℝ E
  exact ((@stdOrthonormalBasis _ _ _ _ _ this).reindex <| finCongr h).adjustToOrientation x
  -- 🎉 no goals
#align orientation.fin_orthonormal_basis Orientation.finOrthonormalBasis

/-- `Orientation.finOrthonormalBasis` gives a basis with the required orientation. -/
@[simp]
theorem finOrthonormalBasis_orientation (hn : 0 < n) (h : finrank ℝ E = n)
    (x : Orientation ℝ E (Fin n)) : (x.finOrthonormalBasis hn h).toBasis.orientation = x := by
  haveI := Fin.pos_iff_nonempty.1 hn
  -- ⊢ Basis.orientation (OrthonormalBasis.toBasis (Orientation.finOrthonormalBasis …
  haveI := finiteDimensional_of_finrank (h.symm ▸ hn : 0 < finrank ℝ E)
  -- ⊢ Basis.orientation (OrthonormalBasis.toBasis (Orientation.finOrthonormalBasis …
  exact ((@stdOrthonormalBasis _ _ _ _ _ this).reindex <|
    finCongr h).orientation_adjustToOrientation x
#align orientation.fin_orthonormal_basis_orientation Orientation.finOrthonormalBasis_orientation

section VolumeForm

variable [_i : Fact (finrank ℝ E = n)] (o : Orientation ℝ E (Fin n))

-- Porting note: added instance
instance : IsEmpty (Fin Nat.zero) := by simp only [Nat.zero_eq]; infer_instance
                                        -- ⊢ IsEmpty (Fin 0)
                                                                 -- 🎉 no goals

/-- The volume form on an oriented real inner product space, a nonvanishing top-dimensional
alternating form uniquely defined by compatibility with the orientation and inner product structure.
-/
irreducible_def volumeForm : AlternatingMap ℝ E ℝ (Fin n) := by
  classical
    cases' n with n
    · let opos : AlternatingMap ℝ E ℝ (Fin 0) := AlternatingMap.constOfIsEmpty ℝ E (Fin 0) (1 : ℝ)
      exact o.eq_or_eq_neg_of_isEmpty.by_cases (fun _ => opos) fun _ => -opos
    · exact (o.finOrthonormalBasis n.succ_pos _i.out).toBasis.det
#align orientation.volume_form Orientation.volumeForm

@[simp]
theorem volumeForm_zero_pos [_i : Fact (finrank ℝ E = 0)] :
    Orientation.volumeForm (positiveOrientation : Orientation ℝ E (Fin 0)) =
      AlternatingMap.constLinearEquivOfIsEmpty 1 := by
  simp [volumeForm, Or.by_cases, if_pos]
  -- 🎉 no goals
#align orientation.volume_form_zero_pos Orientation.volumeForm_zero_pos

theorem volumeForm_zero_neg [_i : Fact (finrank ℝ E = 0)] :
    Orientation.volumeForm (-positiveOrientation : Orientation ℝ E (Fin 0)) =
      -AlternatingMap.constLinearEquivOfIsEmpty 1 := by
  simp_rw [volumeForm, Or.by_cases, positiveOrientation]
  -- ⊢ Nat.rec (motive := fun t => 0 = t → AlternatingMap ℝ E ℝ (Fin 0)) (fun h =>  …
  apply if_neg
  -- ⊢ ¬-rayOfNeZero ℝ (↑AlternatingMap.constLinearEquivOfIsEmpty 1) (_ : ↑Alternat …
  simp only [neg_rayOfNeZero]
  -- ⊢ ¬rayOfNeZero ℝ (-↑AlternatingMap.constLinearEquivOfIsEmpty 1) (_ : -↑Alterna …
  rw [ray_eq_iff, SameRay.sameRay_comm]
  -- ⊢ ¬SameRay ℝ (↑AlternatingMap.constLinearEquivOfIsEmpty 1) (-↑AlternatingMap.c …
  intro h
  -- ⊢ False
  simpa using
    congr_arg AlternatingMap.constLinearEquivOfIsEmpty.symm (eq_zero_of_sameRay_self_neg h)
#align orientation.volume_form_zero_neg Orientation.volumeForm_zero_neg

/-- The volume form on an oriented real inner product space can be evaluated as the determinant with
respect to any orthonormal basis of the space compatible with the orientation. -/
theorem volumeForm_robust (b : OrthonormalBasis (Fin n) ℝ E) (hb : b.toBasis.orientation = o) :
    o.volumeForm = b.toBasis.det := by
  cases n
  -- ⊢ volumeForm o = Basis.det (OrthonormalBasis.toBasis b)
  · classical
      have : o = positiveOrientation := hb.symm.trans b.toBasis.orientation_isEmpty
      simp_rw [volumeForm, Or.by_cases, dif_pos this, Basis.det_isEmpty]
  · simp_rw [volumeForm]
    -- ⊢ Basis.det (OrthonormalBasis.toBasis (Orientation.finOrthonormalBasis (_ : 0  …
    rw [same_orientation_iff_det_eq_det, hb]
    -- ⊢ Basis.orientation (OrthonormalBasis.toBasis (Orientation.finOrthonormalBasis …
    exact o.finOrthonormalBasis_orientation _ _
    -- 🎉 no goals
#align orientation.volume_form_robust Orientation.volumeForm_robust

/-- The volume form on an oriented real inner product space can be evaluated as the determinant with
respect to any orthonormal basis of the space compatible with the orientation. -/
theorem volumeForm_robust_neg (b : OrthonormalBasis (Fin n) ℝ E) (hb : b.toBasis.orientation ≠ o) :
    o.volumeForm = -b.toBasis.det := by
  cases' n with n
  -- ⊢ volumeForm o = -Basis.det (OrthonormalBasis.toBasis b)
  · classical
      have : positiveOrientation ≠ o := by rwa [b.toBasis.orientation_isEmpty] at hb
      simp_rw [volumeForm, Or.by_cases, dif_neg this.symm, Basis.det_isEmpty]
  let e : OrthonormalBasis (Fin n.succ) ℝ E := o.finOrthonormalBasis n.succ_pos Fact.out
  -- ⊢ volumeForm o = -Basis.det (OrthonormalBasis.toBasis b)
  simp_rw [volumeForm]
  -- ⊢ Basis.det (OrthonormalBasis.toBasis (Orientation.finOrthonormalBasis (_ : 0  …
  apply e.det_eq_neg_det_of_opposite_orientation b
  -- ⊢ Basis.orientation (OrthonormalBasis.toBasis e) ≠ Basis.orientation (Orthonor …
  convert hb.symm
  -- ⊢ Basis.orientation (OrthonormalBasis.toBasis e) = o
  exact o.finOrthonormalBasis_orientation _ _
  -- 🎉 no goals
#align orientation.volume_form_robust_neg Orientation.volumeForm_robust_neg

@[simp]
theorem volumeForm_neg_orientation : (-o).volumeForm = -o.volumeForm := by
  cases' n with n
  -- ⊢ volumeForm (-o) = -volumeForm o
  · refine' o.eq_or_eq_neg_of_isEmpty.elim _ _ <;> rintro rfl
    -- ⊢ o = positiveOrientation → volumeForm (-o) = -volumeForm o
                                                   -- ⊢ volumeForm (-positiveOrientation) = -volumeForm positiveOrientation
                                                   -- ⊢ volumeForm (- -positiveOrientation) = -volumeForm (-positiveOrientation)
    · simp [volumeForm_zero_neg]
      -- 🎉 no goals
    · rw [neg_neg (positiveOrientation (R := ℝ))] -- Porting note: added
      -- ⊢ volumeForm positiveOrientation = -volumeForm (-positiveOrientation)
      simp [volumeForm_zero_neg]
      -- 🎉 no goals
  let e : OrthonormalBasis (Fin n.succ) ℝ E := o.finOrthonormalBasis n.succ_pos Fact.out
  -- ⊢ volumeForm (-o) = -volumeForm o
  have h₁ : e.toBasis.orientation = o := o.finOrthonormalBasis_orientation _ _
  -- ⊢ volumeForm (-o) = -volumeForm o
  have h₂ : e.toBasis.orientation ≠ -o := by
    symm
    rw [e.toBasis.orientation_ne_iff_eq_neg, h₁]
  rw [o.volumeForm_robust e h₁, (-o).volumeForm_robust_neg e h₂]
  -- 🎉 no goals
#align orientation.volume_form_neg_orientation Orientation.volumeForm_neg_orientation

theorem volumeForm_robust' (b : OrthonormalBasis (Fin n) ℝ E) (v : Fin n → E) :
    |o.volumeForm v| = |b.toBasis.det v| := by
  cases n
  -- ⊢ |↑(volumeForm o) v| = |↑(Basis.det (OrthonormalBasis.toBasis b)) v|
  · refine' o.eq_or_eq_neg_of_isEmpty.elim _ _ <;> rintro rfl <;> simp
    -- ⊢ o = positiveOrientation → |↑(volumeForm o) v| = |↑(Basis.det (OrthonormalBas …
                                                   -- ⊢ |↑(volumeForm positiveOrientation) v| = |↑(Basis.det (OrthonormalBasis.toBas …
                                                   -- ⊢ |↑(volumeForm (-positiveOrientation)) v| = |↑(Basis.det (OrthonormalBasis.to …
                                                                  -- 🎉 no goals
                                                                  -- 🎉 no goals
  · rw [o.volumeForm_robust (b.adjustToOrientation o) (b.orientation_adjustToOrientation o),
      b.abs_det_adjustToOrientation]
#align orientation.volume_form_robust' Orientation.volumeForm_robust'

/-- Let `v` be an indexed family of `n` vectors in an oriented `n`-dimensional real inner
product space `E`. The output of the volume form of `E` when evaluated on `v` is bounded in absolute
value by the product of the norms of the vectors `v i`. -/
theorem abs_volumeForm_apply_le (v : Fin n → E) : |o.volumeForm v| ≤ ∏ i : Fin n, ‖v i‖ := by
  cases' n with n
  -- ⊢ |↑(volumeForm o) v| ≤ ∏ i : Fin Nat.zero, ‖v i‖
  · refine' o.eq_or_eq_neg_of_isEmpty.elim _ _ <;> rintro rfl <;> simp
    -- ⊢ o = positiveOrientation → |↑(volumeForm o) v| ≤ ∏ i : Fin Nat.zero, ‖v i‖
                                                   -- ⊢ |↑(volumeForm positiveOrientation) v| ≤ ∏ i : Fin Nat.zero, ‖v i‖
                                                   -- ⊢ |↑(volumeForm (-positiveOrientation)) v| ≤ ∏ i : Fin Nat.zero, ‖v i‖
                                                                  -- 🎉 no goals
                                                                  -- 🎉 no goals
  haveI : FiniteDimensional ℝ E := fact_finiteDimensional_of_finrank_eq_succ n
  -- ⊢ |↑(volumeForm o) v| ≤ ∏ i : Fin (Nat.succ n), ‖v i‖
  have : finrank ℝ E = Fintype.card (Fin n.succ) := by simpa using _i.out
  -- ⊢ |↑(volumeForm o) v| ≤ ∏ i : Fin (Nat.succ n), ‖v i‖
  let b : OrthonormalBasis (Fin n.succ) ℝ E := gramSchmidtOrthonormalBasis this v
  -- ⊢ |↑(volumeForm o) v| ≤ ∏ i : Fin (Nat.succ n), ‖v i‖
  have hb : b.toBasis.det v = ∏ i, ⟪b i, v i⟫ := gramSchmidtOrthonormalBasis_det this v
  -- ⊢ |↑(volumeForm o) v| ≤ ∏ i : Fin (Nat.succ n), ‖v i‖
  rw [o.volumeForm_robust' b, hb, Finset.abs_prod]
  -- ⊢ ∏ x : Fin (Nat.succ n), |inner (↑b x) (v x)| ≤ ∏ i : Fin (Nat.succ n), ‖v i‖
  apply Finset.prod_le_prod
  -- ⊢ ∀ (i : Fin (Nat.succ n)), i ∈ Finset.univ → 0 ≤ |inner (↑b i) (v i)|
  · intro i _
    -- ⊢ 0 ≤ |inner (↑b i) (v i)|
    positivity
    -- 🎉 no goals
  intro i _
  -- ⊢ |inner (↑b i) (v i)| ≤ ‖v i‖
  convert abs_real_inner_le_norm (b i) (v i)
  -- ⊢ ‖v i‖ = ‖↑b i‖ * ‖v i‖
  simp [b.orthonormal.1 i]
  -- 🎉 no goals
#align orientation.abs_volume_form_apply_le Orientation.abs_volumeForm_apply_le

theorem volumeForm_apply_le (v : Fin n → E) : o.volumeForm v ≤ ∏ i : Fin n, ‖v i‖ :=
  (le_abs_self _).trans (o.abs_volumeForm_apply_le v)
#align orientation.volume_form_apply_le Orientation.volumeForm_apply_le

/-- Let `v` be an indexed family of `n` orthogonal vectors in an oriented `n`-dimensional
real inner product space `E`. The output of the volume form of `E` when evaluated on `v` is, up to
sign, the product of the norms of the vectors `v i`. -/
theorem abs_volumeForm_apply_of_pairwise_orthogonal {v : Fin n → E}
    (hv : Pairwise fun i j => ⟪v i, v j⟫ = 0) : |o.volumeForm v| = ∏ i : Fin n, ‖v i‖ := by
  cases' n with n
  -- ⊢ |↑(volumeForm o) v| = ∏ i : Fin Nat.zero, ‖v i‖
  · refine' o.eq_or_eq_neg_of_isEmpty.elim _ _ <;> rintro rfl <;> simp
    -- ⊢ o = positiveOrientation → |↑(volumeForm o) v| = ∏ i : Fin Nat.zero, ‖v i‖
                                                   -- ⊢ |↑(volumeForm positiveOrientation) v| = ∏ i : Fin Nat.zero, ‖v i‖
                                                   -- ⊢ |↑(volumeForm (-positiveOrientation)) v| = ∏ i : Fin Nat.zero, ‖v i‖
                                                                  -- 🎉 no goals
                                                                  -- 🎉 no goals
  haveI : FiniteDimensional ℝ E := fact_finiteDimensional_of_finrank_eq_succ n
  -- ⊢ |↑(volumeForm o) v| = ∏ i : Fin (Nat.succ n), ‖v i‖
  have hdim : finrank ℝ E = Fintype.card (Fin n.succ) := by simpa using _i.out
  -- ⊢ |↑(volumeForm o) v| = ∏ i : Fin (Nat.succ n), ‖v i‖
  let b : OrthonormalBasis (Fin n.succ) ℝ E := gramSchmidtOrthonormalBasis hdim v
  -- ⊢ |↑(volumeForm o) v| = ∏ i : Fin (Nat.succ n), ‖v i‖
  have hb : b.toBasis.det v = ∏ i, ⟪b i, v i⟫ := gramSchmidtOrthonormalBasis_det hdim v
  -- ⊢ |↑(volumeForm o) v| = ∏ i : Fin (Nat.succ n), ‖v i‖
  rw [o.volumeForm_robust' b, hb, Finset.abs_prod]
  -- ⊢ ∏ x : Fin (Nat.succ n), |inner (↑b x) (v x)| = ∏ i : Fin (Nat.succ n), ‖v i‖
  by_cases h : ∃ i, v i = 0
  -- ⊢ ∏ x : Fin (Nat.succ n), |inner (↑b x) (v x)| = ∏ i : Fin (Nat.succ n), ‖v i‖
  obtain ⟨i, hi⟩ := h
  -- ⊢ ∏ x : Fin (Nat.succ n), |inner (↑b x) (v x)| = ∏ i : Fin (Nat.succ n), ‖v i‖
  · rw [Finset.prod_eq_zero (Finset.mem_univ i), Finset.prod_eq_zero (Finset.mem_univ i)] <;>
    -- ⊢ ‖v i‖ = 0
      simp [hi]
      -- 🎉 no goals
      -- 🎉 no goals
  push_neg at h
  -- ⊢ ∏ x : Fin (Nat.succ n), |inner (↑b x) (v x)| = ∏ i : Fin (Nat.succ n), ‖v i‖
  congr
  -- ⊢ (fun x => |inner (↑b x) (v x)|) = fun i => ‖v i‖
  ext i
  -- ⊢ |inner (↑b i) (v i)| = ‖v i‖
  have hb : b i = ‖v i‖⁻¹ • v i := gramSchmidtOrthonormalBasis_apply_of_orthogonal hdim hv (h i)
  -- ⊢ |inner (↑b i) (v i)| = ‖v i‖
  simp only [hb, inner_smul_left, real_inner_self_eq_norm_mul_norm, IsROrC.conj_to_real]
  -- ⊢ |‖v i‖⁻¹ * (‖v i‖ * ‖v i‖)| = ‖v i‖
  rw [abs_of_nonneg]
  -- ⊢ ‖v i‖⁻¹ * (‖v i‖ * ‖v i‖) = ‖v i‖
  · field_simp
    -- 🎉 no goals
  · positivity
    -- 🎉 no goals
#align orientation.abs_volume_form_apply_of_pairwise_orthogonal Orientation.abs_volumeForm_apply_of_pairwise_orthogonal

/-- The output of the volume form of an oriented real inner product space `E` when evaluated on an
orthonormal basis is ±1. -/
theorem abs_volumeForm_apply_of_orthonormal (v : OrthonormalBasis (Fin n) ℝ E) :
    |o.volumeForm v| = 1 := by
  simpa [o.volumeForm_robust' v v] using congr_arg abs v.toBasis.det_self
  -- 🎉 no goals
#align orientation.abs_volume_form_apply_of_orthonormal Orientation.abs_volumeForm_apply_of_orthonormal

theorem volumeForm_map {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [Fact (finrank ℝ F = n)] (φ : E ≃ₗᵢ[ℝ] F) (x : Fin n → F) :
    (Orientation.map (Fin n) φ.toLinearEquiv o).volumeForm x = o.volumeForm (φ.symm ∘ x) := by
  cases' n with n
  -- ⊢ ↑(volumeForm (↑(map (Fin Nat.zero) φ.toLinearEquiv) o)) x = ↑(volumeForm o)  …
  · refine' o.eq_or_eq_neg_of_isEmpty.elim _ _ <;> rintro rfl <;> simp
    -- ⊢ o = positiveOrientation → ↑(volumeForm (↑(map (Fin Nat.zero) φ.toLinearEquiv …
                                                   -- ⊢ ↑(volumeForm (↑(map (Fin Nat.zero) φ.toLinearEquiv) positiveOrientation)) x  …
                                                   -- ⊢ ↑(volumeForm (↑(map (Fin Nat.zero) φ.toLinearEquiv) (-positiveOrientation))) …
                                                                  -- 🎉 no goals
                                                                  -- 🎉 no goals
  let e : OrthonormalBasis (Fin n.succ) ℝ E := o.finOrthonormalBasis n.succ_pos Fact.out
  -- ⊢ ↑(volumeForm (↑(map (Fin (Nat.succ n)) φ.toLinearEquiv) o)) x = ↑(volumeForm …
  have he : e.toBasis.orientation = o :=
    o.finOrthonormalBasis_orientation n.succ_pos Fact.out
  have heφ : (e.map φ).toBasis.orientation = Orientation.map (Fin n.succ) φ.toLinearEquiv o := by
    rw [← he]
    exact e.toBasis.orientation_map φ.toLinearEquiv
  rw [(Orientation.map (Fin n.succ) φ.toLinearEquiv o).volumeForm_robust (e.map φ) heφ]
  -- ⊢ ↑(Basis.det (OrthonormalBasis.toBasis (OrthonormalBasis.map e φ))) x = ↑(vol …
  rw [o.volumeForm_robust e he]
  -- ⊢ ↑(Basis.det (OrthonormalBasis.toBasis (OrthonormalBasis.map e φ))) x = ↑(Bas …
  simp
  -- 🎉 no goals
#align orientation.volume_form_map Orientation.volumeForm_map

/-- The volume form is invariant under pullback by a positively-oriented isometric automorphism. -/
theorem volumeForm_comp_linearIsometryEquiv (φ : E ≃ₗᵢ[ℝ] E)
    (hφ : 0 < LinearMap.det (φ.toLinearEquiv : E →ₗ[ℝ] E)) (x : Fin n → E) :
    o.volumeForm (φ ∘ x) = o.volumeForm x := by
  cases' n with n -- Porting note: need to explicitly prove `FiniteDimensional ℝ E`
  -- ⊢ ↑(volumeForm o) (↑φ ∘ x) = ↑(volumeForm o) x
  · refine' o.eq_or_eq_neg_of_isEmpty.elim _ _ <;> rintro rfl <;> simp
    -- ⊢ o = positiveOrientation → ↑(volumeForm o) (↑φ ∘ x) = ↑(volumeForm o) x
                                                   -- ⊢ ↑(volumeForm positiveOrientation) (↑φ ∘ x) = ↑(volumeForm positiveOrientatio …
                                                   -- ⊢ ↑(volumeForm (-positiveOrientation)) (↑φ ∘ x) = ↑(volumeForm (-positiveOrien …
                                                                  -- 🎉 no goals
                                                                  -- 🎉 no goals
  haveI : FiniteDimensional ℝ E := fact_finiteDimensional_of_finrank_eq_succ n
  -- ⊢ ↑(volumeForm o) (↑φ ∘ x) = ↑(volumeForm o) x
  convert o.volumeForm_map φ (φ ∘ x)
  -- ⊢ o = ↑(map (Fin (Nat.succ n)) φ.toLinearEquiv) o
  · symm
    -- ⊢ ↑(map (Fin (Nat.succ n)) φ.toLinearEquiv) o = o
    rwa [← o.map_eq_iff_det_pos φ.toLinearEquiv] at hφ
    -- ⊢ Fintype.card (Fin (Nat.succ n)) = finrank ℝ E
    rw [_i.out, Fintype.card_fin]
    -- 🎉 no goals
  · ext
    -- ⊢ x x✝ = (↑(LinearIsometryEquiv.symm φ) ∘ ↑φ ∘ x) x✝
    simp
    -- 🎉 no goals
#align orientation.volume_form_comp_linear_isometry_equiv Orientation.volumeForm_comp_linearIsometryEquiv

end VolumeForm

end Orientation
