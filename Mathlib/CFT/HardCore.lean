module

public import Mathlib.RingTheory.Extension.Presentation.Submersive
public import Mathlib.RingTheory.Extension.Presentation.Core
public import Mathlib.RingTheory.Extension.Cotangent.Basis
public import Mathlib.RingTheory.Extension.Cotangent.Free
public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree


@[expose] public section

open TensorProduct

variable {R S ι σ : Type*} [CommRing R] [CommRing S] [Algebra R S]

namespace Algebra.SubmersivePresentation

variable [Finite σ] (P : Algebra.SubmersivePresentation R S ι σ)

lemma exists_sum_eq_σ_jacobian_mul_σ_jacobian_inv_sub_one
    [DecidableEq σ] [Fintype σ] :
    ∃ v : σ → MvPolynomial ι R, ∑ i, v i * P.relation i =
        P.jacobiMatrix.det * P.σ ↑(P.jacobian_isUnit.unit⁻¹) - 1 := by
  have H : P.jacobiMatrix.det * P.σ ↑(P.jacobian_isUnit.unit⁻¹) - 1 ∈ P.ker := by
    simp [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
  rwa [← P.span_range_relation_eq_ker, Ideal.mem_span_range_iff_exists_fun] at H

/-- An arbitrarily chosen relation exhibiting the fact that `P.jacobian` is invertible. -/
noncomputable
def jacobianRelations (s : σ) : MvPolynomial ι R :=
  letI := Fintype.ofFinite σ
  letI := Classical.decEq σ
  P.exists_sum_eq_σ_jacobian_mul_σ_jacobian_inv_sub_one.choose s

lemma jacobianRelations_spec [DecidableEq σ] [Fintype σ] :
    ∑ i, P.jacobianRelations i * P.relation i =
      P.jacobiMatrix.det * P.σ ↑(P.jacobian_isUnit.unit⁻¹) - 1 := by
  delta jacobianRelations
  convert P.exists_sum_eq_σ_jacobian_mul_σ_jacobian_inv_sub_one.choose_spec

/-- The set of coefficients that is enough to descend a submersive presentation `P`. -/
def coeffs : Set R :=
  P.toPresentation.coeffs ∪ (P.σ (P.jacobian_isUnit.unit⁻¹:)).coeffs ∪
    ⋃ i, (P.jacobianRelations i).coeffs

lemma finite_coeffs : P.coeffs.Finite :=
  .union (P.toPresentation.finite_coeffs.union (by simp))
    (.iUnion Set.finite_univ (by simp) (by simp))

lemma coeffs_toPresentation_subset_coeffs : P.toPresentation.coeffs ⊆ P.coeffs :=
  Set.subset_union_left.trans Set.subset_union_left

/-- A type class witnessing the fact that `R₀` contains enough coefficients to descend
`P` to a submersive presentation. -/
class HasCoeffs (R₀ : Type*) [CommRing R₀] [Algebra R₀ R] [Algebra R₀ S]
    [IsScalarTower R₀ R S] where
  coeffs_subset_range : P.coeffs ⊆ ↑(algebraMap R₀ R).range

variable (R₀ : Type*) [CommRing R₀] [Algebra R₀ R] [Algebra R₀ S] [IsScalarTower R₀ R S]
  [P.HasCoeffs R₀]

instance (priority := low) : P.toPresentation.HasCoeffs R₀ where
  coeffs_subset_range := P.coeffs_toPresentation_subset_coeffs.trans HasCoeffs.coeffs_subset_range

/-- The jacobian of a presentation in the smaller coefficient ring, provided `P.HasCoeffs R₀`. -/
noncomputable
def jacobianOfHasCoeffs : MvPolynomial ι R₀ :=
  letI := Classical.decEq σ
  letI := Fintype.ofFinite σ
  (Matrix.of fun i j ↦ MvPolynomial.pderiv (P.map i) (P.relationOfHasCoeffs R₀ j)).det

@[simp]
lemma map_jacobianOfHasCoeffs [Fintype σ] [DecidableEq σ] :
    (P.jacobianOfHasCoeffs R₀).map (algebraMap R₀ R) = P.jacobiMatrix.det := by
  rw [jacobianOfHasCoeffs, @RingHom.map_det]
  congr! 1
  ext1 i j
  simp [Presentation.map_relationOfHasCoeffs, ← MvPolynomial.pderiv_map, P.jacobiMatrix_apply]

@[simp]
lemma aeval_jacobianOfHasCoeffs :
    MvPolynomial.aeval P.val (P.jacobianOfHasCoeffs R₀) = P.jacobian := by
  classical
  let : Fintype σ := Fintype.ofFinite _
  rw [← MvPolynomial.aeval_map_algebraMap R, map_jacobianOfHasCoeffs,
    P.jacobian_eq_jacobiMatrix_det, Generators.algebraMap_apply]

/-- The inverse jacobian of a presentation in the smaller coefficient ring,
provided `P.HasCoeffs R₀`. -/
noncomputable
def invJacobianOfHasCoeffs : MvPolynomial ι R₀ :=
  (MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
    ((Set.subset_union_right.trans Set.subset_union_left).trans
      (HasCoeffs.coeffs_subset_range (P := P)))).choose

@[simp]
lemma map_invJacobianOfHasCoeffs :
    (P.invJacobianOfHasCoeffs R₀).map (algebraMap R₀ R) = P.σ ↑(P.jacobian_isUnit.unit⁻¹) :=
  (MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
    ((Set.subset_union_right.trans Set.subset_union_left).trans
      (HasCoeffs.coeffs_subset_range (P := P)))).choose_spec

@[simp]
lemma aeval_invJacobianOfHasCoeffs :
    MvPolynomial.aeval P.val (P.invJacobianOfHasCoeffs R₀) = ↑(P.jacobian_isUnit.unit⁻¹) := by
  simpa [-map_invJacobianOfHasCoeffs, MvPolynomial.aeval_map_algebraMap] using
    congr(MvPolynomial.aeval P.val $(P.map_invJacobianOfHasCoeffs R₀))

/-- An arbitrarily chosen relation exhibiting the fact that `P.jacobian` is invertible,
provided `P.HasCoeffs R₀`. -/
noncomputable
def jacobianRelationsOfHasCoeffs (i : σ) : MvPolynomial ι R₀ :=
  (MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
    ((Set.subset_iUnion _ i).trans (Set.subset_union_right.trans
      (HasCoeffs.coeffs_subset_range (P := P))))).choose

@[simp]
lemma map_jacobianRelationsOfHasCoeffs (i : σ) :
    (P.jacobianRelationsOfHasCoeffs R₀ i).map (algebraMap R₀ R) = P.jacobianRelations i :=
  (MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
    ((Set.subset_iUnion _ i).trans (Set.subset_union_right.trans
      (HasCoeffs.coeffs_subset_range (P := P))))).choose_spec

lemma sum_jacobianRelationsOfHasCoeffs_mul_relationOfHasCoeffs [FaithfulSMul R₀ R] [Fintype σ] :
    ∑ i, P.jacobianRelationsOfHasCoeffs R₀ i * P.relationOfHasCoeffs R₀ i =
        P.jacobianOfHasCoeffs R₀ * P.invJacobianOfHasCoeffs R₀ - 1 := by
  classical
  apply MvPolynomial.map_injective _ (FaithfulSMul.algebraMap_injective R₀ R)
  simp [P.map_relationOfHasCoeffs, jacobianRelations_spec]

/-- The submersive presentation on `P.ModelOfHasCoeffs R₀` provided `P.HasCoeffs R₀`. -/
noncomputable
def submersivePresentationOfHasCoeffs [FaithfulSMul R₀ R] :
    Algebra.SubmersivePresentation R₀ (P.ModelOfHasCoeffs R₀) ι σ where
  __ := Algebra.Presentation.naive
  map := P.map
  map_inj := P.map_inj
  jacobian_isUnit := by
    classical
    let : Fintype σ := Fintype.ofFinite _
    have := congr((Ideal.Quotient.mk _ : _ →+* P.ModelOfHasCoeffs R₀)
      $(P.sum_jacobianRelationsOfHasCoeffs_mul_relationOfHasCoeffs R₀))
    simp only [map_sum, map_mul, Ideal.Quotient.mk_span_range, mul_zero, Finset.sum_const_zero,
      map_sub, map_one, @eq_comm (P.ModelOfHasCoeffs R₀) 0, sub_eq_zero] at this
    convert IsUnit.of_mul_eq_one _ this
    rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, jacobianOfHasCoeffs]
    congr 2
    ext1 i j
    simp [PreSubmersivePresentation.jacobiMatrix_apply]

end Algebra.SubmersivePresentation

namespace Algebra

universe u

variable {R : Type*} {A : Type u} {B : Type*}
  [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra A B]

theorem IsStandardSmoothOfRelativeDimension.exists_subalgebra_finiteType
    (n : ℕ) [IsStandardSmoothOfRelativeDimension n A B] :
    ∃ (A₀ : Subalgebra R A) (B₀ : Type u) (_ : CommRing B₀) (_ : Algebra A₀ B₀),
      A₀.FG ∧ IsStandardSmoothOfRelativeDimension n A₀ B₀ ∧ Nonempty (B ≃ₐ[A] A ⊗[A₀] B₀) := by
  obtain ⟨ι, σ, _, _, P, hP⟩ := IsStandardSmoothOfRelativeDimension.out (n := n) (R := A) (S := B)
  let A₀ := Algebra.adjoin R P.coeffs
  have : P.HasCoeffs A₀ := ⟨by simp [A₀]⟩
  exact ⟨A₀, (P.ModelOfHasCoeffs A₀:), inferInstance, inferInstance,
    ⟨P.finite_coeffs.toFinset, by simp [A₀]⟩, ⟨_, _, _, inferInstance,
      P.submersivePresentationOfHasCoeffs A₀, hP⟩, ⟨(P.tensorModelOfHasCoeffsEquiv A₀).symm⟩⟩

theorem Etale.exists_subalgebra_finiteType [Etale A B] :
    ∃ (A₀ : Subalgebra R A) (B₀ : Type u) (_ : CommRing B₀) (_ : Algebra A₀ B₀),
      A₀.FG ∧ Etale A₀ B₀ ∧ Nonempty (B ≃ₐ[A] A ⊗[A₀] B₀) := by
  simp only [Etale.iff_isStandardSmoothOfRelativeDimension_zero] at *
  exact IsStandardSmoothOfRelativeDimension.exists_subalgebra_finiteType ..

end Algebra
