module

public import Mathlib.RingTheory.Extension.Presentation.Submersive
public import Mathlib.RingTheory.Extension.Presentation.Core
public import Mathlib.RingTheory.Extension.Cotangent.Basis
public import Mathlib.RingTheory.Extension.Cotangent.Free


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

namespace Algebra -- start stolen from #31081

open KaehlerDifferential

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

namespace Generators

open MvPolynomial

variable {ι ι' : Type*} {σ κ : Type*}

/-- Extend generators by more variables. -/
noncomputable def extend (P : Generators R S ι) (b : ι' → S) : Generators R S (ι ⊕ ι') :=
  .ofSurjective (Sum.elim P.val b) fun s ↦ by
    use rename Sum.inl (P.σ s)
    simp [aeval_rename]

@[simp]
lemma extend_val_inl (P : Generators R S ι) (b : ι' → S) (i : ι) :
    (P.extend b).val (.inl i) = P.val i := rfl

@[simp]
lemma extend_val_inr (P : Generators R S ι) (b : ι' → S) (i : ι') :
    (P.extend b).val (.inr i) = b i := rfl

variable (P : Generators R S ι) {u : σ → ι} (hu : Function.Injective u)
  {v : κ → ι} (hv : Function.Injective v)

lemma cotangentRestrict_bijective_of_basis_kaehlerDifferential
    (huv : IsCompl (Set.range v) (Set.range u)) (b : Module.Basis κ S (Ω[S⁄R]))
    (hb : ∀ k, b k = (D R S) (P.val (v k))) [Subsingleton (H1Cotangent R S)] :
    Function.Bijective (cotangentRestrict P hu) := by
  refine P.cotangentRestrict_bijective_of_isCompl _ huv ?_ ?_
  · simp_rw [← hb]
    exact b.span_eq
  · apply disjoint_ker_toKaehler_of_linearIndependent
    simp_rw [← hb]
    exact b.linearIndependent

end Generators

/-- If `H¹(S/R) = 0` and `Ω[S⁄R]` is free on `{d sᵢ}ᵢ` for some `sᵢ : S`, then `S`
is `R`-standard smooth. -/
theorem IsStandardSmooth.of_basis_kaehlerDifferential [FinitePresentation R S]
    [Subsingleton (H1Cotangent R S)]
    {I : Type*} (b : Module.Basis I S (Ω[S⁄R])) (hb : Set.range b ⊆ Set.range (D R S)) :
    IsStandardSmooth R S := by
  nontriviality S
  obtain ⟨n, ⟨P⟩⟩ := (FiniteType.iff_exists_generators (R := R) (S := S)).mp inferInstance
  choose f' hf' using hb
  let P := P.extend fun i ↦ f' ⟨i, rfl⟩
  have hb (i : I) : b i = D R S (P.val (Sum.inr i)) := by simp [P, hf']
  have : Function.Bijective (P.cotangentRestrict _) :=
    P.cotangentRestrict_bijective_of_basis_kaehlerDifferential Sum.inl_injective
      Set.isCompl_range_inl_range_inr.symm b hb
  let bcot' : Module.Basis (Fin n) S P.toExtension.Cotangent :=
    .ofRepr (.ofBijective (P.cotangentRestrict _) this)
  have : Finite I := Module.Finite.finite_basis b
  obtain ⟨Q, bcot, hcomp, hbcot⟩ := P.exists_presentation_of_basis_cotangent bcot'
  let P' : PreSubmersivePresentation R S (Unit ⊕ Fin n ⊕ I) (Unit ⊕ Fin n) :=
    { __ := Q
      map := Sum.map _root_.id Sum.inl
      map_inj := Sum.map_injective.mpr ⟨fun _ _ h ↦ h, Sum.inl_injective⟩ }
  have hcompl : IsCompl (Set.range (Sum.inr ∘ Sum.inr)) (Set.range P'.map) := by
    simp [P', ← eq_compl_iff_isCompl, Set.ext_iff, Set.mem_compl_iff]
  have hbij : Function.Bijective (P'.cotangentRestrict P'.map_inj) := by
    apply P'.cotangentRestrict_bijective_of_basis_kaehlerDifferential P'.map_inj hcompl b
    intro k
    simp only [hb, ← hcomp, P', Function.comp_def]
  let P'' : SubmersivePresentation R S _ _ :=
    ⟨P', P'.isUnit_jacobian_of_cotangentRestrict_bijective bcot hbcot hbij⟩
  exact P''.isStandardSmooth

/-- An `R`-algebra `S` of finite presentation is standard smooth if and only if
`H¹(S/R) = 0` and `Ω[S⁄R]` is free on `{d sᵢ}ᵢ` for some `sᵢ : S`. -/
theorem IsStandardSmooth.iff_exists_basis_kaehlerDifferential [FinitePresentation R S] :
    IsStandardSmooth R S ↔ Subsingleton (H1Cotangent R S) ∧
      ∃ (I : Type) (b : Module.Basis I S (Ω[S⁄R])), Set.range b ⊆ Set.range (D R S) := by
  refine ⟨fun h ↦ ⟨inferInstance, ?_⟩, fun ⟨h, ⟨_, b, hb⟩⟩ ↦ .of_basis_kaehlerDifferential b hb⟩
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := Algebra.IsStandardSmooth.out (R := R) (S := S)
  exact ⟨_, P.basisKaehler, by simp [Set.range_subset_iff, SubmersivePresentation.basisKaehler,
    SubmersivePresentation.basisKaehlerOfIsCompl, Module.Basis.ofSplitExact]⟩

lemma IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth [Nontrivial S]
    [IsStandardSmooth R S] (n : ℕ) :
    IsStandardSmoothOfRelativeDimension n R S ↔ Module.rank S Ω[S⁄R] = n := by
  refine ⟨fun h ↦ IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential _, fun h ↦ ?_⟩
  obtain ⟨_, _, _, _, ⟨P⟩⟩ := ‹IsStandardSmooth R S›
  refine ⟨_, _, _, ‹_›, ⟨P, ?_⟩⟩
  apply Nat.cast_injective (R := Cardinal)
  rwa [← P.rank_kaehlerDifferential]

/-- `S` is an étale `R`-algebra if and only if it is standard smooth of relative dimension `0`. -/
theorem Etale.iff_isStandardSmoothOfRelativeDimension_zero :
    Etale R S ↔ IsStandardSmoothOfRelativeDimension 0 R S := by
  refine ⟨fun h ↦ ?_, fun _ ↦ inferInstance⟩
  nontriviality S
  suffices h : IsStandardSmooth R S by
    simp [IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth]
  rw [IsStandardSmooth.iff_exists_basis_kaehlerDifferential]
  refine ⟨inferInstance, ⟨Empty, Module.Basis.empty Ω[S⁄R], ?_⟩⟩
  simp [Set.range_subset_iff]

end Algebra -- end stolen from #31081

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
