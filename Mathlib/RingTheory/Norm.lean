/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Galois

#align_import ring_theory.norm from "leanprover-community/mathlib"@"fecd3520d2a236856f254f27714b80dcfe28ea57"

/-!
# Norm for (finite) ring extensions

Suppose we have an `R`-algebra `S` with a finite basis. For each `s : S`,
the determinant of the linear map given by multiplying by `s` gives information
about the roots of the minimal polynomial of `s` over `R`.

## Implementation notes

Typically, the norm is defined specifically for finite field extensions.
The current definition is as general as possible and the assumption that we have
fields or that the extension is finite is added to the lemmas as needed.

We only define the norm for left multiplication (`Algebra.leftMulMatrix`,
i.e. `LinearMap.mulLeft`).
For now, the definitions assume `S` is commutative, so the choice doesn't
matter anyway.

See also `Algebra.trace`, which is defined similarly as the trace of
`Algebra.leftMulMatrix`.

## References

 * https://en.wikipedia.org/wiki/Field_norm

-/


universe u v w

variable {R S T : Type*} [CommRing R] [Ring S]
variable [Algebra R S]
variable {K L F : Type*} [Field K] [Field L] [Field F]
variable [Algebra K L] [Algebra K F]
variable {ι : Type w}

open FiniteDimensional

open LinearMap

open Matrix Polynomial

open scoped Matrix

namespace Algebra

variable (R)

/-- The norm of an element `s` of an `R`-algebra is the determinant of `(*) s`. -/
noncomputable def norm : S →* R :=
  LinearMap.det.comp (lmul R S).toRingHom.toMonoidHom
#align algebra.norm Algebra.norm

theorem norm_apply (x : S) : norm R x = LinearMap.det (lmul R S x) := rfl
#align algebra.norm_apply Algebra.norm_apply

theorem norm_eq_one_of_not_exists_basis (h : ¬∃ s : Finset S, Nonempty (Basis s R S)) (x : S) :
    norm R x = 1 := by rw [norm_apply, LinearMap.det]; split_ifs <;> trivial
#align algebra.norm_eq_one_of_not_exists_basis Algebra.norm_eq_one_of_not_exists_basis

variable {R}

theorem norm_eq_one_of_not_module_finite (h : ¬Module.Finite R S) (x : S) : norm R x = 1 := by
  refine norm_eq_one_of_not_exists_basis _ (mt ?_ h) _
  rintro ⟨s, ⟨b⟩⟩
  exact Module.Finite.of_basis b
#align algebra.norm_eq_one_of_not_module_finite Algebra.norm_eq_one_of_not_module_finite

-- Can't be a `simp` lemma because it depends on a choice of basis
theorem norm_eq_matrix_det [Fintype ι] [DecidableEq ι] (b : Basis ι R S) (s : S) :
    norm R s = Matrix.det (Algebra.leftMulMatrix b s) := by
  rw [norm_apply, ← LinearMap.det_toMatrix b, ← toMatrix_lmul_eq]; rfl
#align algebra.norm_eq_matrix_det Algebra.norm_eq_matrix_det

/-- If `x` is in the base ring `K`, then the norm is `x ^ [L : K]`. -/
theorem norm_algebraMap_of_basis [Fintype ι] (b : Basis ι R S) (x : R) :
    norm R (algebraMap R S x) = x ^ Fintype.card ι := by
  haveI := Classical.decEq ι
  rw [norm_apply, ← det_toMatrix b, lmul_algebraMap]
  convert @det_diagonal _ _ _ _ _ fun _ : ι => x
  · ext (i j); rw [toMatrix_lsmul]
  · rw [Finset.prod_const, Finset.card_univ]
#align algebra.norm_algebra_map_of_basis Algebra.norm_algebraMap_of_basis

/-- If `x` is in the base field `K`, then the norm is `x ^ [L : K]`.

(If `L` is not finite-dimensional over `K`, then `norm = 1 = x ^ 0 = x ^ (finrank L K)`.)
-/
@[simp]
protected theorem norm_algebraMap {L : Type*} [Ring L] [Algebra K L] (x : K) :
    norm K (algebraMap K L x) = x ^ finrank K L := by
  by_cases H : ∃ s : Finset L, Nonempty (Basis s K L)
  · rw [norm_algebraMap_of_basis H.choose_spec.some, finrank_eq_card_basis H.choose_spec.some]
  · rw [norm_eq_one_of_not_exists_basis K H, finrank_eq_zero_of_not_exists_basis, pow_zero]
    rintro ⟨s, ⟨b⟩⟩
    exact H ⟨s, ⟨b⟩⟩
#align algebra.norm_algebra_map Algebra.norm_algebraMap

section EqProdRoots

/-- Given `pb : PowerBasis K S`, then the norm of `pb.gen` is
`(-1) ^ pb.dim * coeff (minpoly K pb.gen) 0`. -/
theorem PowerBasis.norm_gen_eq_coeff_zero_minpoly (pb : PowerBasis R S) :
    norm R pb.gen = (-1) ^ pb.dim * coeff (minpoly R pb.gen) 0 := by
  rw [norm_eq_matrix_det pb.basis, det_eq_sign_charpoly_coeff, charpoly_leftMulMatrix,
    Fintype.card_fin]
#align algebra.power_basis.norm_gen_eq_coeff_zero_minpoly Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly

/-- Given `pb : PowerBasis R S`, then the norm of `pb.gen` is
`((minpoly R pb.gen).aroots F).prod`. -/
theorem PowerBasis.norm_gen_eq_prod_roots [Algebra R F] (pb : PowerBasis R S)
    (hf : (minpoly R pb.gen).Splits (algebraMap R F)) :
    algebraMap R F (norm R pb.gen) = ((minpoly R pb.gen).aroots F).prod := by
  haveI := Module.nontrivial R F
  have := minpoly.monic pb.isIntegral_gen
  rw [PowerBasis.norm_gen_eq_coeff_zero_minpoly, ← pb.natDegree_minpoly, RingHom.map_mul,
    ← coeff_map,
    prod_roots_eq_coeff_zero_of_monic_of_split (this.map _) ((splits_id_iff_splits _).2 hf),
    this.natDegree_map, map_pow, ← mul_assoc, ← mul_pow]
  simp only [map_neg, _root_.map_one, neg_mul, neg_neg, one_pow, one_mul]
#align algebra.power_basis.norm_gen_eq_prod_roots Algebra.PowerBasis.norm_gen_eq_prod_roots

end EqProdRoots

section EqZeroIff

variable [Finite ι]

@[simp]
theorem norm_zero [Nontrivial S] [Module.Free R S] [Module.Finite R S] : norm R (0 : S) = 0 := by
  nontriviality
  rw [norm_apply, coe_lmul_eq_mul, map_zero, LinearMap.det_zero' (Module.Free.chooseBasis R S)]
#align algebra.norm_zero Algebra.norm_zero

@[simp]
theorem norm_eq_zero_iff [IsDomain R] [IsDomain S] [Module.Free R S] [Module.Finite R S] {x : S} :
    norm R x = 0 ↔ x = 0 := by
  constructor
  on_goal 1 => let b := Module.Free.chooseBasis R S
  swap
  · rintro rfl; exact norm_zero
  · letI := Classical.decEq (Module.Free.ChooseBasisIndex R S)
    rw [norm_eq_matrix_det b, ← Matrix.exists_mulVec_eq_zero_iff]
    rintro ⟨v, v_ne, hv⟩
    rw [← b.equivFun.apply_symm_apply v, b.equivFun_symm_apply, b.equivFun_apply,
      leftMulMatrix_mulVec_repr] at hv
    refine (mul_eq_zero.mp (b.ext_elem fun i => ?_)).resolve_right (show ∑ i, v i • b i ≠ 0 from ?_)
    · simpa only [LinearEquiv.map_zero, Pi.zero_apply] using congr_fun hv i
    · contrapose! v_ne with sum_eq
      apply b.equivFun.symm.injective
      rw [b.equivFun_symm_apply, sum_eq, LinearEquiv.map_zero]
#align algebra.norm_eq_zero_iff Algebra.norm_eq_zero_iff

theorem norm_ne_zero_iff [IsDomain R] [IsDomain S] [Module.Free R S] [Module.Finite R S] {x : S} :
    norm R x ≠ 0 ↔ x ≠ 0 := not_iff_not.mpr norm_eq_zero_iff
#align algebra.norm_ne_zero_iff Algebra.norm_ne_zero_iff

/-- This is `Algebra.norm_eq_zero_iff` composed with `Algebra.norm_apply`. -/
@[simp]
theorem norm_eq_zero_iff' [IsDomain R] [IsDomain S] [Module.Free R S] [Module.Finite R S] {x : S} :
    LinearMap.det (LinearMap.mul R S x) = 0 ↔ x = 0 := norm_eq_zero_iff
#align algebra.norm_eq_zero_iff' Algebra.norm_eq_zero_iff'

theorem norm_eq_zero_iff_of_basis [IsDomain R] [IsDomain S] (b : Basis ι R S) {x : S} :
    Algebra.norm R x = 0 ↔ x = 0 := by
  haveI : Module.Free R S := Module.Free.of_basis b
  haveI : Module.Finite R S := Module.Finite.of_basis b
  exact norm_eq_zero_iff
#align algebra.norm_eq_zero_iff_of_basis Algebra.norm_eq_zero_iff_of_basis

theorem norm_ne_zero_iff_of_basis [IsDomain R] [IsDomain S] (b : Basis ι R S) {x : S} :
    Algebra.norm R x ≠ 0 ↔ x ≠ 0 :=
  not_iff_not.mpr (norm_eq_zero_iff_of_basis b)
#align algebra.norm_ne_zero_iff_of_basis Algebra.norm_ne_zero_iff_of_basis

end EqZeroIff

open IntermediateField

variable (K)

theorem norm_eq_norm_adjoin [FiniteDimensional K L] [IsSeparable K L] (x : L) :
    norm K x = norm K (AdjoinSimple.gen K x) ^ finrank K⟮x⟯ L := by
  letI := isSeparable_tower_top_of_isSeparable K K⟮x⟯ L
  let pbL := Field.powerBasisOfFiniteOfSeparable K⟮x⟯ L
  let pbx := IntermediateField.adjoin.powerBasis (IsSeparable.isIntegral K x)
  -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
  erw [← AdjoinSimple.algebraMap_gen K x, norm_eq_matrix_det (pbx.basis.smul pbL.basis) _,
    smul_leftMulMatrix_algebraMap, det_blockDiagonal, norm_eq_matrix_det pbx.basis]
  simp only [Finset.card_fin, Finset.prod_const]
  congr
  rw [← PowerBasis.finrank, AdjoinSimple.algebraMap_gen K x]
#align algebra.norm_eq_norm_adjoin Algebra.norm_eq_norm_adjoin

variable {K}

section IntermediateField

theorem _root_.IntermediateField.AdjoinSimple.norm_gen_eq_one {x : L} (hx : ¬IsIntegral K x) :
    norm K (AdjoinSimple.gen K x) = 1 := by
  rw [norm_eq_one_of_not_exists_basis]
  contrapose! hx
  obtain ⟨s, ⟨b⟩⟩ := hx
  refine .of_mem_of_fg K⟮x⟯.toSubalgebra ?_ x ?_
  · exact (Submodule.fg_iff_finiteDimensional _).mpr (of_fintype_basis b)
  · exact IntermediateField.subset_adjoin K _ (Set.mem_singleton x)
#align intermediate_field.adjoin_simple.norm_gen_eq_one IntermediateField.AdjoinSimple.norm_gen_eq_one

theorem _root_.IntermediateField.AdjoinSimple.norm_gen_eq_prod_roots (x : L)
    (hf : (minpoly K x).Splits (algebraMap K F)) :
    (algebraMap K F) (norm K (AdjoinSimple.gen K x)) =
      ((minpoly K x).aroots F).prod := by
  have injKxL := (algebraMap K⟮x⟯ L).injective
  by_cases hx : IsIntegral K x; swap
  · simp [minpoly.eq_zero hx, IntermediateField.AdjoinSimple.norm_gen_eq_one hx, aroots_def]
  rw [← adjoin.powerBasis_gen hx, PowerBasis.norm_gen_eq_prod_roots] <;>
    rw [adjoin.powerBasis_gen hx, ← minpoly.algebraMap_eq injKxL] <;>
    try simp only [AdjoinSimple.algebraMap_gen _ _]
  exact hf
#align intermediate_field.adjoin_simple.norm_gen_eq_prod_roots IntermediateField.AdjoinSimple.norm_gen_eq_prod_roots

end IntermediateField

section EqProdEmbeddings

open IntermediateField IntermediateField.AdjoinSimple Polynomial

variable (F) (E : Type*) [Field E] [Algebra K E]

theorem norm_eq_prod_embeddings_gen [Algebra R F] (pb : PowerBasis R S)
    (hE : (minpoly R pb.gen).Splits (algebraMap R F)) (hfx : (minpoly R pb.gen).Separable) :
    algebraMap R F (norm R pb.gen) =
      (@Finset.univ _ (PowerBasis.AlgHom.fintype pb)).prod fun σ => σ pb.gen := by
  letI := Classical.decEq F
  rw [PowerBasis.norm_gen_eq_prod_roots pb hE]
  rw [@Fintype.prod_equiv (S →ₐ[R] F) _ _ (PowerBasis.AlgHom.fintype pb) _ _ pb.liftEquiv'
    (fun σ => σ pb.gen) (fun x => x) ?_]
  · rw [Finset.prod_mem_multiset, Finset.prod_eq_multiset_prod, Multiset.toFinset_val,
      Multiset.dedup_eq_self.mpr, Multiset.map_id]
    · exact nodup_roots hfx.map
    · intro x; rfl
  · intro σ; simp only [PowerBasis.liftEquiv'_apply_coe]
#align algebra.norm_eq_prod_embeddings_gen Algebra.norm_eq_prod_embeddings_gen

theorem norm_eq_prod_roots [IsSeparable K L] [FiniteDimensional K L] {x : L}
    (hF : (minpoly K x).Splits (algebraMap K F)) :
    algebraMap K F (norm K x) =
      ((minpoly K x).aroots F).prod ^ finrank K⟮x⟯ L := by
  rw [norm_eq_norm_adjoin K x, map_pow, IntermediateField.AdjoinSimple.norm_gen_eq_prod_roots _ hF]
#align algebra.norm_eq_prod_roots Algebra.norm_eq_prod_roots

theorem prod_embeddings_eq_finrank_pow [Algebra L F] [IsScalarTower K L F] [IsAlgClosed E]
    [IsSeparable K F] [FiniteDimensional K F] (pb : PowerBasis K L) :
    ∏ σ : F →ₐ[K] E, σ (algebraMap L F pb.gen) =
      ((@Finset.univ _ (PowerBasis.AlgHom.fintype pb)).prod
        fun σ : L →ₐ[K] E => σ pb.gen) ^ finrank L F := by
  haveI : FiniteDimensional L F := FiniteDimensional.right K L F
  haveI : IsSeparable L F := isSeparable_tower_top_of_isSeparable K L F
  letI : Fintype (L →ₐ[K] E) := PowerBasis.AlgHom.fintype pb
  rw [Fintype.prod_equiv algHomEquivSigma (fun σ : F →ₐ[K] E => _) fun σ => σ.1 pb.gen,
    ← Finset.univ_sigma_univ, Finset.prod_sigma, ← Finset.prod_pow]
  · refine Finset.prod_congr rfl fun σ _ => ?_
    letI : Algebra L E := σ.toRingHom.toAlgebra
    simp_rw [Finset.prod_const]
    congr
    exact AlgHom.card L F E
  · intro σ
    simp only [algHomEquivSigma, Equiv.coe_fn_mk, AlgHom.restrictDomain, AlgHom.comp_apply,
      IsScalarTower.coe_toAlgHom']
#align algebra.prod_embeddings_eq_finrank_pow Algebra.prod_embeddings_eq_finrank_pow

variable (K)

/-- For `L/K` a finite separable extension of fields and `E` an algebraically closed extension
of `K`, the norm (down to `K`) of an element `x` of `L` is equal to the product of the images
of `x` over all the `K`-embeddings `σ` of `L` into `E`. -/
theorem norm_eq_prod_embeddings [FiniteDimensional K L] [IsSeparable K L] [IsAlgClosed E] (x : L) :
    algebraMap K E (norm K x) = ∏ σ : L →ₐ[K] E, σ x := by
  have hx := IsSeparable.isIntegral K x
  rw [norm_eq_norm_adjoin K x, RingHom.map_pow, ← adjoin.powerBasis_gen hx,
    norm_eq_prod_embeddings_gen E (adjoin.powerBasis hx) (IsAlgClosed.splits_codomain _)]
  · exact (prod_embeddings_eq_finrank_pow L (L := K⟮x⟯) E (adjoin.powerBasis hx)).symm
  · haveI := isSeparable_tower_bot_of_isSeparable K K⟮x⟯ L
    exact IsSeparable.separable K _
#align algebra.norm_eq_prod_embeddings Algebra.norm_eq_prod_embeddings

theorem norm_eq_prod_automorphisms [FiniteDimensional K L] [IsGalois K L] (x : L) :
    algebraMap K L (norm K x) = ∏ σ : L ≃ₐ[K] L, σ x := by
  apply NoZeroSMulDivisors.algebraMap_injective L (AlgebraicClosure L)
  rw [map_prod (algebraMap L (AlgebraicClosure L))]
  rw [← Fintype.prod_equiv (Normal.algHomEquivAut K (AlgebraicClosure L) L)]
  · rw [← norm_eq_prod_embeddings _ _ x, ← IsScalarTower.algebraMap_apply]
  · intro σ
    simp only [Normal.algHomEquivAut, AlgHom.restrictNormal', Equiv.coe_fn_mk,
      AlgEquiv.coe_ofBijective, AlgHom.restrictNormal_commutes, id.map_eq_id, RingHom.id_apply]
#align algebra.norm_eq_prod_automorphisms Algebra.norm_eq_prod_automorphisms

theorem isIntegral_norm [Algebra R L] [Algebra R K] [IsScalarTower R K L] [IsSeparable K L]
    [FiniteDimensional K L] {x : L} (hx : IsIntegral R x) : IsIntegral R (norm K x) := by
  have hx' : IsIntegral K x := hx.tower_top
  rw [← isIntegral_algebraMap_iff (algebraMap K (AlgebraicClosure L)).injective, norm_eq_prod_roots]
  · refine (IsIntegral.multiset_prod fun y hy => ?_).pow _
    rw [mem_roots_map (minpoly.ne_zero hx')] at hy
    use minpoly R x, minpoly.monic hx
    rw [← aeval_def] at hy ⊢
    exact minpoly.aeval_of_isScalarTower R x y hy
  · apply IsAlgClosed.splits_codomain
#align algebra.is_integral_norm Algebra.isIntegral_norm

lemma norm_eq_of_algEquiv [Ring T] [Algebra R T] (e : S ≃ₐ[R] T) (x) :
    Algebra.norm R (e x) = Algebra.norm R x := by
  simp_rw [Algebra.norm_apply, ← LinearMap.det_conj _ e.toLinearEquiv]; congr; ext; simp

lemma norm_eq_of_ringEquiv {A B C : Type*} [CommRing A] [CommRing B] [Ring C]
    [Algebra A C] [Algebra B C] (e : A ≃+* B) (he : (algebraMap B C).comp e = algebraMap A C)
    (x : C) :
    e (Algebra.norm A x) = Algebra.norm B x := by
  classical
  by_cases h : ∃ s : Finset C, Nonempty (Basis s B C)
  · obtain ⟨s, ⟨b⟩⟩ := h
    letI : Algebra A B := RingHom.toAlgebra e
    letI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' he.symm
    rw [Algebra.norm_eq_matrix_det b,
      Algebra.norm_eq_matrix_det (b.mapCoeffs e.symm (by simp [Algebra.smul_def, ← he])),
      e.map_det]
    congr
    ext i j
    simp [leftMulMatrix_apply, LinearMap.toMatrix_apply]
  rw [norm_eq_one_of_not_exists_basis _ h, norm_eq_one_of_not_exists_basis, _root_.map_one]
  intro ⟨s, ⟨b⟩⟩
  exact h ⟨s, ⟨b.mapCoeffs e (by simp [Algebra.smul_def, ← he])⟩⟩

lemma norm_eq_of_equiv_equiv {A₁ B₁ A₂ B₂ : Type*} [CommRing A₁] [Ring B₁]
    [CommRing A₂] [Ring B₂] [Algebra A₁ B₁] [Algebra A₂ B₂] (e₁ : A₁ ≃+* A₂) (e₂ : B₁ ≃+* B₂)
    (he : RingHom.comp (algebraMap A₂ B₂) ↑e₁ = RingHom.comp ↑e₂ (algebraMap A₁ B₁)) (x) :
    Algebra.norm A₁ x = e₁.symm (Algebra.norm A₂ (e₂ x)) := by
  letI := (RingHom.comp (e₂ : B₁ →+* B₂) (algebraMap A₁ B₁)).toAlgebra' ?_
  · let e' : B₁ ≃ₐ[A₁] B₂ := { e₂ with commutes' := fun _ ↦ rfl }
    rw [← Algebra.norm_eq_of_ringEquiv e₁ he, ← Algebra.norm_eq_of_algEquiv e',
      RingEquiv.symm_apply_apply]
    rfl
  intros c x
  apply e₂.symm.injective
  simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, _root_.map_mul,
    RingEquiv.symm_apply_apply, commutes]

variable {F} (L)

-- TODO. Generalize this proof to rings
theorem norm_norm [Algebra L F] [IsScalarTower K L F] [IsSeparable K F] (x : F) :
    norm K (norm L x) = norm K x := by
  by_cases hKF : FiniteDimensional K F
  · let A := AlgebraicClosure K
    apply (algebraMap K A).injective
    haveI : FiniteDimensional L F := FiniteDimensional.right K L F
    haveI : FiniteDimensional K L := FiniteDimensional.left K L F
    haveI : IsSeparable K L := isSeparable_tower_bot_of_isSeparable K L F
    haveI : IsSeparable L F := isSeparable_tower_top_of_isSeparable K L F
    letI : ∀ σ : L →ₐ[K] A,
        haveI := σ.toRingHom.toAlgebra
        Fintype (F →ₐ[L] A) := fun _ => inferInstance
    rw [norm_eq_prod_embeddings K A (_ : F),
      Fintype.prod_equiv algHomEquivSigma (fun σ : F →ₐ[K] A => σ x)
        (fun π : Σ f : L →ₐ[K] A, _ => (π.2 : F → A) x) fun _ => rfl]
    suffices ∀ σ : L →ₐ[K] A,
        haveI := σ.toRingHom.toAlgebra
        ∏ π : F →ₐ[L] A, π x = σ (norm L x)
      by simp_rw [← Finset.univ_sigma_univ, Finset.prod_sigma, this, norm_eq_prod_embeddings]
    intro σ
    letI : Algebra L A := σ.toRingHom.toAlgebra
    rw [← norm_eq_prod_embeddings L A (_ : F)]
    rfl
  · rw [norm_eq_one_of_not_module_finite hKF]
    by_cases hKL : FiniteDimensional K L
    · have hLF : ¬FiniteDimensional L F := by
        refine (mt ?_) hKF
        intro hKF
        exact FiniteDimensional.trans K L F
      rw [norm_eq_one_of_not_module_finite hLF, _root_.map_one]
    · rw [norm_eq_one_of_not_module_finite hKL]
#align algebra.norm_norm Algebra.norm_norm

end EqProdEmbeddings

end Algebra
