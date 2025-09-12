/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.RingTheory.Norm.Defs
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Galois.Basic

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

open Module

open LinearMap

open Matrix Polynomial

open scoped Matrix

namespace Algebra

section EqProdRoots

/-- Given `pb : PowerBasis K S`, then the norm of `pb.gen` is
`(-1) ^ pb.dim * coeff (minpoly K pb.gen) 0`. -/
theorem PowerBasis.norm_gen_eq_coeff_zero_minpoly (pb : PowerBasis R S) :
    norm R pb.gen = (-1) ^ pb.dim * coeff (minpoly R pb.gen) 0 := by
  rw [norm_eq_matrix_det pb.basis, det_eq_sign_charpoly_coeff, charpoly_leftMulMatrix,
    Fintype.card_fin]

/-- Given `pb : PowerBasis R S`, then the norm of `pb.gen` is
`((minpoly R pb.gen).aroots F).prod`. -/
theorem PowerBasis.norm_gen_eq_prod_roots [Algebra R F] (pb : PowerBasis R S)
    (hf : (minpoly R pb.gen).Splits (algebraMap R F)) :
    algebraMap R F (norm R pb.gen) = ((minpoly R pb.gen).aroots F).prod := by
  haveI := Module.nontrivial R F
  have := minpoly.monic pb.isIntegral_gen
  rw [PowerBasis.norm_gen_eq_coeff_zero_minpoly, ← pb.natDegree_minpoly, RingHom.map_mul,
    ← coeff_map,
    prod_roots_eq_coeff_zero_of_monic_of_splits (this.map _) ((splits_id_iff_splits _).2 hf),
    this.natDegree_map, map_pow, ← mul_assoc, ← mul_pow]
  simp only [map_neg, map_one, neg_mul, neg_neg, one_pow, one_mul]

end EqProdRoots

section EqZeroIff

variable [Finite ι]

@[simp]
theorem norm_zero [Nontrivial S] [Module.Free R S] [Module.Finite R S] : norm R (0 : S) = 0 := by
  nontriviality
  rw [norm_apply, coe_lmul_eq_mul, map_zero, LinearMap.det_zero' (Module.Free.chooseBasis R S)]

@[simp]
theorem norm_eq_zero_iff [IsDomain R] [IsDomain S] [Module.Free R S] [Module.Finite R S] {x : S} :
    norm R x = 0 ↔ x = 0 := by
  constructor
  swap
  · rintro rfl; exact norm_zero
  · let b := Module.Free.chooseBasis R S
    let decEq := Classical.decEq (Module.Free.ChooseBasisIndex R S)
    rw [norm_eq_matrix_det b, ← Matrix.exists_mulVec_eq_zero_iff]
    rintro ⟨v, v_ne, hv⟩
    rw [← b.equivFun.apply_symm_apply v, b.equivFun_symm_apply, b.equivFun_apply,
      leftMulMatrix_mulVec_repr] at hv
    refine (mul_eq_zero.mp (b.ext_elem fun i => ?_)).resolve_right (show ∑ i, v i • b i ≠ 0 from ?_)
    · simpa only [LinearEquiv.map_zero, Pi.zero_apply] using congr_fun hv i
    · contrapose! v_ne with sum_eq
      apply b.equivFun.symm.injective
      rw [b.equivFun_symm_apply, sum_eq, LinearEquiv.map_zero]

theorem norm_ne_zero_iff [IsDomain R] [IsDomain S] [Module.Free R S] [Module.Finite R S] {x : S} :
    norm R x ≠ 0 ↔ x ≠ 0 := not_iff_not.mpr norm_eq_zero_iff

/-- This is `Algebra.norm_eq_zero_iff` composed with `Algebra.norm_apply`. -/
@[simp]
theorem norm_eq_zero_iff' [IsDomain R] [IsDomain S] [Module.Free R S] [Module.Finite R S] {x : S} :
    LinearMap.det (LinearMap.mul R S x) = 0 ↔ x = 0 := norm_eq_zero_iff

theorem norm_eq_zero_iff_of_basis [IsDomain R] [IsDomain S] (b : Basis ι R S) {x : S} :
    Algebra.norm R x = 0 ↔ x = 0 := by
  haveI : Module.Free R S := Module.Free.of_basis b
  haveI : Module.Finite R S := Module.Finite.of_basis b
  exact norm_eq_zero_iff

theorem norm_ne_zero_iff_of_basis [IsDomain R] [IsDomain S] (b : Basis ι R S) {x : S} :
    Algebra.norm R x ≠ 0 ↔ x ≠ 0 :=
  not_iff_not.mpr (norm_eq_zero_iff_of_basis b)

end EqZeroIff

open IntermediateField

variable (K) in
theorem norm_eq_norm_adjoin [FiniteDimensional K L] [Algebra.IsSeparable K L] (x : L) :
    norm K x = norm K (AdjoinSimple.gen K x) ^ finrank K⟮x⟯ L := by
  letI := Algebra.isSeparable_tower_top_of_isSeparable K K⟮x⟯ L
  let pbL := Field.powerBasisOfFiniteOfSeparable K⟮x⟯ L
  let pbx := IntermediateField.adjoin.powerBasis (Algebra.IsSeparable.isIntegral K x)
  rw [← AdjoinSimple.algebraMap_gen K x, norm_eq_matrix_det (pbx.basis.smulTower pbL.basis) _,
    smulTower_leftMulMatrix_algebraMap, det_blockDiagonal, AdjoinSimple.algebraMap_gen,
    norm_eq_matrix_det pbx.basis]
  simp only [Finset.card_fin, Finset.prod_const]
  congr
  rw [← PowerBasis.finrank]

section IntermediateField

theorem _root_.IntermediateField.AdjoinSimple.norm_gen_eq_one {x : L} (hx : ¬IsIntegral K x) :
    norm K (AdjoinSimple.gen K x) = 1 := by
  rw [norm_eq_one_of_not_exists_basis]
  contrapose! hx
  obtain ⟨s, ⟨b⟩⟩ := hx
  refine .of_mem_of_fg K⟮x⟯.toSubalgebra ?_ x ?_
  · exact (Submodule.fg_iff_finiteDimensional _).mpr (.of_fintype_basis b)
  · exact IntermediateField.subset_adjoin K _ (Set.mem_singleton x)

theorem _root_.IntermediateField.AdjoinSimple.norm_gen_eq_prod_roots (x : L)
    (hf : (minpoly K x).Splits (algebraMap K F)) :
    (algebraMap K F) (norm K (AdjoinSimple.gen K x)) =
      ((minpoly K x).aroots F).prod := by
  have injKxL := (algebraMap K⟮x⟯ L).injective
  by_cases hx : IsIntegral K x; swap
  · simp [minpoly.eq_zero hx, IntermediateField.AdjoinSimple.norm_gen_eq_one hx, aroots_def]
  rw [← adjoin.powerBasis_gen hx, PowerBasis.norm_gen_eq_prod_roots] <;>
    rw [adjoin.powerBasis_gen hx, ← minpoly.algebraMap_eq injKxL] <;>
    simp only [AdjoinSimple.algebraMap_gen _ _, hf]

end IntermediateField

section EqProdEmbeddings

open IntermediateField IntermediateField.AdjoinSimple Polynomial

variable (F) (E : Type*) [Field E] [Algebra K E]

theorem norm_eq_prod_embeddings_gen [Algebra R F] (pb : PowerBasis R S)
    (hE : (minpoly R pb.gen).Splits (algebraMap R F)) (hfx : IsSeparable R pb.gen) :
    algebraMap R F (norm R pb.gen) =
      (@Finset.univ _ (PowerBasis.AlgHom.fintype pb)).prod fun σ => σ pb.gen := by
  letI := Classical.decEq F
  rw [PowerBasis.norm_gen_eq_prod_roots pb hE]
  rw [@Fintype.prod_equiv (S →ₐ[R] F) _ _ (PowerBasis.AlgHom.fintype pb) _ _ pb.liftEquiv'
    (fun σ => σ pb.gen) (fun x => x) ?_]
  · rw [Finset.prod_mem_multiset, Finset.prod_eq_multiset_prod, Multiset.toFinset_val,
      Multiset.dedup_eq_self.mpr, Multiset.map_id]
    · exact nodup_roots (.map hfx)
    · intro x; rfl
  · intro σ; simp only [PowerBasis.liftEquiv'_apply_coe]

theorem norm_eq_prod_roots [Algebra.IsSeparable K L] [FiniteDimensional K L] {x : L}
    (hF : (minpoly K x).Splits (algebraMap K F)) :
    algebraMap K F (norm K x) =
      ((minpoly K x).aroots F).prod ^ finrank K⟮x⟯ L := by
  rw [norm_eq_norm_adjoin K x, map_pow, IntermediateField.AdjoinSimple.norm_gen_eq_prod_roots _ hF]

theorem prod_embeddings_eq_finrank_pow [Algebra L F] [IsScalarTower K L F] [IsAlgClosed E]
    [Algebra.IsSeparable K F] [FiniteDimensional K F] (pb : PowerBasis K L) :
    ∏ σ : F →ₐ[K] E, σ (algebraMap L F pb.gen) =
      ((@Finset.univ _ (PowerBasis.AlgHom.fintype pb)).prod
        fun σ : L →ₐ[K] E => σ pb.gen) ^ finrank L F := by
  haveI : FiniteDimensional L F := FiniteDimensional.right K L F
  haveI : Algebra.IsSeparable L F := Algebra.isSeparable_tower_top_of_isSeparable K L F
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

variable (K)

/-- For `L/K` a finite separable extension of fields and `E` an algebraically closed extension
of `K`, the norm (down to `K`) of an element `x` of `L` is equal to the product of the images
of `x` over all the `K`-embeddings `σ` of `L` into `E`. -/
theorem norm_eq_prod_embeddings [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsAlgClosed E]
    (x : L) : algebraMap K E (norm K x) = ∏ σ : L →ₐ[K] E, σ x := by
  have hx := Algebra.IsSeparable.isIntegral K x
  rw [norm_eq_norm_adjoin K x, RingHom.map_pow, ← adjoin.powerBasis_gen hx,
    norm_eq_prod_embeddings_gen E (adjoin.powerBasis hx) (IsAlgClosed.splits_codomain _)]
  · exact (prod_embeddings_eq_finrank_pow L (L := K⟮x⟯) E (adjoin.powerBasis hx)).symm
  · haveI := Algebra.isSeparable_tower_bot_of_isSeparable K K⟮x⟯ L
    exact Algebra.IsSeparable.isSeparable K _

theorem norm_eq_prod_automorphisms [FiniteDimensional K L] [IsGalois K L] (x : L) :
    algebraMap K L (norm K x) = ∏ σ : L ≃ₐ[K] L, σ x := by
  apply FaithfulSMul.algebraMap_injective L (AlgebraicClosure L)
  rw [map_prod (algebraMap L (AlgebraicClosure L))]
  rw [← Fintype.prod_equiv (Normal.algHomEquivAut K (AlgebraicClosure L) L)]
  · rw [← norm_eq_prod_embeddings _ _ x, ← IsScalarTower.algebraMap_apply]
  · intro σ
    simp only [Normal.algHomEquivAut, AlgHom.restrictNormal', Equiv.coe_fn_mk,
      AlgEquiv.coe_ofBijective, AlgHom.restrictNormal_commutes, algebraMap_self, RingHom.id_apply]

theorem isIntegral_norm [Algebra R L] [Algebra R K] [IsScalarTower R K L] [Algebra.IsSeparable K L]
    [FiniteDimensional K L] {x : L} (hx : IsIntegral R x) : IsIntegral R (norm K x) := by
  have hx' : IsIntegral K x := hx.tower_top
  rw [← isIntegral_algebraMap_iff (algebraMap K (AlgebraicClosure L)).injective, norm_eq_prod_roots]
  · refine (IsIntegral.multiset_prod fun y hy => ?_).pow _
    rw [mem_roots_map (minpoly.ne_zero hx')] at hy
    use minpoly R x, minpoly.monic hx
    rw [← aeval_def] at hy ⊢
    exact minpoly.aeval_of_isScalarTower R x y hy
  · apply IsAlgClosed.splits_codomain

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
  rw [norm_eq_one_of_not_exists_basis _ h, norm_eq_one_of_not_exists_basis, map_one]
  intro ⟨s, ⟨b⟩⟩
  exact h ⟨s, ⟨b.mapCoeffs e (by simp [Algebra.smul_def, ← he])⟩⟩

lemma norm_eq_of_equiv_equiv {A₁ B₁ A₂ B₂ : Type*} [CommRing A₁] [Ring B₁]
    [CommRing A₂] [Ring B₂] [Algebra A₁ B₁] [Algebra A₂ B₂] (e₁ : A₁ ≃+* A₂) (e₂ : B₁ ≃+* B₂)
    (he : RingHom.comp (algebraMap A₂ B₂) ↑e₁ = RingHom.comp ↑e₂ (algebraMap A₁ B₁)) (x) :
    Algebra.norm A₁ x = e₁.symm (Algebra.norm A₂ (e₂ x)) := by
  letI := (RingHom.comp (e₂ : B₁ →+* B₂) (algebraMap A₁ B₁)).toAlgebra' ?_
  · let e' : B₁ ≃ₐ[A₁] B₂ := { e₂ with commutes' := fun _ ↦ rfl }
    rw [← Algebra.norm_eq_of_ringEquiv e₁ he, ← Algebra.norm_eq_of_algEquiv e']
    simp [e']
  intro c x
  apply e₂.symm.injective
  simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, map_mul,
    RingEquiv.symm_apply_apply, commutes]

end EqProdEmbeddings

end Algebra
