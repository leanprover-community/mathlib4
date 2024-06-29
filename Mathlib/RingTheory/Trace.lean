/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Trace
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.Galois
import Mathlib.RingTheory.PowerBasis
import Mathlib.FieldTheory.Minpoly.MinpolyDiv

#align_import ring_theory.trace from "leanprover-community/mathlib"@"3e068ece210655b7b9a9477c3aff38a492400aa1"

/-!
# Trace for (finite) ring extensions.

Suppose we have an `R`-algebra `S` with a finite basis. For each `s : S`,
the trace of the linear map given by multiplying by `s` gives information about
the roots of the minimal polynomial of `s` over `R`.

## Main definitions

 * `Algebra.trace R S x`: the trace of an element `s` of an `R`-algebra `S`
 * `Algebra.traceForm R S`: bilinear form sending `x`, `y` to the trace of `x * y`
 * `Algebra.traceMatrix R b`: the matrix whose `(i j)`-th element is the trace of `b i * b j`.
 * `Algebra.embeddingsMatrix A C b : Matrix κ (B →ₐ[A] C) C` is the matrix whose
   `(i, σ)` coefficient is `σ (b i)`.
 * `Algebra.embeddingsMatrixReindex A C b e : Matrix κ κ C` is the matrix whose `(i, j)`
   coefficient is `σⱼ (b i)`, where `σⱼ : B →ₐ[A] C` is the embedding corresponding to `j : κ`
   given by a bijection `e : κ ≃ (B →ₐ[A] C)`.

## Main results

 * `trace_algebraMap_of_basis`, `trace_algebraMap`: if `x : K`, then `Tr_{L/K} x = [L : K] x`
 * `trace_trace_of_basis`, `trace_trace`: `Tr_{L/K} (Tr_{F/L} x) = Tr_{F/K} x`
 * `trace_eq_sum_roots`: the trace of `x : K(x)` is the sum of all conjugate roots of `x`
 * `trace_eq_sum_embeddings`: the trace of `x : K(x)` is the sum of all embeddings of `x` into an
   algebraically closed field
 * `traceForm_nondegenerate`: the trace form over a separable extension is a nondegenerate
   bilinear form
* `traceForm_dualBasis_powerBasis_eq`: The dual basis of a powerbasis `{1, x, x²...}` under the
   trace form is `aᵢ / f'(x)`, with `f` being the minpoly of `x` and `f / (X - x) = ∑ aᵢxⁱ`.

## Implementation notes

Typically, the trace is defined specifically for finite field extensions.
The definition is as general as possible and the assumption that we have
fields or that the extension is finite is added to the lemmas as needed.

We only define the trace for left multiplication (`Algebra.leftMulMatrix`,
i.e. `LinearMap.mulLeft`).
For now, the definitions assume `S` is commutative, so the choice doesn't matter anyway.

## References

 * https://en.wikipedia.org/wiki/Field_trace

-/


universe u v w z

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T]
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable {ι κ : Type w} [Fintype ι]

open FiniteDimensional

open LinearMap (BilinForm)
open LinearMap

open Matrix

open scoped Matrix

namespace Algebra

variable (b : Basis ι R S)
variable (R S)

/-- The trace of an element `s` of an `R`-algebra is the trace of `(s * ·)`,
as an `R`-linear map. -/
noncomputable def trace : S →ₗ[R] R :=
  (LinearMap.trace R S).comp (lmul R S).toLinearMap
#align algebra.trace Algebra.trace

variable {S}

-- Not a `simp` lemma since there are more interesting ways to rewrite `trace R S x`,
-- for example `trace_trace`
theorem trace_apply (x) : trace R S x = LinearMap.trace R S (lmul R S x) :=
  rfl
#align algebra.trace_apply Algebra.trace_apply

theorem trace_eq_zero_of_not_exists_basis (h : ¬∃ s : Finset S, Nonempty (Basis s R S)) :
    trace R S = 0 := by ext s; simp [trace_apply, LinearMap.trace, h]
#align algebra.trace_eq_zero_of_not_exists_basis Algebra.trace_eq_zero_of_not_exists_basis

variable {R}

-- Can't be a `simp` lemma because it depends on a choice of basis
theorem trace_eq_matrix_trace [DecidableEq ι] (b : Basis ι R S) (s : S) :
    trace R S s = Matrix.trace (Algebra.leftMulMatrix b s) := by
  rw [trace_apply, LinearMap.trace_eq_matrix_trace _ b, ← toMatrix_lmul_eq]; rfl
#align algebra.trace_eq_matrix_trace Algebra.trace_eq_matrix_trace

/-- If `x` is in the base field `K`, then the trace is `[L : K] * x`. -/
theorem trace_algebraMap_of_basis (x : R) : trace R S (algebraMap R S x) = Fintype.card ι • x := by
  haveI := Classical.decEq ι
  rw [trace_apply, LinearMap.trace_eq_matrix_trace R b, Matrix.trace]
  convert Finset.sum_const x
  simp [-coe_lmul_eq_mul]

#align algebra.trace_algebra_map_of_basis Algebra.trace_algebraMap_of_basis

/-- If `x` is in the base field `K`, then the trace is `[L : K] * x`.

(If `L` is not finite-dimensional over `K`, then `trace` and `finrank` return `0`.)
-/
@[simp]
theorem trace_algebraMap (x : K) : trace K L (algebraMap K L x) = finrank K L • x := by
  by_cases H : ∃ s : Finset L, Nonempty (Basis s K L)
  · rw [trace_algebraMap_of_basis H.choose_spec.some, finrank_eq_card_basis H.choose_spec.some]
  · simp [trace_eq_zero_of_not_exists_basis K H, finrank_eq_zero_of_not_exists_basis_finset H]
#align algebra.trace_algebra_map Algebra.trace_algebraMap

theorem trace_trace_of_basis [Algebra S T] [IsScalarTower R S T] {ι κ : Type*} [Finite ι]
    [Finite κ] (b : Basis ι R S) (c : Basis κ S T) (x : T) :
    trace R S (trace S T x) = trace R T x := by
  haveI := Classical.decEq ι
  haveI := Classical.decEq κ
  cases nonempty_fintype ι
  cases nonempty_fintype κ
  rw [trace_eq_matrix_trace (b.smul c), trace_eq_matrix_trace b, trace_eq_matrix_trace c,
    Matrix.trace, Matrix.trace, Matrix.trace, ← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [AlgHom.map_sum, smul_leftMulMatrix, Finset.sum_apply,
    Matrix.diag, Finset.sum_apply
      i (Finset.univ : Finset κ) fun y => leftMulMatrix b (leftMulMatrix c x y y)]
#align algebra.trace_trace_of_basis Algebra.trace_trace_of_basis

theorem trace_comp_trace_of_basis [Algebra S T] [IsScalarTower R S T] {ι κ : Type*} [Finite ι]
    [Finite κ] (b : Basis ι R S) (c : Basis κ S T) :
    (trace R S).comp ((trace S T).restrictScalars R) = trace R T := by
  ext
  rw [LinearMap.comp_apply, LinearMap.restrictScalars_apply, trace_trace_of_basis b c]
#align algebra.trace_comp_trace_of_basis Algebra.trace_comp_trace_of_basis

@[simp]
theorem trace_trace [Algebra K T] [Algebra L T] [IsScalarTower K L T] [FiniteDimensional K L]
    [FiniteDimensional L T] (x : T) : trace K L (trace L T x) = trace K T x :=
  trace_trace_of_basis (Basis.ofVectorSpace K L) (Basis.ofVectorSpace L T) x
#align algebra.trace_trace Algebra.trace_trace

@[simp]
theorem trace_comp_trace [Algebra K T] [Algebra L T] [IsScalarTower K L T] [FiniteDimensional K L]
    [FiniteDimensional L T] : (trace K L).comp ((trace L T).restrictScalars K) = trace K T := by
  ext; rw [LinearMap.comp_apply, LinearMap.restrictScalars_apply, trace_trace]
#align algebra.trace_comp_trace Algebra.trace_comp_trace

@[simp]
theorem trace_prod_apply [Module.Free R S] [Module.Free R T] [Module.Finite R S] [Module.Finite R T]
    (x : S × T) : trace R (S × T) x = trace R S x.fst + trace R T x.snd := by
  nontriviality R
  let f := (lmul R S).toLinearMap.prodMap (lmul R T).toLinearMap
  have : (lmul R (S × T)).toLinearMap = (prodMapLinear R S T S T R).comp f :=
    LinearMap.ext₂ Prod.mul_def
  simp_rw [trace, this]
  exact trace_prodMap' _ _
#align algebra.trace_prod_apply Algebra.trace_prod_apply

theorem trace_prod [Module.Free R S] [Module.Free R T] [Module.Finite R S] [Module.Finite R T] :
    trace R (S × T) = (trace R S).coprod (trace R T) :=
  LinearMap.ext fun p => by rw [coprod_apply, trace_prod_apply]
#align algebra.trace_prod Algebra.trace_prod

section TraceForm

variable (R S)

/-- The `traceForm` maps `x y : S` to the trace of `x * y`.
It is a symmetric bilinear form and is nondegenerate if the extension is separable. -/
noncomputable def traceForm : BilinForm R S :=
  LinearMap.compr₂ (lmul R S).toLinearMap (trace R S)
#align algebra.trace_form Algebra.traceForm

variable {S}

-- This is a nicer lemma than the one produced by `@[simps] def traceForm`.
@[simp]
theorem traceForm_apply (x y : S) : traceForm R S x y = trace R S (x * y) :=
  rfl
#align algebra.trace_form_apply Algebra.traceForm_apply

theorem traceForm_isSymm : (traceForm R S).IsSymm := fun _ _ => congr_arg (trace R S) (mul_comm _ _)
#align algebra.trace_form_is_symm Algebra.traceForm_isSymm

theorem traceForm_toMatrix [DecidableEq ι] (i j) :
    BilinForm.toMatrix b (traceForm R S) i j = trace R S (b i * b j) := by
  rw [BilinForm.toMatrix_apply, traceForm_apply]
#align algebra.trace_form_to_matrix Algebra.traceForm_toMatrix

theorem traceForm_toMatrix_powerBasis (h : PowerBasis R S) :
    BilinForm.toMatrix h.basis (traceForm R S) = of fun i j => trace R S (h.gen ^ (i.1 + j.1)) := by
  ext; rw [traceForm_toMatrix, of_apply, pow_add, h.basis_eq_pow, h.basis_eq_pow]
#align algebra.trace_form_to_matrix_power_basis Algebra.traceForm_toMatrix_powerBasis

end TraceForm

end Algebra

section EqSumRoots

open Algebra Polynomial

variable {F : Type*} [Field F]
variable [Algebra K S] [Algebra K F]

/-- Given `pb : PowerBasis K S`, the trace of `pb.gen` is `-(minpoly K pb.gen).nextCoeff`. -/
theorem PowerBasis.trace_gen_eq_nextCoeff_minpoly [Nontrivial S] (pb : PowerBasis K S) :
    Algebra.trace K S pb.gen = -(minpoly K pb.gen).nextCoeff := by
  have d_pos : 0 < pb.dim := PowerBasis.dim_pos pb
  have d_pos' : 0 < (minpoly K pb.gen).natDegree := by simpa
  haveI : Nonempty (Fin pb.dim) := ⟨⟨0, d_pos⟩⟩
  rw [trace_eq_matrix_trace pb.basis, trace_eq_neg_charpoly_coeff, charpoly_leftMulMatrix, ←
    pb.natDegree_minpoly, Fintype.card_fin, ← nextCoeff_of_natDegree_pos d_pos']
#align power_basis.trace_gen_eq_next_coeff_minpoly PowerBasis.trace_gen_eq_nextCoeff_minpoly

/-- Given `pb : PowerBasis K S`, then the trace of `pb.gen` is
`((minpoly K pb.gen).aroots F).sum`. -/
theorem PowerBasis.trace_gen_eq_sum_roots [Nontrivial S] (pb : PowerBasis K S)
    (hf : (minpoly K pb.gen).Splits (algebraMap K F)) :
    algebraMap K F (trace K S pb.gen) = ((minpoly K pb.gen).aroots F).sum := by
  rw [PowerBasis.trace_gen_eq_nextCoeff_minpoly, RingHom.map_neg, ←
    nextCoeff_map (algebraMap K F).injective,
    sum_roots_eq_nextCoeff_of_monic_of_split ((minpoly.monic (PowerBasis.isIntegral_gen _)).map _)
      ((splits_id_iff_splits _).2 hf),
    neg_neg]
#align power_basis.trace_gen_eq_sum_roots PowerBasis.trace_gen_eq_sum_roots

namespace IntermediateField.AdjoinSimple

open IntermediateField

theorem trace_gen_eq_zero {x : L} (hx : ¬IsIntegral K x) :
    Algebra.trace K K⟮x⟯ (AdjoinSimple.gen K x) = 0 := by
  rw [trace_eq_zero_of_not_exists_basis, LinearMap.zero_apply]
  contrapose! hx
  obtain ⟨s, ⟨b⟩⟩ := hx
  refine .of_mem_of_fg K⟮x⟯.toSubalgebra ?_ x ?_
  · exact (Submodule.fg_iff_finiteDimensional _).mpr (FiniteDimensional.of_fintype_basis b)
  · exact subset_adjoin K _ (Set.mem_singleton x)
#align intermediate_field.adjoin_simple.trace_gen_eq_zero IntermediateField.AdjoinSimple.trace_gen_eq_zero

theorem trace_gen_eq_sum_roots (x : L) (hf : (minpoly K x).Splits (algebraMap K F)) :
    algebraMap K F (trace K K⟮x⟯ (AdjoinSimple.gen K x)) =
      ((minpoly K x).aroots F).sum := by
  have injKxL := (algebraMap K⟮x⟯ L).injective
  by_cases hx : IsIntegral K x; swap
  · simp [minpoly.eq_zero hx, trace_gen_eq_zero hx, aroots_def]
  rw [← adjoin.powerBasis_gen hx, (adjoin.powerBasis hx).trace_gen_eq_sum_roots] <;>
    rw [adjoin.powerBasis_gen hx, ← minpoly.algebraMap_eq injKxL] <;>
    try simp only [AdjoinSimple.algebraMap_gen _ _]
  exact hf
#align intermediate_field.adjoin_simple.trace_gen_eq_sum_roots IntermediateField.AdjoinSimple.trace_gen_eq_sum_roots

end IntermediateField.AdjoinSimple

open IntermediateField

variable (K)

theorem trace_eq_trace_adjoin [FiniteDimensional K L] (x : L) :
    Algebra.trace K L x = finrank K⟮x⟯ L • trace K K⟮x⟯ (AdjoinSimple.gen K x) := by
  -- Porting note: `conv` was
  -- `conv in x => rw [← IntermediateField.AdjoinSimple.algebraMap_gen K x]`
  -- and it was after the first `rw`.
  conv =>
    lhs
    rw [← IntermediateField.AdjoinSimple.algebraMap_gen K x]
  rw [← trace_trace (L := K⟮x⟯), trace_algebraMap, LinearMap.map_smul_of_tower]
#align trace_eq_trace_adjoin trace_eq_trace_adjoin

variable {K}

theorem trace_eq_sum_roots [FiniteDimensional K L] {x : L}
    (hF : (minpoly K x).Splits (algebraMap K F)) :
    algebraMap K F (Algebra.trace K L x) =
      finrank K⟮x⟯ L • ((minpoly K x).aroots F).sum := by
  rw [trace_eq_trace_adjoin K x, Algebra.smul_def, RingHom.map_mul, ← Algebra.smul_def,
    IntermediateField.AdjoinSimple.trace_gen_eq_sum_roots _ hF, IsScalarTower.algebraMap_smul]
#align trace_eq_sum_roots trace_eq_sum_roots

end EqSumRoots

variable {F : Type*} [Field F]
variable [Algebra R L] [Algebra L F] [Algebra R F] [IsScalarTower R L F]

open Polynomial

attribute [-instance] Field.toEuclideanDomain

theorem Algebra.isIntegral_trace [FiniteDimensional L F] {x : F} (hx : IsIntegral R x) :
    IsIntegral R (Algebra.trace L F x) := by
  have hx' : IsIntegral L x := hx.tower_top
  rw [← isIntegral_algebraMap_iff (algebraMap L (AlgebraicClosure F)).injective, trace_eq_sum_roots]
  · refine (IsIntegral.multiset_sum ?_).nsmul _
    intro y hy
    rw [mem_roots_map (minpoly.ne_zero hx')] at hy
    use minpoly R x, minpoly.monic hx
    rw [← aeval_def] at hy ⊢
    exact minpoly.aeval_of_isScalarTower R x y hy
  · apply IsAlgClosed.splits_codomain
#align algebra.is_integral_trace Algebra.isIntegral_trace

lemma Algebra.trace_eq_of_algEquiv {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] (e : B ≃ₐ[A] C) (x) :
    Algebra.trace A C (e x) = Algebra.trace A B x := by
  simp_rw [Algebra.trace_apply, ← LinearMap.trace_conj' _ e.toLinearEquiv]
  congr; ext; simp [LinearEquiv.conj_apply]

lemma Algebra.trace_eq_of_ringEquiv {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A C] [Algebra B C] (e : A ≃+* B) (he : (algebraMap B C).comp e = algebraMap A C) (x) :
    e (Algebra.trace A C x) = Algebra.trace B C x := by
  classical
  by_cases h : ∃ s : Finset C, Nonempty (Basis s B C)
  · obtain ⟨s, ⟨b⟩⟩ := h
    letI : Algebra A B := RingHom.toAlgebra e
    letI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' he.symm
    rw [Algebra.trace_eq_matrix_trace b,
      Algebra.trace_eq_matrix_trace (b.mapCoeffs e.symm (by simp [Algebra.smul_def, ← he]))]
    show e.toAddMonoidHom _ = _
    rw [AddMonoidHom.map_trace]
    congr
    ext i j
    simp [leftMulMatrix_apply, LinearMap.toMatrix_apply]
  rw [trace_eq_zero_of_not_exists_basis _ h, trace_eq_zero_of_not_exists_basis,
    LinearMap.zero_apply, LinearMap.zero_apply, map_zero]
  intro ⟨s, ⟨b⟩⟩
  exact h ⟨s, ⟨b.mapCoeffs e (by simp [Algebra.smul_def, ← he])⟩⟩

lemma Algebra.trace_eq_of_equiv_equiv {A₁ B₁ A₂ B₂ : Type*} [CommRing A₁] [CommRing B₁]
    [CommRing A₂] [CommRing B₂] [Algebra A₁ B₁] [Algebra A₂ B₂] (e₁ : A₁ ≃+* A₂) (e₂ : B₁ ≃+* B₂)
    (he : RingHom.comp (algebraMap A₂ B₂) ↑e₁ = RingHom.comp ↑e₂ (algebraMap A₁ B₁)) (x) :
    Algebra.trace A₁ B₁ x = e₁.symm (Algebra.trace A₂ B₂ (e₂ x)) := by
  letI := (RingHom.comp (e₂ : B₁ →+* B₂) (algebraMap A₁ B₁)).toAlgebra
  let e' : B₁ ≃ₐ[A₁] B₂ := { e₂ with commutes' := fun _ ↦ rfl }
  rw [← Algebra.trace_eq_of_ringEquiv e₁ he, ← Algebra.trace_eq_of_algEquiv e',
    RingEquiv.symm_apply_apply]
  rfl

section EqSumEmbeddings

variable [Algebra K F] [IsScalarTower K L F]

open Algebra IntermediateField

variable (F) (E : Type*) [Field E] [Algebra K E]

theorem trace_eq_sum_embeddings_gen (pb : PowerBasis K L)
    (hE : (minpoly K pb.gen).Splits (algebraMap K E)) (hfx : (minpoly K pb.gen).Separable) :
    algebraMap K E (Algebra.trace K L pb.gen) =
      (@Finset.univ _ (PowerBasis.AlgHom.fintype pb)).sum fun σ => σ pb.gen := by
  letI := Classical.decEq E
  -- Porting note: the following `letI` was not needed.
  letI : Fintype (L →ₐ[K] E) := PowerBasis.AlgHom.fintype pb
  rw [pb.trace_gen_eq_sum_roots hE, Fintype.sum_equiv pb.liftEquiv', Finset.sum_mem_multiset,
    Finset.sum_eq_multiset_sum, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr _,
    Multiset.map_id]
  · exact nodup_roots ((separable_map _).mpr hfx)
  -- Porting note: the following goal does not exist in mathlib3.
  · exact (fun x => x.1)
  · intro x; rfl
  · intro σ
    rw [PowerBasis.liftEquiv'_apply_coe]
#align trace_eq_sum_embeddings_gen trace_eq_sum_embeddings_gen

variable [IsAlgClosed E]

theorem sum_embeddings_eq_finrank_mul [FiniteDimensional K F] [IsSeparable K F]
    (pb : PowerBasis K L) :
    ∑ σ : F →ₐ[K] E, σ (algebraMap L F pb.gen) =
      finrank L F •
        (@Finset.univ _ (PowerBasis.AlgHom.fintype pb)).sum fun σ : L →ₐ[K] E => σ pb.gen := by
  haveI : FiniteDimensional L F := FiniteDimensional.right K L F
  haveI : IsSeparable L F := isSeparable_tower_top_of_isSeparable K L F
  letI : Fintype (L →ₐ[K] E) := PowerBasis.AlgHom.fintype pb
  letI : ∀ f : L →ₐ[K] E, Fintype (haveI := f.toRingHom.toAlgebra; AlgHom L F E) := ?_
  · rw [Fintype.sum_equiv algHomEquivSigma (fun σ : F →ₐ[K] E => _) fun σ => σ.1 pb.gen, ←
      Finset.univ_sigma_univ, Finset.sum_sigma, ← Finset.sum_nsmul]
    · refine Finset.sum_congr rfl fun σ _ => ?_
      letI : Algebra L E := σ.toRingHom.toAlgebra
      -- Porting note: `Finset.card_univ` was inside `simp only`.
      simp only [Finset.sum_const]
      congr
      rw [← AlgHom.card L F E]
      exact Finset.card_univ (α := F →ₐ[L] E)
    · intro σ
      simp only [algHomEquivSigma, Equiv.coe_fn_mk, AlgHom.restrictDomain, AlgHom.comp_apply,
        IsScalarTower.coe_toAlgHom']
#align sum_embeddings_eq_finrank_mul sum_embeddings_eq_finrank_mul

theorem trace_eq_sum_embeddings [FiniteDimensional K L] [IsSeparable K L] {x : L} :
    algebraMap K E (Algebra.trace K L x) = ∑ σ : L →ₐ[K] E, σ x := by
  have hx := IsSeparable.isIntegral K x
  let pb := adjoin.powerBasis hx
  rw [trace_eq_trace_adjoin K x, Algebra.smul_def, RingHom.map_mul, ← adjoin.powerBasis_gen hx,
    trace_eq_sum_embeddings_gen E pb (IsAlgClosed.splits_codomain _)]
  -- Porting note: the following `convert` was `exact`, with `← algebra.smul_def, algebra_map_smul`
  -- in the previous `rw`.
  · convert (sum_embeddings_eq_finrank_mul L E pb).symm
    ext
    simp
  · haveI := isSeparable_tower_bot_of_isSeparable K K⟮x⟯ L
    exact IsSeparable.separable K _
#align trace_eq_sum_embeddings trace_eq_sum_embeddings

theorem trace_eq_sum_automorphisms (x : L) [FiniteDimensional K L] [IsGalois K L] :
    algebraMap K L (Algebra.trace K L x) = ∑ σ : L ≃ₐ[K] L, σ x := by
  apply NoZeroSMulDivisors.algebraMap_injective L (AlgebraicClosure L)
  rw [_root_.map_sum (algebraMap L (AlgebraicClosure L))]
  rw [← Fintype.sum_equiv (Normal.algHomEquivAut K (AlgebraicClosure L) L)]
  · rw [← trace_eq_sum_embeddings (AlgebraicClosure L)]
    · simp only [algebraMap_eq_smul_one]
      -- Porting note: `smul_one_smul` was in the `simp only`.
      apply smul_one_smul
  · intro σ
    simp only [Normal.algHomEquivAut, AlgHom.restrictNormal', Equiv.coe_fn_mk,
      AlgEquiv.coe_ofBijective, AlgHom.restrictNormal_commutes, id.map_eq_id, RingHom.id_apply]
#align trace_eq_sum_automorphisms trace_eq_sum_automorphisms

end EqSumEmbeddings

section DetNeZero

namespace Algebra

variable (A : Type u) {B : Type v} (C : Type z)
variable [CommRing A] [CommRing B] [Algebra A B] [CommRing C] [Algebra A C]

open Finset

/-- Given an `A`-algebra `B` and `b`, a `κ`-indexed family of elements of `B`, we define
`traceMatrix A b` as the matrix whose `(i j)`-th element is the trace of `b i * b j`. -/
noncomputable def traceMatrix (b : κ → B) : Matrix κ κ A :=
  of fun i j => traceForm A B (b i) (b j)
#align algebra.trace_matrix Algebra.traceMatrix

-- TODO: set as an equation lemma for `traceMatrix`, see mathlib4#3024
@[simp]
theorem traceMatrix_apply (b : κ → B) (i j) : traceMatrix A b i j = traceForm A B (b i) (b j) :=
  rfl
#align algebra.trace_matrix_apply Algebra.traceMatrix_apply

theorem traceMatrix_reindex {κ' : Type*} (b : Basis κ A B) (f : κ ≃ κ') :
    traceMatrix A (b.reindex f) = reindex f f (traceMatrix A b) := by ext (x y); simp
#align algebra.trace_matrix_reindex Algebra.traceMatrix_reindex

variable {A}

theorem traceMatrix_of_matrix_vecMul [Fintype κ] (b : κ → B) (P : Matrix κ κ A) :
    traceMatrix A (b ᵥ* P.map (algebraMap A B)) = Pᵀ * traceMatrix A b * P := by
  ext (α β)
  rw [traceMatrix_apply, vecMul, dotProduct, vecMul, dotProduct, Matrix.mul_apply,
    BilinForm.sum_left,
    Fintype.sum_congr _ _ fun i : κ =>
      BilinForm.sum_right _ _ (b i * P.map (algebraMap A B) i α) fun y : κ =>
        b y * P.map (algebraMap A B) y β,
    sum_comm]
  congr; ext x
  rw [Matrix.mul_apply, sum_mul]
  congr; ext y
  rw [map_apply, traceForm_apply, mul_comm (b y), ← smul_def]
  simp only [id.smul_eq_mul, RingHom.id_apply, map_apply, transpose_apply, LinearMap.map_smulₛₗ,
    traceForm_apply, Algebra.smul_mul_assoc]
  rw [mul_comm (b x), ← smul_def]
  ring_nf
  rw [mul_assoc]
  simp [mul_comm]
#align algebra.trace_matrix_of_matrix_vec_mul Algebra.traceMatrix_of_matrix_vecMul

theorem traceMatrix_of_matrix_mulVec [Fintype κ] (b : κ → B) (P : Matrix κ κ A) :
    traceMatrix A (P.map (algebraMap A B) *ᵥ b) = P * traceMatrix A b * Pᵀ := by
  refine AddEquiv.injective (transposeAddEquiv κ κ A) ?_
  rw [transposeAddEquiv_apply, transposeAddEquiv_apply, ← vecMul_transpose, ← transpose_map,
    traceMatrix_of_matrix_vecMul, transpose_transpose]
#align algebra.trace_matrix_of_matrix_mul_vec Algebra.traceMatrix_of_matrix_mulVec

theorem traceMatrix_of_basis [Fintype κ] [DecidableEq κ] (b : Basis κ A B) :
    traceMatrix A b = BilinForm.toMatrix b (traceForm A B) := by
  ext (i j)
  rw [traceMatrix_apply, traceForm_apply, traceForm_toMatrix]
#align algebra.trace_matrix_of_basis Algebra.traceMatrix_of_basis

theorem traceMatrix_of_basis_mulVec (b : Basis ι A B) (z : B) :
    traceMatrix A b *ᵥ b.equivFun z = fun i => trace A B (z * b i) := by
  ext i
  rw [← col_apply (ι := Fin 1) (traceMatrix A b *ᵥ b.equivFun z) i 0, col_mulVec,
    Matrix.mul_apply, traceMatrix]
  simp only [col_apply, traceForm_apply]
  conv_lhs =>
    congr
    rfl
    ext
    rw [mul_comm _ (b.equivFun z _), ← smul_eq_mul, of_apply, ← LinearMap.map_smul]
  rw [← _root_.map_sum]
  congr
  conv_lhs =>
    congr
    rfl
    ext
    rw [← mul_smul_comm]
  rw [← Finset.mul_sum, mul_comm z]
  congr
  rw [b.sum_equivFun]
#align algebra.trace_matrix_of_basis_mul_vec Algebra.traceMatrix_of_basis_mulVec

variable (A)

/-- `embeddingsMatrix A C b : Matrix κ (B →ₐ[A] C) C` is the matrix whose `(i, σ)` coefficient is
  `σ (b i)`. It is mostly useful for fields when `Fintype.card κ = finrank A B` and `C` is
  algebraically closed. -/
def embeddingsMatrix (b : κ → B) : Matrix κ (B →ₐ[A] C) C :=
  of fun i (σ : B →ₐ[A] C) => σ (b i)
#align algebra.embeddings_matrix Algebra.embeddingsMatrix

-- TODO: set as an equation lemma for `embeddingsMatrix`, see mathlib4#3024
@[simp]
theorem embeddingsMatrix_apply (b : κ → B) (i) (σ : B →ₐ[A] C) :
    embeddingsMatrix A C b i σ = σ (b i) :=
  rfl
#align algebra.embeddings_matrix_apply Algebra.embeddingsMatrix_apply

/-- `embeddingsMatrixReindex A C b e : Matrix κ κ C` is the matrix whose `(i, j)` coefficient
  is `σⱼ (b i)`, where `σⱼ : B →ₐ[A] C` is the embedding corresponding to `j : κ` given by a
  bijection `e : κ ≃ (B →ₐ[A] C)`. It is mostly useful for fields and `C` is algebraically closed.
  In this case, in presence of `h : Fintype.card κ = finrank A B`, one can take
  `e := equivOfCardEq ((AlgHom.card A B C).trans h.symm)`. -/
def embeddingsMatrixReindex (b : κ → B) (e : κ ≃ (B →ₐ[A] C)) :=
  reindex (Equiv.refl κ) e.symm (embeddingsMatrix A C b)
#align algebra.embeddings_matrix_reindex Algebra.embeddingsMatrixReindex

variable {A}

theorem embeddingsMatrixReindex_eq_vandermonde (pb : PowerBasis A B)
    (e : Fin pb.dim ≃ (B →ₐ[A] C)) :
    embeddingsMatrixReindex A C pb.basis e = (vandermonde fun i => e i pb.gen)ᵀ := by
  ext i j
  simp [embeddingsMatrixReindex, embeddingsMatrix]
#align algebra.embeddings_matrix_reindex_eq_vandermonde Algebra.embeddingsMatrixReindex_eq_vandermonde

section Field

variable (K) (E : Type z) [Field E]
variable [Algebra K E]
variable [Module.Finite K L] [IsSeparable K L] [IsAlgClosed E]
variable (b : κ → L) (pb : PowerBasis K L)

theorem traceMatrix_eq_embeddingsMatrix_mul_trans : (traceMatrix K b).map (algebraMap K E) =
    embeddingsMatrix K E b * (embeddingsMatrix K E b)ᵀ := by
  ext (i j); simp [trace_eq_sum_embeddings, embeddingsMatrix, Matrix.mul_apply]
#align algebra.trace_matrix_eq_embeddings_matrix_mul_trans Algebra.traceMatrix_eq_embeddingsMatrix_mul_trans

theorem traceMatrix_eq_embeddingsMatrixReindex_mul_trans [Fintype κ] (e : κ ≃ (L →ₐ[K] E)) :
    (traceMatrix K b).map (algebraMap K E) =
      embeddingsMatrixReindex K E b e * (embeddingsMatrixReindex K E b e)ᵀ := by
  rw [traceMatrix_eq_embeddingsMatrix_mul_trans, embeddingsMatrixReindex, reindex_apply,
    transpose_submatrix, ← submatrix_mul_transpose_submatrix, ← Equiv.coe_refl, Equiv.refl_symm]
#align algebra.trace_matrix_eq_embeddings_matrix_reindex_mul_trans Algebra.traceMatrix_eq_embeddingsMatrixReindex_mul_trans

end Field

end Algebra

open Algebra

variable (pb : PowerBasis K L)

theorem det_traceMatrix_ne_zero' [IsSeparable K L] : det (traceMatrix K pb.basis) ≠ 0 := by
  suffices algebraMap K (AlgebraicClosure L) (det (traceMatrix K pb.basis)) ≠ 0 by
    refine mt (fun ht => ?_) this
    rw [ht, RingHom.map_zero]
  haveI : FiniteDimensional K L := pb.finite
  let e : Fin pb.dim ≃ (L →ₐ[K] AlgebraicClosure L) := (Fintype.equivFinOfCardEq ?_).symm
  · rw [RingHom.map_det, RingHom.mapMatrix_apply,
      traceMatrix_eq_embeddingsMatrixReindex_mul_trans K _ _ e,
      embeddingsMatrixReindex_eq_vandermonde, det_mul, det_transpose]
    refine mt mul_self_eq_zero.mp ?_
    simp only [det_vandermonde, Finset.prod_eq_zero_iff, not_exists, sub_eq_zero]
    rintro i ⟨_, j, hij, h⟩
    exact (Finset.mem_Ioi.mp hij).ne' (e.injective <| pb.algHom_ext h)
  · rw [AlgHom.card, pb.finrank]
#align det_trace_matrix_ne_zero' det_traceMatrix_ne_zero'

theorem det_traceForm_ne_zero [IsSeparable K L] [DecidableEq ι] (b : Basis ι K L) :
    det (BilinForm.toMatrix b (traceForm K L)) ≠ 0 := by
  haveI : FiniteDimensional K L := FiniteDimensional.of_fintype_basis b
  let pb : PowerBasis K L := Field.powerBasisOfFiniteOfSeparable _ _
  rw [← BilinForm.toMatrix_mul_basis_toMatrix pb.basis b, ←
    det_comm' (pb.basis.toMatrix_mul_toMatrix_flip b) _, ← Matrix.mul_assoc, det_mul]
  swap; · apply Basis.toMatrix_mul_toMatrix_flip
  refine
    mul_ne_zero
      (isUnit_of_mul_eq_one _ ((b.toMatrix pb.basis)ᵀ * b.toMatrix pb.basis).det ?_).ne_zero ?_
  · calc
      (pb.basis.toMatrix b * (pb.basis.toMatrix b)ᵀ).det *
            ((b.toMatrix pb.basis)ᵀ * b.toMatrix pb.basis).det =
          (pb.basis.toMatrix b * (b.toMatrix pb.basis * pb.basis.toMatrix b)ᵀ *
              b.toMatrix pb.basis).det := by
        simp only [← det_mul, Matrix.mul_assoc, Matrix.transpose_mul]
      _ = 1 := by
        simp only [Basis.toMatrix_mul_toMatrix_flip, Matrix.transpose_one, Matrix.mul_one,
          Matrix.det_one]
  simpa only [traceMatrix_of_basis] using det_traceMatrix_ne_zero' pb
#align det_trace_form_ne_zero det_traceForm_ne_zero

variable (K L)

theorem traceForm_nondegenerate [FiniteDimensional K L] [IsSeparable K L] :
    (traceForm K L).Nondegenerate :=
  BilinForm.nondegenerate_of_det_ne_zero (traceForm K L) _
    (det_traceForm_ne_zero (FiniteDimensional.finBasis K L))
#align trace_form_nondegenerate traceForm_nondegenerate

theorem Algebra.trace_ne_zero [FiniteDimensional K L] [IsSeparable K L] :
    Algebra.trace K L ≠ 0 := by
  intro e
  let pb : PowerBasis K L := Field.powerBasisOfFiniteOfSeparable _ _
  apply det_traceMatrix_ne_zero' pb
  rw [show traceMatrix K pb.basis = 0 by ext; simp [e], Matrix.det_zero]
  rw [← pb.finrank, ← Fin.pos_iff_nonempty]
  exact finrank_pos

theorem Algebra.trace_surjective [FiniteDimensional K L] [IsSeparable K L] :
    Function.Surjective (Algebra.trace K L) := by
  rw [← LinearMap.range_eq_top]
  apply (IsSimpleOrder.eq_bot_or_eq_top (α := Ideal K) _).resolve_left
  rw [LinearMap.range_eq_bot]
  exact Algebra.trace_ne_zero K L

variable {K L}

/--
The dual basis of a powerbasis `{1, x, x²...}` under the trace form is `aᵢ / f'(x)`,
with `f` being the minimal polynomial of `x` and `f / (X - x) = ∑ aᵢxⁱ`.
-/
lemma traceForm_dualBasis_powerBasis_eq [FiniteDimensional K L] [IsSeparable K L]
    (pb : PowerBasis K L) (i) :
    (Algebra.traceForm K L).dualBasis (traceForm_nondegenerate K L) pb.basis i =
      (minpolyDiv K pb.gen).coeff i / aeval pb.gen (derivative <| minpoly K pb.gen) := by
  classical
  apply ((Algebra.traceForm K L).toDual (traceForm_nondegenerate K L)).injective
  apply pb.basis.ext
  intro j
  simp only [BilinForm.toDual_def, BilinForm.apply_dualBasis_left]
  apply (algebraMap K (AlgebraicClosure K)).injective
  have := congr_arg (coeff · i) (sum_smul_minpolyDiv_eq_X_pow (AlgebraicClosure K)
    pb.adjoin_gen_eq_top (r := j) (pb.finrank.symm ▸ j.prop))
  simp only [AlgEquiv.toAlgHom_eq_coe, Polynomial.map_smul, map_div₀,
    map_pow, RingHom.coe_coe, AlgHom.coe_coe, finset_sum_coeff, coeff_smul, coeff_map, smul_eq_mul,
    coeff_X_pow, ← Fin.ext_iff, @eq_comm _ i] at this
  rw [PowerBasis.coe_basis]
  simp only [RingHom.map_ite_one_zero, traceForm_apply]
  rw [← this, trace_eq_sum_embeddings (E := AlgebraicClosure K)]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [_root_.map_mul, map_div₀, map_pow]
  ring

end DetNeZero
