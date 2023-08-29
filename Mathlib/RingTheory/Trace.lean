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

open LinearMap

open Matrix

open scoped BigOperators

open scoped Matrix

namespace Algebra

variable (b : Basis ι R S)

variable (R S)

/-- The trace of an element `s` of an `R`-algebra is the trace of `(*) s`,
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
                        -- ⊢ ↑(trace R S) s = ↑0 s
                               -- 🎉 no goals
#align algebra.trace_eq_zero_of_not_exists_basis Algebra.trace_eq_zero_of_not_exists_basis

variable {R}

-- Can't be a `simp` lemma because it depends on a choice of basis
theorem trace_eq_matrix_trace [DecidableEq ι] (b : Basis ι R S) (s : S) :
    trace R S s = Matrix.trace (Algebra.leftMulMatrix b s) := by
  rw [trace_apply, LinearMap.trace_eq_matrix_trace _ b, ← toMatrix_lmul_eq]; rfl
  -- ⊢ Matrix.trace (↑(toMatrix b b) (↑(lmul R S) s)) = Matrix.trace (↑(toMatrix b  …
                                                                             -- 🎉 no goals
#align algebra.trace_eq_matrix_trace Algebra.trace_eq_matrix_trace

/-- If `x` is in the base field `K`, then the trace is `[L : K] * x`. -/
theorem trace_algebraMap_of_basis (x : R) : trace R S (algebraMap R S x) = Fintype.card ι • x := by
  haveI := Classical.decEq ι
  -- ⊢ ↑(trace R S) (↑(algebraMap R S) x) = Fintype.card ι • x
  rw [trace_apply, LinearMap.trace_eq_matrix_trace R b, Matrix.trace]
  -- ⊢ ∑ i : ι, Matrix.diag (↑(toMatrix b b) (↑(lmul R S) (↑(algebraMap R S) x))) i …
  convert Finset.sum_const x
  -- ⊢ Matrix.diag (↑(toMatrix b b) (↑(lmul R S) (↑(algebraMap R S) x))) x✝ = x
-- Porting note: was `simp [-coe_lmul_eq_mul]`.
  simp only [AlgHom.commutes, toMatrix_algebraMap, diag_apply, Matrix.scalar_apply_eq]
  -- 🎉 no goals

#align algebra.trace_algebra_map_of_basis Algebra.trace_algebraMap_of_basis

/-- If `x` is in the base field `K`, then the trace is `[L : K] * x`.

(If `L` is not finite-dimensional over `K`, then `trace` and `finrank` return `0`.)
-/
@[simp]
theorem trace_algebraMap (x : K) : trace K L (algebraMap K L x) = finrank K L • x := by
  by_cases H : ∃ s : Finset L, Nonempty (Basis s K L)
  -- ⊢ ↑(trace K L) (↑(algebraMap K L) x) = finrank K L • x
  · rw [trace_algebraMap_of_basis H.choose_spec.some, finrank_eq_card_basis H.choose_spec.some]
    -- 🎉 no goals
  · simp [trace_eq_zero_of_not_exists_basis K H, finrank_eq_zero_of_not_exists_basis_finset H]
    -- 🎉 no goals
#align algebra.trace_algebra_map Algebra.trace_algebraMap

theorem trace_trace_of_basis [Algebra S T] [IsScalarTower R S T] {ι κ : Type*} [Finite ι]
    [Finite κ] (b : Basis ι R S) (c : Basis κ S T) (x : T) :
    trace R S (trace S T x) = trace R T x := by
  haveI := Classical.decEq ι
  -- ⊢ ↑(trace R S) (↑(trace S T) x) = ↑(trace R T) x
  haveI := Classical.decEq κ
  -- ⊢ ↑(trace R S) (↑(trace S T) x) = ↑(trace R T) x
  cases nonempty_fintype ι
  -- ⊢ ↑(trace R S) (↑(trace S T) x) = ↑(trace R T) x
  cases nonempty_fintype κ
  -- ⊢ ↑(trace R S) (↑(trace S T) x) = ↑(trace R T) x
  rw [trace_eq_matrix_trace (b.smul c), trace_eq_matrix_trace b, trace_eq_matrix_trace c,
    Matrix.trace, Matrix.trace, Matrix.trace, ← Finset.univ_product_univ, Finset.sum_product]
  refine' Finset.sum_congr rfl fun i _ => _
  -- ⊢ Matrix.diag (↑(leftMulMatrix b) (∑ i : κ, Matrix.diag (↑(leftMulMatrix c) x) …
  simp only [AlgHom.map_sum, smul_leftMulMatrix, Finset.sum_apply,
    Matrix.diag]
-- Porting note: the `rw` was inside `simp only`, but it doesn't work anymore.
  rw [Finset.sum_apply
      i (Finset.univ : Finset κ) fun y => leftMulMatrix b (leftMulMatrix c x y y)]
  apply Finset.sum_apply
  -- 🎉 no goals
#align algebra.trace_trace_of_basis Algebra.trace_trace_of_basis

theorem trace_comp_trace_of_basis [Algebra S T] [IsScalarTower R S T] {ι κ : Type*} [Finite ι]
    [Fintype κ] (b : Basis ι R S) (c : Basis κ S T) :
    (trace R S).comp ((trace S T).restrictScalars R) = trace R T := by
  ext
  -- ⊢ ↑(comp (trace R S) (↑R (trace S T))) x✝ = ↑(trace R T) x✝
  rw [LinearMap.comp_apply, LinearMap.restrictScalars_apply, trace_trace_of_basis b c]
  -- 🎉 no goals
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
  -- ⊢ ↑(comp (trace K L) (↑K (trace L T))) x✝ = ↑(trace K T) x✝
       -- 🎉 no goals
#align algebra.trace_comp_trace Algebra.trace_comp_trace

@[simp]
theorem trace_prod_apply [Module.Free R S] [Module.Free R T] [Module.Finite R S] [Module.Finite R T]
    (x : S × T) : trace R (S × T) x = trace R S x.fst + trace R T x.snd := by
  nontriviality R
  -- ⊢ ↑(trace R (S × T)) x = ↑(trace R S) x.fst + ↑(trace R T) x.snd
  let f := (lmul R S).toLinearMap.prodMap (lmul R T).toLinearMap
  -- ⊢ ↑(trace R (S × T)) x = ↑(trace R S) x.fst + ↑(trace R T) x.snd
  have : (lmul R (S × T)).toLinearMap = (prodMapLinear R S T S T R).comp f :=
    LinearMap.ext₂ Prod.mul_def
  simp_rw [trace, this]
  -- ⊢ ↑(comp (LinearMap.trace R (S × T)) (comp (prodMapLinear R S T S T R) (prodMa …
  exact trace_prodMap' _ _
  -- 🎉 no goals
#align algebra.trace_prod_apply Algebra.trace_prod_apply

theorem trace_prod [Module.Free R S] [Module.Free R T] [Module.Finite R S] [Module.Finite R T] :
    trace R (S × T) = (trace R S).coprod (trace R T) :=
  LinearMap.ext fun p => by rw [coprod_apply, trace_prod_apply]
                            -- 🎉 no goals
#align algebra.trace_prod Algebra.trace_prod

section TraceForm

variable (R S)

/-- The `traceForm` maps `x y : S` to the trace of `x * y`.
It is a symmetric bilinear form and is nondegenerate if the extension is separable. -/
noncomputable def traceForm : BilinForm R S :=
-- Porting note: dot notation `().toBilin` does not work anymore.
  LinearMap.toBilin (LinearMap.compr₂ (lmul R S).toLinearMap (trace R S))
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
  -- 🎉 no goals
#align algebra.trace_form_to_matrix Algebra.traceForm_toMatrix

theorem traceForm_toMatrix_powerBasis (h : PowerBasis R S) :
    BilinForm.toMatrix h.basis (traceForm R S) = of fun i j => trace R S (h.gen ^ (i.1 + j.1)) :=
  by ext; rw [traceForm_toMatrix, of_apply, pow_add, h.basis_eq_pow, h.basis_eq_pow]
     -- ⊢ ↑(BilinForm.toMatrix h.basis) (traceForm R S) i✝ x✝ = ↑of (fun i j => ↑(trac …
          -- 🎉 no goals
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
  -- ⊢ ↑(Algebra.trace K S) pb.gen = -nextCoeff (minpoly K pb.gen)
  have d_pos' : 0 < (minpoly K pb.gen).natDegree := by simpa
  -- ⊢ ↑(Algebra.trace K S) pb.gen = -nextCoeff (minpoly K pb.gen)
  haveI : Nonempty (Fin pb.dim) := ⟨⟨0, d_pos⟩⟩
  -- ⊢ ↑(Algebra.trace K S) pb.gen = -nextCoeff (minpoly K pb.gen)
  rw [trace_eq_matrix_trace pb.basis, trace_eq_neg_charpoly_coeff, charpoly_leftMulMatrix, ←
    pb.natDegree_minpoly, Fintype.card_fin, ← nextCoeff_of_pos_natDegree _ d_pos']
#align power_basis.trace_gen_eq_next_coeff_minpoly PowerBasis.trace_gen_eq_nextCoeff_minpoly

/-- Given `pb : PowerBasis K S`, then the trace of `pb.gen` is
`((minpoly K pb.gen).map (algebraMap K F)).roots.sum`. -/
theorem PowerBasis.trace_gen_eq_sum_roots [Nontrivial S] (pb : PowerBasis K S)
    (hf : (minpoly K pb.gen).Splits (algebraMap K F)) :
    algebraMap K F (trace K S pb.gen) = ((minpoly K pb.gen).map (algebraMap K F)).roots.sum := by
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
  -- ⊢ ¬∃ s, Nonempty (Basis { x_1 // x_1 ∈ s } K { x_1 // x_1 ∈ K⟮x⟯ })
  contrapose! hx
  -- ⊢ IsIntegral K x
  obtain ⟨s, ⟨b⟩⟩ := hx
  -- ⊢ IsIntegral K x
  refine' isIntegral_of_mem_of_FG K⟮x⟯.toSubalgebra _ x _
  -- ⊢ Submodule.FG (↑Subalgebra.toSubmodule K⟮x⟯.toSubalgebra)
  · exact (Submodule.fg_iff_finiteDimensional _).mpr (FiniteDimensional.of_fintype_basis b)
    -- 🎉 no goals
  · exact subset_adjoin K _ (Set.mem_singleton x)
    -- 🎉 no goals
#align intermediate_field.adjoin_simple.trace_gen_eq_zero IntermediateField.AdjoinSimple.trace_gen_eq_zero

theorem trace_gen_eq_sum_roots (x : L) (hf : (minpoly K x).Splits (algebraMap K F)) :
    algebraMap K F (trace K K⟮x⟯ (AdjoinSimple.gen K x)) =
      ((minpoly K x).map (algebraMap K F)).roots.sum := by
  have injKxL := (algebraMap K⟮x⟯ L).injective
  -- ⊢ ↑(algebraMap K F) (↑(Algebra.trace K { x_1 // x_1 ∈ K⟮x⟯ }) (gen K x)) = Mul …
  by_cases hx : IsIntegral K x; swap
  -- ⊢ ↑(algebraMap K F) (↑(Algebra.trace K { x_1 // x_1 ∈ K⟮x⟯ }) (gen K x)) = Mul …
                                -- ⊢ ↑(algebraMap K F) (↑(Algebra.trace K { x_1 // x_1 ∈ K⟮x⟯ }) (gen K x)) = Mul …
  · simp [minpoly.eq_zero hx, trace_gen_eq_zero hx]
    -- 🎉 no goals
  have hx' : IsIntegral K (AdjoinSimple.gen K x) := by
    rwa [← isIntegral_algebraMap_iff injKxL, AdjoinSimple.algebraMap_gen]
  rw [← adjoin.powerBasis_gen hx, (adjoin.powerBasis hx).trace_gen_eq_sum_roots] <;>
  -- ⊢ Multiset.sum (roots (Polynomial.map (algebraMap K F) (minpoly K (adjoin.powe …
      rw [adjoin.powerBasis_gen hx, minpoly.eq_of_algebraMap_eq injKxL hx'] <;>
      -- ⊢ x = ↑(algebraMap { x_1 // x_1 ∈ K⟮x⟯ } L) (gen K x)
    try simp only [AdjoinSimple.algebraMap_gen _ _]
    -- 🎉 no goals
    -- ⊢ Splits (algebraMap K F) (minpoly K ?m.547269)
    -- ⊢ ?m.547269 = x
    -- ⊢ L
  · exact hf
    -- 🎉 no goals
  · rfl
    -- 🎉 no goals
#align intermediate_field.adjoin_simple.trace_gen_eq_sum_roots IntermediateField.AdjoinSimple.trace_gen_eq_sum_roots

end IntermediateField.AdjoinSimple

open IntermediateField

variable (K)

theorem trace_eq_trace_adjoin [FiniteDimensional K L] (x : L) :
    Algebra.trace K L x = finrank K⟮x⟯ L • trace K K⟮x⟯ (AdjoinSimple.gen K x) := by
-- Porting note: `conv` was `conv in x => rw [← IntermediateField.AdjoinSimple.algebraMap_gen K x]`
-- and it was after the first `rw`.
  conv =>
    lhs
    rw [← IntermediateField.AdjoinSimple.algebraMap_gen K x]
  rw [← @trace_trace _ _ K K⟮x⟯ _ _ _ _ _ _ _ _ _, trace_algebraMap, LinearMap.map_smul_of_tower]
  -- 🎉 no goals
#align trace_eq_trace_adjoin trace_eq_trace_adjoin

variable {K}

theorem trace_eq_sum_roots [FiniteDimensional K L] {x : L}
    (hF : (minpoly K x).Splits (algebraMap K F)) :
    algebraMap K F (Algebra.trace K L x) =
      finrank K⟮x⟯ L • ((minpoly K x).map (algebraMap K _)).roots.sum := by
  rw [trace_eq_trace_adjoin K x, Algebra.smul_def, RingHom.map_mul, ← Algebra.smul_def,
    IntermediateField.AdjoinSimple.trace_gen_eq_sum_roots _ hF]
-- Porting note: last `simp` was `IsScalarTower.algebraMap_smul` inside the `rw`.
  simp only [eq_natCast, map_natCast, nsmul_eq_mul]
  -- 🎉 no goals
#align trace_eq_sum_roots trace_eq_sum_roots

end EqSumRoots

variable {F : Type*} [Field F]

variable [Algebra R L] [Algebra L F] [Algebra R F] [IsScalarTower R L F]

open Polynomial

attribute [-instance] Field.toEuclideanDomain

theorem Algebra.isIntegral_trace [FiniteDimensional L F] {x : F} (hx : IsIntegral R x) :
    IsIntegral R (Algebra.trace L F x) := by
  have hx' : IsIntegral L x := isIntegral_of_isScalarTower hx
  -- ⊢ IsIntegral R (↑(trace L F) x)
  rw [← isIntegral_algebraMap_iff (algebraMap L (AlgebraicClosure F)).injective, trace_eq_sum_roots]
  -- ⊢ IsIntegral R (finrank { x_1 // x_1 ∈ L⟮x⟯ } F • Multiset.sum (roots (Polynom …
  · refine' (IsIntegral.multiset_sum _).nsmul _
    -- ⊢ ∀ (x_1 : (fun x => AlgebraicClosure F) (↑(trace L F) x)), x_1 ∈ roots (Polyn …
    intro y hy
    -- ⊢ IsIntegral R y
    rw [mem_roots_map (minpoly.ne_zero hx')] at hy
    -- ⊢ IsIntegral R y
    use minpoly R x, minpoly.monic hx
    -- ⊢ eval₂ (algebraMap R ((fun x => AlgebraicClosure F) (↑(trace L F) x))) y (min …
    rw [← aeval_def] at hy ⊢
    -- ⊢ ↑(aeval y) (minpoly R x) = 0
    exact minpoly.aeval_of_isScalarTower R x y hy
    -- 🎉 no goals
  · apply IsAlgClosed.splits_codomain
    -- 🎉 no goals
#align algebra.is_integral_trace Algebra.isIntegral_trace

section EqSumEmbeddings

variable [Algebra K F] [IsScalarTower K L F]

open Algebra IntermediateField

variable (F) (E : Type*) [Field E] [Algebra K E]

theorem trace_eq_sum_embeddings_gen (pb : PowerBasis K L)
    (hE : (minpoly K pb.gen).Splits (algebraMap K E)) (hfx : (minpoly K pb.gen).Separable) :
    algebraMap K E (Algebra.trace K L pb.gen) =
      (@Finset.univ _ (PowerBasis.AlgHom.fintype pb)).sum fun σ => σ pb.gen := by
  letI := Classical.decEq E
  -- ⊢ ↑(algebraMap K E) (↑(Algebra.trace K L) pb.gen) = ∑ σ : L →ₐ[K] E, ↑σ pb.gen
-- Porting note: the following `letI` was not needed.
  letI : Fintype (L →ₐ[K] E) := (PowerBasis.AlgHom.fintype pb)
  -- ⊢ ↑(algebraMap K E) (↑(Algebra.trace K L) pb.gen) = ∑ σ : L →ₐ[K] E, ↑σ pb.gen
  rw [pb.trace_gen_eq_sum_roots hE, Fintype.sum_equiv pb.liftEquiv', Finset.sum_mem_multiset,
    Finset.sum_eq_multiset_sum, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr _,
    Multiset.map_id]
  · exact nodup_roots ((separable_map _).mpr hfx)
    -- 🎉 no goals
-- Porting note: the following goal does not exist in mathlib3.
  · exact (fun x => x.1)
    -- 🎉 no goals
  · intro x; rfl
    -- ⊢ ↑x = _root_.id ↑x
             -- 🎉 no goals
  · intro σ
    -- ⊢ ↑σ pb.gen = ↑(↑(PowerBasis.liftEquiv' pb) σ)
    rw [PowerBasis.liftEquiv'_apply_coe]
    -- 🎉 no goals
#align trace_eq_sum_embeddings_gen trace_eq_sum_embeddings_gen

variable [IsAlgClosed E]

theorem sum_embeddings_eq_finrank_mul [FiniteDimensional K F] [IsSeparable K F]
    (pb : PowerBasis K L) :
    ∑ σ : F →ₐ[K] E, σ (algebraMap L F pb.gen) =
      finrank L F •
        (@Finset.univ _ (PowerBasis.AlgHom.fintype pb)).sum fun σ : L →ₐ[K] E => σ pb.gen := by
  haveI : FiniteDimensional L F := FiniteDimensional.right K L F
  -- ⊢ ∑ σ : F →ₐ[K] E, ↑σ (↑(algebraMap L F) pb.gen) = finrank L F • ∑ σ : L →ₐ[K] …
  haveI : IsSeparable L F := isSeparable_tower_top_of_isSeparable K L F
  -- ⊢ ∑ σ : F →ₐ[K] E, ↑σ (↑(algebraMap L F) pb.gen) = finrank L F • ∑ σ : L →ₐ[K] …
  letI : Fintype (L →ₐ[K] E) := PowerBasis.AlgHom.fintype pb
  -- ⊢ ∑ σ : F →ₐ[K] E, ↑σ (↑(algebraMap L F) pb.gen) = finrank L F • ∑ σ : L →ₐ[K] …
  letI : ∀ f : L →ₐ[K] E, Fintype (@AlgHom L F E _ _ _ _ f.toRingHom.toAlgebra) := ?_
  -- ⊢ ∑ σ : F →ₐ[K] E, ↑σ (↑(algebraMap L F) pb.gen) = finrank L F • ∑ σ : L →ₐ[K] …
  rw [Fintype.sum_equiv algHomEquivSigma (fun σ : F →ₐ[K] E => _) fun σ => σ.1 pb.gen, ←
    Finset.univ_sigma_univ, Finset.sum_sigma, ← Finset.sum_nsmul]
  refine' Finset.sum_congr rfl fun σ _ => _
  · letI : Algebra L E := σ.toRingHom.toAlgebra
    -- ⊢ ∑ s : F →ₐ[L] E, ↑{ fst := σ, snd := s }.fst pb.gen = finrank L F • ↑σ pb.gen
-- Porting note: `Finset.card_univ` was inside `simp only`.
    simp only [Finset.sum_const]
    -- ⊢ Finset.card Finset.univ • ↑σ pb.gen = finrank L F • ↑σ pb.gen
    congr
    -- ⊢ Finset.card Finset.univ = finrank L F
    rw [← AlgHom.card L F E]
    -- ⊢ Finset.card Finset.univ = Fintype.card (F →ₐ[L] E)
    exact Finset.card_univ (α := F →ₐ[L] E)
    -- 🎉 no goals
  · intro σ
    -- ⊢ ↑σ (↑(algebraMap L F) pb.gen) = ↑(↑algHomEquivSigma σ).fst pb.gen
    simp only [algHomEquivSigma, Equiv.coe_fn_mk, AlgHom.restrictDomain, AlgHom.comp_apply,
      IsScalarTower.coe_toAlgHom']
#align sum_embeddings_eq_finrank_mul sum_embeddings_eq_finrank_mul

theorem trace_eq_sum_embeddings [FiniteDimensional K L] [IsSeparable K L] {x : L} :
    algebraMap K E (Algebra.trace K L x) = ∑ σ : L →ₐ[K] E, σ x := by
  have hx := IsSeparable.isIntegral K x
  -- ⊢ ↑(algebraMap K E) (↑(Algebra.trace K L) x) = ∑ σ : L →ₐ[K] E, ↑σ x
  let pb := (adjoin.powerBasis hx)
  -- ⊢ ↑(algebraMap K E) (↑(Algebra.trace K L) x) = ∑ σ : L →ₐ[K] E, ↑σ x
  rw [trace_eq_trace_adjoin K x, Algebra.smul_def, RingHom.map_mul, ← adjoin.powerBasis_gen hx,
    trace_eq_sum_embeddings_gen E pb (IsAlgClosed.splits_codomain _)]
-- Porting note: the following `convert` was `exact`, with `← algebra.smul_def, algebra_map_smul`
-- in the previous `rw`.
  · convert (sum_embeddings_eq_finrank_mul L E pb).symm
    -- ⊢ HMul.hMul (↑(algebraMap K E) (↑(algebraMap ℕ ((fun x => K) (adjoin.powerBasi …
    ext
    -- ⊢ ↑(algebraMap K E) (↑(algebraMap ℕ ((fun x => K) (adjoin.powerBasis hx).gen)) …
    simp
    -- 🎉 no goals
  · haveI := isSeparable_tower_bot_of_isSeparable K K⟮x⟯ L
    -- ⊢ Separable (minpoly K pb.gen)
    exact IsSeparable.separable K _
    -- 🎉 no goals
#align trace_eq_sum_embeddings trace_eq_sum_embeddings

theorem trace_eq_sum_automorphisms (x : L) [FiniteDimensional K L] [IsGalois K L] :
    algebraMap K L (Algebra.trace K L x) = ∑ σ : L ≃ₐ[K] L, σ x := by
  apply NoZeroSMulDivisors.algebraMap_injective L (AlgebraicClosure L)
  -- ⊢ ↑(algebraMap L (AlgebraicClosure L)) (↑(algebraMap K L) (↑(Algebra.trace K L …
  rw [_root_.map_sum (algebraMap L (AlgebraicClosure L))]
  -- ⊢ ↑(algebraMap L (AlgebraicClosure L)) (↑(algebraMap K L) (↑(Algebra.trace K L …
  rw [← Fintype.sum_equiv (Normal.algHomEquivAut K (AlgebraicClosure L) L)]
  · rw [← trace_eq_sum_embeddings (AlgebraicClosure L)]
    -- ⊢ ↑(algebraMap L (AlgebraicClosure L)) (↑(algebraMap K L) (↑(Algebra.trace K L …
    · simp only [algebraMap_eq_smul_one]
      -- ⊢ (↑(Algebra.trace K L) x • 1) • 1 = ↑(Algebra.trace K L) ?m.944006 • 1
-- Porting note: `smul_one_smul` was in the `simp only`.
      apply smul_one_smul
      -- 🎉 no goals
  · intro σ
    -- ⊢ ↑σ x = ↑(algebraMap L (AlgebraicClosure L)) (↑(↑(Normal.algHomEquivAut K (Al …
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
                                                                      -- ⊢ traceMatrix A (↑(Basis.reindex b f)) x y = ↑(reindex f f) (traceMatrix A ↑b) …
                                                                                 -- 🎉 no goals
#align algebra.trace_matrix_reindex Algebra.traceMatrix_reindex

variable {A}

theorem traceMatrix_of_matrix_vecMul [Fintype κ] (b : κ → B) (P : Matrix κ κ A) :
    traceMatrix A ((P.map (algebraMap A B)).vecMul b) = Pᵀ * traceMatrix A b * P := by
  ext (α β)
  -- ⊢ traceMatrix A (vecMul b (Matrix.map P ↑(algebraMap A B))) α β = (Pᵀ * traceM …
  rw [traceMatrix_apply, vecMul, dotProduct, vecMul, dotProduct, Matrix.mul_apply,
    BilinForm.sum_left,
    Fintype.sum_congr _ _ fun i : κ =>
      @BilinForm.sum_right _ _ _ _ _ _ _ _ (b i * P.map (algebraMap A B) i α) fun y : κ =>
        b y * P.map (algebraMap A B) y β,
    sum_comm]
  congr; ext x
  -- ⊢ (fun y => ∑ x : κ, BilinForm.bilin (traceForm A B) (b x * Matrix.map P (↑(al …
         -- ⊢ ∑ x_1 : κ, BilinForm.bilin (traceForm A B) (b x_1 * Matrix.map P (↑(algebraM …
  rw [Matrix.mul_apply, sum_mul]
  -- ⊢ ∑ x_1 : κ, BilinForm.bilin (traceForm A B) (b x_1 * Matrix.map P (↑(algebraM …
  congr; ext y
  -- ⊢ (fun x_1 => BilinForm.bilin (traceForm A B) (b x_1 * Matrix.map P (↑(algebra …
         -- ⊢ BilinForm.bilin (traceForm A B) (b y * Matrix.map P (↑(algebraMap A B)) y α) …
  rw [map_apply, traceForm_apply, mul_comm (b y), ← smul_def]
  -- ⊢ ↑(trace A B) (P y α • b y * (b x * Matrix.map P (↑(algebraMap A B)) x β)) =  …
  simp only [id.smul_eq_mul, RingHom.id_apply, map_apply, transpose_apply, LinearMap.map_smulₛₗ,
    traceForm_apply, Algebra.smul_mul_assoc]
  rw [mul_comm (b x), ← smul_def]
  -- ⊢ P y α * ↑(trace A B) (b y * P x β • b x) = P y α * traceMatrix A b y x * P x β
  ring_nf
  -- ⊢ P y α * ↑(trace A B) (b y * P x β • b x) = P y α * traceMatrix A b y x * P x β
  rw [mul_assoc]
  -- ⊢ P y α * ↑(trace A B) (b y * P x β • b x) = P y α * (traceMatrix A b y x * P  …
  simp [mul_comm]
  -- 🎉 no goals
#align algebra.trace_matrix_of_matrix_vec_mul Algebra.traceMatrix_of_matrix_vecMul

theorem traceMatrix_of_matrix_mulVec [Fintype κ] (b : κ → B) (P : Matrix κ κ A) :
    traceMatrix A ((P.map (algebraMap A B)).mulVec b) = P * traceMatrix A b * Pᵀ := by
  refine' AddEquiv.injective (transposeAddEquiv κ κ A) _
  -- ⊢ ↑(transposeAddEquiv κ κ A) (traceMatrix A (mulVec (Matrix.map P ↑(algebraMap …
  rw [transposeAddEquiv_apply, transposeAddEquiv_apply, ← vecMul_transpose, ← transpose_map,
    traceMatrix_of_matrix_vecMul, transpose_transpose, transpose_mul, transpose_transpose,
    transpose_mul]
#align algebra.trace_matrix_of_matrix_mul_vec Algebra.traceMatrix_of_matrix_mulVec

theorem traceMatrix_of_basis [Fintype κ] [DecidableEq κ] (b : Basis κ A B) :
    traceMatrix A b = BilinForm.toMatrix b (traceForm A B) := by
  ext (i j)
  -- ⊢ traceMatrix A (↑b) i j = ↑(BilinForm.toMatrix b) (traceForm A B) i j
  rw [traceMatrix_apply, traceForm_apply, traceForm_toMatrix]
  -- 🎉 no goals
#align algebra.trace_matrix_of_basis Algebra.traceMatrix_of_basis

theorem traceMatrix_of_basis_mulVec (b : Basis ι A B) (z : B) :
    (traceMatrix A b).mulVec (b.equivFun z) = fun i => trace A B (z * b i) := by
  ext i
  -- ⊢ mulVec (traceMatrix A ↑b) (↑(Basis.equivFun b) z) i = ↑(trace A B) (z * ↑b i)
  rw [← col_apply ((traceMatrix A b).mulVec (b.equivFun z)) i Unit.unit, col_mulVec,
    Matrix.mul_apply, traceMatrix]
  simp only [col_apply, traceForm_apply]
  -- ⊢ ∑ x : ι, ↑of (fun i j => ↑(trace A B) (↑b i * ↑b j)) i x * ↑(Basis.equivFun  …
  conv_lhs =>
    congr
    rfl
    ext
    rw [mul_comm _ (b.equivFun z _), ← smul_eq_mul, of_apply, ← LinearMap.map_smul]
  rw [← LinearMap.map_sum]
  -- ⊢ ↑(trace A B) (∑ i_1 : ι, ↑(Basis.equivFun b) z i_1 • (↑b i * ↑b i_1)) = ↑(tr …
  congr
  -- ⊢ ∑ i_1 : ι, ↑(Basis.equivFun b) z i_1 • (↑b i * ↑b i_1) = z * ↑b i
  conv_lhs =>
    congr
    rfl
    ext
    rw [← mul_smul_comm]
  rw [← Finset.mul_sum, mul_comm z]
  -- ⊢ ↑b i * ∑ x : ι, ↑(Basis.equivFun b) z x • ↑b x = ↑b i * z
  congr
  -- ⊢ ∑ x : ι, ↑(Basis.equivFun b) z x • ↑b x = z
  rw [b.sum_equivFun]
  -- 🎉 no goals
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
  -- ⊢ embeddingsMatrixReindex A C (↑pb.basis) e i j = (vandermonde fun i => ↑(↑e i …
  simp [embeddingsMatrixReindex, embeddingsMatrix]
  -- 🎉 no goals
#align algebra.embeddings_matrix_reindex_eq_vandermonde Algebra.embeddingsMatrixReindex_eq_vandermonde

section Field

variable (K) (E : Type z) [Field E]

variable [Algebra K E]

variable [Module.Finite K L] [IsSeparable K L] [IsAlgClosed E]

variable (b : κ → L) (pb : PowerBasis K L)

theorem traceMatrix_eq_embeddingsMatrix_mul_trans :
    (traceMatrix K b).map (algebraMap K E) = embeddingsMatrix K E b * (embeddingsMatrix K E b)ᵀ :=
  by ext (i j); simp [trace_eq_sum_embeddings, embeddingsMatrix, Matrix.mul_apply]
     -- ⊢ Matrix.map (traceMatrix K b) (↑(algebraMap K E)) i j = (embeddingsMatrix K E …
                -- 🎉 no goals
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
    refine' mt (fun ht => _) this
    rw [ht, RingHom.map_zero]
  haveI : FiniteDimensional K L := pb.finiteDimensional
  -- ⊢ ↑(algebraMap K (AlgebraicClosure L)) (det (traceMatrix K ↑pb.basis)) ≠ 0
  let e : Fin pb.dim ≃ (L →ₐ[K] AlgebraicClosure L) := (Fintype.equivFinOfCardEq ?_).symm
  -- ⊢ ↑(algebraMap K (AlgebraicClosure L)) (det (traceMatrix K ↑pb.basis)) ≠ 0
  rw [RingHom.map_det, RingHom.mapMatrix_apply,
    traceMatrix_eq_embeddingsMatrixReindex_mul_trans K _ _ e,
    embeddingsMatrixReindex_eq_vandermonde, det_mul, det_transpose]
-- Porting note: the following is necessary.
  haveI := IsDomain.to_noZeroDivisors (AlgebraicClosure L)
  -- ⊢ det (vandermonde fun i => ↑(↑e i) pb.gen) * det (vandermonde fun i => ↑(↑e i …
  refine' mt mul_self_eq_zero.mp _
  -- ⊢ ¬det (vandermonde fun i => ↑(↑e i) pb.gen) = 0
  · simp only [det_vandermonde, Finset.prod_eq_zero_iff, not_exists, sub_eq_zero]
    -- ⊢ ∀ (x : Fin pb.dim), ¬(x ∈ Finset.univ ∧ ∃ a, a ∈ Finset.Ioi x ∧ ↑(↑(Fintype. …
    rintro i ⟨_, j, hij, h⟩
    -- ⊢ False
    exact (Finset.mem_Ioi.mp hij).ne' (e.injective <| pb.algHom_ext h)
    -- 🎉 no goals
  · rw [AlgHom.card, pb.finrank]
    -- 🎉 no goals
#align det_trace_matrix_ne_zero' det_traceMatrix_ne_zero'

theorem det_traceForm_ne_zero [IsSeparable K L] [DecidableEq ι] (b : Basis ι K L) :
    det (BilinForm.toMatrix b (traceForm K L)) ≠ 0 := by
  haveI : FiniteDimensional K L := FiniteDimensional.of_fintype_basis b
  -- ⊢ det (↑(BilinForm.toMatrix b) (traceForm K L)) ≠ 0
  let pb : PowerBasis K L := Field.powerBasisOfFiniteOfSeparable _ _
  -- ⊢ det (↑(BilinForm.toMatrix b) (traceForm K L)) ≠ 0
  rw [← BilinForm.toMatrix_mul_basis_toMatrix pb.basis b, ←
    det_comm' (pb.basis.toMatrix_mul_toMatrix_flip b) _, ← Matrix.mul_assoc, det_mul]
  swap; · apply Basis.toMatrix_mul_toMatrix_flip
  -- ⊢ Basis.toMatrix b ↑pb.basis * Basis.toMatrix pb.basis ↑b = 1
          -- 🎉 no goals
  refine'
    mul_ne_zero
      (isUnit_of_mul_eq_one _ ((b.toMatrix pb.basis)ᵀ * b.toMatrix pb.basis).det _).ne_zero _
  · calc
      (pb.basis.toMatrix b * (pb.basis.toMatrix b)ᵀ).det *
            ((b.toMatrix pb.basis)ᵀ * b.toMatrix pb.basis).det =
          (pb.basis.toMatrix b * (b.toMatrix pb.basis * pb.basis.toMatrix b)ᵀ *
              b.toMatrix pb.basis).det :=
        by simp only [← det_mul, Matrix.mul_assoc, Matrix.transpose_mul]
      _ = 1 := by
        simp only [Basis.toMatrix_mul_toMatrix_flip, Matrix.transpose_one, Matrix.mul_one,
          Matrix.det_one]
  simpa only [traceMatrix_of_basis] using det_traceMatrix_ne_zero' pb
  -- 🎉 no goals
#align det_trace_form_ne_zero det_traceForm_ne_zero

variable (K L)

theorem traceForm_nondegenerate [FiniteDimensional K L] [IsSeparable K L] :
    (traceForm K L).Nondegenerate :=
  BilinForm.nondegenerate_of_det_ne_zero (traceForm K L) _
    (det_traceForm_ne_zero (FiniteDimensional.finBasis K L))
#align trace_form_nondegenerate traceForm_nondegenerate

end DetNeZero
