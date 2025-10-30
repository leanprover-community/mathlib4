/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Minpoly.MinpolyDiv
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.Trace.Defs

/-!
# Trace for (finite) ring extensions.

Suppose we have an `R`-algebra `S` with a finite basis. For each `s : S`,
the trace of the linear map given by multiplying by `s` gives information about
the roots of the minimal polynomial of `s` over `R`.

## Main definitions

* `Algebra.embeddingsMatrix A C b : Matrix κ (B →ₐ[A] C) C` is the matrix whose
  `(i, σ)` coefficient is `σ (b i)`.
* `Algebra.embeddingsMatrixReindex A C b e : Matrix κ κ C` is the matrix whose `(i, j)`
  coefficient is `σⱼ (b i)`, where `σⱼ : B →ₐ[A] C` is the embedding corresponding to `j : κ`
  given by a bijection `e : κ ≃ (B →ₐ[A] C)`.
* `Module.Basis.traceDual`: The dual basis of a basis under the trace form in a finite separable
  extension.

## Main results

* `trace_eq_sum_embeddings`: the trace of `x : K(x)` is the sum of all embeddings of `x` into an
  algebraically closed field
* `traceForm_nondegenerate`: the trace form over a separable extension is a nondegenerate
  bilinear form
* `Module.Basis.traceDual_powerBasis_eq`: The dual basis of a power basis `{1, x, x²...}` under the
  trace form is `aᵢ / f'(x)`, with `f` being the minpoly of `x` and `f / (X - x) = ∑ aᵢxⁱ`.

## References

* https://en.wikipedia.org/wiki/Field_trace

-/

universe u v w z

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T]
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable {ι κ : Type w}

open Module

open LinearMap (BilinForm)
open LinearMap

open Matrix

open scoped Matrix

theorem Algebra.traceForm_toMatrix_powerBasis (h : PowerBasis R S) :
    BilinForm.toMatrix h.basis (traceForm R S) = of fun i j => trace R S (h.gen ^ (i.1 + j.1)) := by
  ext; rw [traceForm_toMatrix, of_apply, pow_add, h.basis_eq_pow, h.basis_eq_pow]

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

/-- Given `pb : PowerBasis K S`, then the trace of `pb.gen` is
`((minpoly K pb.gen).aroots F).sum`. -/
theorem PowerBasis.trace_gen_eq_sum_roots [Nontrivial S] (pb : PowerBasis K S)
    (hf : (minpoly K pb.gen).Splits (algebraMap K F)) :
    algebraMap K F (trace K S pb.gen) = ((minpoly K pb.gen).aroots F).sum := by
  rw [PowerBasis.trace_gen_eq_nextCoeff_minpoly, RingHom.map_neg, ←
    nextCoeff_map (algebraMap K F).injective, nextCoeff_eq_neg_sum_roots_of_monic_of_splits
      ((minpoly.monic (PowerBasis.isIntegral_gen _)).map _) ((splits_id_iff_splits _).2 hf),
    neg_neg]

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

end IntermediateField.AdjoinSimple

open IntermediateField

variable (K)

theorem trace_eq_trace_adjoin [FiniteDimensional K L] (x : L) :
    trace K L x = finrank K⟮x⟯ L • trace K K⟮x⟯ (AdjoinSimple.gen K x) := by
  rw [← trace_trace (S := K⟮x⟯)]
  conv in x => rw [← AdjoinSimple.algebraMap_gen K x]
  rw [trace_algebraMap, LinearMap.map_smul_of_tower]

variable {K} in
/-- Trace of the generator of a simple adjoin equals negative of the next coefficient of
its minimal polynomial coefficient. -/
theorem trace_adjoinSimpleGen {x : L} (hx : IsIntegral K x) :
    trace K K⟮x⟯ (AdjoinSimple.gen K x) = -(minpoly K x).nextCoeff := by
  simpa [minpoly_gen K x] using PowerBasis.trace_gen_eq_nextCoeff_minpoly <| adjoin.powerBasis hx

theorem trace_eq_finrank_mul_minpoly_nextCoeff [FiniteDimensional K L] (x : L) :
    trace K L x = finrank K⟮x⟯ L * -(minpoly K x).nextCoeff := by
  rw [trace_eq_trace_adjoin, trace_adjoinSimpleGen (.of_finite K x), Algebra.smul_def]; rfl

variable {K}

theorem trace_eq_sum_roots [FiniteDimensional K L] {x : L}
    (hF : (minpoly K x).Splits (algebraMap K F)) :
    algebraMap K F (Algebra.trace K L x) =
      finrank K⟮x⟯ L • ((minpoly K x).aroots F).sum := by
  rw [trace_eq_trace_adjoin K x, Algebra.smul_def, RingHom.map_mul, ← Algebra.smul_def,
    IntermediateField.AdjoinSimple.trace_gen_eq_sum_roots _ hF, IsScalarTower.algebraMap_smul]

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
    (hE : (minpoly K pb.gen).Splits (algebraMap K E)) (hfx : IsSeparable K pb.gen) :
    algebraMap K E (Algebra.trace K L pb.gen) =
      (@Finset.univ _ (PowerBasis.AlgHom.fintype pb)).sum fun σ => σ pb.gen := by
  letI := Classical.decEq E
  letI : Fintype (L →ₐ[K] E) := PowerBasis.AlgHom.fintype pb
  rw [pb.trace_gen_eq_sum_roots hE, Fintype.sum_equiv pb.liftEquiv', Finset.sum_mem_multiset,
    Finset.sum_eq_multiset_sum, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr _,
    Multiset.map_id]
  · exact nodup_roots ((separable_map _).mpr hfx)
  swap
  · intro x; rfl
  · intro σ
    rw [PowerBasis.liftEquiv'_apply_coe, id_def]

variable [IsAlgClosed E]

theorem sum_embeddings_eq_finrank_mul [FiniteDimensional K F] [Algebra.IsSeparable K F]
    (pb : PowerBasis K L) :
    ∑ σ : F →ₐ[K] E, σ (algebraMap L F pb.gen) =
      finrank L F •
        (@Finset.univ _ (PowerBasis.AlgHom.fintype pb)).sum fun σ : L →ₐ[K] E => σ pb.gen := by
  haveI : FiniteDimensional L F := FiniteDimensional.right K L F
  haveI : Algebra.IsSeparable L F := Algebra.isSeparable_tower_top_of_isSeparable K L F
  letI : Fintype (L →ₐ[K] E) := PowerBasis.AlgHom.fintype pb
  rw [Fintype.sum_equiv algHomEquivSigma (fun σ : F →ₐ[K] E => _) fun σ => σ.1 pb.gen,
    ← Finset.univ_sigma_univ, Finset.sum_sigma, ← Finset.sum_nsmul]
  · refine Finset.sum_congr rfl fun σ _ => ?_
    letI : Algebra L E := σ.toRingHom.toAlgebra
    simp_rw [Finset.sum_const, Finset.card_univ, ← AlgHom.card L F E]
  · intro σ
    simp only [algHomEquivSigma, Equiv.coe_fn_mk, AlgHom.restrictDomain, AlgHom.comp_apply,
      IsScalarTower.coe_toAlgHom']

theorem trace_eq_sum_embeddings [FiniteDimensional K L] [Algebra.IsSeparable K L] {x : L} :
    algebraMap K E (Algebra.trace K L x) = ∑ σ : L →ₐ[K] E, σ x := by
  have hx := Algebra.IsSeparable.isIntegral K x
  let pb := adjoin.powerBasis hx
  rw [trace_eq_trace_adjoin K x, Algebra.smul_def, RingHom.map_mul, ← adjoin.powerBasis_gen hx,
    trace_eq_sum_embeddings_gen E pb (IsAlgClosed.splits_codomain _), ← Algebra.smul_def,
    algebraMap_smul]
  · exact (sum_embeddings_eq_finrank_mul L E pb).symm
  · haveI := Algebra.isSeparable_tower_bot_of_isSeparable K K⟮x⟯ L
    exact Algebra.IsSeparable.isSeparable K _

theorem trace_eq_sum_automorphisms (x : L) [FiniteDimensional K L] [IsGalois K L] :
    algebraMap K L (Algebra.trace K L x) = ∑ σ : Gal(L/K), σ x := by
  apply FaithfulSMul.algebraMap_injective L (AlgebraicClosure L)
  rw [_root_.map_sum (algebraMap L (AlgebraicClosure L))]
  rw [← Fintype.sum_equiv (Normal.algHomEquivAut K (AlgebraicClosure L) L)]
  · rw [← trace_eq_sum_embeddings (AlgebraicClosure L) (x := x)]
    simp only [algebraMap_eq_smul_one, smul_one_smul]
  · intro σ
    simp only [Normal.algHomEquivAut, AlgHom.restrictNormal', Equiv.coe_fn_mk,
      AlgEquiv.coe_ofBijective, AlgHom.restrictNormal_commutes, algebraMap_self, RingHom.id_apply]

end EqSumEmbeddings

section NotIsSeparable

lemma Algebra.trace_eq_zero_of_not_isSeparable (H : ¬ Algebra.IsSeparable K L) :
    trace K L = 0 := by
  obtain ⟨p, hp⟩ := ExpChar.exists K
  have := expChar_ne_zero K p
  ext x
  by_cases h₀ : FiniteDimensional K L; swap
  · rw [trace_eq_zero_of_not_exists_basis]
    rintro ⟨s, ⟨b⟩⟩
    exact h₀ (Module.Finite.of_basis b)
  by_cases hx : IsSeparable K x
  · lift x to separableClosure K L using hx
    rw [← IntermediateField.algebraMap_apply, ← trace_trace (S := separableClosure K L),
      trace_algebraMap]
    obtain ⟨n, hn⟩ := IsPurelyInseparable.finrank_eq_pow (separableClosure K L) L p
    cases n with
    | zero =>
      rw [pow_zero, IntermediateField.finrank_eq_one_iff_eq_top, separableClosure.eq_top_iff] at hn
      cases H hn
    | succ n =>
      cases hp with
      | zero =>
        rw [one_pow, IntermediateField.finrank_eq_one_iff_eq_top, separableClosure.eq_top_iff] at hn
        cases H hn
      | prime hprime =>
        rw [hn, pow_succ', MulAction.mul_smul, LinearMap.map_smul_of_tower, nsmul_eq_mul,
          CharP.cast_eq_zero, zero_mul, LinearMap.zero_apply]
  · rw [trace_eq_finrank_mul_minpoly_nextCoeff]
    obtain ⟨g, hg₁, m, hg₂⟩ :=
      (minpoly.irreducible (IsIntegral.isIntegral (R := K) x)).hasSeparableContraction p
    cases m with
    | zero =>
      obtain rfl : g = minpoly K x := by simpa using hg₂
      cases hx hg₁
    | succ n =>
      rw [nextCoeff, if_neg, ← hg₂, coeff_expand (by positivity),
        if_neg, neg_zero, mul_zero, LinearMap.zero_apply]
      · rw [natDegree_expand]
        intro h
        have := Nat.dvd_sub (dvd_mul_left (p ^ (n + 1)) g.natDegree) h
        rw [tsub_tsub_cancel_of_le, Nat.dvd_one] at this
        · obtain rfl : g = minpoly K x := by simpa [this] using hg₂
          cases hx hg₁
        · rw [Nat.one_le_iff_ne_zero]
          have : g.natDegree ≠ 0 := fun e ↦ by
            have := congr(natDegree $hg₂)
            rw [natDegree_expand, e, zero_mul] at this
            exact (minpoly.natDegree_pos (IsIntegral.isIntegral x)).ne this
          positivity
      · exact (minpoly.natDegree_pos (IsIntegral.isIntegral x)).ne'

end NotIsSeparable

section DetNeZero

namespace Algebra

variable (A : Type u) {B : Type v} (C : Type z)
variable [CommRing A] [CommRing B] [Algebra A B] [CommRing C] [Algebra A C]

open Finset

/-- Given an `A`-algebra `B` and `b`, a `κ`-indexed family of elements of `B`, we define
`traceMatrix A b` as the matrix whose `(i j)`-th element is the trace of `b i * b j`. -/
noncomputable def traceMatrix (b : κ → B) : Matrix κ κ A :=
  of fun i j => traceForm A B (b i) (b j)

-- TODO: set as an equation lemma for `traceMatrix`, see https://github.com/leanprover-community/mathlib4/pull/3024
@[simp]
theorem traceMatrix_apply (b : κ → B) (i j) : traceMatrix A b i j = traceForm A B (b i) (b j) :=
  rfl

theorem traceMatrix_reindex {κ' : Type*} (b : Basis κ A B) (f : κ ≃ κ') :
    traceMatrix A (b.reindex f) = reindex f f (traceMatrix A b) := by ext (x y); simp

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
    Algebra.smul_mul_assoc]
  rw [mul_comm (b x), ← smul_def]
  ring_nf
  rw [mul_assoc]
  simp [mul_comm]

theorem traceMatrix_of_matrix_mulVec [Fintype κ] (b : κ → B) (P : Matrix κ κ A) :
    traceMatrix A (P.map (algebraMap A B) *ᵥ b) = P * traceMatrix A b * Pᵀ := by
  refine AddEquiv.injective (transposeAddEquiv κ κ A) ?_
  rw [transposeAddEquiv_apply, transposeAddEquiv_apply, ← vecMul_transpose, ← transpose_map,
    traceMatrix_of_matrix_vecMul, transpose_transpose]

theorem traceMatrix_of_basis [Fintype κ] [DecidableEq κ] (b : Basis κ A B) :
    traceMatrix A b = BilinForm.toMatrix b (traceForm A B) := by
  ext (i j)
  rw [traceMatrix_apply, traceForm_apply, traceForm_toMatrix]

theorem traceMatrix_of_basis_mulVec [Fintype ι] (b : Basis ι A B) (z : B) :
    traceMatrix A b *ᵥ b.equivFun z = fun i => trace A B (z * b i) := by
  ext i
  rw [← replicateCol_apply (ι := Fin 1) (traceMatrix A b *ᵥ b.equivFun z) i 0, replicateCol_mulVec,
    Matrix.mul_apply, traceMatrix]
  simp only [replicateCol_apply, traceForm_apply]
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

variable (A)

/-- `embeddingsMatrix A C b : Matrix κ (B →ₐ[A] C) C` is the matrix whose `(i, σ)` coefficient is
  `σ (b i)`. It is mostly useful for fields when `Fintype.card κ = finrank A B` and `C` is
  algebraically closed. -/
def embeddingsMatrix (b : κ → B) : Matrix κ (B →ₐ[A] C) C :=
  of fun i (σ : B →ₐ[A] C) => σ (b i)

-- TODO: set as an equation lemma for `embeddingsMatrix`, see https://github.com/leanprover-community/mathlib4/pull/3024
@[simp]
theorem embeddingsMatrix_apply (b : κ → B) (i) (σ : B →ₐ[A] C) :
    embeddingsMatrix A C b i σ = σ (b i) :=
  rfl

/-- `embeddingsMatrixReindex A C b e : Matrix κ κ C` is the matrix whose `(i, j)` coefficient
  is `σⱼ (b i)`, where `σⱼ : B →ₐ[A] C` is the embedding corresponding to `j : κ` given by a
  bijection `e : κ ≃ (B →ₐ[A] C)`. It is mostly useful for fields and `C` is algebraically closed.
  In this case, in presence of `h : Fintype.card κ = finrank A B`, one can take
  `e := equivOfCardEq ((AlgHom.card A B C).trans h.symm)`. -/
def embeddingsMatrixReindex (b : κ → B) (e : κ ≃ (B →ₐ[A] C)) :=
  reindex (Equiv.refl κ) e.symm (embeddingsMatrix A C b)

variable {A}

theorem embeddingsMatrixReindex_eq_vandermonde (pb : PowerBasis A B)
    (e : Fin pb.dim ≃ (B →ₐ[A] C)) :
    embeddingsMatrixReindex A C pb.basis e = (vandermonde fun i => e i pb.gen)ᵀ := by
  ext i j
  simp [embeddingsMatrixReindex, embeddingsMatrix]

section Field

variable (K) (E : Type z) [Field E]
variable [Algebra K E]
variable [Module.Finite K L] [Algebra.IsSeparable K L] [IsAlgClosed E]
variable (b : κ → L) (pb : PowerBasis K L)

theorem traceMatrix_eq_embeddingsMatrix_mul_trans : (traceMatrix K b).map (algebraMap K E) =
    embeddingsMatrix K E b * (embeddingsMatrix K E b)ᵀ := by
  ext (i j); simp [trace_eq_sum_embeddings, embeddingsMatrix, Matrix.mul_apply]

theorem traceMatrix_eq_embeddingsMatrixReindex_mul_trans [Fintype κ] (e : κ ≃ (L →ₐ[K] E)) :
    (traceMatrix K b).map (algebraMap K E) =
      embeddingsMatrixReindex K E b e * (embeddingsMatrixReindex K E b e)ᵀ := by
  rw [traceMatrix_eq_embeddingsMatrix_mul_trans, embeddingsMatrixReindex, reindex_apply,
    transpose_submatrix, ← submatrix_mul_transpose_submatrix, ← Equiv.coe_refl, Equiv.refl_symm]

end Field

end Algebra

open Algebra

variable (pb : PowerBasis K L)

theorem det_traceMatrix_ne_zero' [Algebra.IsSeparable K L] : det (traceMatrix K pb.basis) ≠ 0 := by
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

theorem det_traceForm_ne_zero [Algebra.IsSeparable K L] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K L) :
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

variable (K L)

/-- Let $L/K$ be a finite extension of fields. If $L/K$ is separable,
then `traceForm` is nondegenerate. -/
@[stacks 0BIL "(1) => (3)"]
theorem traceForm_nondegenerate [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    (traceForm K L).Nondegenerate :=
  BilinForm.nondegenerate_of_det_ne_zero (traceForm K L) _
    (det_traceForm_ne_zero (Module.finBasis K L))

@[stacks 0BIL]
theorem traceForm_nondegenerate_tfae [FiniteDimensional K L] :
    [Algebra.IsSeparable K L, Algebra.trace K L ≠ 0, (traceForm K L).Nondegenerate].TFAE := by
  tfae_have 1 → 3 := fun _ ↦ traceForm_nondegenerate K L
  tfae_have 3 → 2 := fun H₁ H₂ ↦ H₁.ne_zero (by ext; simp [H₂])
  tfae_have 2 → 1 := not_imp_comm.mp Algebra.trace_eq_zero_of_not_isSeparable
  tfae_finish

theorem Algebra.trace_ne_zero [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    Algebra.trace K L ≠ 0 :=
  ((traceForm_nondegenerate_tfae K L).out 0 1).mp ‹_›

theorem Algebra.trace_surjective [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    Function.Surjective (Algebra.trace K L) := by
  rw [← LinearMap.range_eq_top]
  apply (IsSimpleOrder.eq_bot_or_eq_top (α := Ideal K) _).resolve_left
  rw [LinearMap.range_eq_bot]
  exact Algebra.trace_ne_zero K L

end DetNeZero

section isNilpotent

namespace Algebra

/-- The trace of a nilpotent element is nilpotent. -/
lemma isNilpotent_trace_of_isNilpotent {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {x : S}
    (hx : IsNilpotent x) : IsNilpotent (trace R S x) :=
  LinearMap.isNilpotent_trace_of_isNilpotent (hx.map (lmul R S))

@[deprecated (since := "2025-10-21")] alias trace_isNilpotent_of_isNilpotent :=
  isNilpotent_trace_of_isNilpotent

end Algebra

end isNilpotent

section Basis

open Algebra

variable [FiniteDimensional K L] [Algebra.IsSeparable K L] [Finite ι] [DecidableEq ι]
  (b : Basis ι K L)

/--
The dual basis of a basis under the trace form in a finite separable extension.
-/
noncomputable def Module.Basis.traceDual :
    Basis ι K L :=
  (traceForm K L).dualBasis (traceForm_nondegenerate K L) b

theorem Module.Basis.traceDual_def :
    b.traceDual = (traceForm K L).dualBasis (traceForm_nondegenerate K L) b := rfl

@[simp]
theorem Module.Basis.traceDual_repr_apply (x : L) (i : ι) :
    (b.traceDual).repr x i = (traceForm K L x) (b i) :=
  (traceForm K L).dualBasis_repr_apply _ b _ i

@[simp]
theorem Module.Basis.trace_traceDual_mul (i j : ι) :
    trace K L ((b.traceDual i) * (b j)) = if j = i then 1 else 0 :=
  (traceForm K L).apply_dualBasis_left _ _ i j

@[simp]
theorem Module.Basis.trace_mul_traceDual (i j : ι) :
    trace K L ((b i) * (b.traceDual j)) = if i = j then 1 else 0 :=
  (traceForm K L).apply_dualBasis_right _ (traceForm_isSymm K) _ i j

@[simp]
theorem Module.Basis.traceDual_traceDual :
    b.traceDual.traceDual = b :=
  (traceForm K L).dualBasis_dualBasis _ (traceForm_isSymm K) _

variable (K L)

theorem Module.Basis.traceDual_involutive :
    Function.Involutive (Basis.traceDual : Basis ι K L → Basis ι K L) :=
  (traceForm K L).dualBasis_involutive _ (traceForm_isSymm K)

theorem Module.Basis.traceDual_injective :
    Function.Injective (Basis.traceDual : Basis ι K L → Basis ι K L) :=
  (traceForm K L).dualBasis_injective _ (traceForm_isSymm K)

variable {K L b}

@[simp]
theorem Module.Basis.traceDual_inj {b' : Basis ι K L} :
    b.traceDual = b'.traceDual ↔ b = b' :=
  (traceDual_injective K L).eq_iff

/--
A family of vectors `v` is the dual for the trace of the basis `b` if and only if
`∀ i j, Tr(v i * b j) = δ_ij`.
-/
@[simp]
theorem Module.Basis.traceDual_eq_iff {v : ι → L} :
    b.traceDual = v ↔ ∀ i j, traceForm K L (v i) (b j) = if j = i then 1 else 0 :=
  (traceForm K L).dualBasis_eq_iff (traceForm_nondegenerate K L) b v

/--
The dual basis of a powerbasis `{1, x, x²...}` under the trace form is `aᵢ / f'(x)`,
with `f` being the minimal polynomial of `x` and `f / (X - x) = ∑ aᵢxⁱ`.
-/
lemma Module.Basis.traceDual_powerBasis_eq (pb : PowerBasis K L) (i) :
    pb.basis.traceDual i =
      (minpolyDiv K pb.gen).coeff i / aeval pb.gen (derivative <| minpoly K pb.gen) := by
  revert i
  rw [← funext_iff, Basis.traceDual_eq_iff]
  intro i j
  apply (algebraMap K (AlgebraicClosure K)).injective
  have := congr_arg (coeff · i) (sum_smul_minpolyDiv_eq_X_pow (AlgebraicClosure K)
    pb.adjoin_gen_eq_top (r := j) (pb.finrank.symm ▸ j.prop))
  simp only [Polynomial.map_smul, map_div₀, map_pow, RingHom.coe_coe, finset_sum_coeff, coeff_smul,
    coeff_map, smul_eq_mul, coeff_X_pow, ← Fin.ext_iff, @eq_comm _ i] at this
  rw [PowerBasis.coe_basis]
  simp only [traceForm_apply, MonoidWithZeroHom.map_ite_one_zero]
  rw [← this, trace_eq_sum_embeddings (E := AlgebraicClosure K)]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [map_mul, map_div₀, map_pow]
  ring

@[deprecated (since := "2025-06-25")] alias traceForm_dualBasis_powerBasis_eq :=
  Module.Basis.traceDual_powerBasis_eq

end Basis
