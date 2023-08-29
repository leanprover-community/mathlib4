/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Trace
import Mathlib.RingTheory.Norm

#align_import ring_theory.discriminant from "leanprover-community/mathlib"@"3e068ece210655b7b9a9477c3aff38a492400aa1"

/-!
# Discriminant of a family of vectors

Given an `A`-algebra `B` and `b`, an `ι`-indexed family of elements of `B`, we define the
*discriminant* of `b` as the determinant of the matrix whose `(i j)`-th element is the trace of
`b i * b j`.

## Main definition

* `Algebra.discr A b` : the discriminant of `b : ι → B`.

## Main results

* `Algebra.discr_zero_of_not_linearIndependent` : if `b` is not linear independent, then
  `Algebra.discr A b = 0`.
* `Algebra.discr_of_matrix_vecMul` and `Algebra.discr_of_matrix_mulVec` : formulas relating
  `Algebra.discr A ι b` with `Algebra.discr A ((P.map (algebraMap A B)).vecMul b)` and
  `Algebra.discr A ((P.map (algebraMap A B)).mulVec b)`.
* `Algebra.discr_not_zero_of_basis` : over a field, if `b` is a basis, then
  `Algebra.discr K b ≠ 0`.
* `Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two` : if `L/K` is a field extension and
  `b : ι → L`, then `discr K b` is the square of the determinant of the matrix whose `(i, j)`
  coefficient is `σⱼ (b i)`, where `σⱼ : L →ₐ[K] E` is the embedding in an algebraically closed
  field `E` corresponding to `j : ι` via a bijection `e : ι ≃ (L →ₐ[K] E)`.
* `Algebra.discr_powerBasis_eq_prod` : the discriminant of a power basis.
* `Algebra.discr_isIntegral` : if `K` and `L` are fields and `IsScalarTower R K L`, if
  `b : ι → L` satisfies ` ∀ i, IsIntegral R (b i)`, then `IsIntegral R (discr K b)`.
* `Algebra.discr_mul_isIntegral_mem_adjoin` : let `K` be the fraction field of an integrally
  closed domain `R` and let `L` be a finite separable extension of `K`. Let `B : PowerBasis K L`
  be such that `IsIntegral R B.gen`. Then for all, `z : L` we have
  `(discr K B.basis) • z ∈ adjoin R ({B.gen} : set L)`.

## Implementation details

Our definition works for any `A`-algebra `B`, but note that if `B` is not free as an `A`-module,
then `trace A B = 0` by definition, so `discr A b = 0` for any `b`.
-/


universe u v w z

open scoped Matrix BigOperators

open Matrix FiniteDimensional Fintype Polynomial Finset IntermediateField

namespace Algebra

variable (A : Type u) {B : Type v} (C : Type z) {ι : Type w} [DecidableEq ι]

variable [CommRing A] [CommRing B] [Algebra A B] [CommRing C] [Algebra A C]

section Discr

/-- Given an `A`-algebra `B` and `b`, an `ι`-indexed family of elements of `B`, we define
`discr A ι b` as the determinant of `traceMatrix A ι b`. -/
-- Porting note: using `[DecidableEq ι]` instead of `by classical...` did not work in
-- mathlib3.
noncomputable def discr (A : Type u) {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Fintype ι] (b : ι → B) := (traceMatrix A b).det
#align algebra.discr Algebra.discr

theorem discr_def [Fintype ι] (b : ι → B) : discr A b = (traceMatrix A b).det := by
-- Porting note: `unfold discr` was not necessary. `rfl` still does not work.
  unfold discr
  -- ⊢ det (traceMatrix A b) = det (traceMatrix A b)
  convert rfl
  -- 🎉 no goals


#align algebra.discr_def Algebra.discr_def

variable {ι' : Type*} [Fintype ι'] [Fintype ι] [DecidableEq ι']

section Basic

@[simp]
theorem discr_reindex (b : Basis ι A B) (f : ι ≃ ι') : discr A (b ∘ ⇑f.symm) = discr A b := by
  classical rw [← Basis.coe_reindex, discr_def, traceMatrix_reindex, det_reindex_self, ← discr_def]
  -- 🎉 no goals
#align algebra.discr_reindex Algebra.discr_reindex

/-- If `b` is not linear independent, then `Algebra.discr A b = 0`. -/
theorem discr_zero_of_not_linearIndependent [IsDomain A] {b : ι → B}
    (hli : ¬LinearIndependent A b) : discr A b = 0 := by
  classical
  obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.1 hli
  have : (traceMatrix A b).mulVec g = 0 := by
    ext i
    have : ∀ j, (trace A B) (b i * b j) * g j = (trace A B) (g j • b j * b i) := by
      intro j;
      simp [mul_comm]
    simp only [mulVec, dotProduct, traceMatrix_apply, Pi.zero_apply, traceForm_apply, fun j =>
      this j, ← LinearMap.map_sum, ← sum_mul, hg, zero_mul, LinearMap.map_zero]
  by_contra h
  rw [discr_def] at h
  simp [Matrix.eq_zero_of_mulVec_eq_zero h this] at hi
#align algebra.discr_zero_of_not_linear_independent Algebra.discr_zero_of_not_linearIndependent

variable {A}

/-- Relation between `Algebra.discr A ι b` and
`Algebra.discr A ((P.map (algebraMap A B)).vecMul b)`. -/
theorem discr_of_matrix_vecMul (b : ι → B) (P : Matrix ι ι A) :
    discr A ((P.map (algebraMap A B)).vecMul b) = P.det ^ 2 * discr A b := by
  rw [discr_def, traceMatrix_of_matrix_vecMul, det_mul, det_mul, det_transpose, mul_comm, ←
    mul_assoc, discr_def, pow_two]
#align algebra.discr_of_matrix_vec_mul Algebra.discr_of_matrix_vecMul

/-- Relation between `Algebra.discr A ι b` and
`Algebra.discr A ((P.map (algebraMap A B)).mulVec b)`. -/
theorem discr_of_matrix_mulVec (b : ι → B) (P : Matrix ι ι A) :
    discr A ((P.map (algebraMap A B)).mulVec b) = P.det ^ 2 * discr A b := by
  rw [discr_def, traceMatrix_of_matrix_mulVec, det_mul, det_mul, det_transpose, mul_comm, ←
    mul_assoc, discr_def, pow_two]
#align algebra.discr_of_matrix_mul_vec Algebra.discr_of_matrix_mulVec

end Basic

section Field

variable (K : Type u) {L : Type v} (E : Type z) [Field K] [Field L] [Field E]

variable [Algebra K L] [Algebra K E]

variable [Module.Finite K L] [IsAlgClosed E]

/-- Over a field, if `b` is a basis, then `Algebra.discr K b ≠ 0`. -/
theorem discr_not_zero_of_basis [IsSeparable K L] (b : Basis ι K L) :
    discr K b ≠ 0 := by
  cases isEmpty_or_nonempty ι
  -- ⊢ discr K ↑b ≠ 0
-- Porting note: the following proof was `simp [discr]`. Variations like `exact this` do not work.
  · have : det (traceMatrix K ↑b) ≠ 0 := by simp
    -- ⊢ discr K ↑b ≠ 0
    unfold discr
    -- ⊢ det (traceMatrix K ↑b) ≠ 0
    convert this
    -- 🎉 no goals
  · have :=
      span_eq_top_of_linearIndependent_of_card_eq_finrank b.linearIndependent
        (finrank_eq_card_basis b).symm
    classical
    rw [discr_def, traceMatrix]
    simp_rw [← Basis.mk_apply b.linearIndependent this.ge]
    rw [← traceMatrix, traceMatrix_of_basis, ← BilinForm.nondegenerate_iff_det_ne_zero]
    exact traceForm_nondegenerate _ _
#align algebra.discr_not_zero_of_basis Algebra.discr_not_zero_of_basis

/-- Over a field, if `b` is a basis, then `Algebra.discr K b` is a unit. -/
theorem discr_isUnit_of_basis [IsSeparable K L] (b : Basis ι K L) : IsUnit (discr K b) :=
  IsUnit.mk0 _ (discr_not_zero_of_basis _ _)
#align algebra.discr_is_unit_of_basis Algebra.discr_isUnit_of_basis

variable (b : ι → L) (pb : PowerBasis K L)

/-- If `L/K` is a field extension and `b : ι → L`, then `discr K b` is the square of the
determinant of the matrix whose `(i, j)` coefficient is `σⱼ (b i)`, where `σⱼ : L →ₐ[K] E` is the
embedding in an algebraically closed field `E` corresponding to `j : ι` via a bijection
`e : ι ≃ (L →ₐ[K] E)`. -/
theorem discr_eq_det_embeddingsMatrixReindex_pow_two [IsSeparable K L] (e : ι ≃ (L →ₐ[K] E)) :
    algebraMap K E (discr K b) = (embeddingsMatrixReindex K E b e).det ^ 2 := by
  rw [discr_def, RingHom.map_det, RingHom.mapMatrix_apply,
    traceMatrix_eq_embeddingsMatrixReindex_mul_trans, det_mul, det_transpose, pow_two]
#align algebra.discr_eq_det_embeddings_matrix_reindex_pow_two Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two

/-- The discriminant of a power basis. -/
theorem discr_powerBasis_eq_prod (e : Fin pb.dim ≃ (L →ₐ[K] E)) [IsSeparable K L] :
    algebraMap K E (discr K pb.basis) =
      ∏ i : Fin pb.dim, ∏ j in Ioi i, (e j pb.gen - e i pb.gen) ^ 2 := by
  rw [discr_eq_det_embeddingsMatrixReindex_pow_two K E pb.basis e,
    embeddingsMatrixReindex_eq_vandermonde, det_transpose, det_vandermonde, ← prod_pow]
  congr; ext i
  -- ⊢ (fun x => (∏ j in Ioi x, (↑(↑e j) pb.gen - ↑(↑e x) pb.gen)) ^ 2) = fun i =>  …
         -- ⊢ (∏ j in Ioi i, (↑(↑e j) pb.gen - ↑(↑e i) pb.gen)) ^ 2 = ∏ j in Ioi i, (↑(↑e  …
  rw [← prod_pow]
  -- 🎉 no goals
#align algebra.discr_power_basis_eq_prod Algebra.discr_powerBasis_eq_prod

/-- A variation of `Algebra.discr_powerBasis_eq_prod`. -/
theorem discr_powerBasis_eq_prod' [IsSeparable K L] (e : Fin pb.dim ≃ (L →ₐ[K] E)) :
    algebraMap K E (discr K pb.basis) =
      ∏ i : Fin pb.dim, ∏ j in Ioi i, -((e j pb.gen - e i pb.gen) * (e i pb.gen - e j pb.gen)) := by
  rw [discr_powerBasis_eq_prod _ _ _ e]
  -- ⊢ ∏ i : Fin pb.dim, ∏ j in Ioi i, (↑(↑e j) pb.gen - ↑(↑e i) pb.gen) ^ 2 = ∏ i  …
  congr; ext i; congr; ext j
  -- ⊢ (fun i => ∏ j in Ioi i, (↑(↑e j) pb.gen - ↑(↑e i) pb.gen) ^ 2) = fun i => ∏  …
         -- ⊢ ∏ j in Ioi i, (↑(↑e j) pb.gen - ↑(↑e i) pb.gen) ^ 2 = ∏ j in Ioi i, -((↑(↑e  …
                -- ⊢ (fun j => (↑(↑e j) pb.gen - ↑(↑e i) pb.gen) ^ 2) = fun j => -((↑(↑e j) pb.ge …
                       -- ⊢ (↑(↑e j) pb.gen - ↑(↑e i) pb.gen) ^ 2 = -((↑(↑e j) pb.gen - ↑(↑e i) pb.gen)  …
  ring
  -- 🎉 no goals
#align algebra.discr_power_basis_eq_prod' Algebra.discr_powerBasis_eq_prod'

local notation "n" => finrank K L

/-- A variation of `Algebra.discr_powerBasis_eq_prod`. -/
theorem discr_powerBasis_eq_prod'' [IsSeparable K L] (e : Fin pb.dim ≃ (L →ₐ[K] E)) :
    algebraMap K E (discr K pb.basis) =
      (-1) ^ (n * (n - 1) / 2) *
        ∏ i : Fin pb.dim, ∏ j in Ioi i, (e j pb.gen - e i pb.gen) * (e i pb.gen - e j pb.gen) := by
  rw [discr_powerBasis_eq_prod' _ _ _ e]
  -- ⊢ ∏ i : Fin pb.dim, ∏ j in Ioi i, -((↑(↑e j) pb.gen - ↑(↑e i) pb.gen) * (↑(↑e  …
  simp_rw [fun i j => neg_eq_neg_one_mul ((e j pb.gen - e i pb.gen) * (e i pb.gen - e j pb.gen)),
    prod_mul_distrib]
  congr
  -- ⊢ ∏ x : Fin pb.dim, ∏ x in Ioi x, -1 = (-1) ^ (n * (n - 1) / 2)
  simp only [prod_pow_eq_pow_sum, prod_const]
  -- ⊢ (-1) ^ ∑ x : Fin pb.dim, Finset.card (Ioi x) = (-1) ^ (n * (n - 1) / 2)
  congr
  -- ⊢ ∑ x : Fin pb.dim, Finset.card (Ioi x) = n * (n - 1) / 2
  rw [← @Nat.cast_inj ℚ, Nat.cast_sum]
  -- ⊢ ∑ x : Fin pb.dim, ↑(Finset.card (Ioi x)) = ↑(n * (n - 1) / 2)
  have : ∀ x : Fin pb.dim, ↑x + 1 ≤ pb.dim := by simp [Nat.succ_le_iff, Fin.is_lt]
  -- ⊢ ∑ x : Fin pb.dim, ↑(Finset.card (Ioi x)) = ↑(n * (n - 1) / 2)
  simp_rw [Fin.card_Ioi, Nat.sub_sub, add_comm 1]
  -- ⊢ ∑ x : Fin pb.dim, ↑(pb.dim - (↑x + 1)) = ↑(n * (n - 1) / 2)
  simp only [Nat.cast_sub, this, Finset.card_fin, nsmul_eq_mul, sum_const, sum_sub_distrib,
    Nat.cast_add, Nat.cast_one, sum_add_distrib, mul_one]
  rw [← Nat.cast_sum, ← @Finset.sum_range ℕ _ pb.dim fun i => i, sum_range_id]
  -- ⊢ ↑pb.dim * ↑pb.dim - (↑(pb.dim * (pb.dim - 1) / 2) + ↑pb.dim) = ↑(n * (n - 1) …
  have hn : n = pb.dim := by
    rw [← AlgHom.card K L E, ← Fintype.card_fin pb.dim]
    exact card_congr (Equiv.symm e)
  have h₂ : 2 ∣ pb.dim * (pb.dim - 1) := even_iff_two_dvd.1 (Nat.even_mul_self_pred _)
  -- ⊢ ↑pb.dim * ↑pb.dim - (↑(pb.dim * (pb.dim - 1) / 2) + ↑pb.dim) = ↑(n * (n - 1) …
  have hne : ((2 : ℕ) : ℚ) ≠ 0 := by simp
  -- ⊢ ↑pb.dim * ↑pb.dim - (↑(pb.dim * (pb.dim - 1) / 2) + ↑pb.dim) = ↑(n * (n - 1) …
  have hle : 1 ≤ pb.dim := by
    rw [← hn, Nat.one_le_iff_ne_zero, ← zero_lt_iff, FiniteDimensional.finrank_pos_iff]
    infer_instance
  rw [hn, Nat.cast_div h₂ hne, Nat.cast_mul, Nat.cast_sub hle]
  -- ⊢ ↑pb.dim * ↑pb.dim - (↑pb.dim * (↑pb.dim - ↑1) / ↑2 + ↑pb.dim) = ↑pb.dim * (↑ …
  field_simp
  -- ⊢ ↑pb.dim * ↑pb.dim * 2 - (↑pb.dim * (↑pb.dim - 1) + ↑pb.dim * 2) = ↑pb.dim *  …
  ring
  -- 🎉 no goals
#align algebra.discr_power_basis_eq_prod'' Algebra.discr_powerBasis_eq_prod''

/-- Formula for the discriminant of a power basis using the norm of the field extension. -/
-- Porting note: `(minpoly K pb.gen).derivative` does not work anymore.
theorem discr_powerBasis_eq_norm [IsSeparable K L] :
    discr K pb.basis =
      (-1) ^ (n * (n - 1) / 2) *
      norm K (aeval pb.gen (derivative (R := K) (minpoly K pb.gen))) := by
  let E := AlgebraicClosure L
  -- ⊢ discr K ↑pb.basis = (-1) ^ (n * (n - 1) / 2) * ↑(norm K) (↑(aeval pb.gen) (↑ …
  letI := fun a b : E => Classical.propDecidable (Eq a b)
  -- ⊢ discr K ↑pb.basis = (-1) ^ (n * (n - 1) / 2) * ↑(norm K) (↑(aeval pb.gen) (↑ …
  have e : Fin pb.dim ≃ (L →ₐ[K] E) := by
    refine' equivOfCardEq _
    rw [Fintype.card_fin, AlgHom.card]
    exact (PowerBasis.finrank pb).symm
  have hnodup : ((minpoly K pb.gen).map (algebraMap K E)).roots.Nodup :=
    nodup_roots (Separable.map (IsSeparable.separable K pb.gen))
  have hroots : ∀ σ : L →ₐ[K] E, σ pb.gen ∈ ((minpoly K pb.gen).map (algebraMap K E)).roots := by
    intro σ
    rw [mem_roots, IsRoot.def, eval_map, ← aeval_def, aeval_algHom_apply]
    repeat' simp [minpoly.ne_zero (IsSeparable.isIntegral K pb.gen)]
  apply (algebraMap K E).injective
  -- ⊢ ↑(algebraMap K E) (discr K ↑pb.basis) = ↑(algebraMap K E) ((-1) ^ (n * (n -  …
  rw [RingHom.map_mul, RingHom.map_pow, RingHom.map_neg, RingHom.map_one,
    discr_powerBasis_eq_prod'' _ _ _ e]
  congr
  -- ⊢ ∏ i : Fin pb.dim, ∏ j in Ioi i, (↑(↑e j) pb.gen - ↑(↑e i) pb.gen) * (↑(↑e i) …
  rw [norm_eq_prod_embeddings, prod_prod_Ioi_mul_eq_prod_prod_off_diag]
  -- ⊢ ∏ i : Fin pb.dim, ∏ j in {i}ᶜ, (↑(↑e j) pb.gen - ↑(↑e i) pb.gen) = ∏ σ : (fu …
  conv_rhs =>
    congr
    rfl
    ext σ
    rw [← aeval_algHom_apply,
      aeval_root_derivative_of_splits (minpoly.monic (IsSeparable.isIntegral K pb.gen))
        (IsAlgClosed.splits_codomain _) (hroots σ),
      ← Finset.prod_mk _ (hnodup.erase _)]
  rw [prod_sigma', prod_sigma']
  -- ⊢ ∏ x in Finset.sigma univ fun i => {i}ᶜ, (↑(↑e x.snd) pb.gen - ↑(↑e x.fst) pb …
  refine'
    prod_bij (fun i _ => ⟨e i.2, e i.1 pb.gen⟩) (fun i hi => _) (fun i _ => by simp )
      (fun i j hi hj hij => _) fun σ hσ => _
  · simp only [true_and_iff, Finset.mem_mk, mem_univ, mem_sigma]
    -- ⊢ ↑(↑e i.fst) pb.gen ∈ Multiset.erase (roots (Polynomial.map (algebraMap K (Al …
    rw [Multiset.mem_erase_of_ne fun h => ?_]
    -- ⊢ ↑(↑e i.fst) pb.gen ∈ roots (Polynomial.map (algebraMap K (AlgebraicClosure L …
    · exact hroots _
      -- 🎉 no goals
-- Porting note: `@mem_compl` was not necessary.
    · simp only [true_and_iff, mem_univ, Ne.def, mem_sigma, @mem_compl _ _ _ (_),
        mem_singleton] at hi
      rw [← PowerBasis.liftEquiv_apply_coe, ← PowerBasis.liftEquiv_apply_coe] at h
      -- ⊢ False
      exact hi (e.injective <| pb.liftEquiv.injective <| Subtype.eq h.symm)
      -- 🎉 no goals
  · simp only [Sigma.mk.inj_iff, EmbeddingLike.apply_eq_iff_eq, heq_eq_eq] at hij
    -- ⊢ i = j
    have h := hij.2
    -- ⊢ i = j
    rw [← PowerBasis.liftEquiv_apply_coe, ← PowerBasis.liftEquiv_apply_coe] at h
    -- ⊢ i = j
    refine' Sigma.eq (Equiv.injective e (Equiv.injective _ (Subtype.eq h))) (by simp [hij.1])
    -- 🎉 no goals
  · simp only [true_and_iff, Finset.mem_mk, mem_univ, mem_sigma] at hσ ⊢
    -- ⊢ ∃ a h, σ = { fst := ↑e a.snd, snd := ↑(↑e a.fst) pb.gen }
    simp only [Sigma.exists, exists_prop, mem_compl, mem_singleton, Ne.def]
    -- ⊢ ∃ a b, b ∈ {a}ᶜ ∧ σ = { fst := ↑e b, snd := ↑(↑e a) pb.gen }
    refine' ⟨e.symm (PowerBasis.lift pb σ.2 _), e.symm σ.1, ⟨_, Sigma.eq _ _⟩⟩
    · rw [aeval_def, eval₂_eq_eval_map, ← IsRoot.def, ← mem_roots]
      -- ⊢ σ.snd ∈ roots (Polynomial.map (algebraMap K E) (minpoly K pb.gen))
      · exact Multiset.erase_subset _ _ hσ
        -- 🎉 no goals
      · simp [minpoly.ne_zero (IsSeparable.isIntegral K pb.gen)]
        -- 🎉 no goals
-- Porting note: the `simp only` was not needed.
    · simp only [@mem_compl _ _ _ (_), mem_singleton]
      -- ⊢ ¬↑e.symm σ.fst = ↑e.symm (PowerBasis.lift pb σ.snd (_ : ↑(aeval σ.snd) (minp …
      intro h
      -- ⊢ False
      replace h := AlgHom.congr_fun (Equiv.injective _ h) pb.gen
      -- ⊢ False
      rw [PowerBasis.lift_gen] at h
      -- ⊢ False
      rw [← h] at hσ
      -- ⊢ False
      exact hnodup.not_mem_erase hσ
      -- 🎉 no goals
    all_goals simp
    -- 🎉 no goals
#align algebra.discr_power_basis_eq_norm Algebra.discr_powerBasis_eq_norm

section Integral

variable {R : Type z} [CommRing R] [Algebra R K] [Algebra R L] [IsScalarTower R K L]

/-- If `K` and `L` are fields and `IsScalarTower R K L`, and `b : ι → L` satisfies
` ∀ i, IsIntegral R (b i)`, then `IsIntegral R (discr K b)`. -/
theorem discr_isIntegral {b : ι → L} (h : ∀ i, IsIntegral R (b i)) : IsIntegral R (discr K b) := by
  classical
  rw [discr_def]
  exact IsIntegral.det fun i j => isIntegral_trace (isIntegral_mul (h i) (h j))
#align algebra.discr_is_integral Algebra.discr_isIntegral

/-- If `b` and `b'` are `ℚ`-bases of a number field `K` such that
`∀ i j, IsIntegral ℤ (b.toMatrix b' i j)` and `∀ i j, IsIntegral ℤ (b'.toMatrix b i j)` then
`discr ℚ b = discr ℚ b'`. -/
theorem discr_eq_discr_of_toMatrix_coeff_isIntegral [NumberField K] {b : Basis ι ℚ K}
    {b' : Basis ι' ℚ K} (h : ∀ i j, IsIntegral ℤ (b.toMatrix b' i j))
    (h' : ∀ i j, IsIntegral ℤ (b'.toMatrix b i j)) : discr ℚ b = discr ℚ b' := by
  replace h' : ∀ i j, IsIntegral ℤ (b'.toMatrix (b.reindex (b.indexEquiv b')) i j)
  -- ⊢ ∀ (i j : ι'), IsIntegral ℤ (Basis.toMatrix b' (↑(Basis.reindex b (Basis.inde …
  · intro i j
    -- ⊢ IsIntegral ℤ (Basis.toMatrix b' (↑(Basis.reindex b (Basis.indexEquiv b b'))) …
    convert h' i ((b.indexEquiv b').symm j)
    -- ⊢ Basis.toMatrix b' (↑(Basis.reindex b (Basis.indexEquiv b b'))) i j = Basis.t …
-- Porting note: `simp; rfl` was `simpa`.
    simp; rfl
    -- ⊢ Basis.toMatrix b' (↑b ∘ ↑(Basis.indexEquiv b b').symm) i j = Basis.toMatrix  …
          -- 🎉 no goals
  classical
  rw [← (b.reindex (b.indexEquiv b')).toMatrix_map_vecMul b', discr_of_matrix_vecMul,
    ← one_mul (discr ℚ b), Basis.coe_reindex, discr_reindex]
  congr
  have hint : IsIntegral ℤ ((b.reindex (b.indexEquiv b')).toMatrix b').det :=
    IsIntegral.det fun i j => h _ _
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  have hunit : IsUnit r := by
    have : IsIntegral ℤ (b'.toMatrix (b.reindex (b.indexEquiv b'))).det :=
      IsIntegral.det fun i j => h' _ _
    obtain ⟨r', hr'⟩ := IsIntegrallyClosed.isIntegral_iff.1 this
    refine' isUnit_iff_exists_inv.2 ⟨r', _⟩
    suffices algebraMap ℤ ℚ (r * r') = 1 by
      rw [← RingHom.map_one (algebraMap ℤ ℚ)] at this
      exact (IsFractionRing.injective ℤ ℚ) this
    rw [RingHom.map_mul, hr, hr', ← det_mul, Basis.toMatrix_mul_toMatrix_flip, det_one]
  rw [← RingHom.map_one (algebraMap ℤ ℚ), ← hr]
  cases' Int.isUnit_iff.1 hunit with hp hm
  · simp [hp]
  · simp [hm]
#align algebra.discr_eq_discr_of_to_matrix_coeff_is_integral Algebra.discr_eq_discr_of_toMatrix_coeff_isIntegral

/-- Let `K` be the fraction field of an integrally closed domain `R` and let `L` be a finite
separable extension of `K`. Let `B : PowerBasis K L` be such that `IsIntegral R B.gen`.
Then for all, `z : L` that are integral over `R`, we have
`(discr K B.basis) • z ∈ adjoin R ({B.gen} : set L)`. -/
theorem discr_mul_isIntegral_mem_adjoin [IsDomain R] [IsSeparable K L] [IsIntegrallyClosed R]
    [IsFractionRing R K] {B : PowerBasis K L} (hint : IsIntegral R B.gen) {z : L}
    (hz : IsIntegral R z) : discr K B.basis • z ∈ adjoin R ({B.gen} : Set L) := by
  have hinv : IsUnit (traceMatrix K B.basis).det := by
    simpa [← discr_def] using discr_isUnit_of_basis _ B.basis
  have H :
    (traceMatrix K B.basis).det • (traceMatrix K B.basis).mulVec (B.basis.equivFun z) =
      (traceMatrix K B.basis).det • fun i => trace K L (z * B.basis i) :=
    by congr; exact traceMatrix_of_basis_mulVec _ _
  have cramer := mulVec_cramer (traceMatrix K B.basis) fun i => trace K L (z * B.basis i)
  -- ⊢ discr K ↑B.basis • z ∈ adjoin R {B.gen}
  suffices ∀ i, ((traceMatrix K B.basis).det • B.basis.equivFun z) i ∈ (⊥ : Subalgebra R K) by
    rw [← B.basis.sum_repr z, Finset.smul_sum]
    refine' Subalgebra.sum_mem _ fun i _ => _
    replace this := this i
    rw [← discr_def, Pi.smul_apply, mem_bot] at this
    obtain ⟨r, hr⟩ := this
    rw [Basis.equivFun_apply] at hr
    rw [← smul_assoc, ← hr, algebraMap_smul]
    refine' Subalgebra.smul_mem _ _ _
    rw [B.basis_eq_pow i]
    refine' Subalgebra.pow_mem _ (subset_adjoin (Set.mem_singleton _)) _
  intro i
  -- ⊢ (det (traceMatrix K ↑B.basis) • ↑(Basis.equivFun B.basis) z) i ∈ ⊥
  rw [← H, ← mulVec_smul] at cramer
  -- ⊢ (det (traceMatrix K ↑B.basis) • ↑(Basis.equivFun B.basis) z) i ∈ ⊥
  replace cramer := congr_arg (mulVec (traceMatrix K B.basis)⁻¹) cramer
  -- ⊢ (det (traceMatrix K ↑B.basis) • ↑(Basis.equivFun B.basis) z) i ∈ ⊥
  rw [mulVec_mulVec, nonsing_inv_mul _ hinv, mulVec_mulVec, nonsing_inv_mul _ hinv, one_mulVec,
    one_mulVec] at cramer
  rw [← congr_fun cramer i, cramer_apply, det_apply]
  -- ⊢ ∑ σ : Equiv.Perm (Fin B.dim), ↑Equiv.Perm.sign σ • ∏ i_1 : Fin B.dim, update …
  refine'
    Subalgebra.sum_mem _ fun σ _ => Subalgebra.zsmul_mem _ (Subalgebra.prod_mem _ fun j _ => _) _
  by_cases hji : j = i
  -- ⊢ updateColumn (traceMatrix K ↑B.basis) i (fun i => ↑(trace K L) (z * ↑B.basis …
  · simp only [updateColumn_apply, hji, eq_self_iff_true, PowerBasis.coe_basis]
    -- ⊢ (if True then ↑(trace K L) (z * B.gen ^ ↑(↑σ i)) else traceMatrix K (fun i = …
    exact
      mem_bot.2
        (IsIntegrallyClosed.isIntegral_iff.1 <|
          isIntegral_trace <| isIntegral_mul hz <| IsIntegral.pow hint _)
  · simp only [updateColumn_apply, hji, PowerBasis.coe_basis]
    -- ⊢ (if False then ↑(trace K L) (z * B.gen ^ ↑(↑σ j)) else traceMatrix K (fun i  …
    exact
      mem_bot.2
        (IsIntegrallyClosed.isIntegral_iff.1 <|
          isIntegral_trace <| isIntegral_mul (IsIntegral.pow hint _) (IsIntegral.pow hint _))
#align algebra.discr_mul_is_integral_mem_adjoin Algebra.discr_mul_isIntegral_mem_adjoin

end Integral

end Field

section Int

/-- Two (finite) ℤ-bases have the same discriminant. -/
theorem discr_eq_discr [Fintype ι] (b : Basis ι ℤ A) (b' : Basis ι ℤ A) :
    Algebra.discr ℤ b = Algebra.discr ℤ b' := by
  convert Algebra.discr_of_matrix_vecMul b' (b'.toMatrix b)
  -- ⊢ ↑b = vecMul (↑b') (Matrix.map (Basis.toMatrix b' ↑b) ↑(algebraMap ℤ A))
  · rw [Basis.toMatrix_map_vecMul]
    -- 🎉 no goals
  · suffices IsUnit (b'.toMatrix b).det by
      rw [Int.isUnit_iff, ← sq_eq_one_iff] at this
      rw [this, one_mul]
    rw [← LinearMap.toMatrix_id_eq_basis_toMatrix b b']
    -- ⊢ IsUnit (det (↑(LinearMap.toMatrix b b') LinearMap.id))
    exact LinearEquiv.isUnit_det (LinearEquiv.refl ℤ A) b b'
    -- 🎉 no goals

end Int

end Discr

end Algebra
