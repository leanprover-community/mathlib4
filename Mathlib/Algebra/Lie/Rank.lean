/-
Copyright (c) 2024 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Data.MvPolynomial.Monad
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ

/-!
# Rank of a Lie algebra and regular elements

Let `L` be a Lie algebra over a nontrivial commutative ring `R`,
and assume that `L` is finite free as `R`-module.
Then the coefficients of the characteristic polynomial of `ad R L x` are polynomial in `x`.
The *rank* of `L` is the smallest `n` for which the `n`-th coefficient is not the zero polynomial.

Continuing to write `n` for the rank of `L`, an element `x` of `L` is *regular*
if the `n`-th coefficient of the characteristic polynomial of `ad R L x` is non-zero.

## Main declarations

* `LieAlgebra.rank R L` is the rank of a Lie algebra `L` over a commutative ring `R`.
* `LieAlgebra.IsRegular R x` is the predicate that an element `x` of a Lie algebra `L` is regular.

## References

* [barnes1967]: "On Cartan subalgebras of Lie algebras" by D.W. Barnes.

-/

open scoped BigOperators

lemma MvPolynomial.totalDegree_monomial_le
    {R σ : Type*} [CommSemiring R] [Fintype σ] (m : σ →₀ ℕ) (r : R) :
    (monomial m r).totalDegree ≤ m.sum fun _ ↦ id := by
  if hr : r = 0 then
    simp only [hr, map_zero, totalDegree_zero, zero_le]
  else
    rw [totalDegree_monomial _ hr]
    exact le_rfl

section Basis

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]

open scoped Matrix

-- move to Mathlib.LinearAlgebra.Matrix.ToLin
@[simps! repr_apply repr_symm_apply]
noncomputable
def Basis.end (b : Basis ι R M) : Basis (ι × ι) R (Module.End R M) :=
  (Matrix.stdBasis R ι ι).map (LinearMap.toMatrix b b).symm

-- move to Mathlib.LinearAlgebra.Matrix.ToLin
lemma Basis.end_apply (b : Basis ι R M) (ij : ι × ι) :
    (b.end ij) = (Matrix.toLin b b) (Matrix.stdBasis R ι ι ij) := by
  erw [end_repr_symm_apply, Finsupp.total_single, one_smul]

-- move to Mathlib.LinearAlgebra.Matrix.ToLin
lemma Basis.end_apply_apply (b : Basis ι R M) (ij : ι × ι) (k : ι) :
    (b.end ij) (b k) = if ij.2 = k then b ij.1 else 0 := by
  rcases ij with ⟨i, j⟩
  rw [end_apply, Matrix.stdBasis_eq_stdBasisMatrix, Matrix.toLin_self]
  dsimp only [Matrix.stdBasisMatrix]
  simp_rw [ite_smul, one_smul, zero_smul, ite_and, Finset.sum_ite_eq, Finset.mem_univ, if_true]


open Algebra.TensorProduct LinearMap in
lemma Basis.baseChange_end (A : Type*) [CommRing A] [Algebra R A] (b : Basis ι R M) (ij : ι × ι) :
    baseChange A (b.end ij) = (basis A b).end ij := by
  apply (basis A b).ext
  intro k
  conv_lhs => simp only [basis_apply, baseChange_tmul]
  simp_rw [end_apply_apply, basis_apply]
  split <;> simp only [TensorProduct.tmul_zero]

#find_home! Basis.baseChange_end

end Basis

namespace LinearMap

variable (R A M : Type*) [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup M] [Module R M]

open Module
open scoped TensorProduct

noncomputable
def TensorProductEndₗ : A ⊗[R] (End R M) →ₗ[A] End A (A ⊗[R] M) :=
  TensorProduct.AlgebraTensorModule.lift <|
  { toFun := fun a ↦ a • baseChangeHom R A M M
    map_add' := by simp only [add_smul, forall_true_iff]
    map_smul' := by simp only [smul_assoc, RingHom.id_apply, forall_true_iff] }

noncomputable
def TensorProductEnd : A ⊗[R] (End R M) →ₐ[A] End A (A ⊗[R] M) :=
  Algebra.TensorProduct.algHomOfLinearMapTensorProduct
    (TensorProductEndₗ R A M)
    (fun a b f g ↦ by
      apply LinearMap.ext
      intro x
      simp only [TensorProductEndₗ, mul_comm a b, mul_eq_comp,
        TensorProduct.AlgebraTensorModule.lift_apply, TensorProduct.lift.tmul, coe_restrictScalars,
        coe_mk, AddHom.coe_mk, mul_smul, smul_apply, baseChangeHom_apply, baseChange_comp,
        comp_apply, Algebra.mul_smul_comm, Algebra.smul_mul_assoc])
    (by
      apply LinearMap.ext
      intro x
      simp only [TensorProductEndₗ, TensorProduct.AlgebraTensorModule.lift_apply,
        TensorProduct.lift.tmul, coe_restrictScalars, coe_mk, AddHom.coe_mk, one_smul,
        baseChangeHom_apply, baseChange_eq_ltensor, one_apply]
      erw [lTensor_id, LinearMap.id_apply])

end LinearMap

namespace Matrix

variable {m n o R S : Type*}
variable [Fintype n] [Fintype o] [CommSemiring R] [CommSemiring S]

open MvPolynomial

noncomputable
def toMvPolynomial (M : Matrix m n R) (i : m) : MvPolynomial n R :=
  ∑ j, monomial (.single j 1) (M i j)

lemma toMvPolynomial_eval_eq_apply (M : Matrix m n R) (i : m) (c : n → R) :
    eval c (M.toMvPolynomial i) = (M *ᵥ c) i := by
  simp only [toMvPolynomial, map_sum, eval_monomial, pow_zero, Finsupp.prod_single_index, pow_one,
    mulVec, dotProduct]

lemma toMvPolynomial_map (f : R →+* S) (M : Matrix m n R) (i : m) :
    (M.map f).toMvPolynomial i = MvPolynomial.map f (M.toMvPolynomial i) := by
  simp only [toMvPolynomial, map_apply, map_sum, map_monomial]

lemma toMvPolynomial_isHomogeneous (M : Matrix m n R) (i : m) :
    (M.toMvPolynomial i).IsHomogeneous 1 := by
  apply MvPolynomial.IsHomogeneous.sum
  rintro j -
  apply MvPolynomial.isHomogeneous_monomial _ _ _
  rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, Finsupp.single_eq_same]

lemma toMvPolynomial_totalDegree_le (M : Matrix m n R) (i : m) :
    (M.toMvPolynomial i).totalDegree ≤ 1 := by
  apply (toMvPolynomial_isHomogeneous _ _).totalDegree_le

@[simp]
lemma toMvPolynomial_constantCoeff (M : Matrix m n R) (i : m) :
    constantCoeff (M.toMvPolynomial i) = 0 := by
  simp only [toMvPolynomial, ← C_mul_X_eq_monomial, map_sum, _root_.map_mul, constantCoeff_X,
    mul_zero, Finset.sum_const_zero]

@[simp]
lemma toMvPolynomial_zero (i : m) : (0 : Matrix m n R).toMvPolynomial i = 0 := by
  simp only [toMvPolynomial, zero_apply, map_zero, Finset.sum_const_zero]

lemma toMvPolynomial_add (M N : Matrix m n R) (i : m) :
    (M + N).toMvPolynomial i = M.toMvPolynomial i + N.toMvPolynomial i := by
  simp only [toMvPolynomial, add_apply, map_add, Finset.sum_add_distrib]

lemma toMvPolynomial_mul (M : Matrix m n R) (N : Matrix n o R) (i : m) :
    (M * N).toMvPolynomial i = bind₁ N.toMvPolynomial (M.toMvPolynomial i) := by
  simp only [toMvPolynomial, mul_apply, map_sum, Finset.sum_comm (γ := o), bind₁, aeval,
    AlgHom.coe_mk, coe_eval₂Hom, eval₂_monomial, algebraMap_apply, Algebra.id.map_eq_id,
    RingHom.id_apply, C_apply, pow_zero, Finsupp.prod_single_index, pow_one, Finset.mul_sum,
    monomial_mul, zero_add]

end Matrix

namespace LinearMap

variable {R M₁ M₂ M₃ ι₁ ι₂ ι₃ : Type*}
variable [CommRing R] [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
variable [Module R M₁] [Module R M₂] [Module R M₃]
variable [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
variable [DecidableEq ι₁] [DecidableEq ι₂] [DecidableEq ι₃]
variable (b₁ : Basis ι₁ R M₁) (b₂ : Basis ι₂ R M₂) (b₃ : Basis ι₃ R M₃)

open MvPolynomial

noncomputable
def toMvPolynomial (f : M₁ →ₗ[R] M₂) (i : ι₂) :
    MvPolynomial ι₁ R :=
  (toMatrix b₁ b₂ f).toMvPolynomial i

lemma toMvPolynomial_eval_eq_apply (f : M₁ →ₗ[R] M₂) (i : ι₂) (c : ι₁ →₀ R) :
    eval c (f.toMvPolynomial b₁ b₂ i) = b₂.repr (f (b₁.repr.symm c)) i := by
  rw [toMvPolynomial, Matrix.toMvPolynomial_eval_eq_apply,
    ← LinearMap.toMatrix_mulVec_repr b₁ b₂, LinearEquiv.apply_symm_apply]

open Algebra.TensorProduct in
lemma toMvPolynomial_baseChange (f : M₁ →ₗ[R] M₂) (i : ι₂) (A : Type*) [CommRing A] [Algebra R A] :
    (f.baseChange A).toMvPolynomial (basis A b₁) (basis A b₂) i =
      MvPolynomial.map (algebraMap R A) (f.toMvPolynomial b₁ b₂ i) := by
  simp only [toMvPolynomial, toMatrix_baseChange, Matrix.toMvPolynomial_map]

lemma toMvPolynomial_isHomogeneous (f : M₁ →ₗ[R] M₂) (i : ι₂) :
    (f.toMvPolynomial b₁ b₂ i).IsHomogeneous 1 :=
  Matrix.toMvPolynomial_isHomogeneous _ _

lemma toMvPolynomial_totalDegree_le (f : M₁ →ₗ[R] M₂) (i : ι₂) :
    (f.toMvPolynomial b₁ b₂ i).totalDegree ≤ 1 :=
  Matrix.toMvPolynomial_totalDegree_le _ _

@[simp]
lemma toMvPolynomial_constantCoeff (f : M₁ →ₗ[R] M₂) (i : ι₂) :
    constantCoeff (f.toMvPolynomial b₁ b₂ i) = 0 :=
  Matrix.toMvPolynomial_constantCoeff _ _

@[simp]
lemma toMvPolynomial_zero (i : ι₂) : (0 : M₁ →ₗ[R] M₂).toMvPolynomial b₁ b₂ i = 0 := by
  simp only [toMvPolynomial, map_zero, Matrix.toMvPolynomial_zero]

lemma toMvPolynomial_add (f g : M₁ →ₗ[R] M₂) (i : ι₂) :
    (f + g).toMvPolynomial b₁ b₂ i = f.toMvPolynomial b₁ b₂ i + g.toMvPolynomial b₁ b₂ i := by
  simp only [toMvPolynomial, map_add, Matrix.toMvPolynomial_add]

lemma toMvPolynomial_comp (g : M₂ →ₗ[R] M₃) (f : M₁ →ₗ[R] M₂) (i : ι₃) :
    (g ∘ₗ f).toMvPolynomial b₁ b₃ i =
      bind₁ (f.toMvPolynomial b₁ b₂) (g.toMvPolynomial b₂ b₃ i) := by
  simp only [toMvPolynomial, toMatrix_comp b₁ b₂ b₃, Matrix.toMvPolynomial_mul]
  rfl

end LinearMap

variable {R L M n ι ιM : Type*}

section LinearAlgebra

variable [CommRing R] [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M]
variable (φ : L →ₗ[R] Module.End R M)
variable [Fintype ι] [Fintype ιM] [DecidableEq ι]

namespace LinearMap

-- local notation "φ" => LieModule.toEndomorphism R L M

section basic

variable [DecidableEq ιM] (b : Basis ι R L) (bₘ : Basis ιM R M)

open LieModule LinearMap MvPolynomial in
/-- Let `M` be a Lie module of a Lie algebra `L` over `R`,
and let `b` be a basis of `L` and `bₘ` a basis of `M`.
Then `lieMatrixPoly b bₘ (i,j)` is the polynomial that evaluates on elements `x` of `L`
to the `(i,j)`-th coefficient of the matrix representation of `⁅x, ·⁆` acting on `M`. -/
noncomputable
def lieMatrixPoly (ij : ιM × ιM) : MvPolynomial ι R :=
  φ.toMvPolynomial b bₘ.end ij

open LinearMap in
@[simp]
lemma lieMatrixPoly_eval_eq_toMatrix (ij : ιM × ιM) (c : ι →₀ R) :
    MvPolynomial.eval c (lieMatrixPoly φ b bₘ ij) =
      (toMatrix bₘ bₘ <| φ (b.repr.symm c)) ij.1 ij.2 := by
  simp only [lieMatrixPoly, toMvPolynomial_eval_eq_apply]
  rfl

lemma lieMatrixPoly_eval_eq_lie (ij : ιM × ιM) (c : ι →₀ R) :
    MvPolynomial.eval c (lieMatrixPoly φ b bₘ ij) = bₘ.repr (φ (b.repr.symm c) (bₘ ij.2)) ij.1 := by
  rw [lieMatrixPoly_eval_eq_toMatrix, Basis.repr_symm_apply, LinearMap.toMatrix_apply]

open Matrix

/-- Let `M` be a Lie module of a Lie algebra `L` over `R`,
and let `b` be a basis of `L` and `bₘ` a basis of `M`.
Then `lieCharpoly φ b bₘ` is the polynomial that evaluates on elements `x` of `L`
to the characteristic polynomial of `⁅x, ·⁆` acting on `M`. -/
noncomputable
def lieCharpoly : Polynomial (MvPolynomial ι R) :=
  (charpoly.univ R ιM).map <| MvPolynomial.bind₁ (lieMatrixPoly φ b bₘ)

lemma lieCharpoly_monic : (lieCharpoly φ b bₘ).Monic :=
  (charpoly.univ_monic R ιM).map _

lemma lieCharpoly_ne_zero [Nontrivial R] : (lieCharpoly φ b bₘ) ≠ 0 :=
  (lieCharpoly_monic _ _ _).ne_zero

@[simp]
lemma lieCharpoly_natDegree [Nontrivial R] : (lieCharpoly φ b bₘ).natDegree = Fintype.card ιM := by
  rw [lieCharpoly, (charpoly.univ_monic _ _).natDegree_map, charpoly.univ_natDegree]

lemma lieCharpoly_coeff_isHomogeneous (i j : ℕ) (hij : i + j = Fintype.card ιM) :
    ((lieCharpoly φ b bₘ).coeff i).IsHomogeneous j := by
  rw [lieCharpoly, Polynomial.coeff_map, ← one_mul j]
  apply (charpoly.univ_coeff_isHomogeneous _ _ _ _ hij).eval₂
  · exact fun r ↦ MvPolynomial.isHomogeneous_C _ _
  · exact LinearMap.toMvPolynomial_isHomogeneous _ _ _

open Algebra.TensorProduct MvPolynomial in
lemma lieCharpoly_baseChange (A : Type*) [CommRing A] [Algebra R A] :
    lieCharpoly (TensorProductEndₗ _ _ _ ∘ₗ φ.baseChange A) (basis A b) (basis A bₘ) =
      (lieCharpoly φ b bₘ).map (MvPolynomial.map (algebraMap R A)) := by
  simp only [lieCharpoly]
  rw [← charpoly.univ_map_map _ (algebraMap R A)]
  simp only [Polynomial.map_map]
  congr 1
  apply ringHom_ext
  · intro r
    simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, map_C, bind₁_C_right]
  · rintro ij
    simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, map_X,
      bind₁_X_right, lieMatrixPoly]
    classical
    rw [toMvPolynomial_comp _ (basis A (Basis.end bₘ)), ← toMvPolynomial_baseChange]
    suffices toMvPolynomial (basis A bₘ.end) (basis A bₘ).end (TensorProductEndₗ R A M) ij = X ij by
      rw [this, bind₁_X_right]
    simp only [toMvPolynomial, Matrix.toMvPolynomial]
    suffices ∀ kl,
      (toMatrix (basis A (Basis.end bₘ)) (Basis.end (basis A bₘ))) (TensorProductEndₗ R A M) ij kl =
      if kl = ij then 1 else 0 by
      rw [Finset.sum_eq_single ij]
      · rw [this, if_pos rfl, X]
      · rintro kl - H
        rw [this, if_neg H, map_zero]
      · intro h
        exact (h (Finset.mem_univ _)).elim
    intro kl
    rw [toMatrix_apply, TensorProductEndₗ, TensorProduct.AlgebraTensorModule.lift_apply,
      basis_apply, TensorProduct.lift.tmul, coe_restrictScalars]
    dsimp only [coe_mk, AddHom.coe_mk, smul_apply, baseChangeHom_apply]
    rw [one_smul, Basis.baseChange_end, Basis.repr_self_apply]

open LinearMap in
lemma lieCharpoly_map_eq_toMatrix_charpoly (x : L) :
    (lieCharpoly φ b bₘ).map (MvPolynomial.eval (b.repr x)) = (toMatrix bₘ bₘ (φ x)).charpoly := by
  erw [lieCharpoly, Polynomial.map_map, MvPolynomial.comp_eval₂Hom, charpoly.univ_map_eval₂Hom]
  congr
  ext
  rw [of_apply, Function.curry_apply, lieMatrixPoly_eval_eq_toMatrix, LinearEquiv.symm_apply_apply]

lemma lieCharpoly_map_eq_toMatrix_charpoly' [Module.Finite R M] [Module.Free R M]
    (x : L) :
    (lieCharpoly φ b bₘ).map (MvPolynomial.eval (b.repr x)) = (φ x).charpoly := by
  nontriviality R
  rw [lieCharpoly_map_eq_toMatrix_charpoly, LinearMap.charpoly_toMatrix]

lemma lieCharpoly_map_eq_toMatrix_charpoly'' [Module.Finite R M] [Module.Free R M]
    (x : ι → R) :
    (lieCharpoly φ b bₘ).map (MvPolynomial.eval x) =
      (φ (b.repr.symm (Finsupp.equivFunOnFinite.symm x))).charpoly := by
  rw [← lieCharpoly_map_eq_toMatrix_charpoly' φ b bₘ, Basis.repr_symm_apply, Basis.repr_total]
  rfl

open Algebra.TensorProduct TensorProduct in
lemma lieCharpoly_map_eq_toMatrix_charpoly'''
    (A : Type*) [CommRing A] [Algebra R A] [Module.Finite A (A ⊗[R] M)] [Module.Free A (A ⊗[R] M)]
    (x : ι → A) :
    (lieCharpoly φ b bₘ).map (MvPolynomial.aeval x).toRingHom =
      LinearMap.charpoly ((TensorProductEndₗ R A M).comp (baseChange A φ)
        ((basis A b).repr.symm (Finsupp.equivFunOnFinite.symm x))) := by
  rw [← lieCharpoly_map_eq_toMatrix_charpoly''
    (TensorProductEndₗ R A M ∘ₗ baseChange A φ) _ (basis A bₘ),
    lieCharpoly_baseChange, Polynomial.map_map]
  congr
  symm
  apply DFunLike.ext
  intro
  apply MvPolynomial.eval_map

open Algebra.TensorProduct MvPolynomial in
lemma lieCharpoly_basisIndep (bₘ' : Basis ιM R M) :
    lieCharpoly φ b bₘ = lieCharpoly φ b bₘ' := by
  let f : Polynomial (MvPolynomial ι R) → Polynomial (MvPolynomial ι R) :=
    Polynomial.map (MvPolynomial.aeval X).toRingHom
  have hf : Function.Injective f := by
    simp only [f, aeval_X_left, AlgHom.toRingHom_eq_coe, AlgHom.id_toRingHom, Polynomial.map_id]
    exact Polynomial.map_injective (RingHom.id _) Function.injective_id
  apply hf
  dsimp only
  let _h1 : Module.Finite (MvPolynomial ι R) (TensorProduct R (MvPolynomial ι R) M) :=
    Module.Finite.of_basis (basis (MvPolynomial ι R) bₘ)
  let _h2 : Module.Free (MvPolynomial ι R) (TensorProduct R (MvPolynomial ι R) M) :=
    Module.Free.of_basis (basis (MvPolynomial ι R) bₘ)
  simp only [f, lieCharpoly_map_eq_toMatrix_charpoly''', lieCharpoly_map_eq_toMatrix_charpoly''']

open LinearMap in
lemma lieCharpoly_eval_eq_toMatrix_charpoly_coeff (x : L) (i : ℕ) :
    MvPolynomial.eval (b.repr x) ((lieCharpoly φ b bₘ).coeff i) =
      (toMatrix bₘ bₘ (φ x)).charpoly.coeff i := by
  simp [← lieCharpoly_map_eq_toMatrix_charpoly φ b bₘ x]

end basic

section module

variable [DecidableEq ιM] [Nontrivial R] [Module.Finite R M] [Module.Free R M]
variable (b : Basis ι R L) (bₘ : Basis ιM R M) (x : L)

@[simp]
lemma lieCharpoly_map :
    (lieCharpoly φ b bₘ).map (MvPolynomial.eval (b.repr x)) = (φ x).charpoly := by
  rw [lieCharpoly_map_eq_toMatrix_charpoly, LinearMap.charpoly_toMatrix]

@[simp]
lemma lieCharpoly_eval (i : ℕ) :
    MvPolynomial.eval (b.repr x) ((lieCharpoly φ b bₘ).coeff i) = (φ x).charpoly.coeff i := by
  rw [lieCharpoly_eval_eq_toMatrix_charpoly_coeff, LinearMap.charpoly_toMatrix]

end module

end LinearMap

end LinearAlgebra

namespace LieAlgebra

variable [CommRing R] [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
variable [DecidableEq ι] [DecidableEq ιM] [Nontrivial R] [Module.Finite R L] [Module.Free R L]
variable [Fintype ι]
variable (b : Basis ι R L) (bₘ : Basis ιM R L) (x : L)

open LieAlgebra LinearMap Module.Free

variable (R L)

open Matrix.charpoly Classical in
/--
Let `L` be a Lie algebra over a nontrivial commutative ring `R`,
and assume that `L` is finite free as `R`-module.
Then the coefficients of the characteristic polynomial of `ad R L x` are polynomial in `x`.
The *rank* of `L` is the smallest `n` for which the `n`-th coefficient is not the zero polynomial.
-/
noncomputable
def rank : ℕ := (lieCharpoly (ad R L) (chooseBasis R L) (chooseBasis R L)).natTrailingDegree

-- TODO: generalize to arbitrary basis, by carefully tracing all the polynomials
lemma lieCharpoly_coeff_rank_ne_zero :
    (lieCharpoly (ad R L) (chooseBasis R L) (chooseBasis R L)).coeff (rank R L) ≠ 0 := by
  apply Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr
  apply lieCharpoly_ne_zero

open FiniteDimensional
lemma rank_le_card : rank R L ≤ Fintype.card ι := by
  apply Polynomial.natTrailingDegree_le_of_ne_zero
  rw [← FiniteDimensional.finrank_eq_card_basis b, finrank_eq_card_chooseBasisIndex,
      ← lieCharpoly_natDegree _ (chooseBasis R L) (chooseBasis R L), Polynomial.coeff_natDegree,
    (lieCharpoly_monic _ _ _).leadingCoeff]
  apply one_ne_zero

open FiniteDimensional
lemma rank_le_finrank : rank R L ≤ finrank R L := by
  simpa only [finrank_eq_card_chooseBasisIndex R L] using rank_le_card R L (chooseBasis R L)

variable {L}

lemma rank_le_natTrailingDegree_charpoly_ad :
    rank R L ≤ (ad R L x).charpoly.natTrailingDegree := by
  apply Polynomial.natTrailingDegree_le_of_ne_zero
  intro h
  apply_fun (MvPolynomial.eval ((chooseBasis R L).repr x)) at h
  rw [lieCharpoly_eval, map_zero] at h
  apply Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr _ h
  apply (LinearMap.charpoly_monic _).ne_zero

/-- Let `x` be an element of a Lie algebra `L` over `R`, and write `n` for `rank R L`.
Then `x` is *regular*
if the `n`-th coefficient of the characteristic polynomial of `ad R L x` is non-zero. -/
def IsRegular (x : L) : Prop :=
  Polynomial.coeff (ad R L x).charpoly (rank R L) ≠ 0

lemma isRegular_def :
    IsRegular R x = (Polynomial.coeff (ad R L x).charpoly (rank R L) ≠ 0) := rfl

lemma isRegular_iff_coeff_lieCharpoly_rank_ne_zero :
    IsRegular R x ↔
    MvPolynomial.eval ((chooseBasis R L).repr x)
      ((lieCharpoly (ad R L) (chooseBasis R L) (chooseBasis R L)).coeff (rank R L)) ≠ 0 := by
  rw [IsRegular, lieCharpoly_eval]
  rfl

lemma isRegular_iff_natTrailingDegree_charpoly_eq_rank :
    IsRegular R x ↔ (ad R L x).charpoly.natTrailingDegree = rank R L := by
  rw [isRegular_def]
  constructor
  · intro h
    exact le_antisymm
      (Polynomial.natTrailingDegree_le_of_ne_zero h)
      (rank_le_natTrailingDegree_charpoly_ad R x)
  · intro h
    rw [← h]
    apply Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr
    apply (LinearMap.charpoly_monic _).ne_zero

section IsDomain

variable (L)
variable [IsDomain R]

open Module.Free

open Cardinal FiniteDimensional MvPolynomial in
lemma exists_isRegular_of_finrank_le_card (h : finrank R L ≤ #R) :
    ∃ x : L, IsRegular R x := by
  let b := chooseBasis R L
  let n := Fintype.card (ChooseBasisIndex R L)
  have aux : ((lieCharpoly (ad R L) b b).coeff (rank R L)).IsHomogeneous (n - rank R L) :=
    lieCharpoly_coeff_isHomogeneous _ b b (rank R L) (n - rank R L) (by simp [rank_le_card _ _ b])
  obtain ⟨x, hx⟩ : ∃ r, eval r ((lieCharpoly _ b b).coeff (rank R L)) ≠ 0 := by
    by_contra! h₀
    apply lieCharpoly_coeff_rank_ne_zero R L
    apply aux.eq_zero_of_forall_eval_eq_zero_of_le_card h₀ (le_trans _ h)
    simp only [finrank_eq_card_chooseBasisIndex, Nat.cast_le, Nat.sub_le]
  let c := Finsupp.equivFunOnFinite.symm x
  use b.repr.symm c
  rwa [isRegular_iff_coeff_lieCharpoly_rank_ne_zero, LinearEquiv.apply_symm_apply]

lemma exists_isRegular [Infinite R] : ∃ x : L, IsRegular R x := by
  apply exists_isRegular_of_finrank_le_card
  exact (Cardinal.nat_lt_aleph0 _).le.trans <| Cardinal.infinite_iff.mp ‹Infinite R›

end IsDomain

end LieAlgebra
