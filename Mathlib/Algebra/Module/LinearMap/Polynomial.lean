/-
Copyright (c) 2024 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ

/-!
# Characteristic polynomials of linear families of endomorphisms

The coefficients of the characteristic polynomials of a linear family of endomorphisms
are homogeneous polynomials in the parameters.
This result is used in Lie theory
to establish the existence of regular elements and Cartan subalgebras,
and ultimately a well-defined notion of rank for Lie algebras.

In this file we prove this result about characteristic polynomials.
Let `L` and `M` be modules over a nontrivial commutative ring `R`,
and let `φ : L →ₗ[R] Module.End R M` be a linear map.
Let `b` be a basis of `L`, indexed by `ι`.
Then we define a multivariate polynomial with variables indexed by `ι`
that evaluates on elements `x` of `L` to the characteristic polynomial of `φ x`.

## Main declarations

* `Matrix.toMvPolynomial M i`: the family of multivariate polynomials that evaluates on `c : n → R`
  to the dot product of the `i`-th row of `M` with `c`.
  `Matrix.toMvPolynomial M i` is the sum of the monomials `C (M i j) * X j`.
* `LinearMap.toMvPolynomial b₁ b₂ f`: a version of `Matrix.toMvPolynomial` for linear maps `f`
  with respect to bases `b₁` and `b₂` of the domain and codomain.
* `LinearMap.polyCharpoly`: the multivariate polynomial that evaluates on elements `x` of `L`
  to the characteristic polynomial of `φ x`.
* `LinearMap.polyCharpoly_map_eq_charpoly`: the evaluation of `polyCharpoly` on elements `x` of `L`
  is the characteristic polynomial of `φ x`.
* `LinearMap.polyCharpoly_coeff_isHomogeneous`: the coefficients of `polyCharpoly`
  are homogeneous polynomials in the parameters.
* `LinearMap.nilRank`: the smallest index at which `polyCharpoly` has a non-zero coefficient,
  which is independent of the choice of basis for `L`.
* `LinearMap.IsNilRegular`: an element `x` of `L` is *nil-regular* with respect to `φ`
  if the `n`-th coefficient of the characteristic polynomial of `φ x` is non-zero,
  where `n` denotes the nil-rank of `φ`.

## Implementation details

We show that `LinearMap.polyCharpoly` does not depend on the choice of basis of the target module.
This is done via `LinearMap.polyCharpoly_eq_polyCharpolyAux`
and `LinearMap.polyCharpolyAux_basisIndep`.
The latter is proven by considering
the base change of the `R`-linear map `φ : L →ₗ[R] End R M`
to the multivariate polynomial ring `MvPolynomial ι R`,
and showing that `polyCharpolyAux φ` is equal to the characteristic polynomial of this base change.
The proof concludes because characteristic polynomials are independent of the chosen basis.

## References

* [barnes1967]: "On Cartan subalgebras of Lie algebras" by D.W. Barnes.

-/

open scoped Matrix

namespace Matrix

variable {m n o R S : Type*}
variable [Fintype n] [Fintype o] [CommSemiring R] [CommSemiring S]

open MvPolynomial

/-- Let `M` be an `(m × n)`-matrix over `R`.
Then `Matrix.toMvPolynomial M` is the family (indexed by `i : m`)
of multivariate polynomials in `n` variables over `R` that evaluates on `c : n → R`
to the dot product of the `i`-th row of `M` with `c`:
`Matrix.toMvPolynomial M i` is the sum of the monomials `C (M i j) * X j`. -/
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
  apply MvPolynomial.isHomogeneous_monomial _ _
  rw [degree, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton,
    Finsupp.single_eq_same]

lemma toMvPolynomial_totalDegree_le (M : Matrix m n R) (i : m) :
    (M.toMvPolynomial i).totalDegree ≤ 1 := by
  apply (toMvPolynomial_isHomogeneous _ _).totalDegree_le

@[simp]
lemma toMvPolynomial_constantCoeff (M : Matrix m n R) (i : m) :
    constantCoeff (M.toMvPolynomial i) = 0 := by
  simp only [toMvPolynomial, ← C_mul_X_eq_monomial, map_sum, _root_.map_mul, constantCoeff_X,
    mul_zero, Finset.sum_const_zero]

@[simp]
lemma toMvPolynomial_zero : (0 : Matrix m n R).toMvPolynomial = 0 := by
  ext; simp only [toMvPolynomial, zero_apply, map_zero, Finset.sum_const_zero, Pi.zero_apply]

@[simp]
lemma toMvPolynomial_one [DecidableEq n] : (1 : Matrix n n R).toMvPolynomial = X := by
  ext i : 1
  rw [toMvPolynomial, Finset.sum_eq_single i]
  · simp only [one_apply_eq, ← C_mul_X_eq_monomial, C_1, one_mul]
  · rintro j - hj
    simp only [one_apply_ne hj.symm, map_zero]
  · intro h
    exact (h (Finset.mem_univ _)).elim

lemma toMvPolynomial_add (M N : Matrix m n R) :
    (M + N).toMvPolynomial = M.toMvPolynomial + N.toMvPolynomial := by
  ext i : 1
  simp only [toMvPolynomial, add_apply, map_add, Finset.sum_add_distrib, Pi.add_apply]

lemma toMvPolynomial_mul (M : Matrix m n R) (N : Matrix n o R) (i : m) :
    (M * N).toMvPolynomial i = bind₁ N.toMvPolynomial (M.toMvPolynomial i) := by
  simp only [toMvPolynomial, mul_apply, map_sum, Finset.sum_comm (γ := o), bind₁, aeval,
    AlgHom.coe_mk, coe_eval₂Hom, eval₂_monomial, algebraMap_apply, Algebra.id.map_eq_id,
    RingHom.id_apply, C_apply, pow_zero, Finsupp.prod_single_index, pow_one, Finset.mul_sum,
    monomial_mul, zero_add]

end Matrix

namespace LinearMap

open MvPolynomial

section

variable {R M₁ M₂ ι₁ ι₂ : Type*}
variable [CommRing R] [AddCommGroup M₁] [AddCommGroup M₂]
variable [Module R M₁] [Module R M₂]
variable [Fintype ι₁] [Finite ι₂]
variable [DecidableEq ι₁]
variable (b₁ : Basis ι₁ R M₁) (b₂ : Basis ι₂ R M₂)

/-- Let `f : M₁ →ₗ[R] M₂` be an `R`-linear map
between modules `M₁` and `M₂` with bases `b₁` and `b₂` respectively.
Then `LinearMap.toMvPolynomial b₁ b₂ f` is the family of multivariate polynomials over `R`
that evaluates on an element `x` of `M₁` (represented on the basis `b₁`)
to the element `f x` of `M₂` (represented on the basis `b₂`). -/
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
lemma toMvPolynomial_zero : (0 : M₁ →ₗ[R] M₂).toMvPolynomial b₁ b₂ = 0 := by
  unfold toMvPolynomial; simp only [map_zero, Matrix.toMvPolynomial_zero]

@[simp]
lemma toMvPolynomial_id : (id : M₁ →ₗ[R] M₁).toMvPolynomial b₁ b₁ = X := by
  unfold toMvPolynomial; simp only [toMatrix_id, Matrix.toMvPolynomial_one]

lemma toMvPolynomial_add (f g : M₁ →ₗ[R] M₂) :
    (f + g).toMvPolynomial b₁ b₂ = f.toMvPolynomial b₁ b₂ + g.toMvPolynomial b₁ b₂ := by
  unfold toMvPolynomial; simp only [map_add, Matrix.toMvPolynomial_add]

end

variable {R M₁ M₂ M₃ ι₁ ι₂ ι₃ : Type*}
variable [CommRing R] [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
variable [Module R M₁] [Module R M₂] [Module R M₃]
variable [Fintype ι₁] [Fintype ι₂] [Finite ι₃]
variable [DecidableEq ι₁] [DecidableEq ι₂]
variable (b₁ : Basis ι₁ R M₁) (b₂ : Basis ι₂ R M₂) (b₃ : Basis ι₃ R M₃)

lemma toMvPolynomial_comp (g : M₂ →ₗ[R] M₃) (f : M₁ →ₗ[R] M₂) (i : ι₃) :
    (g ∘ₗ f).toMvPolynomial b₁ b₃ i =
      bind₁ (f.toMvPolynomial b₁ b₂) (g.toMvPolynomial b₂ b₃ i) := by
  simp only [toMvPolynomial, toMatrix_comp b₁ b₂ b₃, Matrix.toMvPolynomial_mul]
  rfl

end LinearMap

variable {R L M n ι ι' ιM : Type*}
variable [CommRing R] [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M]
variable (φ : L →ₗ[R] Module.End R M)
variable [Fintype ι] [Fintype ι'] [Fintype ιM] [DecidableEq ι] [DecidableEq ι']

namespace LinearMap

section aux

variable [DecidableEq ιM] (b : Basis ι R L) (bₘ : Basis ιM R M)

open Matrix

/-- (Implementation detail, see `LinearMap.polyCharpoly`.)

Let `L` and `M` be finite free modules over `R`,
and let `φ : L →ₗ[R] Module.End R M` be a linear map.
Let `b` be a basis of `L` and `bₘ` a basis of `M`.
Then `LinearMap.polyCharpolyAux φ b bₘ` is the polynomial that evaluates on elements `x` of `L`
to the characteristic polynomial of `φ x` acting on `M`.

This definition does not depend on the choice of `bₘ`
(see `LinearMap.polyCharpolyAux_basisIndep`). -/
noncomputable
def polyCharpolyAux : Polynomial (MvPolynomial ι R) :=
  (charpoly.univ R ιM).map <| MvPolynomial.bind₁ (φ.toMvPolynomial b bₘ.end)

open Algebra.TensorProduct MvPolynomial in
lemma polyCharpolyAux_baseChange (A : Type*) [CommRing A] [Algebra R A] :
    polyCharpolyAux (tensorProduct _ _ _ _ ∘ₗ φ.baseChange A) (basis A b) (basis A bₘ) =
      (polyCharpolyAux φ b bₘ).map (MvPolynomial.map (algebraMap R A)) := by
  simp only [polyCharpolyAux]
  rw [← charpoly.univ_map_map _ (algebraMap R A)]
  simp only [Polynomial.map_map]
  congr 1
  apply ringHom_ext
  · intro r
    simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, map_C, bind₁_C_right]
  · rintro ij
    simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, map_X, bind₁_X_right]
    classical
    rw [toMvPolynomial_comp _ (basis A (Basis.end bₘ)), ← toMvPolynomial_baseChange]
    suffices toMvPolynomial (basis A bₘ.end) (basis A bₘ).end (tensorProduct R A M M) ij = X ij by
      rw [this, bind₁_X_right]
    simp only [toMvPolynomial, Matrix.toMvPolynomial]
    suffices ∀ kl,
        (toMatrix (basis A bₘ.end) (basis A bₘ).end) (tensorProduct R A M M) ij kl =
        if kl = ij then 1 else 0 by
      rw [Finset.sum_eq_single ij]
      · rw [this, if_pos rfl, X]
      · rintro kl - H
        rw [this, if_neg H, map_zero]
      · intro h
        exact (h (Finset.mem_univ _)).elim
    intro kl
    rw [toMatrix_apply, tensorProduct, TensorProduct.AlgebraTensorModule.lift_apply,
      basis_apply, TensorProduct.lift.tmul, coe_restrictScalars]
    dsimp only [coe_mk, AddHom.coe_mk, smul_apply, baseChangeHom_apply]
    rw [one_smul, Basis.baseChange_end, Basis.repr_self_apply]

open LinearMap in
lemma polyCharpolyAux_map_eq_toMatrix_charpoly (x : L) :
    (polyCharpolyAux φ b bₘ).map (MvPolynomial.eval (b.repr x)) =
      (toMatrix bₘ bₘ (φ x)).charpoly := by
  erw [polyCharpolyAux, Polynomial.map_map, MvPolynomial.comp_eval₂Hom, charpoly.univ_map_eval₂Hom]
  congr
  ext
  rw [of_apply, Function.curry_apply, toMvPolynomial_eval_eq_apply, LinearEquiv.symm_apply_apply]
  rfl

open LinearMap in
lemma polyCharpolyAux_eval_eq_toMatrix_charpoly_coeff (x : L) (i : ℕ) :
    MvPolynomial.eval (b.repr x) ((polyCharpolyAux φ b bₘ).coeff i) =
      (toMatrix bₘ bₘ (φ x)).charpoly.coeff i := by
  simp [← polyCharpolyAux_map_eq_toMatrix_charpoly φ b bₘ x]

@[simp]
lemma polyCharpolyAux_map_eq_charpoly [Module.Finite R M] [Module.Free R M]
    (x : L) :
    (polyCharpolyAux φ b bₘ).map (MvPolynomial.eval (b.repr x)) = (φ x).charpoly := by
  nontriviality R
  rw [polyCharpolyAux_map_eq_toMatrix_charpoly, LinearMap.charpoly_toMatrix]

@[simp]
lemma polyCharpolyAux_coeff_eval [Module.Finite R M] [Module.Free R M] (x : L) (i : ℕ) :
    MvPolynomial.eval (b.repr x) ((polyCharpolyAux φ b bₘ).coeff i) = (φ x).charpoly.coeff i := by
  nontriviality R
  rw [← polyCharpolyAux_map_eq_charpoly φ b bₘ x, Polynomial.coeff_map]

lemma polyCharpolyAux_map_eval [Module.Finite R M] [Module.Free R M]
    (x : ι → R) :
    (polyCharpolyAux φ b bₘ).map (MvPolynomial.eval x) =
      (φ (b.repr.symm (Finsupp.equivFunOnFinite.symm x))).charpoly := by
  simp only [← polyCharpolyAux_map_eq_charpoly φ b bₘ, LinearEquiv.apply_symm_apply,
    Finsupp.equivFunOnFinite, Equiv.coe_fn_symm_mk, Finsupp.coe_mk]

open Algebra.TensorProduct TensorProduct in
lemma polyCharpolyAux_map_aeval
    (A : Type*) [CommRing A] [Algebra R A] [Module.Finite A (A ⊗[R] M)] [Module.Free A (A ⊗[R] M)]
    (x : ι → A) :
    (polyCharpolyAux φ b bₘ).map (MvPolynomial.aeval x).toRingHom =
      LinearMap.charpoly ((tensorProduct R A M M).comp (baseChange A φ)
        ((basis A b).repr.symm (Finsupp.equivFunOnFinite.symm x))) := by
  rw [← polyCharpolyAux_map_eval (tensorProduct R A M M ∘ₗ baseChange A φ) _ (basis A bₘ),
    polyCharpolyAux_baseChange, Polynomial.map_map]
  congr
  exact DFunLike.ext _ _ fun f ↦ (MvPolynomial.eval_map (algebraMap R A) x f).symm

open Algebra.TensorProduct MvPolynomial in
/-- `LinearMap.polyCharpolyAux` is independent of the choice of basis of the target module.

Proof strategy:
1. Rewrite `polyCharpolyAux` as the (honest, ordinary) characteristic polynomial
   of the basechange of `φ` to the multivariate polynomial ring `MvPolynomial ι R`.
2. Use that the characteristic polynomial of a linear map is independent of the choice of basis.
   This independence result is used transitively via
   `LinearMap.polyCharpolyAux_map_aeval` and `LinearMap.polyCharpolyAux_map_eq_charpoly`. -/
lemma polyCharpolyAux_basisIndep {ιM' : Type*} [Fintype ιM'] [DecidableEq ιM']
    (bₘ' : Basis ιM' R M) :
    polyCharpolyAux φ b bₘ = polyCharpolyAux φ b bₘ' := by
  let f : Polynomial (MvPolynomial ι R) → Polynomial (MvPolynomial ι R) :=
    Polynomial.map (MvPolynomial.aeval X).toRingHom
  have hf : Function.Injective f := by
    simp only [f, aeval_X_left, AlgHom.toRingHom_eq_coe, AlgHom.id_toRingHom, Polynomial.map_id]
    exact Polynomial.map_injective (RingHom.id _) Function.injective_id
  apply hf
  let _h1 : Module.Finite (MvPolynomial ι R) (TensorProduct R (MvPolynomial ι R) M) :=
    Module.Finite.of_basis (basis (MvPolynomial ι R) bₘ)
  let _h2 : Module.Free (MvPolynomial ι R) (TensorProduct R (MvPolynomial ι R) M) :=
    Module.Free.of_basis (basis (MvPolynomial ι R) bₘ)
  simp only [f, polyCharpolyAux_map_aeval, polyCharpolyAux_map_aeval]

end aux

open FiniteDimensional Matrix

variable [Module.Free R M] [Module.Finite R M] (b : Basis ι R L)

/-- Let `L` and `M` be finite free modules over `R`,
and let `φ : L →ₗ[R] Module.End R M` be a linear family of endomorphisms.
Let `b` be a basis of `L` and `bₘ` a basis of `M`.
Then `LinearMap.polyCharpoly φ b` is the polynomial that evaluates on elements `x` of `L`
to the characteristic polynomial of `φ x` acting on `M`. -/
noncomputable
def polyCharpoly : Polynomial (MvPolynomial ι R) :=
  φ.polyCharpolyAux b (Module.Free.chooseBasis R M)

lemma polyCharpoly_eq_of_basis [DecidableEq ιM] (bₘ : Basis ιM R M) :
    polyCharpoly φ b =
    (charpoly.univ R ιM).map (MvPolynomial.bind₁ (φ.toMvPolynomial b bₘ.end)) := by
  rw [polyCharpoly, φ.polyCharpolyAux_basisIndep b (Module.Free.chooseBasis R M) bₘ,
    polyCharpolyAux]

lemma polyCharpoly_monic : (polyCharpoly φ b).Monic :=
  (charpoly.univ_monic R _).map _

lemma polyCharpoly_ne_zero [Nontrivial R] : (polyCharpoly φ b) ≠ 0 :=
  (polyCharpoly_monic _ _).ne_zero

@[simp]
lemma polyCharpoly_natDegree [Nontrivial R] :
    (polyCharpoly φ b).natDegree = finrank R M := by
  rw [polyCharpoly, polyCharpolyAux, (charpoly.univ_monic _ _).natDegree_map,
    charpoly.univ_natDegree, finrank_eq_card_chooseBasisIndex]

lemma polyCharpoly_coeff_isHomogeneous (i j : ℕ) (hij : i + j = finrank R M) [Nontrivial R] :
    ((polyCharpoly φ b).coeff i).IsHomogeneous j := by
  rw [finrank_eq_card_chooseBasisIndex] at hij
  rw [polyCharpoly, polyCharpolyAux, Polynomial.coeff_map, ← one_mul j]
  apply (charpoly.univ_coeff_isHomogeneous _ _ _ _ hij).eval₂
  · exact fun r ↦ MvPolynomial.isHomogeneous_C _ _
  · exact LinearMap.toMvPolynomial_isHomogeneous _ _ _

open Algebra.TensorProduct MvPolynomial in
lemma polyCharpoly_baseChange (A : Type*) [CommRing A] [Algebra R A] :
    polyCharpoly (tensorProduct _ _ _ _ ∘ₗ φ.baseChange A) (basis A b) =
      (polyCharpoly φ b).map (MvPolynomial.map (algebraMap R A)) := by
  unfold polyCharpoly
  rw [← φ.polyCharpolyAux_baseChange]
  apply polyCharpolyAux_basisIndep

@[simp]
lemma polyCharpoly_map_eq_charpoly (x : L) :
    (polyCharpoly φ b).map (MvPolynomial.eval (b.repr x)) = (φ x).charpoly := by
  rw [polyCharpoly, polyCharpolyAux_map_eq_charpoly]

@[simp]
lemma polyCharpoly_coeff_eval (x : L) (i : ℕ) :
    MvPolynomial.eval (b.repr x) ((polyCharpoly φ b).coeff i) = (φ x).charpoly.coeff i := by
  rw [polyCharpoly, polyCharpolyAux_coeff_eval]

lemma polyCharpoly_coeff_eq_zero_of_basis (b : Basis ι R L) (b' : Basis ι' R L) (k : ℕ)
    (H : (polyCharpoly φ b).coeff k = 0) :
    (polyCharpoly φ b').coeff k = 0 := by
  rw [polyCharpoly, polyCharpolyAux, Polynomial.coeff_map] at H ⊢
  set B := (Module.Free.chooseBasis R M).end
  set g := toMvPolynomial b' b LinearMap.id
  apply_fun (MvPolynomial.bind₁ g) at H
  have : toMvPolynomial b' B φ = fun i ↦ (MvPolynomial.bind₁ g) (toMvPolynomial b B φ i) :=
    funext <| toMvPolynomial_comp b' b B φ LinearMap.id
  rwa [map_zero, RingHom.coe_coe, MvPolynomial.bind₁_bind₁, ← this] at H

lemma polyCharpoly_coeff_eq_zero_iff_of_basis (b : Basis ι R L) (b' : Basis ι' R L) (k : ℕ) :
    (polyCharpoly φ b).coeff k = 0 ↔ (polyCharpoly φ b').coeff k = 0 := by
  constructor <;> apply polyCharpoly_coeff_eq_zero_of_basis

section aux

/-- (Implementation detail, see `LinearMap.nilRank`.)

Let `L` and `M` be finite free modules over `R`,
and let `φ : L →ₗ[R] Module.End R M` be a linear family of endomorphisms.
Then `LinearMap.nilRankAux φ b` is the smallest index
at which `LinearMap.polyCharpoly φ b` has a non-zero coefficient.

This number does not depend on the choice of `b`, see `nilRankAux_basis_indep`. -/
noncomputable
def nilRankAux (φ : L →ₗ[R] Module.End R M) (b : Basis ι R L) : ℕ :=
  (polyCharpoly φ b).natTrailingDegree

lemma polyCharpoly_coeff_nilRankAux_ne_zero [Nontrivial R] :
    (polyCharpoly φ b).coeff (nilRankAux φ b) ≠ 0 := by
  apply Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr
  apply polyCharpoly_ne_zero

lemma nilRankAux_le [Nontrivial R] (b : Basis ι R L) (b' : Basis ι' R L) :
    nilRankAux φ b ≤ nilRankAux φ b' := by
  apply Polynomial.natTrailingDegree_le_of_ne_zero
  rw [Ne, (polyCharpoly_coeff_eq_zero_iff_of_basis φ b b' _).not]
  apply polyCharpoly_coeff_nilRankAux_ne_zero

lemma nilRankAux_basis_indep [Nontrivial R] (b : Basis ι R L) (b' : Basis ι' R L) :
    nilRankAux φ b = (polyCharpoly φ b').natTrailingDegree := by
  apply le_antisymm <;> apply nilRankAux_le

end aux

variable [Module.Finite R L] [Module.Free R L]

/-- Let `L` and `M` be finite free modules over `R`,
and let `φ : L →ₗ[R] Module.End R M` be a linear family of endomorphisms.
Then `LinearMap.nilRank φ b` is the smallest index
at which `LinearMap.polyCharpoly φ b` has a non-zero coefficient.

This number does not depend on the choice of `b`,
see `LinearMap.nilRank_eq_polyCharpoly_natTrailingDegree`. -/
noncomputable
def nilRank (φ : L →ₗ[R] Module.End R M) : ℕ :=
  nilRankAux φ (Module.Free.chooseBasis R L)

variable [Nontrivial R]

lemma nilRank_eq_polyCharpoly_natTrailingDegree (b : Basis ι R L) :
    nilRank φ = (polyCharpoly φ b).natTrailingDegree := by
  apply nilRankAux_basis_indep

lemma polyCharpoly_coeff_nilRank_ne_zero :
    (polyCharpoly φ b).coeff (nilRank φ) ≠ 0 := by
  rw [nilRank_eq_polyCharpoly_natTrailingDegree _ b]
  apply polyCharpoly_coeff_nilRankAux_ne_zero

open FiniteDimensional Module.Free

lemma nilRank_le_card (b : Basis ι R M) : nilRank φ ≤ Fintype.card ι := by
  apply Polynomial.natTrailingDegree_le_of_ne_zero
  rw [← FiniteDimensional.finrank_eq_card_basis b, ← polyCharpoly_natDegree φ (chooseBasis R L),
    Polynomial.coeff_natDegree, (polyCharpoly_monic _ _).leadingCoeff]
  apply one_ne_zero

lemma nilRank_le_finrank : nilRank φ ≤ finrank R M := by
  simpa only [finrank_eq_card_chooseBasisIndex R M] using nilRank_le_card φ (chooseBasis R M)

lemma nilRank_le_natTrailingDegree_charpoly (x : L) :
    nilRank φ ≤ (φ x).charpoly.natTrailingDegree := by
  apply Polynomial.natTrailingDegree_le_of_ne_zero
  intro h
  apply_fun (MvPolynomial.eval ((chooseBasis R L).repr x)) at h
  rw [polyCharpoly_coeff_eval, map_zero] at h
  apply Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr _ h
  apply (LinearMap.charpoly_monic _).ne_zero

/-- Let `L` and `M` be finite free modules over `R`,
and let `φ : L →ₗ[R] Module.End R M` be a linear family of endomorphisms,
and denote `n := nilRank φ`.

An element `x : L` is *nil-regular* with respect to `φ`
if the `n`-th coefficient of the characteristic polynomial of `φ x` is non-zero. -/
def IsNilRegular (x : L) : Prop :=
  Polynomial.coeff (φ x).charpoly (nilRank φ) ≠ 0

variable (x : L)

lemma isNilRegular_def :
    IsNilRegular φ x ↔ (Polynomial.coeff (φ x).charpoly (nilRank φ) ≠ 0) := Iff.rfl

lemma isNilRegular_iff_coeff_polyCharpoly_nilRank_ne_zero :
    IsNilRegular φ x ↔
    MvPolynomial.eval (b.repr x)
      ((polyCharpoly φ b).coeff (nilRank φ)) ≠ 0 := by
  rw [IsNilRegular, polyCharpoly_coeff_eval]

lemma isNilRegular_iff_natTrailingDegree_charpoly_eq_nilRank :
    IsNilRegular φ x ↔ (φ x).charpoly.natTrailingDegree = nilRank φ := by
  rw [isNilRegular_def]
  constructor
  · intro h
    exact le_antisymm
      (Polynomial.natTrailingDegree_le_of_ne_zero h)
      (nilRank_le_natTrailingDegree_charpoly φ x)
  · intro h
    rw [← h]
    apply Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr
    apply (LinearMap.charpoly_monic _).ne_zero

section IsDomain

variable [IsDomain R]

open Cardinal FiniteDimensional MvPolynomial in
lemma exists_isNilRegular_of_finrank_le_card (h : finrank R M ≤ #R) :
    ∃ x : L, IsNilRegular φ x := by
  let b := chooseBasis R L
  let bₘ := chooseBasis R M
  let n := Fintype.card (ChooseBasisIndex R M)
  have aux :
    ((polyCharpoly φ b).coeff (nilRank φ)).IsHomogeneous (n - nilRank φ) :=
    polyCharpoly_coeff_isHomogeneous _ b (nilRank φ) (n - nilRank φ)
      (by simp [nilRank_le_card φ bₘ, finrank_eq_card_chooseBasisIndex])
  obtain ⟨x, hx⟩ : ∃ r, eval r ((polyCharpoly _ b).coeff (nilRank φ)) ≠ 0 := by
    by_contra! h₀
    apply polyCharpoly_coeff_nilRank_ne_zero φ b
    apply aux.eq_zero_of_forall_eval_eq_zero_of_le_card h₀ (le_trans _ h)
    simp only [finrank_eq_card_chooseBasisIndex, Nat.cast_le, Nat.sub_le]
  let c := Finsupp.equivFunOnFinite.symm x
  use b.repr.symm c
  rwa [isNilRegular_iff_coeff_polyCharpoly_nilRank_ne_zero _ b, LinearEquiv.apply_symm_apply]

lemma exists_isNilRegular [Infinite R] : ∃ x : L, IsNilRegular φ x := by
  apply exists_isNilRegular_of_finrank_le_card
  exact (Cardinal.nat_lt_aleph0 _).le.trans <| Cardinal.infinite_iff.mp ‹Infinite R›

end IsDomain

end LinearMap
