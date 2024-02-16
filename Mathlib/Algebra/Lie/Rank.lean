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

variable {R L M ι ι' ιM ιM' : Type*}
variable [CommRing R] [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
variable [Fintype ι] [Fintype ιM] [Fintype ι'] [Fintype ιM']

namespace LieAlgebra

local notation "φ" => LieModule.toEndomorphism R L M

section basic

variable [DecidableEq ιM] [DecidableEq ιM']
variable (b : Basis ι R L) (bₘ : Basis ιM R M) (b' : Basis ι' R L) (bₘ' : Basis ιM' R M)

open LieModule LinearMap MvPolynomial in
/-- Let `M` be a Lie module of a Lie algebra `L` over `R`,
and let `b` be a basis of `L` and `bₘ` a basis of `M`.
Then `lieMatrixPoly b bₘ (i,j)` is the polynomial that evaluates on elements `x` of `L`
to the `(i,j)`-th coefficient of the matrix representation of `⁅x, ·⁆` acting on `M`. -/
noncomputable
def lieMatrixPoly (ij : ιM × ιM) : MvPolynomial ι R :=
  ∑ k : ι, monomial (.single k 1) ((toMatrix bₘ bₘ <| φ <| b k) ij.1 ij.2)

open LinearMap in
@[simp]
lemma lieMatrixPoly_eval_eq_toMatrix (ij : ιM × ιM) (c : ι →₀ R) :
    MvPolynomial.eval c (lieMatrixPoly b bₘ ij) =
      (toMatrix bₘ bₘ <| φ (b.repr.symm c)) ij.1 ij.2 := by
  rcases ij with ⟨i, j⟩
  simp only [lieMatrixPoly, map_sum, Basis.repr_symm_apply, MvPolynomial.eval_monomial,
    pow_zero, Finsupp.prod_single_index, pow_one]
  induction c using Finsupp.induction_linear
  case h0 => simp
  case hadd f g hf hg => simp [hf, hg, mul_add, Finset.sum_add_distrib]
  case hsingle k r =>
    rw [Finset.sum_eq_single k, Finsupp.single_eq_same]
    · rw [mul_comm, Finsupp.total_single, LieHom.map_smul, map_smul, Matrix.smul_apply, smul_eq_mul]
    · rintro l - hl; rw [Finsupp.single_eq_of_ne hl.symm, mul_zero]
    · simp only [Finset.mem_univ, not_true_eq_false, IsEmpty.forall_iff]

lemma lieMatrixPoly_eval_eq_lie (ij : ιM × ιM) (c : ι →₀ R) :
    MvPolynomial.eval c (lieMatrixPoly b bₘ ij) = bₘ.repr ⁅b.repr.symm c, bₘ ij.2⁆ ij.1 := by
  rw [lieMatrixPoly_eval_eq_toMatrix, Basis.repr_symm_apply, LinearMap.toMatrix_apply,
    LieModule.toEndomorphism_apply_apply]

open Matrix

/-- Let `M` be a Lie module of a Lie algebra `L` over `R`,
and let `b` be a basis of `L` and `bₘ` a basis of `M`.
Then `lieCharpoly b bₘ` is the polynomial that evaluates on elements `x` of `L`
to the characteristic polynomial of `⁅x, ·⁆` acting on `M`. -/
noncomputable
def lieCharpoly : Polynomial (MvPolynomial ι R) :=
  (charpoly.univ R ιM).map <| MvPolynomial.bind₁ (lieMatrixPoly b bₘ)

lemma lieCharpoly_monic : (lieCharpoly b bₘ).Monic :=
  (charpoly.univ_monic R ιM).map _

lemma lieCharpoly_ne_zero [Nontrivial R] : (lieCharpoly b bₘ) ≠ 0 :=
  (lieCharpoly_monic _ _).ne_zero

@[simp]
lemma lieCharpoly_natDegree [Nontrivial R] : (lieCharpoly b bₘ).natDegree = Fintype.card ιM := by
  rw [lieCharpoly, (charpoly.univ_monic _ _).natDegree_map, charpoly.univ_natDegree]

lemma lieCharpoly_coeff_isHomogeneous (i j : ℕ) (hij : i + j = Fintype.card ιM) :
    ((lieCharpoly b bₘ).coeff i).IsHomogeneous j := by
  rw [lieCharpoly, Polynomial.coeff_map, ← one_mul j]
  apply (charpoly.univ_coeff_isHomogeneous _ _ _ _ hij).eval₂
  · exact fun r ↦ MvPolynomial.isHomogeneous_C _ _
  rintro ⟨x, y⟩
  dsimp only [lieMatrixPoly]
  apply MvPolynomial.IsHomogeneous.sum
  rintro z -
  apply MvPolynomial.isHomogeneous_monomial _ _ _
  simp [Finsupp.single, Pi.single, Function.update]

open LinearMap in
lemma lieCharpoly_map_eq_toMatrix_charpoly (x : L) :
    (lieCharpoly b bₘ).map (MvPolynomial.eval (b.repr x)) = (toMatrix bₘ bₘ (φ x)).charpoly := by
  erw [lieCharpoly, Polynomial.map_map, MvPolynomial.comp_eval₂Hom, charpoly.univ_map_eval₂Hom]
  congr
  ext
  rw [of_apply, Function.curry_apply, lieMatrixPoly_eval_eq_toMatrix, LinearEquiv.symm_apply_apply]

open LinearMap in
lemma lieCharpoly_eval_eq_toMatrix_charpoly_coeff (x : L) (i : ℕ) :
    MvPolynomial.eval (b.repr x) ((lieCharpoly b bₘ).coeff i) =
      (toMatrix bₘ bₘ (φ x)).charpoly.coeff i := by
  simp [← lieCharpoly_map_eq_toMatrix_charpoly b bₘ x]

end basic

section module

variable [DecidableEq ιM] [DecidableEq ιM'] [Nontrivial R] [Module.Finite R M] [Module.Free R M]
variable (b : Basis ι R L) (bₘ : Basis ιM R M) (b' : Basis ι' R L) (bₘ' : Basis ιM' R M)
variable (x : L)

@[simp]
lemma lieCharpoly_map :
    (lieCharpoly b bₘ).map (MvPolynomial.eval (b.repr x)) = (φ x).charpoly := by
  rw [lieCharpoly_map_eq_toMatrix_charpoly, LinearMap.charpoly_toMatrix]

@[simp]
lemma lieCharpoly_eval (i : ℕ) :
    MvPolynomial.eval (b.repr x) ((lieCharpoly b bₘ).coeff i) = (φ x).charpoly.coeff i := by
  rw [lieCharpoly_eval_eq_toMatrix_charpoly_coeff, LinearMap.charpoly_toMatrix]

end module

variable [DecidableEq ι] [DecidableEq ιM] [Nontrivial R] [Module.Finite R L] [Module.Free R L]
variable (b : Basis ι R L) (b' : Basis ι R L) (bₘ : Basis ιM R L) (x : L)

open Module.Free

variable (R L)

open Matrix.charpoly Classical in
/--
Let `L` be a Lie algebra over a nontrivial commutative ring `R`,
and assume that `L` is finite free as `R`-module.
Then the coefficients of the characteristic polynomial of `ad R L x` are polynomial in `x`.
The *rank* of `L` is the smallest `n` for which the `n`-th coefficient is not the zero polynomial.
-/
noncomputable
def rank : ℕ := (lieCharpoly (chooseBasis R L) (chooseBasis R L)).natTrailingDegree

-- TODO: generalize to arbitrary basis, by carefully tracing all the polynomials
lemma lieCharpoly_coeff_rank_ne_zero :
    (lieCharpoly (chooseBasis R L) (chooseBasis R L)).coeff (rank R L) ≠ 0 := by
  apply Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr
  apply lieCharpoly_ne_zero

open FiniteDimensional
lemma rank_le_card : rank R L ≤ Fintype.card ι := by
  apply Polynomial.natTrailingDegree_le_of_ne_zero
  rw [← FiniteDimensional.finrank_eq_card_basis b, finrank_eq_card_chooseBasisIndex,
      ← lieCharpoly_natDegree (chooseBasis R L) (chooseBasis R L), Polynomial.coeff_natDegree,
    (lieCharpoly_monic _ _).leadingCoeff]
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
      ((lieCharpoly (chooseBasis R L) (chooseBasis R L)).coeff (rank R L)) ≠ 0 := by
  rw [IsRegular, lieCharpoly_eval, ad]

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
  have aux : ((lieCharpoly b b).coeff (rank R L)).IsHomogeneous (n - rank R L) :=
    lieCharpoly_coeff_isHomogeneous b b (rank R L) (n - rank R L) (by simp [rank_le_card _ _ b])
  obtain ⟨x, hx⟩ : ∃ r, eval r ((lieCharpoly b b).coeff (rank R L)) ≠ 0 := by
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
