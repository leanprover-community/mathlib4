/-
Copyright (c) 2024 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.Lie.CharPolyPoly
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Data.MvPolynomial.Monad
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

open BigOperators

variable {R L M ι ι' ιM ιM' : Type*}
variable [CommRing R] [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
variable [Fintype ι] [Fintype ιM] [Fintype ι'] [Fintype ιM']

-- move this
instance [Nontrivial R] : Nontrivial (MvPolynomial ι R) :=
  nontrivial_of_ne 0 1 <| by
    intro h
    apply_fun MvPolynomial.coeff 0 at h
    simp at h

section

variable {R S σ τ : Type*} [CommSemiring R] [CommSemiring S]

-- move this
lemma MvPolynomial.IsHomogeneous.pow {φ : MvPolynomial σ R} {m : ℕ}
    (hφ : φ.IsHomogeneous m) (n : ℕ) :
    (φ ^ n).IsHomogeneous (m * n) := by
  rw [show φ ^ n = ∏ _i in Finset.range n, φ by simp]
  rw [show m * n = ∑ _i in Finset.range n, m by simp [mul_comm]]
  apply IsHomogeneous.prod _ _ _ (fun _ _ ↦ hφ)

-- move this
lemma MvPolynomial.IsHomogeneous.eval₂ {φ : MvPolynomial σ R} {m n : ℕ}
    (hφ : φ.IsHomogeneous m) (f : R →+* MvPolynomial τ S) (g : σ → MvPolynomial τ S)
     (hf : ∀ r, (f r).IsHomogeneous 0) (hg : ∀ i, (g i).IsHomogeneous n) :
    (eval₂ f g φ).IsHomogeneous (n * m) := by
  apply IsHomogeneous.sum
  intro i hi
  rw [← zero_add (n * m)]
  apply IsHomogeneous.mul (hf _) _
  convert IsHomogeneous.prod _ _ (fun k ↦ n * i k) _
  · rw [Finsupp.mem_support_iff] at hi
    rw [← Finset.mul_sum, hφ hi]
  · rintro k -
    apply (hg k).pow

-- move this
lemma MvPolynomial.IsHomogeneous.map {φ : MvPolynomial σ R} {n : ℕ}
    (hφ : φ.IsHomogeneous n) (f : R →+* S) :
    (map f φ).IsHomogeneous n := by
  rw [← one_mul n]
  exact hφ.eval₂ _ _ (fun r ↦ isHomogeneous_C _ (f r)) (isHomogeneous_X _)

end

/-!

We follow "On Cartan subalgebras of Lie algebras" by D.W. Barnes.

TODO: add bib entry
-/

namespace LieAlgebra

local notation "φ" => LieModule.toEndomorphism R L M

section basic

variable [DecidableEq ιM] [DecidableEq ιM'] (b : Basis ι R L) (bₘ : Basis ιM R M)

open LieModule LinearMap MvPolynomial in
noncomputable
def lieMatrixPoly (ij : ιM × ιM) : MvPolynomial ι R :=
  ∑ k : ι, monomial (.single k 1) ((toMatrix bₘ bₘ <| φ <| b k) ij.1 ij.2)

@[simp]
lemma lieMatrixPoly_eval (ij : ιM × ιM) (c : ι →₀ R) :
    MvPolynomial.eval c (lieMatrixPoly b bₘ ij) = bₘ.repr ⁅b.repr.symm c, bₘ ij.2⁆ ij.1 := by
  rcases ij with ⟨i, j⟩
  simp only [lieMatrixPoly, map_sum, Basis.repr_symm_apply, MvPolynomial.eval_monomial,
    pow_zero, Finsupp.prod_single_index, pow_one]
  induction c using Finsupp.induction_linear
  case h0 => simp
  case hadd f g hf hg => simp [hf, hg, mul_add, Finset.sum_add_distrib]
  case hsingle k r =>
    rw [Finset.sum_eq_single k, Finsupp.single_eq_same]
    · simp [mul_comm, LinearMap.toMatrix_apply]
    · rintro l - hl; rw [Finsupp.single_eq_of_ne hl.symm, mul_zero]
    · simp only [Finset.mem_univ, not_true_eq_false, IsEmpty.forall_iff]

noncomputable
def lieCharpoly : Polynomial (MvPolynomial ι R) :=
  Matrix.charpoly.univ.map <|
  MvPolynomial.eval₂Hom (Int.castRingHom <| MvPolynomial ι R) (lieMatrixPoly b bₘ)

lemma lieCharpoly_monic : (lieCharpoly b bₘ).Monic :=
  Matrix.charpoly.univ_monic.map _

@[simp]
lemma lieCharpoly_natDegree [Nontrivial R] : (lieCharpoly b bₘ).natDegree = Fintype.card ιM := by
  rw [lieCharpoly, Matrix.charpoly.univ_monic.natDegree_map, Matrix.charpoly.univ_natDegree]

lemma lieCharpoly_coeff_isHomogeneous (i j : ℕ) (hij : i + j = Fintype.card ιM) :
    ((lieCharpoly b bₘ).coeff i).IsHomogeneous j := by
  rw [lieCharpoly, Polynomial.coeff_map, ← one_mul j]
  apply (Matrix.charpoly.univ_coeff_isHomogeneous _ _ hij).eval₂
  · exact fun r ↦ MvPolynomial.isHomogeneous_C _ _
  rintro ⟨x, y⟩
  dsimp [lieMatrixPoly]
  apply MvPolynomial.IsHomogeneous.sum
  rintro z -
  apply MvPolynomial.isHomogeneous_monomial _ _ _
  simp [Finsupp.single, Pi.single, Function.update]

open LinearMap in
lemma lieCharpoly_map_eq_toMatrix_charpoly (x : L) :
    (lieCharpoly b bₘ).map (MvPolynomial.eval (b.repr x)) = (toMatrix bₘ bₘ (φ x)).charpoly := by
  rw [lieCharpoly, Polynomial.map_map]
  convert (Matrix.charpoly.univ_map _)
  apply MvPolynomial.ringHom_ext
  · intro n; simp
  · rintro ⟨i, j⟩
    simp only [MvPolynomial.comp_eval₂Hom, lieMatrixPoly_eval, LinearEquiv.symm_apply_apply,
      MvPolynomial.eval₂Hom_X', toMatrix_apply, ad_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      MvPolynomial.aeval_X, LieModule.toEndomorphism_apply_apply]

open LinearMap in
lemma lieCharpoly_eval_eq_toMatrix_charpoly_coeff (x : L) (i : ℕ) :
    MvPolynomial.eval (b.repr x) ((lieCharpoly b bₘ).coeff i) =
      (toMatrix bₘ bₘ (φ x)).charpoly.coeff i := by
  simp [← lieCharpoly_map_eq_toMatrix_charpoly b bₘ x]

end basic

section module

variable [DecidableEq ιM] [Nontrivial R] [Module.Finite R M] [Module.Free R M]
variable (b : Basis ι R L) (bₘ : Basis ιM R M) (x : L)

@[simp]
lemma lieCharpoly_map :
    (lieCharpoly b bₘ).map (MvPolynomial.eval (b.repr x)) = (φ x).charpoly := by
  rw [lieCharpoly_map_eq_toMatrix_charpoly, LinearMap.charpoly_toMatrix]

@[simp]
lemma lieCharpoly_eval [Nontrivial R] [Module.Finite R M] [Module.Free R M] (x : L) (i : ℕ) :
    MvPolynomial.eval (b.repr x) ((lieCharpoly b bₘ).coeff i) =
      (φ x).charpoly.coeff i := by
  rw [lieCharpoly_eval_eq_toMatrix_charpoly_coeff, LinearMap.charpoly_toMatrix]

lemma exists_lieCharpoly_coeff_ne_zero [Nontrivial R] :
    ∃ n, (lieCharpoly b bₘ).coeff n ≠ 0 := by
  have : Polynomial.leadingCoeff (lieCharpoly b bₘ) ≠ 0 := by
    rw [(lieCharpoly_monic b bₘ).leadingCoeff]
    exact one_ne_zero
  refine ⟨_, this⟩

end module

variable [DecidableEq ι] [DecidableEq ιM] [Nontrivial R] [Module.Finite R L] [Module.Free R L]
variable (b : Basis ι R L) (bₘ : Basis ιM R L) (x : L)

open Module.Free

variable (R L)

open Matrix.charpoly Classical in
/--
Let `L` be a Lie algebra over a nontrivial commutative ring `R`,
and assume that `L` is finite free as `R`-module.
Then the coefficients of the characteristic polynomial of `ad R L x` are polynomial in `x`.
The *rank* of `L` is the smallest `n` for which the `n`-th coefficient
is not the zero polynomial.
-/
noncomputable
def rank : ℕ :=
  Nat.find (exists_lieCharpoly_coeff_ne_zero (chooseBasis R L) (chooseBasis R L))

-- TODO: generalize to arbitrary basis
lemma lieCharpoly_coeff_rank_ne_zero :
    (lieCharpoly (chooseBasis R L) (chooseBasis R L)).coeff (rank R L) ≠ 0 := by
  classical
  exact Nat.find_spec (exists_lieCharpoly_coeff_ne_zero (chooseBasis R L) (chooseBasis R L))

open FiniteDimensional
lemma rank_le_card : rank R L ≤ Fintype.card ι := by
  rw [← FiniteDimensional.finrank_eq_card_basis b, finrank_eq_card_chooseBasisIndex]
  classical
  apply Nat.find_le
  rw [← lieCharpoly_natDegree (chooseBasis R L) (chooseBasis R L), Polynomial.coeff_natDegree,
    (lieCharpoly_monic _ _).leadingCoeff]
  apply one_ne_zero

open FiniteDimensional
lemma rank_le_finrank : rank R L ≤ finrank R L := by
  simpa only [finrank_eq_card_chooseBasisIndex R L] using rank_le_card R L (chooseBasis R L)

variable {L}

/-- Let `x` be an element of a Lie algebra `L` over `R`, and write `n` for `rank R L`.
Then `x` is *regular*
if the `n`-th coefficient of the characteristic polynomial of `ad R L x` is non-zero. -/
def IsRegular (x : L) : Prop :=
  Polynomial.coeff (ad R L x).charpoly (rank R L) ≠ 0

lemma isRegular_def (x : L) :
    IsRegular R x = (Polynomial.coeff (ad R L x).charpoly (rank R L) ≠ 0) := rfl

lemma isRegular_iff (x : L) :
    IsRegular R x ↔
    MvPolynomial.eval ((chooseBasis R L).repr x)
      ((lieCharpoly (chooseBasis R L) (chooseBasis R L)).coeff (rank R L)) ≠ 0 := by
  rw [IsRegular, lieCharpoly_eval, ad]

section IsDomain

variable (L)
variable [IsDomain R]

open Module.Free

open Cardinal FiniteDimensional MvPolynomial in
lemma exists_isRegular_of_finrank_le_card (h : finrank R L ≤ #R) :
    ∃ x : L, IsRegular R x := by
  let b := chooseBasis R L
  let n := Fintype.card (ChooseBasisIndex R L)
  have aux₁ := lieCharpoly_coeff_isHomogeneous b b (rank R L) (n - rank R L)
    (by simp [rank_le_card _ _ b])
  have aux₂ : ↑(n - rank R L) ≤ #R := by
    trans ↑n
    · simp only [Nat.cast_le, tsub_le_iff_right, le_add_iff_nonneg_right, zero_le]
    rwa [finrank_eq_card_chooseBasisIndex R L] at h
  obtain ⟨x, hx⟩ :=
    aux₁.exists_eval_ne_zero_of_totalDegree_le_card (lieCharpoly_coeff_rank_ne_zero R L) aux₂
  let c := Finsupp.equivFunOnFinite.symm x
  use b.repr.symm c
  rwa [isRegular_iff, LinearEquiv.apply_symm_apply]

lemma exists_isRegular [Infinite R] : ∃ x : L, IsRegular R x := by
  apply exists_isRegular_of_finrank_le_card
  exact (Cardinal.nat_lt_aleph0 _).le.trans <| Cardinal.infinite_iff.mp ‹Infinite R›

end IsDomain

end LieAlgebra
