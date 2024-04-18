/-
Copyright (c) 2024 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Module.LinearMap.Polynomial

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

namespace LieAlgebra

variable {R L ι : Type*}
variable [CommRing R] [Nontrivial R] [LieRing L] [LieAlgebra R L]
variable [Module.Finite R L] [Module.Free R L] [Fintype ι]
variable (b : Basis ι R L) (x : L)

open LieAlgebra LinearMap Module.Free

variable (R L)

/--
Let `L` be a Lie algebra over a nontrivial commutative ring `R`,
and assume that `L` is finite free as `R`-module.
Then the coefficients of the characteristic polynomial of `ad R L x` are polynomial in `x`.
The *rank* of `L` is the smallest `n` for which the `n`-th coefficient is not the zero polynomial.
-/
noncomputable
def rank : ℕ := (polyCharpoly (ad R L).toLinearMap (chooseBasis R L)).natTrailingDegree

-- TODO: generalize to arbitrary basis, by carefully tracing all the polynomials
lemma polyCharpoly_coeff_rank_ne_zero :
    (polyCharpoly (ad R L).toLinearMap (chooseBasis R L)).coeff (rank R L) ≠ 0 := by
  apply Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr
  apply polyCharpoly_ne_zero

open FiniteDimensional
lemma rank_le_card [StrongRankCondition R] : rank R L ≤ Fintype.card ι := by
  apply Polynomial.natTrailingDegree_le_of_ne_zero
  rw [← FiniteDimensional.finrank_eq_card_basis b, ← polyCharpoly_natDegree _ (chooseBasis R L),
    Polynomial.coeff_natDegree, (polyCharpoly_monic _ _).leadingCoeff]
  apply one_ne_zero

open FiniteDimensional
lemma rank_le_finrank [StrongRankCondition R] : rank R L ≤ finrank R L := by
  simpa only [finrank_eq_card_chooseBasisIndex R L] using rank_le_card R L (chooseBasis R L)

variable {L}

lemma rank_le_natTrailingDegree_charpoly_ad :
    rank R L ≤ (ad R L x).charpoly.natTrailingDegree := by
  apply Polynomial.natTrailingDegree_le_of_ne_zero
  intro h
  apply_fun (MvPolynomial.eval ((chooseBasis R L).repr x)) at h
  rw [polyCharpoly_coeff_eval, map_zero] at h
  apply Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr _ h
  apply (LinearMap.charpoly_monic _).ne_zero

/-- Let `x` be an element of a Lie algebra `L` over `R`, and write `n` for `rank R L`.
Then `x` is *regular*
if the `n`-th coefficient of the characteristic polynomial of `ad R L x` is non-zero. -/
def IsRegular (x : L) : Prop :=
  Polynomial.coeff (ad R L x).charpoly (rank R L) ≠ 0

lemma isRegular_def :
    IsRegular R x = (Polynomial.coeff (ad R L x).charpoly (rank R L) ≠ 0) := rfl

lemma isRegular_iff_coeff_polyCharpoly_rank_ne_zero :
    IsRegular R x ↔
    MvPolynomial.eval ((chooseBasis R L).repr x)
      ((polyCharpoly (ad R L).toLinearMap (chooseBasis R L)).coeff (rank R L)) ≠ 0 := by
  rw [IsRegular, polyCharpoly_coeff_eval]
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
variable [IsDomain R] [StrongRankCondition R]

open Module.Free

open Cardinal FiniteDimensional MvPolynomial in
lemma exists_isRegular_of_finrank_le_card (h : finrank R L ≤ #R) :
    ∃ x : L, IsRegular R x := by
  let b := chooseBasis R L
  let n := Fintype.card (ChooseBasisIndex R L)
  have aux :
    ((polyCharpoly (ad R L).toLinearMap b).coeff (rank R L)).IsHomogeneous (n - rank R L) :=
    polyCharpoly_coeff_isHomogeneous _ b (rank R L) (n - rank R L)
      (by simp [rank_le_card R L b, finrank_eq_card_chooseBasisIndex])
  obtain ⟨x, hx⟩ : ∃ r, eval r ((polyCharpoly _ b).coeff (rank R L)) ≠ 0 := by
    by_contra! h₀
    apply polyCharpoly_coeff_rank_ne_zero R L
    apply aux.eq_zero_of_forall_eval_eq_zero_of_le_card h₀ (le_trans _ h)
    simp only [finrank_eq_card_chooseBasisIndex, Nat.cast_le, Nat.sub_le]
  let c := Finsupp.equivFunOnFinite.symm x
  use b.repr.symm c
  rwa [isRegular_iff_coeff_polyCharpoly_rank_ne_zero, LinearEquiv.apply_symm_apply]

lemma exists_isRegular [Infinite R] : ∃ x : L, IsRegular R x := by
  apply exists_isRegular_of_finrank_le_card
  exact (Cardinal.nat_lt_aleph0 _).le.trans <| Cardinal.infinite_iff.mp ‹Infinite R›

end IsDomain

end LieAlgebra
