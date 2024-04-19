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

variable {R A L ι : Type*}
variable [CommRing R] [Nontrivial R] [CommRing A] [Algebra R A]
variable [LieRing L] [LieAlgebra R L]
variable [Module.Finite R L] [Module.Free R L] [Fintype ι] [DecidableEq ι]
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
def rank : ℕ := polyRank (ad R L).toLinearMap

lemma polyCharpoly_coeff_rank_ne_zero :
    (polyCharpoly (ad R L).toLinearMap b).coeff (rank R L) ≠ 0 :=
  polyCharpoly_coeff_polyRank_ne_zero _ _

lemma rank_eq_natTrailingDegree :
    rank R L = (polyCharpoly (ad R L).toLinearMap b).natTrailingDegree := by
  apply polyRank_eq_polyCharpoly_natTrailingDegree

open FiniteDimensional
lemma rank_le_card [StrongRankCondition R] : rank R L ≤ Fintype.card ι :=
  polyRank_le_card _ b

open FiniteDimensional
lemma rank_le_finrank [StrongRankCondition R] : rank R L ≤ finrank R L :=
  polyRank_le_finrank _

variable {L}

lemma rank_le_natTrailingDegree_charpoly_ad :
    rank R L ≤ (ad R L x).charpoly.natTrailingDegree :=
  polyRank_le_natTrailingDegree_charpoly _ _

/-- Let `x` be an element of a Lie algebra `L` over `R`, and write `n` for `rank R L`.
Then `x` is *regular*
if the `n`-th coefficient of the characteristic polynomial of `ad R L x` is non-zero. -/
def IsRegular (x : L) : Prop := LinearMap.IsRegular (ad R L).toLinearMap x

lemma isRegular_def :
    IsRegular R x = (Polynomial.coeff (ad R L x).charpoly (rank R L) ≠ 0) := rfl

lemma isRegular_iff_coeff_polyCharpoly_rank_ne_zero :
    IsRegular R x ↔
    MvPolynomial.eval (b.repr x)
      ((polyCharpoly (ad R L).toLinearMap b).coeff (rank R L)) ≠ 0 :=
  LinearMap.isRegular_iff_coeff_polyCharpoly_polyRank_ne_zero _ _ _

lemma isRegular_iff_natTrailingDegree_charpoly_eq_rank :
    IsRegular R x ↔ (ad R L x).charpoly.natTrailingDegree = rank R L :=
  LinearMap.isRegular_iff_natTrailingDegree_charpoly_eq_polyRank _ _
section IsDomain

variable (L)
variable [IsDomain R] [StrongRankCondition R]

open Cardinal FiniteDimensional MvPolynomial in
lemma exists_isRegular_of_finrank_le_card (h : finrank R L ≤ #R) :
    ∃ x : L, IsRegular R x :=
  LinearMap.exists_isRegular_of_finrank_le_card _ h

lemma exists_isRegular [Infinite R] : ∃ x : L, IsRegular R x :=
  LinearMap.exists_isRegular _

end IsDomain

end LieAlgebra
