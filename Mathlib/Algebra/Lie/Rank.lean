/-
Copyright (c) 2024 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.Lie.EngelSubalgebra
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Module.LinearMap.Polynomial
import Mathlib.LinearAlgebra.Eigenspace.Zero

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

open Module

variable {R A L M ι ιₘ : Type*}
variable [CommRing R]
variable [CommRing A] [Algebra R A]
variable [LieRing L] [LieAlgebra R L] [Module.Finite R L] [Module.Free R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
variable [Module.Finite R M] [Module.Free R M]
variable [Fintype ι]
variable [Fintype ιₘ]
variable (b : Basis ι R L) (bₘ : Basis ιₘ R M) (x : L)

namespace LieModule

open LieAlgebra LinearMap Module.Free

variable (R L M)

local notation "φ" => LieHom.toLinearMap (LieModule.toEnd R L M)

/--
Let `M` be a representation of a Lie algebra `L` over a nontrivial commutative ring `R`,
and assume that `L` and `M` are finite free as `R`-module.
Then the coefficients of the characteristic polynomial of `⁅x, ·⁆` are polynomial in `x`.
The *rank* of `M` is the smallest `n` for which the `n`-th coefficient is not the zero polynomial.
-/
noncomputable
def rank : ℕ := nilRank φ

lemma polyCharpoly_coeff_rank_ne_zero [Nontrivial R] [DecidableEq ι] :
    (polyCharpoly φ b).coeff (rank R L M) ≠ 0 :=
  polyCharpoly_coeff_nilRank_ne_zero _ _

lemma rank_eq_natTrailingDegree [Nontrivial R] [DecidableEq ι] :
    rank R L M = (polyCharpoly φ b).natTrailingDegree := by
  apply nilRank_eq_polyCharpoly_natTrailingDegree

open Module

include bₘ in
lemma rank_le_card [Nontrivial R] : rank R L M ≤ Fintype.card ιₘ :=
  nilRank_le_card _ bₘ

open Module
lemma rank_le_finrank [Nontrivial R] : rank R L M ≤ finrank R M :=
  nilRank_le_finrank _

variable {L}

lemma rank_le_natTrailingDegree_charpoly_ad [Nontrivial R] :
    rank R L M ≤ (toEnd R L M x).charpoly.natTrailingDegree :=
  nilRank_le_natTrailingDegree_charpoly _ _

/-- Let `x` be an element of a Lie algebra `L` over `R`, and write `n` for `rank R L`.
Then `x` is *regular*
if the `n`-th coefficient of the characteristic polynomial of `ad R L x` is non-zero. -/
def IsRegular (x : L) : Prop := LinearMap.IsNilRegular φ x

lemma isRegular_def :
    IsRegular R M x ↔ (toEnd R L M x).charpoly.coeff (rank R L M) ≠ 0 := Iff.rfl

lemma isRegular_iff_coeff_polyCharpoly_rank_ne_zero [DecidableEq ι] :
    IsRegular R M x ↔
    MvPolynomial.eval (b.repr x)
      ((polyCharpoly φ b).coeff (rank R L M)) ≠ 0 :=
  LinearMap.isNilRegular_iff_coeff_polyCharpoly_nilRank_ne_zero _ _ _

lemma isRegular_iff_natTrailingDegree_charpoly_eq_rank [Nontrivial R] :
    IsRegular R M x ↔ (toEnd R L M x).charpoly.natTrailingDegree = rank R L M :=
  LinearMap.isNilRegular_iff_natTrailingDegree_charpoly_eq_nilRank _ _
section IsDomain

variable (L)
variable [IsDomain R]

open Cardinal Module MvPolynomial in
lemma exists_isRegular_of_finrank_le_card (h : finrank R M ≤ #R) :
    ∃ x : L, IsRegular R M x :=
  LinearMap.exists_isNilRegular_of_finrank_le_card _ h

lemma exists_isRegular [Infinite R] : ∃ x : L, IsRegular R M x :=
  LinearMap.exists_isNilRegular _

end IsDomain

end LieModule

namespace LieAlgebra

open LieAlgebra LinearMap Module.Free

variable (R L)

/--
Let `L` be a Lie algebra over a nontrivial commutative ring `R`,
and assume that `L` is finite free as `R`-module.
Then the coefficients of the characteristic polynomial of `ad R L x` are polynomial in `x`.
The *rank* of `L` is the smallest `n` for which the `n`-th coefficient is not the zero polynomial.
-/
noncomputable
abbrev rank : ℕ := LieModule.rank R L L

lemma polyCharpoly_coeff_rank_ne_zero [Nontrivial R] [DecidableEq ι] :
    (polyCharpoly (ad R L).toLinearMap b).coeff (rank R L) ≠ 0 :=
  polyCharpoly_coeff_nilRank_ne_zero _ _

lemma rank_eq_natTrailingDegree [Nontrivial R] [DecidableEq ι] :
    rank R L = (polyCharpoly (ad R L).toLinearMap b).natTrailingDegree := by
  apply nilRank_eq_polyCharpoly_natTrailingDegree

open Module

include b in
lemma rank_le_card [Nontrivial R] : rank R L ≤ Fintype.card ι :=
  nilRank_le_card _ b

lemma rank_le_finrank [Nontrivial R] : rank R L ≤ finrank R L :=
  nilRank_le_finrank _

variable {L}

lemma rank_le_natTrailingDegree_charpoly_ad [Nontrivial R] :
    rank R L ≤ (ad R L x).charpoly.natTrailingDegree :=
  nilRank_le_natTrailingDegree_charpoly _ _

/-- Let `x` be an element of a Lie algebra `L` over `R`, and write `n` for `rank R L`.
Then `x` is *regular*
if the `n`-th coefficient of the characteristic polynomial of `ad R L x` is non-zero. -/
abbrev IsRegular (x : L) : Prop := LieModule.IsRegular R L x

lemma isRegular_def :
    IsRegular R x ↔ (Polynomial.coeff (ad R L x).charpoly (rank R L) ≠ 0) := Iff.rfl

lemma isRegular_iff_coeff_polyCharpoly_rank_ne_zero [DecidableEq ι] :
    IsRegular R x ↔
    MvPolynomial.eval (b.repr x)
      ((polyCharpoly (ad R L).toLinearMap b).coeff (rank R L)) ≠ 0 :=
  LinearMap.isNilRegular_iff_coeff_polyCharpoly_nilRank_ne_zero _ _ _

lemma isRegular_iff_natTrailingDegree_charpoly_eq_rank [Nontrivial R] :
    IsRegular R x ↔ (ad R L x).charpoly.natTrailingDegree = rank R L :=
  LinearMap.isNilRegular_iff_natTrailingDegree_charpoly_eq_nilRank _ _
section IsDomain

variable (L)
variable [IsDomain R]

open Cardinal Module MvPolynomial in
lemma exists_isRegular_of_finrank_le_card (h : finrank R L ≤ #R) :
    ∃ x : L, IsRegular R x :=
  LinearMap.exists_isNilRegular_of_finrank_le_card _ h

lemma exists_isRegular [Infinite R] : ∃ x : L, IsRegular R x :=
  LinearMap.exists_isNilRegular _

end IsDomain

end LieAlgebra

namespace LieAlgebra

variable (K : Type*) {L : Type*} [Field K] [LieRing L] [LieAlgebra K L] [Module.Finite K L]

open Module LieSubalgebra

lemma finrank_engel (x : L) :
    finrank K (engel K x) = (ad K L x).charpoly.natTrailingDegree :=
  (ad K L x).finrank_maxGenEigenspace

lemma rank_le_finrank_engel (x : L) :
    rank K L ≤ finrank K (engel K x) :=
  (rank_le_natTrailingDegree_charpoly_ad K x).trans
    (finrank_engel K x).ge

lemma isRegular_iff_finrank_engel_eq_rank (x : L) :
    IsRegular K x ↔ finrank K (engel K x) = rank K L := by
  rw [isRegular_iff_natTrailingDegree_charpoly_eq_rank, finrank_engel]

end LieAlgebra
