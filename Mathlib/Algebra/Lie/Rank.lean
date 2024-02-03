import Mathlib.Algebra.Lie.CharPolyPoly
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Data.MvPolynomial.Monad
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

open BigOperators

universe u v w

variable {R : Type u} {L : Type v} {ι : Type w}
variable [CommRing R] [LieRing L] [LieAlgebra R L] [Fintype ι]

-- move this
instance [Nontrivial R] : Nontrivial (MvPolynomial ι R) :=
  nontrivial_of_ne 0 1 <| by
    intro h
    apply_fun MvPolynomial.coeff 0 at h
    simp at h

namespace LieAlgebra

section basis

variable (b : Basis ι R L)

open MvPolynomial in
noncomputable
def adMatrixPoly (ij : ι × ι) : MvPolynomial ι R :=
  ∑ k : ι, monomial (.single k 1) (b.repr ⁅b k, b ij.1⁆ ij.2)

lemma adMatrixPoly_eval (ij : ι × ι) (c : ι →₀ R) :
    MvPolynomial.eval c (adMatrixPoly b ij) = b.repr ⁅b.repr.symm c, b ij.1⁆ ij.2 := by
  rcases ij with ⟨i, j⟩
  simp only [adMatrixPoly, map_sum, Basis.repr_symm_apply, MvPolynomial.eval_monomial,
    pow_zero, Finsupp.prod_single_index, pow_one]
  induction c using Finsupp.induction_linear
  case h0 => simp
  case hadd f g hf hg => simp [hf, hg, mul_add, Finset.sum_add_distrib]
  case hsingle k r =>
    rw [Finset.sum_eq_single k, Finsupp.single_eq_same]
    · simp [mul_comm]
    · rintro l - hl; rw [Finsupp.single_eq_of_ne hl.symm, mul_zero]
    · simp only [Finset.mem_univ, not_true_eq_false, IsEmpty.forall_iff]

variable [DecidableEq ι]

noncomputable
def adCharpoly : Polynomial (MvPolynomial ι R) :=
  Matrix.charpoly.univ.map <|
  MvPolynomial.eval₂Hom (Int.castRingHom <| MvPolynomial ι R) (adMatrixPoly b)

lemma adCharpoly_monic : (adCharpoly b).Monic :=
  Matrix.charpoly.univ_monic.map _

@[simp]
lemma adCharpoly_natDegree [Nontrivial R] : (adCharpoly b).natDegree = Fintype.card ι := by
  rw [adCharpoly, Matrix.charpoly.univ_monic.natDegree_map, Matrix.charpoly.univ_natDegree]

lemma adCharpoly_coeff_isHomogeneous (i j : ℕ) (hij : i + j = Fintype.card ι) :
    ((adCharpoly b).coeff i).IsHomogeneous j := by
  sorry

-- open LinearMap in
-- lemma adCharpoly_map (x : L) :
--     (adCharpoly b).map (MvPolynomial.eval (b.repr x)) = (toMatrix (ad R L x) b b).charpoly := by
--   sorry

-- open LinearMap in
-- lemma adCharpoly_eval (x : ι → R) (i : ℕ) :
--     MvPolynomial.eval x ((adCharpoly b).coeff i) = (toMatrix (ad R L x) b b).charpoly.coeff i := by
--   sorry

end basis

lemma exists_adCharpoly_coeff_ne_zero [DecidableEq ι] [Nontrivial R] (b : Basis ι R L) :
    ∃ n, (adCharpoly b).coeff n ≠ 0 := by
  have : Polynomial.leadingCoeff (adCharpoly b) ≠ 0 := by
    rw [(adCharpoly_monic b).leadingCoeff]
    exact one_ne_zero
  refine ⟨_, this⟩

section base_nontrivial

variable (R L)
variable [Nontrivial R] [Module.Finite R L] [Module.Free R L]

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
  Nat.find (exists_adCharpoly_coeff_ne_zero (Module.Free.chooseBasis R L))

-- TODO: generalize to arbitrary basis
lemma adCharpoly_coeff_rank_ne_zero :
    (adCharpoly (Module.Free.chooseBasis R L)).coeff (rank R L) ≠ 0 := by
  classical
  exact Nat.find_spec (exists_adCharpoly_coeff_ne_zero (Module.Free.chooseBasis R L))

lemma rank_le_card : rank R L ≤ Fintype.card (Module.Free.ChooseBasisIndex R L) := by
  classical
  apply Nat.find_le
  rw [← adCharpoly_natDegree (Module.Free.chooseBasis R L), Polynomial.coeff_natDegree,
    (adCharpoly_monic _).leadingCoeff]
  apply one_ne_zero

lemma rank_le_rank [StrongRankCondition R] : rank R L ≤ Module.rank R L := by
  rw [Module.Free.rank_eq_card_chooseBasisIndex R L, Cardinal.mk_fintype, Nat.cast_le]
  apply rank_le_card

variable {L}

/-- Let `x` be an element of a Lie algebra `L` over `R`, and write `n` for `rank R L`.
Then `x` is *regular*
if the `n`-th coefficient of the characteristic polynomial of `ad R L x` is non-zero. -/
def IsRegular (x : L) : Prop :=
  Polynomial.coeff (ad R L x).charpoly (rank R L) ≠ 0

end base_nontrivial

section base_domain

variable (R L)
variable [IsDomain R] [Module.Finite R L] [Module.Free R L]

open Cardinal MvPolynomial in
lemma exists_isRegular' (h : Cardinal.lift.{u} (Module.rank R L) ≤ Cardinal.lift.{v} #R) :
    ∃ x : L, IsRegular R x := by
  let b := Module.Free.chooseBasis R L
  let n := Fintype.card (Module.Free.ChooseBasisIndex R L)
  have aux₁ := adCharpoly_coeff_isHomogeneous b (rank R L) (n - rank R L) (by simp [rank_le_card])
  have aux₂ : ↑(n - rank R L) ≤ #R := by
    trans ↑n
    · simp only [Nat.cast_le, tsub_le_iff_right, le_add_iff_nonneg_right, zero_le]
    rw [← Cardinal.lift_le.{v}]
    apply le_trans _ h
    rw [Module.Free.rank_eq_card_chooseBasisIndex R L]
    simp
  obtain ⟨x, hx⟩ :=
    aux₁.exists_eval_ne_zero_of_totalDegree_le_card (adCharpoly_coeff_rank_ne_zero R L) aux₂
  let c := Finsupp.equivFunOnFinite.symm x
  use b.repr.symm c
  sorry

lemma exists_isRegular [Infinite R] :
    ∃ x : L, IsRegular R x := by
  apply exists_isRegular'
  rw [Module.Free.rank_eq_card_chooseBasisIndex R L, Cardinal.mk_fintype]
  simp only [Cardinal.lift_natCast, Cardinal.nat_le_lift_iff]
  exact (Cardinal.nat_lt_aleph0 _).le.trans <| Cardinal.infinite_iff.mp ‹Infinite R›

end base_domain

end LieAlgebra

-- end LieAlgebra
