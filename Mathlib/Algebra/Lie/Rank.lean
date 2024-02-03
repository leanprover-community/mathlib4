import Mathlib.Algebra.Lie.CharPolyPoly
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Data.MvPolynomial.Monad

open BigOperators

variable {R L ι : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [Fintype ι]

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

end basis

-- lemma exists_ad_charpoly_coeff_ne_zero (x : L) :
--     ∃ n, (ad R L x).toMatrixcharpoly.coeff n ≠ 0 :=

-- variable (R L)

-- open Matrix.charpoly in
-- def rank : ℕ :=

-- end LieAlgebra
