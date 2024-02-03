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
    (hf : ∃ f', f = MvPolynomial.C.comp f') (hg : ∀ i, (g i).IsHomogeneous n) :
    (eval₂ f g φ).IsHomogeneous (n * m) := by
  apply IsHomogeneous.sum
  intro i hi
  rw [← zero_add (n * m)]
  apply IsHomogeneous.mul _ _
  · rcases hf with ⟨f, rfl⟩
    apply isHomogeneous_C
  · convert IsHomogeneous.prod _ _ (fun k ↦ n * i k) _
    · rw [Finsupp.mem_support_iff] at hi
      rw [← Finset.mul_sum, hφ hi]
    · rintro k -
      apply (hg k).pow

-- move this
lemma MvPolynomial.IsHomogeneous.map {φ : MvPolynomial σ R} {n : ℕ}
    (hφ : φ.IsHomogeneous n) (f : R →+* S) :
    (map f φ).IsHomogeneous n := by
  rw [← one_mul n]
  apply hφ.eval₂ _ _ ⟨f, rfl⟩ (isHomogeneous_X _)

end

namespace LieAlgebra

section basis

variable (b : Basis ι R L)

open MvPolynomial in
noncomputable
def adMatrixPoly (ij : ι × ι) : MvPolynomial ι R :=
  ∑ k : ι, monomial (.single k 1) (b.repr ⁅b k, b ij.2⁆ ij.1)

lemma adMatrixPoly_eval (ij : ι × ι) (c : ι →₀ R) :
    MvPolynomial.eval c (adMatrixPoly b ij) = b.repr ⁅b.repr.symm c, b ij.2⁆ ij.1 := by
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
  rw [adCharpoly, Polynomial.coeff_map, ← one_mul j]
  apply (Matrix.charpoly.univ_coeff_isHomogeneous _ _ hij).eval₂
  · exact ⟨Int.castRingHom _, by ext; simp⟩
  rintro ⟨x, y⟩
  dsimp [adMatrixPoly]
  apply MvPolynomial.IsHomogeneous.sum
  rintro z -
  apply MvPolynomial.isHomogeneous_monomial _ _ _
  simp [Finsupp.single, Pi.single, Function.update]

-- open LinearMap in
-- lemma adCharpoly_map (x : L) :
--     (adCharpoly b).map (MvPolynomial.eval (b.repr x)) = (toMatrix (ad R L x) b b).charpoly := by
--   sorry

/-
Polynomial.coeff (LinearMap.charpoly ((ad R L) x)) (rank R L) ≠ 0 ↔
  (MvPolynomial.eval ⇑((chooseBasis R L).repr x)) (Polynomial.coeff (adCharpoly (chooseBasis R L)) (rank R L)) ≠ 0
-/

-- open LinearMap in
-- lemma adCharpoly_eval (x : L) (i : ℕ) :
--     MvPolynomial.eval (b.repr x) ((adCharpoly b).coeff i) =
--       (toMatrix (ad R L x) b b).charpoly.coeff i := by
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

open Module.Free

-- TODO: generalize to arbitrary basis
open LinearMap in
lemma adCharpoly_map (x : L) :
    (adCharpoly (chooseBasis R L)).map (MvPolynomial.eval ((chooseBasis R L).repr x)) =
      (ad R L x).charpoly := by
  rw [adCharpoly, Polynomial.map_map]
  convert (Matrix.charpoly.univ_map _)
  apply MvPolynomial.ringHom_ext
  · intro n; simp
  · rintro ⟨i, j⟩
    simp only [MvPolynomial.comp_eval₂Hom, adMatrixPoly_eval, LinearEquiv.symm_apply_apply,
      MvPolynomial.eval₂Hom_X', toMatrix_apply, ad_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      MvPolynomial.aeval_X]

-- TODO: generalize to arbitrary basis
open LinearMap in
lemma adCharpoly_eval (x : L) (i : ℕ) :
    MvPolynomial.eval ((chooseBasis R L).repr x) ((adCharpoly (chooseBasis R L)).coeff i) =
      (ad R L x).charpoly.coeff i := by
  simp [← adCharpoly_map]

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
  Nat.find (exists_adCharpoly_coeff_ne_zero (chooseBasis R L))

-- TODO: generalize to arbitrary basis
lemma adCharpoly_coeff_rank_ne_zero :
    (adCharpoly (chooseBasis R L)).coeff (rank R L) ≠ 0 := by
  classical
  exact Nat.find_spec (exists_adCharpoly_coeff_ne_zero (chooseBasis R L))

lemma rank_le_card : rank R L ≤ Fintype.card (ChooseBasisIndex R L) := by
  classical
  apply Nat.find_le
  rw [← adCharpoly_natDegree (chooseBasis R L), Polynomial.coeff_natDegree,
    (adCharpoly_monic _).leadingCoeff]
  apply one_ne_zero

lemma rank_le_rank [StrongRankCondition R] : rank R L ≤ Module.rank R L := by
  rw [rank_eq_card_chooseBasisIndex R L, Cardinal.mk_fintype, Nat.cast_le]
  apply rank_le_card

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
      ((adCharpoly (chooseBasis R L)).coeff (rank R L)) ≠ 0 := by
  rw [IsRegular, adCharpoly_eval]

end base_nontrivial

section base_domain

variable (R L)
variable [IsDomain R] [Module.Finite R L] [Module.Free R L]

open Module.Free

open Cardinal MvPolynomial in
lemma exists_isRegular' (h : Cardinal.lift.{u} (Module.rank R L) ≤ Cardinal.lift.{v} #R) :
    ∃ x : L, IsRegular R x := by
  let b := chooseBasis R L
  let n := Fintype.card (ChooseBasisIndex R L)
  have aux₁ := adCharpoly_coeff_isHomogeneous b (rank R L) (n - rank R L) (by simp [rank_le_card])
  have aux₂ : ↑(n - rank R L) ≤ #R := by
    trans ↑n
    · simp only [Nat.cast_le, tsub_le_iff_right, le_add_iff_nonneg_right, zero_le]
    rw [← Cardinal.lift_le.{v}]
    apply le_trans _ h
    rw [rank_eq_card_chooseBasisIndex R L]
    simp
  obtain ⟨x, hx⟩ :=
    aux₁.exists_eval_ne_zero_of_totalDegree_le_card (adCharpoly_coeff_rank_ne_zero R L) aux₂
  let c := Finsupp.equivFunOnFinite.symm x
  use b.repr.symm c
  rwa [isRegular_iff, LinearEquiv.apply_symm_apply]

lemma exists_isRegular [Infinite R] : ∃ x : L, IsRegular R x := by
  apply exists_isRegular'
  rw [rank_eq_card_chooseBasisIndex R L, Cardinal.mk_fintype]
  simp only [Cardinal.lift_natCast, Cardinal.nat_le_lift_iff]
  exact (Cardinal.nat_lt_aleph0 _).le.trans <| Cardinal.infinite_iff.mp ‹Infinite R›

end base_domain

end LieAlgebra

-- end LieAlgebra
