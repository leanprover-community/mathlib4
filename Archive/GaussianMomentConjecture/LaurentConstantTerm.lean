/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Archive.GaussianMomentConjecture.ConstantTermRelations
import Archive.GaussianMomentConjecture.OrbitProduct
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Computability.Reduce
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.LinearAlgebra.Lagrange

/-!
# Check A for the orbit-product argument: a Laurent constant term is an ordinary coefficient

If `R` is an ordinary polynomial and

`Λ(T) = T⁻ᴹ R(T)`,

then the constant coefficient of `Λ^m` is the coefficient of `X^(M*m)` in
`R^m`.  This is the coefficient-shift identity called **Check A** in the
the orbit-product argument / DvdK formalization map.  Keeping it over an arbitrary commutative
semiring makes the bridge independent of the later complex/Galois argument.
-/

open Polynomial
open scoped BigOperators

namespace GMC2.LaurentConstantTerm

open LaurentPolynomial

variable {A : Type*} [CommSemiring A]

/-- Multiplying a Laurent polynomial by `T^s` translates its coefficient at
`k` to the old coefficient at `k-s`. -/
theorem coeff_mul_T (f : LaurentPolynomial A) (s k : ℤ) :
    (f * (T s : LaurentPolynomial A)).coeff k = f.coeff (k - s) := by
  rw [show (T s : LaurentPolynomial A) = AddMonoidAlgebra.single s (1 : A) from rfl,
    AddMonoidAlgebra.coeff_mul_single_eq_coeff_mul (m₂ := k - s) (fun m' _ => by omega), mul_one]

/-- **Check A.**  For `Λ = R(T) T^{-M}`, `CT(Λ^m) = [X^{Mm}]R^m`.

The left side uses evaluation at exponent `0` because a Laurent polynomial is
implemented as a finitely supported function `ℤ → A`; the right side is the
ordinary polynomial coefficient API consumed by the orbit-product argument generating
polynomial `Φ(X) = X^M - t R(X)`. -/
theorem constantCoeff_shifted_pow_eq_coeff_pow (R : A[X]) (M m : ℕ) :
    ((Polynomial.toLaurent R * (T (-(M : ℤ)) : LaurentPolynomial A)) ^ m).coeff 0 =
      (R ^ m).coeff (M * m) := by
  rw [mul_pow, ← map_pow, T_pow, coeff_mul_T]
  have hindex : (0 - (m : ℤ) * -(M : ℤ)) = ((M * m : ℕ) : ℤ) := by
    push_cast
    ring
  rw [hindex, coeff_toLaurent]
  exact Finsupp.mapDomain_apply (Nat.castEmbedding (R := ℤ)).injective _ _

/-- A product of Laurent monomials retains exactly two coordinates: the
product of coefficients and the sum of exponents. -/
theorem prod_monomial_eq {ι : Type*} (s : Finset ι) (q : ι → ℤ) (c : ι → A) (r : ι → ℕ) :
    ∏ i ∈ s, (LaurentPolynomial.C (c i) * T (q i)) ^ r i =
      LaurentPolynomial.C (∏ i ∈ s, c i ^ r i) * T (∑ i ∈ s, (r i : ℤ) * q i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.prod_insert ha, Finset.sum_insert ha]
      rw [ih]
      simp only [mul_pow, map_pow, T_pow, map_mul]
      rw [T_add]
      ring

/-- The universal relation in `ConstantTermRelations` really is the
constant coefficient of the corresponding finite Laurent polynomial power.
This is the semantic half of Check A and fixes the exact interface to
`GMC2.DvdKInterface.DvdK1`. -/
theorem constantCoeff_pow_eq_aeval_constantTermRelation
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Algebra ℚ A]
    (q : ι → ℤ) (c : ι → A) (m : ℕ) :
    (((∑ i : ι, LaurentPolynomial.C (c i) * T (q i)) ^ m :
        LaurentPolynomial A)).coeff 0 =
      MvPolynomial.aeval c
        (GMC2.ConstantTermRelations.constantTermRelation q m) := by
  classical
  have haeval :
      MvPolynomial.aeval c
          (GMC2.ConstantTermRelations.constantTermRelation q m) =
        ∑ r ∈ Finset.piAntidiag (Finset.univ : Finset ι) m,
          if GMC2.ConstantTermRelations.totalCharge q r = 0 then
            (Nat.multinomial Finset.univ r : A) * ∏ i, c i ^ r i
          else 0 := by
    simp only [GMC2.ConstantTermRelations.constantTermRelation, map_sum,
      MvPolynomial.aeval_def]
    apply Finset.sum_congr rfl
    intro r hr
    split_ifs with hbalanced
    · simp only [MvPolynomial.eval₂_monomial, map_natCast]
      rw [Finsupp.prod_fintype]
      · simp only [Finsupp.coe_equivFunOnFinite_symm]
      · intro i
        simp
    · simp
  rw [Finset.sum_pow_eq_sum_piAntidiag]
  rw [haeval]
  change (AddMonoidAlgebra.coeff
      (∑ k ∈ Finset.piAntidiag (Finset.univ : Finset ι) m,
        (Nat.multinomial Finset.univ k : LaurentPolynomial A) *
          ∏ i, (LaurentPolynomial.C (c i) * T (q i)) ^ k i)) 0 = _
  rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro r hr
  rw [prod_monomial_eq]
  change (((Nat.multinomial Finset.univ r : LaurentPolynomial A) *
      (LaurentPolynomial.C (∏ i, c i ^ r i) *
        T (∑ i, (r i : ℤ) * q i)) : LaurentPolynomial A)).coeff 0 = _
  rw [← mul_assoc, coeff_mul_T]
  have hconst :
      (Nat.multinomial Finset.univ r : LaurentPolynomial A) *
          LaurentPolynomial.C (∏ i, c i ^ r i) =
        LaurentPolynomial.C
          ((Nat.multinomial Finset.univ r : A) * ∏ i, c i ^ r i) := by
    simp only [map_mul, map_natCast]
  rw [hconst]
  by_cases hq : GMC2.ConstantTermRelations.totalCharge q r = 0
  · have hsum : ∑ i, (r i : ℤ) * q i = 0 := by
      simpa only [GMC2.ConstantTermRelations.totalCharge] using hq
    simp only [LaurentPolynomial.C_apply, hsum, zero_sub, neg_zero, hq, if_pos]
  · have hsum : ¬(∑ i, (r i : ℤ) * q i) = 0 := by
      simpa only [GMC2.ConstantTermRelations.totalCharge] using hq
    simp only [LaurentPolynomial.C_apply, zero_sub, neg_eq_zero, hsum, hq, if_false]

/-- Shift every Laurent exponent upward by `M` and regard the result as an
ordinary polynomial.  A lower-bound hypothesis below guarantees that
`Int.toNat` discards no exponent information. -/
noncomputable def shiftedPolynomial
    {ι : Type*} [Fintype ι] (q : ι → ℤ) (c : ι → A) (M : ℕ) : A[X] :=
  ∑ i : ι, Polynomial.monomial (q i + (M : ℤ)).toNat (c i)

/-- Shifting `shiftedPolynomial` back down by `M` recovers the original
Laurent polynomial, provided every shifted exponent is nonnegative. -/
theorem toLaurent_shiftedPolynomial_mul_T
    {ι : Type*} [Fintype ι]
    (q : ι → ℤ) (c : ι → A) (M : ℕ)
    (hM : ∀ i, -(M : ℤ) ≤ q i) :
    Polynomial.toLaurent (shiftedPolynomial q c M) * T (-(M : ℤ)) =
      ∑ i : ι, LaurentPolynomial.C (c i) * T (q i) := by
  classical
  simp only [shiftedPolynomial, map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Polynomial.toLaurent_C_mul_T, mul_assoc, ← T_add]
  congr 2
  have hiM := hM i
  have hnonneg : 0 ≤ q i + (M : ℤ) := by omega
  rw [Int.toNat_of_nonneg hnonneg]
  omega

/-- **Repository-facing Check A.**  If `R` is obtained by shifting the finite
charge support upward by any common `M`, then its central coefficient at every
power is exactly the evaluated universal constant-term relation.

No injectivity, nonzero-coefficient, or straddling hypothesis is needed for
this identity; those hypotheses enter only in the later nonvanishing theorem.
-/
theorem coeff_shiftedPolynomial_pow_eq_aeval_constantTermRelation
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Algebra ℚ A]
    (q : ι → ℤ) (c : ι → A) (M m : ℕ)
    (hM : ∀ i, -(M : ℤ) ≤ q i) :
    ((shiftedPolynomial q c M) ^ m).coeff (M * m) =
      MvPolynomial.aeval c
        (GMC2.ConstantTermRelations.constantTermRelation q m) := by
  rw [← constantCoeff_shifted_pow_eq_coeff_pow]
  rw [toLaurent_shiftedPolynomial_mul_T q c M hM]
  exact constantCoeff_pow_eq_aeval_constantTermRelation q c m

end GMC2.LaurentConstantTerm


namespace GMC2.AdditiveOrbitSum

open Finset MulAction

variable {G Ω B : Type*} [Group G] [Fintype G] [MulAction G Ω]
  [Fintype Ω] [DecidableEq Ω]

/-- Additive companion to `GMC2.OrbitProduct.prod_smul_eq_prod_pow_card_stabilizer`.
For a transitive finite action, summing a function along one group orbit
counts every point with the cardinality of a stabilizer. -/
theorem sum_smul_eq_card_stabilizer_nsmul [IsPretransitive G Ω] [AddCommMonoid B]
    (f : Ω → B) (x : Ω) :
    ∑ g : G, f (g • x) =
      Fintype.card (stabilizer G x) • ∑ α : Ω, f α := by
  rw [← Fintype.sum_fiberwise (fun g : G ↦ g • x) (fun g ↦ f (g • x))]
  have key : ∀ y : Ω,
      (∑ i : {g : G // g • x = y}, f ((i : G) • x)) =
        Fintype.card (stabilizer G x) • f y := by
    intro y
    rw [Finset.sum_congr rfl (fun i _ ↦ congrArg f i.2)]
    simp [GMC2.OrbitProduct.card_fiber_smul_eq_card_stabilizer x y]
  rw [Finset.sum_congr rfl (fun y _ ↦ key y), Finset.smul_sum]

/-- Uniform incidence identity for a subset all of whose group translates
have the same weighted sum `a`.  This is the additive Galois-orbit mechanism:
the left side counts translates, while the right side counts root incidence.
-/
theorem card_nsmul_translateSum_eq [IsPretransitive G Ω] [AddCommMonoid B]
    (f : Ω → B) (S : Finset Ω) (x : Ω) (a : B)
    (htranslate : ∀ g : G, ∑ β ∈ S, f (g • β) = a) :
    Fintype.card G • a =
      (S.card * Fintype.card (stabilizer G x)) • ∑ α : Ω, f α := by
  calc
    Fintype.card G • a = ∑ _g : G, a := by simp
    _ = ∑ g : G, ∑ β ∈ S, f (g • β) :=
      Finset.sum_congr rfl (fun g _ ↦ (htranslate g).symm)
    _ = ∑ β ∈ S, ∑ g : G, f (g • β) := by rw [Finset.sum_comm]
    _ = ∑ β ∈ S,
        Fintype.card (stabilizer G x) • ∑ α : Ω, f α := by
      apply Finset.sum_congr rfl
      intro β hβ
      rw [sum_smul_eq_card_stabilizer_nsmul f β,
        GMC2.OrbitProduct.card_stabilizer_eq_card_stabilizer β x]
    _ = (S.card * Fintype.card (stabilizer G x)) • ∑ α : Ω, f α := by
      rw [Finset.sum_const]
      exact (mul_nsmul' (∑ α : Ω, f α) S.card
        (Fintype.card (stabilizer G x))).symm

omit [DecidableEq Ω] [Fintype G] in
/-- **Additive orbit contradiction.**  Over a characteristic-zero field, no
subset can have every translate of its weighted sum equal to `1` while the
full-orbit weighted sum is `0`.

In the proposed orbit-product route, `f(α)=α^(M-1)/Φ'(α)`, `S` is the small-root
subset, the germ identity gives every translated sum as `1`, and Lagrange
interpolation gives the full-root sum as `0`.
-/
theorem translateSum_one_ne_fullSum_zero
    [IsPretransitive G Ω] [Finite G] {K : Type*} [Field K] [CharZero K]
    (f : Ω → K) (S : Finset Ω) (x : Ω)
    (htranslate : ∀ g : G, ∑ β ∈ S, f (g • β) = 1)
    (hfull : ∑ α : Ω, f α = 0) : False := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  have h := card_nsmul_translateSum_eq f S x 1 htranslate
  rw [hfull, nsmul_zero] at h
  have hcast : (Fintype.card G : K) = 0 := by simp at h
  exact (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) hcast

end GMC2.AdditiveOrbitSum


namespace GMC2.FullRootLagrange

open Polynomial
open scoped BigOperators

/-- Lagrange's top-coefficient identity specialized below the top degree:
for `k+1 < |s|`, the sum of `α^k` divided by the nodal derivative is zero.
This is the residue-at-infinity identity needed by the additive orbit-product argument
route, stated directly for a finite set of distinct roots. -/
theorem sum_pow_div_derivative_nodal_eq_zero
    {K : Type*} [Field K] (s : Finset K) (k : ℕ)
    (hk : k + 1 < s.card) :
    ∑ α ∈ s, α ^ k /
        (Polynomial.derivative (Lagrange.nodal s id)).eval α = 0 := by
  classical
  have hdeg : ((Polynomial.X : K[X]) ^ k).degree < s.card := by
    rw [Polynomial.degree_X_pow]
    exact_mod_cast (lt_trans (Nat.lt_succ_self k) hk)
  have hlag := Lagrange.coeff_eq_sum (s := s) (v := id)
    (P := (Polynomial.X : K[X]) ^ k) Function.injective_id.injOn hdeg
  have hcoeff : ((Polynomial.X : K[X]) ^ k).coeff (s.card - 1) = 0 := by
    rw [Polynomial.coeff_X_pow]
    simp only [ite_eq_right_iff]
    intro heq
    omega
  rw [hcoeff] at hlag
  calc
    ∑ α ∈ s, α ^ k /
        (Polynomial.derivative (Lagrange.nodal s id)).eval α =
        ∑ α ∈ s, ((Polynomial.X : K[X]) ^ k).eval α /
          ∏ β ∈ s.erase α, (α - β) := by
      apply Finset.sum_congr rfl
      intro α hα
      have hderiv := Lagrange.eval_nodal_derivative_eval_node_eq
        (s := s) (v := id) hα
      simp only [id_eq] at hderiv
      rw [hderiv, Lagrange.eval_nodal]
      simp
    _ = 0 := hlag.symm

/-- The exact exponent used by the orbit-product argument: if `0 < M < |s|`, then the full
root sum of `α^(M-1)/Φ'(α)` vanishes for the monic nodal polynomial `Φ`.
-/
theorem sum_pow_pred_div_derivative_nodal_eq_zero
    {K : Type*} [Field K] (s : Finset K) (M : ℕ)
    (hM0 : 0 < M) (hMcard : M < s.card) :
    ∑ α ∈ s, α ^ (M - 1) /
        (Polynomial.derivative (Lagrange.nodal s id)).eval α = 0 := by
  apply sum_pow_div_derivative_nodal_eq_zero s (M - 1)
  omega

end GMC2.FullRootLagrange

