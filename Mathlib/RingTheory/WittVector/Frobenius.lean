/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module ring_theory.witt_vector.frobenius
! leanprover-community/mathlib commit 2196ab363eb097c008d4497125e0dde23fb36db2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Nat.Multiplicity
import Mathbin.Data.Zmod.Algebra
import Mathbin.RingTheory.WittVector.Basic
import Mathbin.RingTheory.WittVector.IsPoly
import Mathbin.FieldTheory.PerfectClosure

/-!
## The Frobenius operator

If `R` has characteristic `p`, then there is a ring endomorphism `frobenius R p`
that raises `r : R` to the power `p`.
By applying `witt_vector.map` to `frobenius R p`, we obtain a ring endomorphism `𝕎 R →+* 𝕎 R`.
It turns out that this endomorphism can be described by polynomials over `ℤ`
that do not depend on `R` or the fact that it has characteristic `p`.
In this way, we obtain a Frobenius endomorphism `witt_vector.frobenius_fun : 𝕎 R → 𝕎 R`
for every commutative ring `R`.

Unfortunately, the aforementioned polynomials can not be obtained using the machinery
of `witt_structure_int` that was developed in `structure_polynomial.lean`.
We therefore have to define the polynomials by hand, and check that they have the required property.

In case `R` has characteristic `p`, we show in `frobenius_fun_eq_map_frobenius`
that `witt_vector.frobenius_fun` is equal to `witt_vector.map (frobenius R p)`.

### Main definitions and results

* `frobenius_poly`: the polynomials that describe the coefficients of `frobenius_fun`;
* `frobenius_fun`: the Frobenius endomorphism on Witt vectors;
* `frobenius_fun_is_poly`: the tautological assertion that Frobenius is a polynomial function;
* `frobenius_fun_eq_map_frobenius`: the fact that in characteristic `p`, Frobenius is equal to
  `witt_vector.map (frobenius R p)`.

TODO: Show that `witt_vector.frobenius_fun` is a ring homomorphism,
and bundle it into `witt_vector.frobenius`.

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]
-/


namespace WittVector

variable {p : ℕ} {R S : Type _} [hp : Fact p.Prime] [CommRing R] [CommRing S]

-- mathport name: expr𝕎
local notation "𝕎" => WittVector p

-- type as `\bbW`
noncomputable section

open MvPolynomial Finset

open scoped BigOperators

variable (p)

include hp

/-- The rational polynomials that give the coefficients of `frobenius x`,
in terms of the coefficients of `x`.
These polynomials actually have integral coefficients,
see `frobenius_poly` and `map_frobenius_poly`. -/
def frobeniusPolyRat (n : ℕ) : MvPolynomial ℕ ℚ :=
  bind₁ (wittPolynomial p ℚ ∘ fun n => n + 1) (xInTermsOfW p ℚ n)
#align witt_vector.frobenius_poly_rat WittVector.frobeniusPolyRat

theorem bind₁_frobeniusPolyRat_wittPolynomial (n : ℕ) :
    bind₁ (frobeniusPolyRat p) (wittPolynomial p ℚ n) = wittPolynomial p ℚ (n + 1) :=
  by
  delta frobenius_poly_rat
  rw [← bind₁_bind₁, bind₁_xInTermsOfW_wittPolynomial, bind₁_X_right]
#align witt_vector.bind₁_frobenius_poly_rat_witt_polynomial WittVector.bind₁_frobeniusPolyRat_wittPolynomial

/-- An auxiliary definition, to avoid an excessive amount of finiteness proofs
for `multiplicity p n`. -/
private def pnat_multiplicity (n : ℕ+) : ℕ :=
  (multiplicity p n).get <| multiplicity.finite_nat_iff.mpr <| ⟨ne_of_gt hp.1.one_lt, n.2⟩

-- mathport name: exprv
local notation "v" => pnatMultiplicity

/-- An auxiliary polynomial over the integers, that satisfies
`p * (frobenius_poly_aux p n) + X n ^ p = frobenius_poly p n`.
This makes it easy to show that `frobenius_poly p n` is congruent to `X n ^ p`
modulo `p`. -/
noncomputable def frobeniusPolyAux : ℕ → MvPolynomial ℕ ℤ
  | n =>
    X (n + 1) -
      ∑ i : Fin n,
        have := i.is_lt
        ∑ j in range (p ^ (n - i)),
          (X i ^ p) ^ (p ^ (n - i) - (j + 1)) * frobenius_poly_aux i ^ (j + 1) *
            C
              ↑((p ^ (n - i)).choose (j + 1) / p ^ (n - i - v p ⟨j + 1, Nat.succ_pos j⟩) *
                    ↑p ^ (j - v p ⟨j + 1, Nat.succ_pos j⟩) :
                  ℕ)
#align witt_vector.frobenius_poly_aux WittVector.frobeniusPolyAux

theorem frobeniusPolyAux_eq (n : ℕ) :
    frobeniusPolyAux p n =
      X (n + 1) -
        ∑ i in range n,
          ∑ j in range (p ^ (n - i)),
            (X i ^ p) ^ (p ^ (n - i) - (j + 1)) * frobeniusPolyAux p i ^ (j + 1) *
              C
                ↑((p ^ (n - i)).choose (j + 1) / p ^ (n - i - v p ⟨j + 1, Nat.succ_pos j⟩) *
                      ↑p ^ (j - v p ⟨j + 1, Nat.succ_pos j⟩) :
                    ℕ) :=
  by rw [frobenius_poly_aux, ← Fin.sum_univ_eq_sum_range]
#align witt_vector.frobenius_poly_aux_eq WittVector.frobeniusPolyAux_eq

/-- The polynomials that give the coefficients of `frobenius x`,
in terms of the coefficients of `x`. -/
def frobeniusPoly (n : ℕ) : MvPolynomial ℕ ℤ :=
  X n ^ p + C ↑p * frobeniusPolyAux p n
#align witt_vector.frobenius_poly WittVector.frobeniusPoly

/-
Our next goal is to prove
```
lemma map_frobenius_poly (n : ℕ) :
  mv_polynomial.map (int.cast_ring_hom ℚ) (frobenius_poly p n) = frobenius_poly_rat p n
```
This lemma has a rather long proof, but it mostly boils down to applying induction,
and then using the following two key facts at the right point.
-/
/-- A key divisibility fact for the proof of `witt_vector.map_frobenius_poly`. -/
theorem MapFrobeniusPoly.key₁ (n j : ℕ) (hj : j < p ^ n) :
    p ^ (n - v p ⟨j + 1, j.succ_pos⟩) ∣ (p ^ n).choose (j + 1) :=
  by
  apply multiplicity.pow_dvd_of_le_multiplicity
  rw [hp.out.multiplicity_choose_prime_pow hj j.succ_ne_zero]
  rfl
#align witt_vector.map_frobenius_poly.key₁ WittVector.MapFrobeniusPoly.key₁

/-- A key numerical identity needed for the proof of `witt_vector.map_frobenius_poly`. -/
theorem MapFrobeniusPoly.key₂ {n i j : ℕ} (hi : i ≤ n) (hj : j < p ^ (n - i)) :
    j - v p ⟨j + 1, j.succ_pos⟩ + n = i + j + (n - i - v p ⟨j + 1, j.succ_pos⟩) :=
  by
  generalize h : v p ⟨j + 1, j.succ_pos⟩ = m
  rsuffices ⟨h₁, h₂⟩ : m ≤ n - i ∧ m ≤ j
  ·
    rw [tsub_add_eq_add_tsub h₂, add_comm i j, add_tsub_assoc_of_le (h₁.trans (Nat.sub_le n i)),
      add_assoc, tsub_right_comm, add_comm i,
      tsub_add_cancel_of_le (le_tsub_of_add_le_right ((le_tsub_iff_left hi).mp h₁))]
  have hle : p ^ m ≤ j + 1 := h ▸ Nat.le_of_dvd j.succ_pos (multiplicity.pow_multiplicity_dvd _)
  exact
    ⟨(pow_le_pow_iff hp.1.one_lt).1 (hle.trans hj),
      Nat.le_of_lt_succ ((Nat.lt_pow_self hp.1.one_lt m).trans_le hle)⟩
#align witt_vector.map_frobenius_poly.key₂ WittVector.MapFrobeniusPoly.key₂

theorem map_frobeniusPoly (n : ℕ) :
    MvPolynomial.map (Int.castRingHom ℚ) (frobeniusPoly p n) = frobeniusPolyRat p n :=
  by
  rw [frobenius_poly, RingHom.map_add, RingHom.map_mul, RingHom.map_pow, map_C, map_X, eq_intCast,
    Int.cast_ofNat, frobenius_poly_rat]
  apply Nat.strong_induction_on n; clear n
  intro n IH
  rw [xInTermsOfW_eq]
  simp only [AlgHom.map_sum, AlgHom.map_sub, AlgHom.map_mul, AlgHom.map_pow, bind₁_C_right]
  have h1 : ↑p ^ n * ⅟ (↑p : ℚ) ^ n = 1 := by rw [← mul_pow, mul_invOf_self, one_pow]
  rw [bind₁_X_right, Function.comp_apply, wittPolynomial_eq_sum_c_mul_x_pow, sum_range_succ,
    sum_range_succ, tsub_self, add_tsub_cancel_left, pow_zero, pow_one, pow_one, sub_mul, add_mul,
    add_mul, mul_right_comm, mul_right_comm (C (↑p ^ (n + 1))), ← C_mul, ← C_mul, pow_succ,
    mul_assoc (↑p) (↑p ^ n), h1, mul_one, C_1, one_mul, add_comm _ (X n ^ p), add_assoc, ← add_sub,
    add_right_inj, frobenius_poly_aux_eq, RingHom.map_sub, map_X, mul_sub, sub_eq_add_neg,
    add_comm _ (C ↑p * X (n + 1)), ← add_sub, add_right_inj, neg_eq_iff_eq_neg, neg_sub, eq_comm]
  simp only [RingHom.map_sum, mul_sum, sum_mul, ← sum_sub_distrib]
  apply sum_congr rfl
  intro i hi
  rw [mem_range] at hi 
  rw [← IH i hi]
  clear IH
  rw [add_comm (X i ^ p), add_pow, sum_range_succ', pow_zero, tsub_zero, Nat.choose_zero_right,
    one_mul, Nat.cast_one, mul_one, mul_add, add_mul, Nat.succ_sub (le_of_lt hi),
    Nat.succ_eq_add_one (n - i), pow_succ, pow_mul, add_sub_cancel, mul_sum, sum_mul]
  apply sum_congr rfl
  intro j hj
  rw [mem_range] at hj 
  rw [RingHom.map_mul, RingHom.map_mul, RingHom.map_pow, RingHom.map_pow, RingHom.map_pow,
    RingHom.map_pow, RingHom.map_pow, map_C, map_X, mul_pow]
  rw [mul_comm (C ↑p ^ i), mul_comm _ ((X i ^ p) ^ _), mul_comm (C ↑p ^ (j + 1)), mul_comm (C ↑p)]
  simp only [mul_assoc]
  apply congr_arg
  apply congr_arg
  rw [← C_eq_coe_nat]
  simp only [← RingHom.map_pow, ← C_mul]
  rw [C_inj]
  simp only [invOf_eq_inv, eq_intCast, inv_pow, Int.cast_ofNat, Nat.cast_mul, Int.cast_mul]
  rw [Rat.coe_nat_div _ _ (map_frobenius_poly.key₁ p (n - i) j hj)]
  simp only [Nat.cast_pow, pow_add, pow_one]
  suffices
    ((p ^ (n - i)).choose (j + 1) * p ^ (j - v p ⟨j + 1, j.succ_pos⟩) * p * p ^ n : ℚ) =
      p ^ j * p * ((p ^ (n - i)).choose (j + 1) * p ^ i) * p ^ (n - i - v p ⟨j + 1, j.succ_pos⟩)
    by
    have aux : ∀ k : ℕ, (p ^ k : ℚ) ≠ 0 := by intro; apply pow_ne_zero; exact_mod_cast hp.1.NeZero
    simpa [aux, -one_div, field_simps] using this.symm
  rw [mul_comm _ (p : ℚ), mul_assoc, mul_assoc, ← pow_add, map_frobenius_poly.key₂ p hi.le hj]
  ring
#align witt_vector.map_frobenius_poly WittVector.map_frobeniusPoly

theorem frobeniusPoly_zMod (n : ℕ) :
    MvPolynomial.map (Int.castRingHom (ZMod p)) (frobeniusPoly p n) = X n ^ p :=
  by
  rw [frobenius_poly, RingHom.map_add, RingHom.map_pow, RingHom.map_mul, map_X, map_C]
  simp only [Int.cast_ofNat, add_zero, eq_intCast, ZMod.nat_cast_self, MulZeroClass.zero_mul, C_0]
#align witt_vector.frobenius_poly_zmod WittVector.frobeniusPoly_zMod

@[simp]
theorem bind₁_frobeniusPoly_wittPolynomial (n : ℕ) :
    bind₁ (frobeniusPoly p) (wittPolynomial p ℤ n) = wittPolynomial p ℤ (n + 1) :=
  by
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  simp only [map_bind₁, map_frobenius_poly, bind₁_frobenius_poly_rat_witt_polynomial,
    map_wittPolynomial]
#align witt_vector.bind₁_frobenius_poly_witt_polynomial WittVector.bind₁_frobeniusPoly_wittPolynomial

variable {p}

/-- `frobenius_fun` is the function underlying the ring endomorphism
`frobenius : 𝕎 R →+* frobenius 𝕎 R`. -/
def frobeniusFun (x : 𝕎 R) : 𝕎 R :=
  mk' p fun n => MvPolynomial.aeval x.coeff (frobeniusPoly p n)
#align witt_vector.frobenius_fun WittVector.frobeniusFun

theorem coeff_frobeniusFun (x : 𝕎 R) (n : ℕ) :
    coeff (frobeniusFun x) n = MvPolynomial.aeval x.coeff (frobeniusPoly p n) := by
  rw [frobenius_fun, coeff_mk]
#align witt_vector.coeff_frobenius_fun WittVector.coeff_frobeniusFun

variable (p)

/-- `frobenius_fun` is tautologically a polynomial function.

See also `frobenius_is_poly`. -/
@[is_poly]
theorem frobeniusFun_isPoly : IsPoly p fun R _Rcr => @frobeniusFun p R _ _Rcr :=
  ⟨⟨frobeniusPoly p, by intros; funext n; apply coeff_frobenius_fun⟩⟩
#align witt_vector.frobenius_fun_is_poly WittVector.frobeniusFun_isPoly

variable {p}

@[ghost_simps]
theorem ghostComponent_frobeniusFun (n : ℕ) (x : 𝕎 R) :
    ghostComponent n (frobeniusFun x) = ghostComponent (n + 1) x := by
  simp only [ghost_component_apply, frobenius_fun, coeff_mk, ← bind₁_frobenius_poly_witt_polynomial,
    aeval_bind₁]
#align witt_vector.ghost_component_frobenius_fun WittVector.ghostComponent_frobeniusFun

/-- If `R` has characteristic `p`, then there is a ring endomorphism
that raises `r : R` to the power `p`.
By applying `witt_vector.map` to this endomorphism,
we obtain a ring endomorphism `frobenius R p : 𝕎 R →+* 𝕎 R`.

The underlying function of this morphism is `witt_vector.frobenius_fun`.
-/
def frobenius : 𝕎 R →+* 𝕎 R where
  toFun := frobeniusFun
  map_zero' :=
    by
    refine'
      is_poly.ext ((frobenius_fun_is_poly p).comp WittVector.zeroIsPoly)
        (WittVector.zeroIsPoly.comp (frobenius_fun_is_poly p)) _ _ 0
    ghost_simp
  map_one' :=
    by
    refine'
      is_poly.ext ((frobenius_fun_is_poly p).comp WittVector.oneIsPoly)
        (WittVector.oneIsPoly.comp (frobenius_fun_is_poly p)) _ _ 0
    ghost_simp
  map_add' := by ghost_calc _ _ <;> ghost_simp
  map_mul' := by ghost_calc _ _ <;> ghost_simp
#align witt_vector.frobenius WittVector.frobenius

theorem coeff_frobenius (x : 𝕎 R) (n : ℕ) :
    coeff (frobenius x) n = MvPolynomial.aeval x.coeff (frobeniusPoly p n) :=
  coeff_frobeniusFun _ _
#align witt_vector.coeff_frobenius WittVector.coeff_frobenius

@[ghost_simps]
theorem ghostComponent_frobenius (n : ℕ) (x : 𝕎 R) :
    ghostComponent n (frobenius x) = ghostComponent (n + 1) x :=
  ghostComponent_frobeniusFun _ _
#align witt_vector.ghost_component_frobenius WittVector.ghostComponent_frobenius

variable (p)

/-- `frobenius` is tautologically a polynomial function. -/
@[is_poly]
theorem frobenius_isPoly : IsPoly p fun R _Rcr => @frobenius p R _ _Rcr :=
  frobeniusFun_isPoly _
#align witt_vector.frobenius_is_poly WittVector.frobenius_isPoly

section CharP

variable [CharP R p]

@[simp]
theorem coeff_frobenius_charP (x : 𝕎 R) (n : ℕ) : coeff (frobenius x) n = x.coeff n ^ p :=
  by
  rw [coeff_frobenius]
  -- outline of the calculation, proofs follow below
  calc
    aeval (fun k => x.coeff k) (frobenius_poly p n) =
        aeval (fun k => x.coeff k)
          (MvPolynomial.map (Int.castRingHom (ZMod p)) (frobenius_poly p n)) :=
      _
    _ = aeval (fun k => x.coeff k) (X n ^ p : MvPolynomial ℕ (ZMod p)) := _
    _ = x.coeff n ^ p := _
    
  · conv_rhs => rw [aeval_eq_eval₂_hom, eval₂_hom_map_hom]
    apply eval₂_hom_congr (RingHom.ext_int _ _) rfl rfl
  · rw [frobenius_poly_zmod]
  · rw [AlgHom.map_pow, aeval_X]
#align witt_vector.coeff_frobenius_char_p WittVector.coeff_frobenius_charP

theorem frobenius_eq_map_frobenius : @frobenius p R _ _ = map (frobenius R p) :=
  by
  ext (x n)
  simp only [coeff_frobenius_char_p, map_coeff, frobenius_def]
#align witt_vector.frobenius_eq_map_frobenius WittVector.frobenius_eq_map_frobenius

@[simp]
theorem frobenius_zmodp (x : 𝕎 (ZMod p)) : frobenius x = x := by
  simp only [ext_iff, coeff_frobenius_char_p, ZMod.pow_card, eq_self_iff_true, forall_const]
#align witt_vector.frobenius_zmodp WittVector.frobenius_zmodp

variable (p R)

/-- `witt_vector.frobenius` as an equiv. -/
@[simps (config := { fullyApplied := false })]
def frobeniusEquiv [PerfectRing R p] : WittVector p R ≃+* WittVector p R :=
  {
    (WittVector.frobenius :
      WittVector p R →+* WittVector p
          R) with
    toFun := WittVector.frobenius
    invFun := map (pthRoot R p)
    left_inv := fun f => ext fun n => by rw [frobenius_eq_map_frobenius]; exact pthRoot_frobenius _
    right_inv := fun f =>
      ext fun n => by rw [frobenius_eq_map_frobenius]; exact frobenius_pthRoot _ }
#align witt_vector.frobenius_equiv WittVector.frobeniusEquiv

theorem frobenius_bijective [PerfectRing R p] :
    Function.Bijective (@WittVector.frobenius p R _ _) :=
  (frobeniusEquiv p R).Bijective
#align witt_vector.frobenius_bijective WittVector.frobenius_bijective

end CharP

end WittVector

