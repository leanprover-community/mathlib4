/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

import Mathlib.Analysis.Complex.IsIntegral
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.NumberTheory.Transcendental.Lindemann.AlgebraicPart
import Mathlib.NumberTheory.Transcendental.Lindemann.AnalyticalPart
import Mathlib.RingTheory.MvPolynomial.Symmetric.Eval

/-!
# The Lindemann-Weierstrass theorem

## References

* [Jacobson, *Basic Algebra I, 4.12*][jacobson1974]
-/

@[expose] public section

open scoped Nat

open Complex Finset Polynomial

variable {ι : Type*}

theorem linearIndependent_exp (u : ι → integralClosure ℚ ℂ) (u_inj : u.Injective) :
    LinearIndependent (integralClosure ℚ ℂ) fun i ↦ exp (u i) := by
  -- Start of proof of theorem 4.22 (Jacobson, p. 281).
  refine linearIndependent_iff_finset_linearIndependent.mpr fun s ↦
    Fintype.linearIndependent_iff.mpr fun v h ↦ ?_
  -- Assume v is not identically zero.
  by_contra v0
  -- This implies we have a similar sum `w + ∑ p, w' p • ∑ u ∈ p.aroots ℂ, exp u = 0` where
  -- `w` and `w' p` are integers, `w ≠ 0`, and the `p` in the support of `w'` are integral
  -- polynomials with nonzero constant coefficients.
  obtain ⟨w, w0, w'', p0, h⟩ :=
    LindemannWeierstrass.exists_add_sum_map_aroots_eq_zero (ι := s)
      expMonoidHom (u ·) (u · |>.2) (Subtype.val_injective.comp (u_inj.comp Subtype.val_injective))
      (v ·) (v · |>.2) (by simpa [funext_iff] using v0) (by simpa [Algebra.smul_def] using h)
  simp_rw [expMonoidHom_apply, toAdd_ofAdd] at h
  let p : w''.support → ℤ[X] := Subtype.val
  let w' := w'' ∘ p
  -- Let `P` be the product of the `p j`, which has a nonzero constant coefficient as well.
  let P := ∏ j, p j
  have P0 : P.eval 0 ≠ 0 := by
    dsimp only [P]; rw [eval_prod, prod_ne_zero_iff]; exact fun ⟨p, hp⟩ _ => p0 p hp
  have P0' : P ≠ 0 := by intro h; simp [h] at P0
  have mem_aroots {j x} (hx : x ∈ (p j).aroots ℂ) : x ∈ P.aroots ℂ := by
    rw [mem_aroots', Polynomial.map_ne_zero_iff (algebraMap ℤ ℂ).injective_int] at hx ⊢
    rw [map_prod]
    exact ⟨P0', prod_eq_zero (mem_univ _) hx.2⟩
  replace h : ↑w + ∑ j, w' j • (((p j).aroots ℂ).map exp).sum = 0 := by
    rwa [Finsupp.sum, ← Finset.sum_coe_sort] at h
  -- The following roughly matches Jacobson, p. 286.
  -- Let `k` be the leading coefficient of `P`, i.e. the product of those of the `p j`.
  let k := P.leadingCoeff
  have k0 : k ≠ 0 := leadingCoeff_ne_zero.mpr P0'
  have sz_h (j) : (p j).leadingCoeff ∣ k :=
    leadingCoeff_dvd_leadingCoeff (dvd_prod_of_mem _ (mem_univ j))
  -- Now there exists a constant `c : ℝ`, such that for each prime `p > |P₀|` we have `nₚ : ℤ` and
  -- `gₚ : ℤ[X]` such that
  -- * `p` does not divide `nₚ`
  -- * `deg(gₚ) ≤ p * deg(f) - 1` (`≤ p * deg(f)` is sufficient)
  -- * all complex roots `r` of `P` satisfy `|nₚ * exp r - p * gₚ(r)| ≤ c ^ p / (p - 1)!`
  obtain ⟨c, hc'⟩ := LindemannWeierstrass.exp_polynomial_approx P P0
  -- Let `L` be a nonnegative upper bound on the norms of the coefficients of the sum.
  let L := ∑ j, ‖w' j‖
  have L0 : 0 ≤ L := sum_nonneg fun _ _ ↦ norm_nonneg _
  -- Now there exists a sufficiently large prime `q` such that
  -- `L * (∑ i, ((p i).aroots ℂ).card) * (‖k‖ ^ P.natDegree * c) ^ q / (q - 1)! < 1`.
  let N := max (P.eval 0).natAbs (max k.natAbs w.natAbs)
  obtain ⟨q, hqN, prime_q, hq⟩ : ∃ q : ℕ, N < q ∧ Nat.Prime q ∧
      L * (∑ i, ((p i).aroots ℂ).card) * (‖k‖ ^ P.natDegree * c) ^ q / (q - 1)! < 1 := by
    have (x : ℝ) : Filter.Tendsto (fun n ↦ x ^ n / (n - 1)!) .atTop (nhds 0) := by
      rw [← Filter.tendsto_add_atTop_iff_nat 1]
      simpa [pow_succ', mul_div_assoc] using
        (FloorSemiring.tendsto_pow_div_factorial_atTop x).const_mul x
    simpa only [Nat.succ_le_iff, mul_div_assoc] using
      Filter.Frequently.forall_exists_of_atTop
        ((Filter.frequently_atTop.mpr Nat.exists_infinite_primes).and_eventually <|
          Filter.Tendsto.eventually_lt_const (u := 1) (by simp)
            ((this (‖k‖ ^ P.natDegree * c)).const_mul (L * ∑ i, Multiset.card ((p i).aroots ℂ))))
        (N + 1)
  -- And this `q` is in particular large enough to apply `hc'`.
  obtain ⟨n, hn, gp, hgp, hc⟩ := hc' q (by order) prime_q
  replace hgp : gp.natDegree ≤ P.natDegree * q := by rw [mul_comm]; exact hgp.trans tsub_le_self
  clear hc'
  let t := P.natDegree * q
  -- Now `k` is a nonzero integer such that for every `j`,
  -- `k ^ t * ∑ u ∈ (p j).aroots ℂ, gp u` is an integer.
  -- Let `sz` be the vector such that `sz j` is that corresponding integer.
  choose sz hsz using fun j ↦
    pow_smul_sum_map_aroots_aeval_mem_range_algebraMap (A := ℂ)
      (p j) gp k t (sz_h j) hgp (IsAlgClosed.splits _)
  replace hsz : k ^ t • ∑ j, w' j • (((p j).aroots ℂ).map fun x => gp.aeval x).sum =
      algebraMap ℤ ℂ (∑ j, w' j • sz j) := by
    simp_rw [smul_sum, smul_comm (k ^ t), ← hsz, map_sum, map_zsmul]
  -- Then `k ^ t * n * w + q * ∑ j, w' j • sz j
  --  = k ^ t • (∑ j, w' j • ∑ u ∈ (p j).aroots ℂ, q • gp u - n • exp u))`.
  have H' := calc
    ((k ^ t * n * w + q * ∑ j, w' j • sz j : ℤ) : ℂ)
    _ = k ^ t • (n • (w : ℂ) +
          q • ∑ j, w' j • (((p j).aroots ℂ).map fun x => gp.aeval x).sum) := by
      rw [smul_add, smul_comm (k ^ t) q, hsz]
      simp [mul_assoc]
    _ = k ^ t •
        (q • ∑ j, w' j • (((p j).aroots ℂ).map fun x => gp.aeval x).sum -
          n • ∑ j, w' j • (((p j).aroots ℂ).map fun x => exp x).sum) := by
      rw [← eq_neg_iff_add_eq_zero] at h
      rw [h, smul_neg, neg_add_eq_sub]
    _ = k ^ t •
          (∑ j, w' j • (((p j).aroots ℂ).map fun x => q • gp.aeval x).sum -
            ∑ j, w' j • (((p j).aroots ℂ).map fun x => n • exp x).sum) := by
      simp_rw [smul_sum, Multiset.smul_sum, Multiset.map_map, Function.comp,
        smul_comm n, smul_comm q]
    _ = k ^ t • ∑ j, w' j • (((p j).aroots ℂ).map fun x =>
                        q • gp.aeval x - n • exp x).sum := by
      simp only [← smul_sub, ← sum_sub_distrib, ← Multiset.sum_map_sub]
  -- And, as we've taken `q` sufficiently large, `‖k ^ t * n * w + q * ∑ j, w' j • sz j‖ < 1`.
  have H := calc
    ‖((k ^ t * n * w + q * ∑ j, w' j • sz j : ℤ) : ℂ)‖
    _ = ‖k ^ t • ∑ j, w' j • (((p j).aroots ℂ).map fun x => q • gp.aeval x - n • exp x).sum‖ := by
      rw [H']
    _ = ‖k ^ t‖ * ‖∑ j, w' j • (((p j).aroots ℂ).map fun x => q • gp.aeval x - n • exp x).sum‖ := by
      rw [norm_smul]
    _ ≤ ‖k ^ t‖ * ∑ j, L * ‖(((p j).aroots ℂ).map fun x => q • gp.aeval x - n • exp x).sum‖ := by
      grw [norm_sum_le]
      simp_rw [norm_smul]
      gcongr
      exact single_le_sum (fun _ _ ↦ norm_nonneg _) (mem_univ _)
    _ ≤ ‖k ^ t‖ *
        ∑ j, L * (Multiset.map (fun x ↦ ‖q • (aeval x) gp - n • cexp x‖) ((p j).aroots ℂ)).sum := by
      gcongr
      grw [norm_multiset_sum_le]
      rw [Multiset.map_map, Function.comp_def]
    _ ≤ ‖k ^ t‖ * ∑ j, L * (((p j).aroots ℂ).map fun _ => c ^ q / ↑(q - 1)!).sum := by
      gcongr
      refine Multiset.sum_map_le_sum_map _ _ fun x hx => ?_
      rw [norm_sub_rev]
      exact hc (mem_aroots hx)
    _ = L * (∑ i, ((p i).aroots ℂ).card) * (‖k‖ ^ P.natDegree * c) ^ q / (q - 1)! := by
      simp_rw [norm_pow, Multiset.map_const', Multiset.sum_replicate, ← mul_sum, ← sum_smul,
        nsmul_eq_mul]
      ring
    _ < 1 := hq
  -- The left-hand side is an integer with norm less than one, so is zero. Since the second term
  -- is a multiple of `q`, so is the first term.
  rw [norm_intCast, ← Int.cast_abs, ← Int.cast_one, Int.cast_lt, Int.abs_lt_one_iff] at H
  replace H : q ∣ (k ^ t * n * w).natAbs := by
    rw [← Int.ofNat_dvd_left, ← Int.dvd_add_self_mul, H]
    exact dvd_zero _
  -- But `q` is prime and divides none of the factors, so we have our contradiction.
  simp_rw [Int.natAbs_mul, prime_q.dvd_mul, Int.natAbs_pow] at H
  obtain (H | H) | H := H
  · order [Nat.le_of_dvd (Int.natAbs_pos.mpr k0) <| prime_q.dvd_of_dvd_pow H]
  · rw [← Int.ofNat_dvd_left] at H
    contradiction
  · order [Nat.le_of_dvd (Int.natAbs_pos.mpr w0) H]

theorem algebraicIndependent_exp (u : ι → integralClosure ℚ ℂ) (hu : LinearIndependent ℕ u) :
    AlgebraicIndependent (integralClosure ℚ ℂ) fun i ↦ exp (u i) := by
  rw [algebraicIndependent_iff]
  intro p hp
  simp_rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq, ← Algebra.smul_def, ← exp_nsmul,
    ← exp_sum] at hp
  norm_cast at hp
  apply AddMonoidAlgebra.ext
  apply linearIndependent_iff.mp (linearIndependent_exp (fun e ↦ ∑ i ∈ e.support, e i • u i) _)
  exacts [hp, hu]

theorem transcendental_exp {a : ℂ} (a0 : a ≠ 0) (ha : IsAlgebraic ℤ a) :
    Transcendental ℤ (exp a) := by
  intro h
  let a' : integralClosure ℚ ℂ := ⟨_, (ha.extendScalars (algebraMap ℤ ℚ).injective_int).isIntegral⟩
  let expa : integralClosure ℚ ℂ := ⟨_, (h.extendScalars (algebraMap ℤ ℚ).injective_int).isIntegral⟩
  have hli := linearIndependent_exp ![a', 0] (by simpa [a', Subtype.ext_iff])
  have := Fintype.linearIndependent_iff.mp hli ![1, -expa] (by simp [expa, a', Algebra.smul_def])
  simp at this

theorem transcendental_e : Transcendental ℤ (exp 1) :=
  transcendental_exp one_ne_zero isAlgebraic_one

theorem transcendental_pi : Transcendental ℤ Real.pi := by
  intro h
  have hpi : IsAlgebraic ℤ (Real.pi : ℂ) := by
    simpa only [coe_algebraMap] using h.algebraMap (A := ℂ)
  have hexp := transcendental_exp (a := Real.pi * I) (by simp [Real.pi_ne_zero])
    (hpi.mul (Complex.isIntegral_I ℤ).isAlgebraic)
  simp [Transcendental, isAlgebraic_one.neg] at hexp

theorem transcendental_log {u : ℂ} (hu0 : Complex.log u ≠ 0) (hu : IsAlgebraic ℤ u) :
    Transcendental ℤ (Complex.log u) := by
  intro h
  have := transcendental_exp hu0 h
  rw [Complex.exp_log (by aesop)] at this
  contradiction
