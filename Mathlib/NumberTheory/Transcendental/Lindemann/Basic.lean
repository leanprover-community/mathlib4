/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Mathlib.Analysis.Complex.IsIntegral
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.NumberTheory.Transcendental.Lindemann.AlgebraicPart
public import Mathlib.NumberTheory.Transcendental.Lindemann.AnalyticalPart
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Eval
public import Mathlib.Topology.Algebra.Order.Floor

/-!
# The Lindemann-Weierstrass theorem

## References

* [Jacobson, *Basic Algebra I, 4.12*][jacobson1974]
-/

@[expose] public section

open scoped Nat

open Complex Finset Polynomial

variable {ι : Type*}

private theorem linearIndependent_exp' [Fintype ι] (u : ι → ℂ) (hu : ∀ i, IsIntegral ℚ (u i))
    (u_inj : Function.Injective u) (v : ι → ℂ) (hv : ∀ i, IsIntegral ℚ (v i))
    (h : ∑ i, v i * exp (u i) = 0) : v = 0 := by
  -- Start of proof of theorem 4.22 (Jacobson, p. 281).
  -- Assume v is not identically zero.
  by_contra! v0
  -- This implies we have a similar sum `w + ∑ j, w' j • ∑ u ∈ (p j).aroots ℂ, exp u = 0` where
  -- `w` and `w' j` are integers, `w ≠ 0`, and `p j` are integral polynomials with nonzero constant
  -- coefficients.
  obtain ⟨w, w0, m, p, p0, w', h⟩ := linearIndependent_exp_aux expMonoidHom u hu u_inj v hv v0 h
  simp_rw [expMonoidHom_apply, toAdd_ofAdd] at h
  -- Note that none of the `p j` are zero.
  have p0' : ∀ j, p j ≠ 0 := by intro j h; simpa [h] using p0 j
  -- And the sum is not trivial. (Otherwise `w = 0`.)
  have m0 : m ≠ 0 := by
    rintro rfl; rw [Fin.sum_univ_zero, add_zero, Int.cast_eq_zero] at h
    exact w0 h
  have I : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero m0)
  -- Let `P` be the product of the `p j`, which has a nonzero constant coefficient as well.
  let P := ∏ j : Fin m, p j
  have P0 : P.eval 0 ≠ 0 := by
    dsimp only [P]; rw [eval_prod, prod_ne_zero_iff]; exact fun j _hj => p0 j
  have P0' : P ≠ 0 := by intro h; simp [h] at P0
  have mem_aroots {j x} (hx : x ∈ (p j).aroots ℂ) : x ∈ P.aroots ℂ := by
    rw [mem_aroots', Polynomial.map_ne_zero_iff (algebraMap ℤ ℂ).injective_int] at hx ⊢
    rw [map_prod]
    exact ⟨P0', prod_eq_zero (mem_univ _) hx.2⟩
  -- Now let `K` be the splitting field of `P` in ℂ.
  obtain ⟨K, _, _, _, _, _⟩ : ∃ (K : Type) (_ : Field K) (_ : Algebra ℚ K) (_ : Algebra K ℂ)
      (_ : IsScalarTower ℚ K ℂ), IsSplittingField ℚ K (P.map (algebraMap ℤ ℚ)) :=
    ⟨IntermediateField.adjoin ℚ ((P.map (algebraMap ℤ ℚ)).rootSet ℂ),
      inferInstance, inferInstance, inferInstance, inferInstance,
      IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)⟩
  have : CharZero K := algebraRat.charZero K
  -- All the `p j` split in `K`.
  have splits_p (j) : ((p j).map (algebraMap ℤ K)).Splits := by
    have P0'' : P.map (algebraMap ℤ K) ≠ 0 := by
      rwa [Polynomial.map_ne_zero_iff (algebraMap ℤ K).injective_int]
    refine .of_dvd ?_ P0'' ?_
    · rw [IsScalarTower.algebraMap_eq ℤ ℚ K, ← Polynomial.map_map]
      exact IsSplittingField.splits _ _
    simp_rw [P, Polynomial.map_prod]
    exact dvd_prod_of_mem _ (mem_univ _)
  -- The roots of `p j` in `ℂ` are simply the roots in `K` embedded into `ℂ`
  have aroots_K_eq_aroots_ℂ (j) (f : ℂ → ℂ) :
      (((p j).aroots K).map fun x => f (algebraMap K ℂ x)) = (((p j).aroots ℂ).map f) := by
    rw [← (splits_p j).aroots_map_algebraMap (B := ℂ), Multiset.map_map, Function.comp_def]
  simp_rw [← aroots_K_eq_aroots_ℂ] at h
  -- The following roughly matches Jacobson, p. 286.
  -- Let `k` be the product of the leading coefficients of the `p j` (i.e., `P.leadingCoeff`).
  let k : ℤ := ∏ j, (p j).leadingCoeff
  have k0 : k ≠ 0 := prod_ne_zero_iff.mpr fun j _hj => leadingCoeff_ne_zero.mpr (p0' j)
  have sz_h₁ (j) : (p j).leadingCoeff ∣ k := dvd_prod_of_mem _ (mem_univ _)
  -- Now there exists a constant `c : ℝ`, such that for each prime `p > |P₀|` we have `nₚ : ℤ` and
  -- `gₚ : ℤ[X]` such that
  -- * `p` does not divide `nₚ`
  -- * `deg(gₚ) ≤ p * deg(f) - 1` (`≤ p * deg(f)` is sufficient)
  -- * all complex roots `r` of `P` satisfy `|nₚ * exp r - p * gₚ(r)| ≤ c ^ p / (p - 1)!`
  obtain ⟨c, hc'⟩ := LindemannWeierstrass.exp_polynomial_approx P P0
  -- Let `L` be a nonnegative upper bound on the norms of the coefficients of the sum.
  let L := sup' univ univ_nonempty fun j => ‖w' j‖
  have L0 : 0 ≤ L := I.elim fun j => (norm_nonneg (w' j)).trans (le_sup' (‖w' ·‖) (mem_univ j))
  -- Now there exists a sufficiently large prime `q` such that
  -- `L * (∑ i, ((p i).aroots ℂ).card) * (‖k‖ ^ P.natDegree * c) ^ q / (q - 1)! < 1`.
  let N := max (P.eval 0).natAbs (max k.natAbs w.natAbs)
  obtain ⟨q, hqN, prime_q, hq⟩ : ∃ q : ℕ, N < q ∧ Nat.Prime q ∧
      L * (∑ i, ((p i).aroots ℂ).card) * (‖k‖ ^ P.natDegree * c) ^ q / (q - 1)! < 1 := by
    have (x : ℝ) : Filter.Tendsto (fun n ↦ x ^ n / (n - 1)!) .atTop (nhds 0) := by
      suffices Filter.Tendsto ((fun n ↦ x ^ (n + 1) / n !) ∘ (· - 1)) .atTop (nhds 0) from
        this.congr' <| Filter.eventually_atTop.mpr ⟨1, fun _ h ↦ by simp [h]⟩
      have := (FloorSemiring.tendsto_pow_div_factorial_atTop x).const_mul x
      simp_rw [← mul_div_assoc, ← pow_succ', mul_zero] at this
      exact this.comp (Filter.tendsto_atTop_atTop.mpr fun b ↦ ⟨b + 1, fun _ ↦ by omega⟩)
    convert Filter.Frequently.forall_exists_of_atTop
      ((Filter.frequently_atTop.mpr Nat.exists_infinite_primes).and_eventually <|
        Filter.Tendsto.eventually_lt_const (u := 1) (by simp)
          ((this (‖k‖ ^ P.natDegree * c)).const_mul (L * ∑ i, Multiset.card ((p i).aroots ℂ))))
      (N + 1) using 2
    rw [ge_iff_le, Nat.succ_le_iff, mul_div_assoc]
  -- And this `q` is in particular large enough to apply `hc'`.
  obtain ⟨n, hn, gp, hgp, hc⟩ := hc' q (by order) prime_q
  replace hgp : gp.natDegree ≤ P.natDegree * q := by rw [mul_comm]; exact hgp.trans tsub_le_self
  clear hc'
  -- In the splitting field `K`, each `p j` has as many roots as its degree.
  have sz_h₂ := fun j => (splits_p j).natDegree_eq_card_roots.symm
  simp_rw [natDegree_map_eq_of_injective (algebraMap ℤ K).injective_int] at sz_h₂
  let t := P.natDegree * q
  -- Now `k` is a positive integer such that for every `j`,
  -- `k ^ t * ∑ u ∈ (p j).aroots K, gp u` is an integer.
  -- Let `sz` be the vector such that `sz j` is that corresponding integer.
  choose sz hsz using fun j ↦
    sum_map_aroots_aeval_mem_range_algebraMap (p j) k t gp (sz_h₁ j) hgp
      (algebraMap ℤ K).injective_int (sz_h₂ j)
  replace hsz : k ^ t • ∑ j, w' j • (((p j).aroots K).map fun x => gp.aeval x).sum =
      algebraMap ℤ K (∑ j, w' j • sz j) := by
    simp_rw [smul_sum, smul_comm (k ^ t), ← hsz, map_sum, map_zsmul]
  -- Then `k ^ t * n * w + q * ∑ j, w' j • sz j
  --  = k ^ t • (∑ j, w' j • ∑ u ∈ (p j).aroots K, q • gp u - n • exp u))`.
  have H' := calc
    ((k ^ t * n * w + q * ∑ j, w' j • sz j : ℤ) : ℂ)
    _ = algebraMap K ℂ (k ^ t • n • (w : K) + q • algebraMap ℤ K (∑ j, w' j • sz j)) := by
      simp [mul_assoc]
    _ = algebraMap K ℂ
          (k ^ t • n • (w : K) +
            q • k ^ t • ∑ j, w' j • (((p j).aroots K).map fun x => gp.aeval x).sum) := by
      rw [hsz]
    _ = algebraMap K ℂ
          (k ^ t • (n • (w : K) +
            q • ∑ j, w' j • (((p j).aroots K).map fun x => gp.aeval x).sum)) := by
      simp_rw [smul_add, smul_comm (k ^ t)]
    _ = k ^ t • (n • (w : ℂ) +
          q • ∑ j, w' j • (((p j).aroots K).map fun x => gp.aeval (algebraMap K ℂ x)).sum) := by
      simp only [map_add, map_nsmul, map_zsmul, map_intCast, map_sum, map_multiset_sum,
        Multiset.map_map, Function.comp, ← aeval_algebraMap_apply]
    _ = k ^ t •
        (q • ∑ j, w' j • (((p j).aroots K).map fun x => gp.aeval (algebraMap K ℂ x)).sum -
          n • ∑ j, w' j • (((p j).aroots K).map fun x => exp (algebraMap K ℂ x)).sum) := by
      rw [← eq_neg_iff_add_eq_zero] at h
      rw [h, smul_neg, neg_add_eq_sub]
    _ = k ^ t •
          (∑ j, w' j • (((p j).aroots K).map fun x => q • gp.aeval (algebraMap K ℂ x)).sum -
            ∑ j, w' j • (((p j).aroots K).map fun x => n • exp (algebraMap K ℂ x)).sum) := by
      simp_rw [smul_sum, Multiset.smul_sum, Multiset.map_map, Function.comp,
        smul_comm n, smul_comm q]
    _ = k ^ t • ∑ j, w' j • (((p j).aroots K).map fun x =>
                        q • gp.aeval (algebraMap K ℂ x) - n • exp (algebraMap K ℂ x)).sum := by
      simp only [← smul_sub, ← sum_sub_distrib, ← Multiset.sum_map_sub]
    _ = k ^ t • ∑ j, w' j • (((p j).aroots ℂ).map fun x => q • gp.aeval x - n • exp x).sum := by
      congr!
      exact aroots_K_eq_aroots_ℂ _ (fun x ↦ q • gp.aeval x - n • exp x)
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
      exact le_sup' (‖w' ·‖) (mem_univ _)
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

theorem linearIndependent_exp (u : ι → integralClosure ℚ ℂ) (u_inj : u.Injective) :
    LinearIndependent (integralClosure ℚ ℂ) fun i ↦ exp (u i) :=
  linearIndependent_iff'.mpr fun s v h ↦ by
    simpa [funext_iff] using linearIndependent_exp' (ι := s) (u ·) (u · |>.2)
      (fun i j ↦ by simpa [Subtype.coe_inj] using @u_inj i j)
      (v ·) (v · |>.2) (by simpa [sum_attach _ fun x ↦ v x * cexp (u x)])

theorem algebraicIndependent_exp (u : ι → integralClosure ℚ ℂ) (hu : LinearIndependent ℕ u) :
    AlgebraicIndependent (integralClosure ℚ ℂ) fun i ↦ exp (u i) := by
  rw [algebraicIndependent_iff]
  intro p hp
  simp_rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq, ← Algebra.smul_def, ← exp_nsmul,
    ← exp_sum] at hp
  norm_cast at hp
  apply linearIndependent_iff.mp (linearIndependent_exp (fun e ↦ ∑ i ∈ e.support, e i • u i) _)
  exacts [hp, hu]

theorem transcendental_exp {a : ℂ} (a0 : a ≠ 0) (ha : IsAlgebraic ℤ a) :
    Transcendental ℤ (exp a) := by
  intro h
  have is_integral_a : IsIntegral ℚ a :=
    isAlgebraic_iff_isIntegral.mp (ha.extendScalars (algebraMap ℤ ℚ).injective_int)
  have is_integral_expa : IsIntegral ℚ (exp a) :=
    isAlgebraic_iff_isIntegral.mp (h.extendScalars (algebraMap ℤ ℚ).injective_int)
  refine by
    simpa [Fin.forall_fin_succ] using linearIndependent_exp' ![a, 0] ?_ ?_ ![1, -exp a] ?_ ?_
  · intro i; fin_cases i
    exacts [is_integral_a, isIntegral_zero]
  · intro i j; fin_cases i, j <;> simp [a0.symm, *]
  · intro i; fin_cases i; exacts [isIntegral_one, is_integral_expa.neg]
  · simp

theorem transcendental_e : Transcendental ℤ (exp 1) :=
  transcendental_exp one_ne_zero isAlgebraic_one

theorem transcendental_pi : Transcendental ℤ Real.pi := by
  intro h
  refine by
    simpa [Fin.forall_fin_succ] using linearIndependent_exp' ![Real.pi * I, 0] ?_ ?_ ![1, 1] ?_ ?_
  · intro i; fin_cases i
    · have isAlgebraic_pi := h.extendScalars (algebraMap ℤ ℚ).injective_int
      have isIntegral_pi : IsIntegral ℚ (Real.pi : ℂ) := by
        simpa only [coe_algebraMap] using isAlgebraic_pi.isIntegral.algebraMap
      exact isIntegral_pi.mul Complex.isIntegral_rat_I
    · exact isIntegral_zero
  · intro i j; fin_cases i, j <;> simp [Real.pi_ne_zero]
  · intro i; fin_cases i <;> exact isIntegral_one
  · simp

theorem transcendental_log {u : ℂ} (hu0 : Complex.log u ≠ 0) (hu : IsAlgebraic ℤ u) :
    Transcendental ℤ (Complex.log u) := by
  intro h
  have := transcendental_exp hu0 h
  rw [Complex.exp_log (by aesop)] at this
  contradiction
