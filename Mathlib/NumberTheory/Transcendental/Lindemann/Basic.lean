/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Mathlib.Analysis.Complex.IsIntegral
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.NumberTheory.Transcendental.Lindemann.AlgebraicPart
import Mathlib.NumberTheory.Transcendental.Lindemann.AnalyticalPart
import Mathlib.NumberTheory.Transcendental.Lindemann.SumAEvalARoots
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.Topology.Algebra.Order.Floor

/-!
# The Lindemann-Weierstrass theorem

## References

* [Jacobson, *Basic Algebra I, 4.12*][jacobson1974]
-/

open scoped Nat

open Complex Finset Polynomial

variable {ι : Type*}

private theorem linearIndependent_exp' [Fintype ι] (u : ι → ℂ) (hu : ∀ i, IsIntegral ℚ (u i))
    (u_inj : Function.Injective u) (v : ι → ℂ) (hv : ∀ i, IsIntegral ℚ (v i))
    (h : ∑ i, v i * exp (u i) = 0) : ∀ i, v i = 0 := by
  rw [funext_iff.symm, ← Pi.zero_def]
  by_contra! v0
  obtain ⟨w, w0, m, p, p0, w', h⟩ := linearIndependent_exp_aux expMonoidHom u hu u_inj v hv v0 h
  have m0 : m ≠ 0 := by
    rintro rfl; rw [Fin.sum_univ_zero, add_zero, Int.cast_eq_zero] at h
    exact w0 h
  have I : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero m0)
  let P := ∏ i : Fin m, p i
  obtain ⟨K, _, _, _, _, _⟩ : ∃ (K : Type) (_ : Field K) (_ : Algebra ℚ K) (_ : Algebra K ℂ)
      (_ : IsScalarTower ℚ K ℂ), IsSplittingField ℚ K (P.map (algebraMap ℤ ℚ)) :=
    ⟨IntermediateField.adjoin ℚ ((P.map (algebraMap ℤ ℚ)).rootSet ℂ),
      inferInstance, inferInstance, inferInstance, inferInstance,
      IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits_codomain _)⟩
  have : CharZero K := algebraRat.charZero K

  have p0' : ∀ j, p j ≠ 0 := by intro j h; specialize p0 j; rw [h, eval_zero] at p0; exact p0 rfl
  have P0 : P.eval 0 ≠ 0 := by
    dsimp only [P]; rw [eval_prod, prod_ne_zero_iff]; exact fun j _hj => p0 j
  have P0' : P ≠ 0 := by intro h; rw [h, eval_zero] at P0; exact P0 rfl
  have P0'' : P.map (algebraMap ℤ K) ≠ 0 := by
    rwa [Polynomial.map_ne_zero_iff (algebraMap ℤ K).injective_int]

  have splits_p : ∀ j, ((p j).map (algebraMap ℤ K)).Splits (RingHom.id K) := by
    intro j
    refine splits_of_splits_of_dvd _ P0'' ?_ ?_
    · rw [IsScalarTower.algebraMap_eq ℤ ℚ K, ← Polynomial.map_map, splits_map_iff, RingHom.id_comp]
      exact IsSplittingField.splits _ _
    simp_rw [P, Polynomial.map_prod]
    exact dvd_prod_of_mem _ (mem_univ _)

  have aroots_K_eq_aroots_ℂ (j) (f : ℂ → ℂ) :
      (((p j).aroots K).map fun x => f (algebraMap K ℂ x)) =
        (((p j).aroots ℂ).map f) := by
    have : (p j).aroots ℂ = ((p j).aroots K).map (algebraMap K ℂ) := by
      rw [← aroots_map ℂ K, ← roots_map _ (splits_p j)]
    rw [this, Multiset.map_map]
    simp_rw [Function.comp_def]

  simp_rw [← aroots_K_eq_aroots_ℂ, expMonoidHom_apply, toAdd_ofAdd] at h

  let k : ℤ := ∏ j, (p j).leadingCoeff
  have k0 : k ≠ 0 := prod_ne_zero_iff.mpr fun j _hj => leadingCoeff_ne_zero.mpr (p0' j)

  obtain ⟨c, hc'⟩ := LindemannWeierstrass.exp_polynomial_approx P P0
  let N := max (eval 0 P).natAbs (max k.natAbs w.natAbs)

  let W := sup' univ univ_nonempty fun j => ‖w' j‖
  have W0 : 0 ≤ W := I.elim fun j => (norm_nonneg (w' j)).trans (le_sup' (‖w' ·‖) (mem_univ j))

  have (x : ℝ) : Filter.Tendsto (fun n ↦ x ^ n / (n - 1)!) .atTop (nhds 0) := by
    suffices Filter.Tendsto ((fun n ↦ x ^ (n + 1) / n !) ∘ (· - 1)) .atTop (nhds 0) from
      this.congr' <| Filter.eventually_atTop.mpr ⟨1, fun _ h ↦ by simp [h]⟩
    have := (FloorSemiring.tendsto_pow_div_factorial_atTop x).const_mul x
    simp_rw [← mul_div_assoc, ← pow_succ', mul_zero] at this
    exact this.comp (Filter.tendsto_atTop_atTop.mpr fun b ↦ ⟨b + 1, fun _ ↦ by omega⟩)

  obtain ⟨q, hqN, prime_q, hq⟩ := Filter.Frequently.forall_exists_of_atTop
    ((Filter.frequently_atTop.mpr Nat.exists_infinite_primes).and_eventually <|
      Filter.Tendsto.eventually_lt_const (u := 1) (by simp)
        ((this (‖k‖ ^ P.natDegree * c)).const_mul (W * ∑ i, Multiset.card ((p i).aroots ℂ))))
    (N + 1)
  rw [ge_iff_le, Nat.succ_le] at hqN
  simp_rw [← mul_div_assoc] at hq

  obtain ⟨n, hn, gp, hgp, hc⟩ := hc' q ((le_max_left _ _).trans_lt hqN) prime_q
  replace hgp : gp.natDegree ≤ P.natDegree * q := by rw [mul_comm]; exact hgp.trans tsub_le_self

  have sz_h₁ : ∀ j, (p j).leadingCoeff ∣ k := fun j => dvd_prod_of_mem _ (mem_univ _)
  have sz_h₂ := fun j => (natDegree_eq_card_roots (splits_p j)).symm
  simp_rw [map_id, natDegree_map_eq_of_injective (algebraMap ℤ K).injective_int] at sz_h₂

  choose sz hsz using fun j ↦
    exists_sum_map_aroot_smul_eq (p j) k (P.natDegree * q) gp (sz_h₁ j) hgp
      (algebraMap ℤ K).injective_int (sz_h₂ j)

  let t := P.natDegree * q

  have H :=
    calc
      ‖algebraMap K ℂ
              ((k ^ t * n * w : ℤ) +
                q • ∑ j, w' j • (((p j).aroots K).map fun x => k ^ t • aeval x gp).sum)‖
        = ‖algebraMap K ℂ
              (k ^ t • n • (w : K) +
                q • ∑ j, w' j • (((p j).aroots K).map fun x => k ^ t • aeval x gp).sum)‖ := by
        simp_rw [zsmul_eq_mul]; norm_cast; rw [mul_assoc]
      _ = ‖algebraMap K ℂ
                (k ^ t • n • (w : K) +
                  q • ∑ j, w' j • (((p j).aroots K).map fun x => k ^ t • aeval x gp).sum) -
              k ^ t •
                n • (w + ∑ j, w' j • (((p j).aroots K).map fun x => exp (algebraMap K ℂ x)).sum)‖ :=
        by rw [h, smul_zero, smul_zero, sub_zero]
      _ = ‖algebraMap K ℂ
                (k ^ t • n • (w : K) +
                  k ^ t • ∑ j, w' j • (((p j).aroots K).map fun x => q • aeval x gp).sum) -
              (k ^ t • n • (w : ℂ) +
                k ^ t •
                  ∑ j, w' j • (((p j).aroots K).map fun x => n • exp (algebraMap K ℂ x)).sum)‖ := by
        simp_rw [smul_add, smul_sum, Multiset.smul_sum, Multiset.map_map, Function.comp,
          smul_comm n, smul_comm (k ^ t), smul_comm q]
      _ = ‖(k ^ t • n • (w : ℂ) +
                  k ^ t •
                    ∑ j,
                      w' j • (((p j).aroots K).map fun x => q • algebraMap K ℂ (aeval x gp)).sum) -
              (k ^ t • n • (w : ℂ) +
                k ^ t •
                  ∑ j, w' j • (((p j).aroots K).map fun x => n • exp (algebraMap K ℂ x)).sum)‖ := by
        simp only [map_add, map_nsmul, map_zsmul, map_intCast, map_sum, map_multiset_sum,
          Multiset.map_map, Function.comp]
      _ = ‖k ^ t •
              ∑ j,
                w' j •
                  (((p j).aroots K).map fun x =>
                      q • algebraMap K ℂ (aeval x gp) - n • exp (algebraMap K ℂ x)).sum‖ := by
        simp only [add_sub_add_left_eq_sub, ← smul_sub, ← sum_sub_distrib,
          ← Multiset.sum_map_sub]
      _ = ‖k ^ t •
              ∑ j,
                w' j •
                  (((p j).aroots K).map fun x =>
                      q • aeval (algebraMap K ℂ x) gp - n • exp (algebraMap K ℂ x)).sum‖ := by
        simp_rw [aeval_algebraMap_apply]
      _ = ‖k ^ t •
              ∑ j,
                w' j •
                  (((p j).aroots K).map fun x =>
                      (fun x' => q • aeval x' gp - n • exp x') (algebraMap K ℂ x)).sum‖ :=
        rfl
      _ = ‖k ^ t • ∑ j, w' j • (((p j).aroots ℂ).map fun x => q • aeval x gp - n • exp x).sum‖ := by
        simp_rw [aroots_K_eq_aroots_ℂ _ (fun x ↦ q • aeval x gp - n • exp x)]
      _ ≤ ‖k ^ t‖ * ∑ j, W * (((p j).aroots ℂ).map fun _ => c ^ q / ↑(q - 1)!).sum := by
        refine (norm_zsmul_le _ _).trans ?_
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        refine (norm_sum_le _ _).trans ?_
        refine sum_le_sum fun j _hj => ?_
        refine (norm_zsmul_le _ _).trans ?_
        refine mul_le_mul (le_sup' (‖w' ·‖) (mem_univ j)) ?_ (norm_nonneg _) W0
        refine (norm_multiset_sum_le _).trans ?_
        rw [Multiset.map_map]
        refine Multiset.sum_map_le_sum_map _ _ fun x hx => ?_
        rw [Function.comp_apply, norm_sub_rev, norm_eq_abs]
        refine hc ?_
        rw [mem_aroots', Polynomial.map_ne_zero_iff (algebraMap ℤ ℂ).injective_int] at hx ⊢
        rw [map_prod]
        exact ⟨P0', prod_eq_zero (mem_univ _) hx.2⟩
  simp_rw [Int.norm_eq_abs, Int.cast_pow, _root_.abs_pow, ← Int.norm_eq_abs, Multiset.map_const',
    Multiset.sum_replicate, ← mul_sum, ← sum_smul, nsmul_eq_mul, mul_comm (‖k‖ ^ t), mul_assoc,
    mul_comm (_ / _ : ℝ), t, pow_mul, mul_div (_ ^ _ : ℝ), ← mul_pow, ← mul_assoc, mul_div, ←
    pow_mul] at H
  replace H := H.trans_lt hq
  have : ∑ j, w' j • (((p j).aroots K).map fun x : K => k ^ (P.natDegree * q) • aeval x gp).sum =
      algebraMap ℤ K (∑ j, w' j • sz j) := by
    simp_rw [map_sum, map_zsmul, hsz]
  rw [this] at H
  have :
    ‖algebraMap K ℂ (↑(k ^ (P.natDegree * q) * n * w) + ↑q * algebraMap ℤ K (∑ j, w' j • sz j))‖ =
      ‖algebraMap ℤ ℂ (k ^ (P.natDegree * q) * n * w + q * ∑ j, w' j • sz j)‖ := by
    simp_rw [IsScalarTower.algebraMap_apply ℤ K ℂ, algebraMap_int_eq, Int.coe_castRingHom]
    norm_cast
  rw [this, algebraMap_int_eq, Int.coe_castRingHom, norm_intCast, ← Int.cast_abs,
    ← Int.cast_one, Int.cast_lt, Int.abs_lt_one_iff] at H
  replace H : (k ^ (P.natDegree * q) * n * w + q * ∑ j : Fin m, w' j • sz j) % q = 0 := by
    rw [H, Int.zero_emod]
  rw [Int.add_mul_emod_self_left, ← Int.dvd_iff_emod_eq_zero] at H
  replace H :=
    (Int.Prime.dvd_mul prime_q H).imp_left (Int.Prime.dvd_mul prime_q ∘ Int.natCast_dvd.mpr)
  revert H; rw [Int.natAbs_pow, imp_false]; push_neg
  exact
    ⟨⟨fun h =>
        Nat.not_dvd_of_pos_of_lt (Int.natAbs_pos.mpr k0)
          (((le_max_left _ _).trans (le_max_right _ _)).trans_lt hqN)
          (Nat.Prime.dvd_of_dvd_pow prime_q h),
        fun h => hn (Int.natCast_dvd.mpr h)⟩,
      Nat.not_dvd_of_pos_of_lt (Int.natAbs_pos.mpr w0)
        (((le_max_right _ _).trans (le_max_right _ _)).trans_lt hqN)⟩

theorem linearIndependent_exp (u : ι → integralClosure ℚ ℂ) (u_inj : u.Injective) :
    LinearIndependent (integralClosure ℚ ℂ) fun i ↦ exp (u i) :=
  linearIndependent_iff'.mpr fun s v h ↦ by
    simpa using linearIndependent_exp' (ι := s) (u ·) (u · |>.2)
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
  rw [Complex.exp_log] at this
  · apply this
    simpa using hu.algebraMap (A := ℂ)
  · simp only [ne_eq, ofReal_eq_zero]
    rintro rfl
    simp at hu0
