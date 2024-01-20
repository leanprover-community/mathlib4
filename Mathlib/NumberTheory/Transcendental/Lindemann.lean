/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Mathlib.NumberTheory.Transcendental.Lindemann.AlgebraicPart
import Mathlib.NumberTheory.Transcendental.Lindemann.AnalyticalPart

/-!
# The Lindemann-Weierstrass theorem
-/

noncomputable section

open scoped BigOperators Nat

open Complex Finset Polynomial

variable {ι : Type*} [Fintype ι]

theorem linear_independent_exp (u : ι → ℂ) (hu : ∀ i, IsIntegral ℚ (u i))
    (u_inj : Function.Injective u) (v : ι → ℂ) (hv : ∀ i, IsIntegral ℚ (v i))
    (h : ∑ i, v i * exp (u i) = 0) : v = 0 := by
  by_contra! v0
  obtain ⟨w, w0, m, p, p0, w', h⟩ := linear_independent_exp_aux u hu u_inj v hv v0 h
  have m0 : m ≠ 0
  · rintro rfl; rw [Fin.sum_univ_zero, add_zero, Int.cast_eq_zero] at h
    exact w0 h
  haveI I : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero m0)
  let P := ∏ i : Fin m, p i
  let K := SplittingField (P.map (algebraMap ℤ ℚ))
  have p0' : ∀ j, p j ≠ 0 := by intro j h; specialize p0 j; rw [h, eval_zero] at p0; exact p0 rfl
  have P0 : P.eval 0 ≠ 0 := by dsimp only; rw [eval_prod, prod_ne_zero_iff]; exact fun j _hj => p0 j
  have P0' : P ≠ 0 := by intro h; rw [h, eval_zero] at P0; exact P0 rfl
  have P0'' : P.map (algebraMap ℤ K) ≠ 0 := by
    rwa [Polynomial.map_ne_zero_iff (algebraMap ℤ K).injective_int]

  have splits_p : ∀ j, ((p j).map (algebraMap ℤ K)).Splits (RingHom.id K)
  · intro j
    refine' splits_of_splits_of_dvd _ P0'' _ _
    · rw [IsScalarTower.algebraMap_eq ℤ ℚ K, ← Polynomial.map_map, splits_map_iff, RingHom.id_comp]
      exact IsSplittingField.splits _ _
    simp_rw [Polynomial.map_prod]
    exact dvd_prod_of_mem _ (mem_univ _)

  have sum_aroots_K_eq_sum_aroots_ℂ :
    ∀ (j) (f : ℂ → ℂ),
      (((p j).aroots K).map fun x => f (algebraMap K ℂ x)).sum =
        (((p j).aroots ℂ).map f).sum
  · intro j f
    have : (p j).aroots ℂ = ((p j).aroots K).map (algebraMap K ℂ) := by
      -- Porting note: `simp_rw [aroots_def]` very slow
      rw [aroots_def, aroots_def, IsScalarTower.algebraMap_eq ℤ K ℂ, ← Polynomial.map_map,
        roots_map _ (splits_p j)]
    rw [this, Multiset.map_map]
    rfl

  replace h :
    (w + ∑ j : Fin m, w' j • (((p j).aroots K).map fun x => exp (algebraMap K ℂ x)).sum : ℂ) = 0 :=
    h ▸
      (congr_arg _ <|
        congr_arg _ <| funext fun j => congr_arg _ <| sum_aroots_K_eq_sum_aroots_ℂ j exp)

  let k : ℤ := ∏ j, (p j).leadingCoeff
  have k0 : k ≠ 0 := prod_ne_zero_iff.mpr fun j _hj => leadingCoeff_ne_zero.mpr (p0' j)

  obtain ⟨c, hc'⟩ := exp_polynomial_approx P P0
  let N := max (eval 0 P).natAbs (max k.natAbs w.natAbs)

  let W := sup' univ univ_nonempty fun j => ‖w' j‖
  have W0 : 0 ≤ W := I.elim fun j => (norm_nonneg (w' j)).trans (le_sup' (‖w' ·‖) (mem_univ j))

  obtain ⟨q, hqN, prime_q, hq⟩ :=
    linear_independent_exp_exists_prime N (W * ↑(∑ i : Fin m, Multiset.card ((p i).aroots ℂ)))
      (‖k‖ ^ P.natDegree * c)

  obtain ⟨n, hn, gp, hgp, hc⟩ := hc' q ((le_max_left _ _).trans_lt hqN) prime_q
  replace hgp : gp.natDegree ≤ P.natDegree * q; · rw [mul_comm]; exact hgp.trans tsub_le_self

  have sz_h₁ : ∀ j, (p j).leadingCoeff ∣ k := fun j => dvd_prod_of_mem _ (mem_univ _)
  have sz_h₂ := fun j => (natDegree_eq_card_roots (splits_p j)).symm
  -- Porting note: `simp_rw [map_id] at sz_h₂` very slow
  conv at sz_h₂ =>
    ext
    rw [map_id, natDegree_map_eq_of_injective (algebraMap ℤ K).injective_int]

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
        -- Porting note: `simp_rw [zsmul_eq_mul]` very slow
        -- simp_rw [zsmul_eq_mul]; norm_cast; rw [mul_assoc]
        rw [zsmul_eq_mul, zsmul_eq_mul]
        congr 3
        norm_cast
        rw [mul_assoc]
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
        -- simp_rw [smul_add, smul_sum, Multiset.smul_sum, Multiset.map_map, Function.comp,
        --  smul_comm n, smul_comm (k ^ t), smul_comm q]
        congr 4 <;>
        · repeat rw [smul_add]
          repeat rw [smul_sum]
          congr; funext
          repeat rw [Multiset.smul_sum]
          repeat rw [Multiset.map_map]
          dsimp only [(· ∘ ·)]
          congr; funext
          repeat rw [smul_comm n]
          repeat rw [smul_comm (k ^ t)]
          repeat rw [smul_comm q]
          simp only [algebraMap_int_eq, nsmul_eq_mul, zsmul_eq_mul, comp_mul_left, Int.cast_pow,
            Int.cast_prod, Function.comp_apply]
          ring
      _ = ‖(k ^ t • n • (w : ℂ) +
                  k ^ t •
                    ∑ j,
                      w' j • (((p j).aroots K).map fun x => q • algebraMap K ℂ (aeval x gp)).sum) -
              (k ^ t • n • (w : ℂ) +
                k ^ t •
                  ∑ j, w' j • (((p j).aroots K).map fun x => n • exp (algebraMap K ℂ x)).sum)‖ := by
        -- simp only [map_add, map_nsmul, map_zsmul, map_intCast, map_sum, map_multiset_sum,
        --   Multiset.map_map, Function.comp]
        congr 4
        rw [map_add, map_zsmul, map_zsmul, map_zsmul, map_intCast, map_sum]
        congr; funext
        rw [map_zsmul, map_multiset_sum, Multiset.map_map]
        congr; funext
        rw [Function.comp_apply, map_nsmul]
      _ = ‖k ^ t •
              ∑ j,
                w' j •
                  (((p j).aroots K).map fun x =>
                      q • algebraMap K ℂ (aeval x gp) - n • exp (algebraMap K ℂ x)).sum‖ := by
        -- simp only [add_sub_add_left_eq_sub, ← smul_sub, ← sum_sub_distrib,
        --   ← Multiset.sum_map_sub]
        rw [add_sub_add_left_eq_sub, ← smul_sub, ← sum_sub_distrib]
        congr; funext
        rw [← smul_sub, ← Multiset.sum_map_sub]
      _ = ‖k ^ t •
              ∑ j,
                w' j •
                  (((p j).aroots K).map fun x =>
                      q • aeval (algebraMap K ℂ x) gp - n • exp (algebraMap K ℂ x)).sum‖ := by
        -- simp_rw [aeval_algebraMap_apply]
        congr; funext; congr; funext; congr 2
        rw [aeval_algebraMap_apply]
      _ = ‖k ^ t •
              ∑ j,
                w' j •
                  (((p j).aroots K).map fun x =>
                      (fun x' => q • aeval x' gp - n • exp x') (algebraMap K ℂ x)).sum‖ :=
        rfl
      _ = ‖k ^ t • ∑ j, w' j • (((p j).aroots ℂ).map fun x => q • aeval x gp - n • exp x).sum‖ := by
        congr; funext; congr 1
        exact sum_aroots_K_eq_sum_aroots_ℂ _ (fun x ↦ q • aeval x gp - n • exp x)
      _ ≤ ‖k ^ t‖ * ∑ j, W * (((p j).aroots ℂ).map fun _ => c ^ q / ↑(q - 1)!).sum := by
        refine' (norm_zsmul_le _ _).trans _
        refine' mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        refine' (norm_sum_le _ _).trans _
        refine' sum_le_sum fun j _hj => _
        refine' (norm_zsmul_le _ _).trans _
        refine' mul_le_mul (le_sup' (‖w' ·‖) (mem_univ j)) _ (norm_nonneg _) W0
        refine' (norm_multiset_sum_le _).trans _
        rw [Multiset.map_map]
        refine' Multiset.sum_map_le_sum_map _ _ fun x hx => _
        rw [Function.comp_apply, norm_sub_rev]
        refine' hc _
        rw [mem_roots_map_of_injective (algebraMap ℤ ℂ).injective_int (p0' j)] at hx
        rw [mem_roots_map_of_injective (algebraMap ℤ ℂ).injective_int P0', ← aeval_def]
        rw [map_prod]
        exact prod_eq_zero (mem_univ j) hx
  -- simp_rw [Int.norm_eq_abs, Int.cast_pow, _root_.abs_pow, ← Int.norm_eq_abs, Multiset.map_const,
  --   Multiset.sum_replicate, ← mul_sum, ← sum_smul, nsmul_eq_mul, mul_comm (‖k‖ ^ t), mul_assoc,
  --   mul_comm (_ / _ : ℝ), t, pow_mul, mul_div (_ ^ _ : ℝ), ← mul_pow, ← mul_assoc, mul_div, ←
  --   pow_mul] at H
  rw [Int.norm_eq_abs, _root_.abs_pow, Int.cast_pow, ← Int.norm_eq_abs] at H
  conv_rhs at H =>
    congr
    · skip
    · congr
      · skip
      · ext
        rw [Multiset.map_const', Multiset.sum_replicate]
  conv_rhs at H =>
    rw [← mul_sum, mul_left_comm, ← sum_smul, nsmul_eq_mul, mul_comm (‖k‖ ^ t), mul_assoc,
      mul_comm (_ / _ : ℝ), pow_mul, mul_div (_ ^ _ : ℝ), ← mul_pow, ← mul_assoc, mul_div]
  replace H := H.trans_lt hq
  have : ∑ j, w' j • (((p j).aroots K).map fun x : K => k ^ (P.natDegree * q) • aeval x gp).sum =
      algebraMap ℤ K (∑ j, w' j • sz j)
  · rw [map_sum]; congr; funext j; rw [map_zsmul, hsz]
  rw [this] at H
  have :
    ‖algebraMap K ℂ (↑(k ^ (P.natDegree * q) * n * w) + ↑q * algebraMap ℤ K (∑ j, w' j • sz j))‖ =
      ‖algebraMap ℤ ℂ (k ^ (P.natDegree * q) * n * w + q * ∑ j, w' j • sz j)‖
  · simp_rw [IsScalarTower.algebraMap_apply ℤ K ℂ, algebraMap_int_eq, Int.coe_castRingHom]
    norm_cast
  rw [nsmul_eq_mul, this, algebraMap_int_eq, Int.coe_castRingHom, norm_int, ← Int.cast_abs,
    ← Int.cast_one, Int.cast_lt, Int.abs_lt_one_iff] at H
  replace H : (k ^ (P.natDegree * q) * n * w + q * ∑ j : Fin m, w' j • sz j) % q = 0
  · rw [H, Int.zero_emod]
  rw [Int.add_mul_emod_self_left, ← Int.dvd_iff_emod_eq_zero] at H
  replace H :=
    (Int.Prime.dvd_mul prime_q H).imp_left (Int.Prime.dvd_mul prime_q ∘ Int.coe_nat_dvd_left.mpr)
  revert H; rw [Int.natAbs_pow, imp_false]; push_neg
  exact
    ⟨⟨fun h =>
        Nat.not_dvd_of_pos_of_lt (Int.natAbs_pos.mpr k0)
          (((le_max_left _ _).trans (le_max_right _ _)).trans_lt hqN)
          (Nat.Prime.dvd_of_dvd_pow prime_q h),
        fun h => hn ((Int.dvd_iff_emod_eq_zero _ _).mp (Int.coe_nat_dvd_left.mpr h))⟩,
      Nat.not_dvd_of_pos_of_lt (Int.natAbs_pos.mpr w0)
        (((le_max_right _ _).trans (le_max_right _ _)).trans_lt hqN)⟩
#align linear_independent_exp linear_independent_exp

theorem Complex.isIntegral_int_i : IsIntegral ℤ I := by
  refine' ⟨X ^ 2 + C 1, monic_X_pow_add_C two_ne_zero, _⟩
  rw [eval₂_add, eval₂_X_pow, eval₂_C, I_sq, eq_intCast, Int.cast_one, add_left_neg]
set_option linter.uppercaseLean3 false in
#align complex.is_integral_int_I Complex.isIntegral_int_i

theorem Complex.isIntegral_rat_i : IsIntegral ℚ I :=
  Complex.isIntegral_int_i.tower_top
set_option linter.uppercaseLean3 false in
#align complex.is_integral_rat_I Complex.isIntegral_rat_i

theorem transcendental_exp {a : ℂ} (a0 : a ≠ 0) (ha : IsAlgebraic ℤ a) :
    Transcendental ℤ (exp a) := by
  intro h
  have is_integral_a : IsIntegral ℚ a :=
    isAlgebraic_iff_isIntegral.mp (ha.tower_top_of_injective (algebraMap ℤ ℚ).injective_int)
  have is_integral_expa : IsIntegral ℚ (exp a) :=
    isAlgebraic_iff_isIntegral.mp (h.tower_top_of_injective (algebraMap ℤ ℚ).injective_int)
  have := linear_independent_exp (fun i : Bool => if i then a else 0) ?_ ?_
      (fun i : Bool => if i then 1 else -exp a) ?_ ?_
  · simpa [ite_eq_iff] using congr_fun this True
  · intro i; dsimp only; split_ifs
    exacts [is_integral_a, isIntegral_zero]
  · intro i j; dsimp
    split_ifs with h_1 h_2 h_2 <;>
      simp only [IsEmpty.forall_iff, forall_true_left, a0, a0.symm, *]
  · intro i; dsimp; split_ifs; exacts [isIntegral_one, is_integral_expa.neg]
  simp
#align transcendental_exp transcendental_exp

theorem transcendental_e : Transcendental ℤ (exp 1) :=
  transcendental_exp one_ne_zero isAlgebraic_one

theorem transcendental_pi : Transcendental ℤ Real.pi := by
  intro h
  have is_integral_pi' : IsIntegral ℚ Real.pi :=
    isAlgebraic_iff_isIntegral.mp
      (h.tower_top_of_injective (algebraMap ℤ ℚ).injective_int)
  have is_integral_pi : IsIntegral ℚ (algebraMap ℝ ℂ Real.pi) :=
    (isIntegral_algebraMap_iff (algebraMap ℝ ℂ).injective).mpr is_integral_pi'
  have := linear_independent_exp (fun i : Bool => if i then Real.pi * I else 0) ?_ ?_
      (fun _ : Bool => 1) ?_ ?_
  · simpa only [Pi.zero_apply, one_ne_zero] using congr_fun this False
  · intro i; dsimp only; split_ifs
    · exact is_integral_pi.mul Complex.isIntegral_rat_i
    · exact isIntegral_zero
  · intro i j; dsimp
    split_ifs <;>
      simp only [IsEmpty.forall_iff, forall_true_left, *, ofReal_eq_zero, mul_eq_zero,
        Real.pi_ne_zero, I_ne_zero, or_false, zero_eq_mul]
  · intro i; dsimp; exact isIntegral_one
  simp
#align transcendental_pi transcendental_pi
