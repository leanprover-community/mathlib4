import Mathlib

open scoped BigOperators
open MeasureTheory intervalIntegral Real fwdDiff fwdDiff_aux Polynomial

/-
The proof idea below is from the PR
'feat(Algebra/Group /ForwardDiff.lean): add five theorems for forward difference #26793'
-/

theorem fwdDiff_iter_pow_eq_zero_of_lt' {j n : ℕ} (h : j < n) :
   ((fwdDiffₗ ℝ ℝ (-1)^n) fun X ↦ X ^ j) = 0 := by
  induction n generalizing j with
  | zero => contradiction
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply]
    have : ((fwdDiffₗ ℝ ℝ (-1)) fun X ↦ X ^ j) =
        ∑ i ∈ Finset.range j, j.choose i • fun X ↦ (-1) ^ (j - i) *X ^ i := by
      ext x
      simp only [fwdDiffₗ_apply, nsmul_eq_mul, fwdDiff, add_pow, Finset.sum_range_succ,]
      sorry
    rw [this, map_sum]
    simp_rw [coe_fwdDiffₗ_pow, fwdDiff_iter_const_smul, ← coe_fwdDiffₗ_pow]
    refine
      Finset.sum_range_induction
        (fun k ↦ j.choose k • (fwdDiffₗ ℝ ℝ (-1) ^ n) fun X ↦ (-1) ^ (j - k) * X ^ k) (fun {j} ↦ 0)
        rfl j ?_
    intro k hk
    simp only [nsmul_eq_mul, zero_add]
    have aux : (fun X : ℝ ↦ (-1) ^ (j - k) * X ^ (k:ℕ)) =
       (-1) ^ (j - k) • (fun X : ℝ ↦ X ^ (k:ℕ)) := by
      sorry
    simp_rw [aux]
    simp_rw [coe_fwdDiffₗ_pow, fwdDiff_iter_const_smul, ← coe_fwdDiffₗ_pow]
    sorry

lemma aux_sum (t : ℕ) (z : ℝ) :
  ∑ j : Fin (t+2), (Nat.choose (t+1) j) * (-1)^(j :ℕ) * (z - j) ^ t = 0 := by
    have sum_shift := fwdDiff_iter_eq_sum_shift (-1 : ℝ) (fun x : ℝ ↦ x ^ t) (t+1) z
    have ineq : t < t+1 := by linarith
    have zero_fwdDiff := fwdDiff_iter_pow_eq_zero_of_lt' ineq
    simp only at zero_fwdDiff
    rw [coe_fwdDiffₗ_pow, funext_iff] at zero_fwdDiff
    simp only [zero_fwdDiff z, Pi.zero_apply, Int.reduceNeg, smul_neg, nsmul_eq_mul, mul_one,
      zsmul_eq_mul, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
      Int.cast_natCast] at sum_shift
    have :(∑ x ∈ Finset.range (t + 1 + 1), (-1) ^ (t + 1 - x) * ↑((t + 1).choose x) * (z + -↑x) ^ t)
       = (-1) ^ (t + 1) * (∑ x ∈ Finset.range (t + 1 + 1), (-1) ^ (x) *
         ↑((t + 1).choose x) * (z + -↑x) ^ t) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i ih
      simp only [Finset.mem_range] at ih
      rw [mul_assoc, mul_assoc]
      nth_rw 2 [← mul_assoc]
      congr
      have ineq : i ≤ t+1 := by linarith
      have hsplit : (-1 : ℝ) ^ (t + 1) =
        (-1 ) ^ (t + 1 - i) * (-1 ) ^ i := by
        have p:= (pow_add (-1 : ℝ) (t + 1 - i) i)
        sorry
      simp only [hsplit, mul_assoc, ← pow_add (-1:ℝ) i i]
      sorry
    rw [this] at sum_shift
    rw [zero_eq_mul] at sum_shift
    sorry



lemma integral_add_pow
    (m : ℕ) {w r s : ℝ} :
    ∫ u in s..r, ((u + w) ^ (m:ℤ))
    = ((r + w) ^ ((m:ℤ) + 1)/(m+1) - ((s + w) ^ ((m:ℤ) + 1))/(m+1)) := by
   refine integral_deriv_eq_sub' (fun {r} ↦ (r + w) ^ (↑m + 1) / (↑m + 1)) ?_ ?_ ?_
   · ext x
     simp
     rw [@mul_div_right_comm]
     nth_rw 2 [← one_mul (x+w)]
     rw [mul_pow, one_pow]
     congr
     field_simp
   · intro x hx
     simp only [differentiableAt_add_const_iff, differentiableAt_fun_id, DifferentiableAt.fun_pow,
       DifferentiableAt.div_const]
   · simp only [zpow_natCast]
     apply Continuous.continuousOn
     apply Continuous.pow
     exact continuous_id.add continuous_const


lemma integral_pow_succ_div
    (m : ℕ) {w z : ℝ} :
    ((z + 1 + w + m : ℝ) ^ (m + 1) / w)
      - ((-w - m + w + m : ℝ) ^ (m + 1) / w)
    = ∫ s in (-w-m)..(z+1),
        ((m + 1 : ℝ) * (s + w + m) ^ m) / w := by
  let F : ℝ → ℝ := fun s ↦ (s + w + m) ^ (m + 1) / w
  let f : ℝ → ℝ := fun x ↦ (((m + 1 : ℝ) * (x + w + m) ^ m) / w)
  have hDeriv :
      ∀ x ∈ Set.Icc (min (z + 1) (-w - m)) (max (z + 1) (-w - m)),
        HasDerivAt F (((m + 1 : ℝ) * (x + w + m) ^ m) / w) x := by
    intro x hx
    have h₁ : HasDerivAt (fun s : ℝ ↦ (s + w + m) ^ (m + 1))
                         ((m + 1 : ℝ) * (x + w + m) ^ m) x := by
      have := (hasDerivAt_id x).add_const (w + m)
      have := this.pow (m+1)
      dsimp at this
      simp only [Nat.cast_add, Nat.cast_one, mul_one] at this
      simp_rw [← add_assoc] at this
      exact this
    simpa [F, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      using h₁.const_mul (1 / w)
  have hDerivEq : deriv F = f := by
    ext x
    have h : HasDerivAt F (f x) x := by
      have h₁ : HasDerivAt
         (fun s : ℝ ↦ (s + w + m) ^ (m + 1))
         ((m + 1 : ℝ) * (x + w + m) ^ m) x := by
         have := (hasDerivAt_id x).add_const (w + m)
         have := this.pow (m + 1)
         simp only [id_eq, ← add_assoc, Nat.cast_add, Nat.cast_one, add_tsub_cancel_right,
           mul_one] at this
         exact this
      have h₂ := h₁.const_mul (1 / w)
      simpa [F, f, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h₂
    simpa using h.deriv
  have hInt : IntervalIntegrable (deriv F) volume (-w - m) (z + 1) := by
    have hCont : Continuous fun s : ℝ ↦ ((m + 1 : ℝ) * (s + w + m) ^ m) / w := by
      simp [mul_comm, div_eq_mul_inv]
      apply Continuous.mul
      · apply continuous_const
      · apply Continuous.mul
        · apply Continuous.pow
          simp_rw [add_assoc]
          exact continuous_add_right (w + ↑m)
        exact continuous_const
    haveI := locallyFinite_volume
    apply Continuous.intervalIntegrable
    rw [hDerivEq]
    exact hCont
  have hDiff :
      ∀ x ∈ Set.uIcc (-w - m) (z + 1) , DifferentiableAt ℝ F x := by
    intro x hx
    exact (hDeriv x (by
      have : x ∈ Set.Icc (min (z + 1) (-w - m)) (max (z + 1) (-w - m)) := by
        simpa [Set.uIcc, Set.Icc, min_comm, max_comm, min_le_iff, le_max_iff] using hx
      exact this)).differentiableAt
  have hFTC := intervalIntegral.integral_deriv_eq_sub hDiff hInt
  simp only [hDerivEq, sub_eq_add_neg, F, f] at hFTC
  exact id (Eq.symm hFTC)

theorem abel_binomial {m : ℕ} : (w z : ℝ)→ (hw : w ≠ 0)→
   (∑ k : Fin (m.succ), (Nat.choose m k) *
   (w + (m - k)) ^ ((m - k : ℤ) - 1) * (z + k) ^ (k : ℤ))
   = (z + w + m) ^ (m : ℤ) / w := by
 classical
 induction m with
 | zero =>
   intro w z hw
   rw [add_assoc, Nat.cast_zero, add_zero, Nat.cast_zero]
   rw [@Fin.sum_univ_one]
   simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Fin.val_eq_zero, Nat.choose_self,
   Nat.cast_one, CharP.cast_eq_zero, sub_self, add_zero, zero_sub, Int.reduceNeg, zpow_neg,
     zpow_one, one_mul, zpow_zero, mul_one, one_div]
 | succ m ih =>
   intro w z hw
   by_cases P : m = 0
   ·  simp [P]
      rw [P]
      simp only [Nat.reduceAdd, Fin.sum_univ_two, Fin.isValue, Fin.val_zero,
        Nat.choose_succ_self_right, zero_add, Nat.cast_one, CharP.cast_eq_zero, sub_zero, pow_zero,
        inv_one, mul_one, add_zero, Fin.val_one, Nat.choose_self, sub_self, pow_one, one_mul]
      rw [@inv_mul_eq_div, one_add_div hw, ← add_assoc]
      ring_nf
   ·  simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, zpow_natCast]
      symm
      calc (z + w + (m + 1)) ^ ((m:ℤ) + 1) / w
         = let f (s : ℝ) := (s + w + m)^(m + 1) / w; f (z + 1) - f (-w - m) := by
            dsimp
            field_simp
            nth_rw 1 [add_comm (m:ℝ) 1, add_assoc, ← add_assoc w 1 (m :ℝ),
               add_comm w 1, ← add_assoc, ← add_assoc]
            rw [← sub_zero ((z + 1 + w + ↑m) ^ ((m :ℤ)+ 1))]
            congr 1
            ring_nf
      _ = ((m : ℝ) +1) * ∫ (s : ℝ) in (-w - m)..(z+1), (s + w + m)^m / w := by
            dsimp
            rw [integral_pow_succ_div] --you can use `integral_pow_succ_div`
            field_simp
      _ = ((m : ℝ) +1) * (∫ (s : ℝ) in (-w - m)..(z+1), ∑ k : Fin (m+1),
         ↑(m.choose k) * (w + (m - k)) ^ ((m : ℤ)- k - 1) * (s + k)^(k:ℤ)) := by
            have := fun s ↦ ih w s hw --induction hypothesis
            simp_rw [this]
            simp only [intervalIntegral.integral_div, zpow_natCast]
      _ = ((m : ℝ) +1) * ∑ k : Fin (m+1), (∫ (s : ℝ) in (-w - m)..(z+1),
         ↑(m.choose k) * (w + (m - k)) ^ ((m : ℤ)- k - 1) * (s + k)^(k:ℤ)) := by
            congr 1
            apply intervalIntegral.integral_finset_sum
            intro i hi
            apply Continuous.intervalIntegrable
            apply Continuous.mul
            · exact continuous_const
            · apply Continuous.pow
              exact continuous_id.add continuous_const
      _ = ∑ k : Fin (m+1), ((m : ℝ) +1) * ↑(m.choose k) * (w + (m - k))^((m : ℤ)- k - 1) *
         (∫ (s : ℝ) in (-w - m)..(z+1), (s + k)^(k:ℤ)) := by
            simp only [zpow_natCast, intervalIntegral.integral_const_mul]
            rw [@Finset.mul_sum]
            ring_nf
      _ = ∑ k : Fin (m+1), ((m : ℝ) +1) * ↑(m.choose k) * (w + (m - k))^((m : ℤ)- k - 1) *
         (let f (s : ℝ) := (s + k)^((k:ℤ) + 1) / (k +1) ; f (z + 1) - f (-w - m)) := by
            dsimp
            apply Finset.sum_congr rfl
            intro x xfin
            congr
            exact integral_add_pow ↑x
      _ = ∑ k : Fin (m+1), ((m : ℝ) +1) * ↑(m.choose k) * (w + (m - k))^((m : ℤ)- k - 1) *
         (z + 1 + k)^((k:ℤ) + 1) / (k + 1)
         - ∑ k : Fin (m+1), ((m : ℝ) +1) * ↑(m.choose k) * (w + (m - k))^((m : ℤ)- k - 1) *
         (-w -m + k)^((k:ℤ) + 1) / (k + 1) := by
            dsimp
            simp_rw [mul_sub] -- a few simp_rw should be enough
            simp_rw [Finset.sum_sub_distrib]
            field_simp
      _ = ∑ k : Fin (m+1), ((m : ℝ) +1) / (k + 1) * ↑(m.choose k) * (z + 1 + k)^((k:ℤ) + 1) *
         (w + (m - k))^((m : ℤ)- k - 1)
         - ∑ k : Fin (m+1), ((m : ℝ) +1) / (k + 1) * ↑(m.choose k) * (-w -m + k)^((k:ℤ) + 1) *
         (w + (m - k))^((m : ℤ)- k - 1) := by
            simp_rw [mul_comm, mul_div_assoc]
            simp_rw [← mul_assoc, mul_comm] -- a few simp_rw should be enough
            simp only [sub_left_inj]
            field_simp
      _ = ∑ k : Fin (m+1), ↑((m+1).choose (k+1)) * (z + 1 + k)^((k:ℤ) + 1) *
         (w + (m - k))^((m : ℤ)- k - 1)
         - ∑ k : Fin (m+1), ↑((m+1).choose (k+1)) * (-w -m + k)^((k:ℤ) + 1) *
         (w + (m - k))^((m : ℤ)- k - 1) := by
            have : ∀ k : Fin (m+1),
            ((m : ℝ) +1) / (k + 1) * ↑(m.choose k) = ↑((m+1).choose (k+1)) := by
             intro k
             have h_nat : ((k : ℕ) + 1) * (m + 1).choose ((k : ℕ) + 1)
                  = (m + 1) * m.choose (k : ℕ) := by
               rw [Nat.succ_mul_choose_eq]
               simp_rw [Nat.succ_eq_add_one]
               rw [mul_comm]
             have h_real : ((k : ℝ) + 1) * ((m + 1).choose ((k : ℕ) + 1) : ℝ)
                  = ((m : ℝ) + 1) * (m.choose (k : ℕ) : ℝ) := by
               simpa using congrArg (fun n : ℕ ↦ (n : ℝ)) h_nat
             have hk1 : ((k : ℝ) + 1) ≠ 0 := by
               exact_mod_cast Nat.succ_ne_zero (k : ℕ)
             field_simp [hk1] at h_real
             field_simp
             rw [← h_real,mul_comm]
            simp_rw [this]
      _ = ∑ k : Fin (m+1), ↑((m+1).choose (k+1)) * (z + 1 + k)^((k:ℤ) + 1) *
         (w + (m - k))^((m : ℤ)- k - 1)
         - ∑ k : Fin (m+1), ↑((m+1).choose (k+1)) * (-1)^((k:ℤ) + 1) *
         (w + (m - k))^(m : ℤ) := by
            congr with k
            rw [mul_assoc, mul_assoc]
            congr 1
            rw [sub_add, neg_sub_left, neg_eq_neg_one_mul, mul_zpow, mul_assoc]
            congr 1
            rw [sub_add_comm, add_comm_sub]
            by_cases p : (w + (↑m - ↑↑k)) =0
            · simp [p]
              rw [zero_pow P]
              simp only [mul_eq_zero]
              left
              refine (zpow_eq_zero_iff ?_).mpr rfl
              exact Nat.cast_add_one_ne_zero ↑k
            · rw [← zpow_add₀ p]
              simp only [add_add_sub_cancel, add_sub_cancel, zpow_natCast]
      _ = ∑ j : Fin ((m+1) +1), ↑((m+1).choose j) * (z + j)^(j:ℤ) *
         (w + (m - j + 1))^((m : ℤ)- j)
         - ∑ j : Fin ((m+1) +1), ↑((m+1).choose j) * (-1)^(j:ℤ) *
         (w + (m - j + 1))^(m : ℤ) := by
            simp
            nth_rw 3 [@Fin.sum_univ_succ]
            nth_rw 4 [@Fin.sum_univ_succ]
            simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.choose_zero_right, Nat.cast_one,
              CharP.cast_eq_zero, add_zero, pow_zero, mul_one, sub_zero, zpow_natCast, one_mul,
              Fin.val_succ, Nat.cast_add, add_sub_add_left_eq_sub]
            congr with k
            · calc
               ((m + 1).choose ((k:ℕ) + 1)) * (z + 1 + k) ^ ((k:ℤ) + 1)
                   * (w + (↑m - ↑↑k)) ^ ((m:ℤ) - k - 1)
                 = ((m + 1).choose ((k:ℕ) + 1)) * (z + (k+1)) ^ ((k:ℤ) + 1)
                   * (w + (↑m - ↑↑k)) ^ ((m:ℤ) - k - 1) := by
                    congr 1
                    congr 1
                    rw [add_assoc, add_comm 1]
               _ = ((m + 1).choose ((k:ℕ) + 1)) * (z + (k+1)) ^ ((k:ℕ) + 1)
                   * (w + ((↑m - (↑↑k + 1) + 1))) ^ ((m:ℤ) - k - 1) := by
                    repeat rw [← add_assoc]
                    congr 1
                    nth_rw 4 [sub_eq_add_neg]
                    rw [← add_assoc, neg_eq_neg_one_mul, mul_add, ← add_assoc, neg_one_mul, neg_one_mul]
                    rw [← sub_eq_add_neg, sub_add, sub_self, sub_zero, add_assoc, ← sub_eq_add_neg]
              simp only [mul_eq_mul_left_iff, mul_eq_zero, Nat.cast_eq_zero, ne_eq, Nat.add_eq_zero,
                Fin.val_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true, pow_eq_zero_iff]
              left
              rw [Int.sub_sub]
            · congr 1
              ring_nf
      _ = ∑ j : Fin ((m+1) +1), ↑((m+1).choose j) * (z + j)^(↑j) *
         (w + (m - j + 1))^((m : ℤ)- j)
         - ∑ j : Fin ((m+1) +1), ↑((m+1).choose j) * (-1)^(↑j) *
         (w + m + 1 - j)^(m : ℤ) := by
            simp only [zpow_natCast, sub_right_inj]
            congr with x
            congr 1
            ring_nf
      _ = ∑ j : Fin ((m+1)+1), ↑((m + 1).choose j) *
         (w + (m + 1 - j)) ^ ((m : ℤ) + 1 - j- 1) * (z + j) ^ ↑j := by
            have := aux_sum m (w + (m :ℝ) +1)
            simp only [zpow_natCast]
            rw [this]
            ring_nf
            congr with x
            congr 1
            congr 1
            ring_nf
