import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-! # Niven's Theorem

This file proves Niven's theorem, stating that the only rational angles _in degrees_ which
also have rational cosines, are 0, 30 degrees, and 90 degrees - up to reflection and shifts
by π. Equivalently, the only rational numbers that occur as `cos(π * p / q)` are the five
values `{-1, -1/2, 0, 1/2, 1}`.
-/

theorem niven {θ : ℝ} (hθ : ∃ r : ℚ, θ = r * Real.pi) (hcos_rational : ∃ q : ℚ, Real.cos θ = q) :
      Real.cos θ = 0 ∨ Real.cos θ = 1/2 ∨ Real.cos θ = -1/2 ∨ Real.cos θ = 1 ∨ Real.cos θ = -1 := by
    -- Since $2 \cos(\theta)$ is an algebraic integer and rational, it must be an integer.
    -- Hence, $2 \cos(\theta) \in \{-2, -1, 0, 1, 2\}$.
    obtain ⟨k, hk⟩ : ∃ k : ℤ, 2 * Real.cos θ = k := by
      have h_alg_int : IsIntegral ℤ (2 * Real.cos θ) := by
        have h_alg_int : IsIntegral ℤ (Complex.exp (θ * .I) + Complex.exp (-θ * .I)) := by
          -- Since $\theta$ is a rational multiple of $\pi$, $e^{i\theta}$ is a root of unity and
          -- hence an algebraic integer.
          rcases hθ with ⟨r, hr⟩
          have h_root_of_unity : ∃ n, n > 0 ∧ (Complex.exp (θ * .I))^n = 1 := by
            -- Since $r$ is rational, we can write $r = p / q$ with $p, q \in ℤ$ and $q > 0$.
            obtain ⟨p, q, hq_pos, hpq_eq⟩ : ∃ p q : ℤ, q > 0 ∧ r = p / q :=
              ⟨r.num, r.den, Nat.cast_pos.mpr r.pos, r.num_div_den.symm⟩
            refine ⟨2 * q.natAbs, by positivity, ?_⟩
            · simp_all [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
              exact ⟨p, by simpa [abs_of_pos hq_pos, field_simps, hq_pos.ne']
                using (by rw [← Int.cast_natCast, ← Int.eq_natAbs_of_nonneg hq_pos.le]; ring_nf)⟩
          rcases h_root_of_unity with ⟨w, hw₁, hw₂⟩
          have h_exp_int : IsIntegral ℤ (Complex.exp (θ * .I)) :=
            ⟨_, Polynomial.monic_X_pow_sub_C 1 hw₁.ne', by simpa [sub_eq_iff_eq_add]⟩
          -- Since algebraic integers are closed under complex conjugation, and $e^{i\theta}$ is
          -- an algebraic integer, $e^{-i\theta}$ must also be an algebraic integer.
          have h_exp_neg_int : IsIntegral ℤ (Complex.exp (-θ * .I)) := by
            have h_exp_neg_int : IsIntegral ℤ (starRingEnd ℂ (Complex.exp (θ * .I))) := by
              obtain ⟨P, hP₁, hP₂⟩ := h_exp_int
              refine ⟨P, hP₁, ?_⟩
              simpa [ Polynomial.eval₂_eq_sum_range ] using congr_arg Star.star hP₂
            convert h_exp_neg_int using 1
            simp [ Complex.ext_iff, Complex.exp_re, Complex.exp_im ]
          exact h_exp_int.add h_exp_neg_int
        convert h_alg_int using 1
        constructor <;> rintro ⟨p, hp⟩ <;> use p
        <;> norm_num [Complex.ext_iff, Complex.exp_re, Complex.exp_im] at *
        <;> simp_all [← two_mul, Real.cos]
        · have hp₂ : p.eval₂ (Int.castRingHom ℂ) (Complex.exp (θ * .I) + Complex.exp (-(θ * .I)))
            = p.eval₂ (Int.castRingHom ℝ) (2 * Real.cos θ) := by
            simp [Polynomial.eval₂_eq_sum_range, Complex.cos, ← Complex.exp_add]
            exact Finset.sum_congr rfl fun _ _ => by ring;
          norm_cast at *
          simp [hp₂, hp.right] at *
        · simp_all [Polynomial.eval₂_eq_sum_range, Complex.exp_re, Complex.exp_im, Complex.cos]
          convert hp.2.1
          norm_num [← Complex.exp_nat_mul, Complex.exp_re, Complex.exp_im, Real.cos]
          rw [← neg_mul, ← Complex.two_cos, mul_pow, mul_pow]
          norm_cast
      -- Since $2 \cos(\theta)$ is an algebraic integer and rational, it must be an integer.
      have h_alg_int_rational : ∀ {x : ℝ}, IsIntegral ℤ x → (∃ q : ℚ, x = q) → ∃ k : ℤ, x = k := by
        rintro x ⟨P, hP₁, hP₂⟩ ⟨q, hq⟩
        have h_alg_int_q : IsIntegral ℤ q := by
          refine ⟨P, hP₁, ?_⟩
          simpa [hq, Polynomial.eval₂_eq_sum_range, ← @Rat.cast_inj ℝ] using hP₂
        -- Since $q$ is a rational number that is also an algebraic integer, $q$ must be an integer.
        have h_q_int : ∀ {q : ℚ}, IsIntegral ℤ q → ∃ k : ℤ, q = k := by
          intro q hq
          -- Let $q = \frac{a}{b}$ with $a, b \in \mathbb{Z}$, $\gcd(a, b) = 1$, and $b > 0$.
          obtain ⟨a, b, hab, hb_pos, rfl⟩ : ∃ a b, Int.gcd a b = 1 ∧ 0 < b ∧ q = a / b :=
            ⟨q.num, q.den, q.reduced, Nat.cast_pos.mpr q.pos, q.num_div_den.symm ⟩;
          -- Since q is a root of a monic polynomial with integer coefficients, b must divide a.
          have h_b_div_a : b ∣ a := by
            obtain ⟨P, hP₁, hP₂⟩ := hq
            -- Multiplying through by $b^n$ gives $a^n + c_{n-1} a^{n-1} b + \cdots + c_0 b^n = 0$.
            have h_mul_b_n : a ^ P.natDegree + ∑ i ∈ Finset.range P.natDegree,
                P.coeff i * a ^ i * b ^ (P.natDegree - i) = 0 := by
              rw [Polynomial.eval₂_eq_sum_range] at hP₂
              -- Multiply through by $b^{P.natDegree}$ to clear the denominators.
              have h_mul_b_n : ∑ i ∈ Finset.range (P.natDegree + 1),
                  (P.coeff i : ℚ) * a ^ i * b ^ (P.natDegree - i) = 0 := by
                convert congr_arg (fun x : ℚ => x * b ^ P.natDegree) hP₂ using 1
                · simp [ Finset.sum_mul, field_simps, hb_pos.ne' ]
                  exact Finset.sum_congr rfl fun i hi => by
                    rw [ eq_div_iff ( by positivity ), mul_assoc]
                    rw [← pow_add, tsub_add_cancel_of_le (Finset.mem_range_succ_iff.mp hi ) ]
                · ring
              norm_cast at h_mul_b_n
              simp_all [Finset.sum_range_succ_comm]
            -- Since every term in the sum except the first is divisible by $b$, it follows that
            -- $b ∣ a^n$.
            have h_b_div_a_n : b ∣ a ^ P.natDegree := ⟨
                -(∑ i ∈ Finset.range P.natDegree, P.coeff i * a ^ i * b ^ (P.natDegree - i))/ b,
                by linarith [Int.ediv_mul_cancel (
                    show b ∣ - ∑ i ∈ Finset.range P.natDegree,
                      P.coeff i * a ^ i * b ^ (P.natDegree - i) from
                    dvd_neg.mpr <| Finset.dvd_sum fun i hi =>
                      dvd_mul_of_dvd_right (dvd_pow_self _ <| Nat.sub_ne_zero_of_lt
                        <| Finset.mem_range.mp hi) _)
                  ]
                ⟩
            rw [← Int.isCoprime_iff_gcd_eq_one] at hab
            -- Since $b ∣ a^n$ and $gcd(a, b) = 1$, it follows that $b ∣ 1$.
            have h_b_div_one : b ∣ 1 := by
              exact hab.symm.pow_right.dvd_of_dvd_mul_left (by simpa)
            exact h_b_div_one.trans (one_dvd _)
          exact ⟨a / b, by simp [h_b_div_a]⟩
        exact Exists.elim (h_q_int h_alg_int_q) fun k hk => ⟨k, hq.trans (mod_cast hk)⟩
      exact h_alg_int_rational h_alg_int ⟨2 * hcos_rational.choose, (by
        push_cast
        linarith [ hcos_rational.choose_spec ])⟩
    obtain ⟨wθ, rfl⟩ := hθ
    obtain ⟨wc, hwc⟩ := hcos_rational
    -- Since $k$ is an integer and $2 * cos(w * pi) = k$, we have $k ∈ \{-2, -1, 0, 1, 2\}$.
    have hk_values : k ∈ ({ -2, -1, 0, 1, 2 } : Set ℤ) := by
      have : k ≤ 2 := Int.le_of_lt_add_one (by
        rw [← @Int.cast_lt ℝ]
        push_cast
        linarith [Real.cos_le_one (wθ * Real.pi)])
      have : k ≥ -2 := Int.le_of_lt_add_one (by
        rw [← @Int.cast_lt ℝ]
        push_cast
        linarith [Real.neg_one_le_cos (wθ * Real.pi)])
      interval_cases k <;> norm_num
    rcases hk_values with (rfl|rfl|rfl|rfl|rfl) <;> simp_all
    · simp [show (wc : ℝ) = -1 by linarith]
    · simp [show (wc : ℝ) = -1/2 by linarith]
    · simp [show (wc : ℝ) = 1/2 by linarith]
