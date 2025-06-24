import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

theorem niven : ∀ (θ : ℝ), (∃ r : ℚ, θ = r * Real.pi) → (∃ q : ℚ, Real.cos θ = q) → Real.cos θ = 0 ∨ Real.cos θ = 1/2 ∨ Real.cos θ = -1/2 ∨ Real.cos θ = 1 ∨ Real.cos θ = -1 := by
    aesop;
    -- Since $2 \cos(\theta)$ is an algebraic integer and rational, it must be an integer. Hence, $2 \cos(\theta) \in \{-2, -1, 0, 1, 2\}$.
    have h_alg_int : ∀ θ : ℝ, (∃ r : ℚ, θ = r * Real.pi) → (∃ q : ℚ, Real.cos θ = q) → ∃ k : ℤ, 2 * Real.cos θ = k := by
      intros θ hθ hcos_rational
      have h_alg_int : IsIntegral ℤ (2 * Real.cos θ) := by
        -- By Niven's theorem, $2 \cos(\theta)$ is an algebraic integer.
        have h_alg_int : IsIntegral ℤ (Complex.exp (θ * Complex.I) + Complex.exp (-θ * Complex.I)) := by
          -- Since $\theta$ is a rational multiple of $\pi$, $e^{i\theta}$ is a root of unity and hence an algebraic integer.
          obtain ⟨r, hr⟩ : ∃ r : ℚ, θ = r * Real.pi := hθ
          have h_root_of_unity : ∃ n : ℕ, n > 0 ∧ (Complex.exp (θ * Complex.I))^n = 1 := by
            -- Since $r$ is rational, we can write $r = p / q$ with $p, q \in ℤ$ and $q > 0$.
            obtain ⟨p, q, hq_pos, hpq_eq⟩ : ∃ p q : ℤ, q > 0 ∧ r = p / q := by
              exact ⟨ r.num, r.den, Nat.cast_pos.mpr r.pos, r.num_div_den.symm ⟩;
            refine' ⟨ 2 * q.natAbs, _, _ ⟩ <;> simp_all ( config := { decide := Bool.true } ) [ ← Complex.exp_nat_mul ];
            -- Case 1
            · positivity;
            -- Case 2
            · exact Complex.exp_eq_one_iff.mpr ⟨ p, by simpa [ abs_of_pos hq_pos, field_simps, hq_pos.ne' ]
                using (by rw [← Int.cast_natCast, ← Int.eq_natAbs_of_nonneg hq_pos.le]; ring_nf)⟩;
          have h_exp_int : IsIntegral ℤ (Complex.exp (θ * Complex.I)) := by
            exact ⟨ Polynomial.X ^ h_root_of_unity.choose - 1, Polynomial.monic_X_pow_sub_C _ ( by linarith [ h_root_of_unity.choose_spec ] ), by simpa [ sub_eq_iff_eq_add ] using h_root_of_unity.choose_spec.2 ⟩;
          -- Similarly, $e^{-i\theta}$ is also an algebraic integer.
          have h_exp_neg_int : IsIntegral ℤ (Complex.exp (-θ * Complex.I)) := by
            -- Since algebraic integers are closed under complex conjugation, and $e^{i\theta}$ is an algebraic integer, $e^{-i\theta}$ must also be an algebraic integer.
            have h_exp_neg_int : IsIntegral ℤ (starRingEnd ℂ (Complex.exp (θ * Complex.I))) := by
              obtain ⟨ P, hP₁, hP₂ ⟩ := h_exp_int;
              exact ⟨ P, hP₁, by simpa [ Polynomial.eval₂_eq_sum_range ] using congr_arg Star.star hP₂ ⟩;
            convert h_exp_neg_int using 1 ; simp ( config := { decide := Bool.true } ) [ Complex.ext_iff, Complex.exp_re, Complex.exp_im ];
          exact IsIntegral.add h_exp_int h_exp_neg_int;
        convert h_alg_int using 1;
        constructor <;> intro h <;> obtain ⟨ p, hp ⟩ := h <;> use p <;> norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im ] at * <;> ( simp_all ( config := { decide := Bool.true } ) [ ← two_mul, Real.cos ] );
        -- Case 1
        · -- Since $Complex.exp (θ * Complex.I) + Complex.exp (-(θ * Complex.I)) = 2 * Real.cos θ$, we can substitute this into the polynomial evaluation.
          have h_subst : Polynomial.eval₂ (Int.castRingHom ℂ) (Complex.exp (θ * Complex.I) + Complex.exp (-(θ * Complex.I))) p = Polynomial.eval₂ (Int.castRingHom ℝ) (2 * Real.cos θ) p := by
            simp ( config := { decide := Bool.true } ) [ Polynomial.eval₂_eq_sum_range, Complex.cos, ← Complex.exp_add ];
            exact Finset.sum_congr rfl fun _ _ => by ring;
          norm_cast at * ; aesop;
        -- Case 2
        · rw [ Polynomial.eval₂_eq_sum_range ] at *; simp_all ( config := { decide := Bool.true } ) [ Complex.exp_re, Complex.exp_im, Complex.cos ] ;
          convert hp.2.1 ; norm_num [ ← Complex.exp_nat_mul, Complex.exp_re, Complex.exp_im, Real.cos ] ; ring
          -- Utilize the known identity for the sum of exponentials: $e^{i\theta} + e^{-i\theta} = 2\cos(\theta)$.
          have h_exp_cos : Complex.exp (θ * Complex.I) + Complex.exp (-(θ * Complex.I)) = 2 * Complex.cos θ := by
            rw [ Complex.cos ] ; ring;
          rw [ h_exp_cos, mul_pow, mul_comm ] ; norm_cast;
      -- Since $2 \cos(\theta)$ is an algebraic integer and rational, it must be an integer.
      have h_alg_int_rational : ∀ {x : ℝ}, IsIntegral ℤ x → (∃ q : ℚ, x = q) → ∃ k : ℤ, x = k := by
        intros x hx hx_rat
        obtain ⟨q, hq⟩ := hx_rat
        have h_alg_int_q : IsIntegral ℤ q := by
          aesop;
          obtain ⟨ P, hP₁, hP₂ ⟩ := hx;
          refine' ⟨ P, hP₁, _ ⟩;
          rw [ Polynomial.eval₂_eq_sum_range ] at *;
          simpa [ ← @Rat.cast_inj ℝ ] using hP₂;
        -- Since $q$ is a rational number that is also an algebraic integer, $q$ must be an integer.
        have h_q_int : ∀ {q : ℚ}, IsIntegral ℤ q → ∃ k : ℤ, q = k := by
          intro q hq; exact (by
          -- Let $q = \frac{a}{b}$ with $a, b \in \mathbb{Z}$, $\gcd(a, b) = 1$, and $b > 0$.
          obtain ⟨a, b, ha_b_coprime, hb_pos, rfl⟩ : ∃ a b : ℤ, Int.gcd a b = 1 ∧ 0 < b ∧ q = a / b := by
            exact ⟨ q.num, q.den, q.reduced, Nat.cast_pos.mpr q.pos, q.num_div_den.symm ⟩;
          -- Since $q$ is a root of a monic polynomial with integer coefficients, $b$ must divide $a$.
          have h_b_div_a : b ∣ a := by
            obtain ⟨ P, hP₁, hP₂ ⟩ := hq;
            -- Multiplying through by $b^n$ gives $a^n + c_{n-1} a^{n-1} b + \cdots + c_0 b^n = 0$.
            have h_mul_b_n : a ^ P.natDegree + ∑ i in Finset.range P.natDegree, P.coeff i * a ^ i * b ^ (P.natDegree - i) = 0 := by
              rw [ Polynomial.eval₂_eq_sum_range ] at hP₂;
              -- Multiply through by $b^{P.natDegree}$ to clear the denominators.
              have h_mul_b_n : (∑ i in Finset.range (P.natDegree + 1), (P.coeff i : ℚ) * a ^ i * b ^ (P.natDegree - i)) = 0 := by
                convert congr_arg ( fun x : ℚ => x * b ^ P.natDegree ) hP₂ using 1;
                -- Case 1
                · simp ( config := { decide := Bool.true } ) [ Finset.sum_mul, field_simps, hb_pos.ne' ];
                  exact Finset.sum_congr rfl fun i hi => by rw [ eq_div_iff ( by positivity ) ] ; rw [ mul_assoc, ← pow_add, tsub_add_cancel_of_le ( Finset.mem_range_succ_iff.mp hi ) ] ;
                -- Case 2
                · ring;
              norm_cast at *; simp_all ( config := { decide := Bool.true } ) [ Finset.sum_range_succ_comm ] ;
            -- Since every term in the sum except the first is divisible by $b$, it follows that $b \mid a^n$.
            have h_b_div_a_n : b ∣ a ^ P.natDegree := by
              exact ⟨ - ( ∑ i in Finset.range P.natDegree, P.coeff i * a ^ i * b ^ ( P.natDegree - i ) ) / b, by linarith [ Int.ediv_mul_cancel ( show b ∣ - ( ∑ i in Finset.range P.natDegree, P.coeff i * a ^ i * b ^ ( P.natDegree - i ) ) from dvd_neg.mpr <| Finset.dvd_sum fun i hi => dvd_mul_of_dvd_right ( dvd_pow_self _ <| Nat.sub_ne_zero_of_lt <| Finset.mem_range.mp hi ) _ ) ] ⟩;
            have := Int.gcd_eq_one_iff_coprime.mp ha_b_coprime;
            -- Since $b \mid a^n$ and $\gcd(a, b) = 1$, it follows that $b \mid 1$.
            have h_b_div_one : b ∣ 1 := by
              exact this.symm.pow_right.dvd_of_dvd_mul_left ( by simpa [ mul_comm ] using h_b_div_a_n );
            exact h_b_div_one.trans ( one_dvd _ );
          exact ⟨ a / b, by simp ( config := { decide := Bool.true } ) [ h_b_div_a ] ⟩);
        exact Exists.elim ( h_q_int h_alg_int_q ) fun k hk => ⟨ k, hq.trans ( mod_cast hk ) ⟩;
      exact h_alg_int_rational h_alg_int ⟨ 2 * hcos_rational.choose, by push_cast; linarith [ hcos_rational.choose_spec ] ⟩;
    obtain ⟨ k, hk ⟩ := h_alg_int _ ⟨ w, rfl ⟩ ⟨ w_1, h_1 ⟩;
    -- Since $k$ is an integer and $2 * \cos(w * \pi) = k$, we have $k \in \{-2, -1, 0, 1, 2\}$.
    have hk_values : k ∈ ({ -2, -1, 0, 1, 2 } : Set ℤ) := by
      have : k ≤ 2 := Int.le_of_lt_add_one ( by rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith [ Real.neg_one_le_cos ( w * Real.pi ), Real.cos_le_one ( w * Real.pi ) ] ) ; ( have : k ≥ -2 := Int.le_of_lt_add_one ( by rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith [ Real.neg_one_le_cos ( w * Real.pi ), Real.cos_le_one ( w * Real.pi ) ] ) ; interval_cases k <;> norm_num; );
    aesop;
    -- Case 1
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| by linarith;
    -- Case 2
    · exact Or.inr <| Or.inr <| Or.inl <| by linarith;
    -- Case 3
    · exact Or.inr <| Or.inl <| by linear_combination hk / 2;
