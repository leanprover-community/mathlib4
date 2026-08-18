/-
Copyright (c) 2025 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/

module

public import Mathlib.NumberTheory.Transcendental.GelfondSchneider.MainAnalytic
public import Mathlib.NumberTheory.Transcendental.GelfondSchneider.MainPostAnalytic

/-!
# Gelfond-Schneider: analytic bounds on the auxiliary function

Upper bounds for `house ρ` and the constants `c₆`, `c₇`, `c₈` entering them.

## References
* Loo-Keng Hua, Introduction to Number Theory, Springer, 1982. Chapter 17.9.
-/

@[expose] public section

open BigOperators Module.Free Fintype NumberField Embeddings FiniteDimensional
   Matrix Set Polynomial Finset IntermediateField Complex AnalyticAt

noncomputable section


namespace GelfondSchneider

variable {K : Type} [Field K] (α : ℂ) (β : ℂ) (σ : K →+* ℂ) (α' : K) (β' : K) (γ' : K)
  (hirr : ∀ i j : ℤ, β ≠ i / j) (htriv : α ≠ 0 ∧ α ≠ 1)
  (habc : α = σ α' ∧ β = σ β' ∧ α ^ β = σ γ')

variable [NumberField K]

variable (q : ℕ) (hq0 : 0 < q)

variable (u : Fin (m K * n K q)) (t : Fin (q * q))

variable (h2mq : 2 * m K ∣ q ^ 2)

variable [DecidableEq (K →+* ℂ)]

/-- A house bound for the scaled coefficient `c₁ • (a + b • β')`. -/
@[nolint unusedArguments]
lemma house_add_mul_le :
    house (c₁ α' β' γ' • ((a q t : K) + b q t • β')) ≤
      (|c₁ α' β' γ'| * |(q : ℤ)|) * (1 + house β') := by
  calc _ ≤ house (c₁ α' β' γ' • ((a q t : ℤ) : K)) +
             house (c₁ α' β' γ' • ((b q t : ℤ) • β')) := ?_
       _ ≤ house ((c₁ α' β' γ' : ℤ) : K) * house ((a q t : ℤ) : K) +
             house ((c₁ α' β' γ' : ℤ) : K) * house ((b q t : ℤ) • β') := ?_
       _ ≤ house ((c₁ α' β' γ' : ℤ) : K) * house ((a q t : ℤ) : K) +
             house ((c₁ α' β' γ' : ℤ) : K) *
               (house ((b q t : ℤ) : K) * house β') := ?_
       _ = |c₁ α' β' γ'| * |(a q t : ℤ)| +
             |c₁ α' β' γ'| * |(b q t : ℤ)| * house β' := ?_
       _ ≤ |c₁ α' β' γ'| * |(q : ℤ)| + |c₁ α' β' γ'| * |(q : ℤ)| * house β' := ?_
       _ = |c₁ α' β' γ'| * |(q : ℤ)| * (1 + house β') := ?_
  · norm_cast; rw [smul_add]; apply house_add_le
  · refine add_le_add (by grind [house_mul_le]) (by grind [house_mul_le])
  · refine add_le_add (by grind)
      (mul_le_mul (le_refl _) (by grind [house_mul_le]) (house_nonneg _) (house_nonneg _))
  · rw [house_intCast]; rw [house_intCast]; rw [house_intCast]; rw [mul_assoc]
  · refine add_le_add (mul_le_mul (le_refl _) (mod_cast ((finProdFinEquiv.symm.toFun t).1).isLt)
      (Int.cast_nonneg (Int.zero_le_ofNat (a q t))) (Int.cast_nonneg (abs_nonneg (c₁ α' β' γ')))) ?_
    · rw [mul_assoc, mul_assoc]
      apply mul_le_mul (by rfl) ?_ (mul_nonneg (by positivity) (house_nonneg _)) (by simp)
      · apply mul_le_mul (mod_cast ((finProdFinEquiv.symm.toFun t).2).isLt) (le_refl _)
          (house_nonneg _) (by simp)
  · rw [mul_add]; simp only [Int.cast_abs, mul_one]

/-! On the other hand `house (ρ) ≤ t c₄ⁿ n⁽ⁿ⁻¹⁾⁄₂ (c₆q)ʳ c₇^q ≤ c₈ʳ r⁽ʳ⁺³⁾⁄₂`.
-/

include α β σ α' β' γ' hirr htriv habc in
@[nolint unusedArguments]
lemma one_le_c₄ : 1 ≤ c₄ α' β' γ' := one_le_mul_of_one_le_of_one_le
  (le_max_left 1 (house.c₁ K * house.c₁ K * 2 * ↑(m K))) (one_le_c₃ α' β' γ')

/-- The constant `|c₁| * (1 + house β')`. -/
def c₆ : ℝ := (|↑(c₁ α' β' γ')| * (1 + house β'))

include α β σ α' β' γ' hirr htriv habc in
@[nolint unusedArguments]
lemma c₆_nonneg : 0 ≤ c₆ α' β' γ' := by
  unfold c₆ house; positivity

include α β σ α' β' γ' hirr htriv habc in
@[nolint unusedArguments]
lemma one_le_c₆ : 1 ≤ c₆ α' β' γ' := by
  unfold c₆
  refine one_le_mul_of_one_le_of_one_le ?_ ?_
  · norm_cast; exact one_le_abs_c₁ α' β' γ'
  · simp only [le_add_iff_nonneg_right]
    exact house_nonneg β'

/-- The constant `(|c₁| ^ 2 * (|c₁| * (house α' * (|c₁| * house γ')))) ^ m`. -/
def c₇ : ℝ := ((((|↑(c₁ α' β' γ')| * |↑(c₁ α' β' γ')| *
  (|↑(c₁ α' β' γ')| * (house α' * (|↑(c₁ α' β' γ')| * house γ'))))) ^ m K))

include α β σ α' β' γ' hirr htriv habc in
@[nolint unusedArguments]
lemma one_le_c₇ : 1 ≤ c₇ α' β' γ' := by
  unfold c₇
  have hc : 0 ≤ c₁ α' β' γ' := le_trans Int.one_nonneg (one_le_c₁ α' β' γ')
  have house_num_mul_int (α : K) (c' : ℤ) (hc' : 0 ≤ c') :
      house ((c' : K) * α) = |(c' : ℝ)| * house α := by
    lift c' to ℕ using hc'
    simpa using house_nat_mul α c'
  have hα : 1 ≤ |(c₁ α' β' γ' : ℝ)| * house α' := by
    rw [← house_num_mul_int (α := α') (c' := c₁ α' β' γ') hc, ← smul_eq_mul]
    exact one_le_house_of_isIntegral (mod_cast isIntegral_c₁α α' β' γ') (mod_cast c₁α_ne_zero α β σ
        α' β' γ' hirr htriv habc)
  have hγ : 1 ≤ |(c₁ α' β' γ' : ℝ)| * house γ' := by
    rw [← house_num_mul_int (α := γ') (c' := c₁ α' β' γ') hc, ← smul_eq_mul]
    exact one_le_house_of_isIntegral (mod_cast isIntegral_c₁γ α' β' γ') (mod_cast c₁γ_ne_zero α β σ
        α' β' γ' hirr htriv habc)
  have hbase :
      1 ≤ |(c₁ α' β' γ' : ℝ)| * |(c₁ α' β' γ' : ℝ)| *
        (|(c₁ α' β' γ' : ℝ)| * (house α' * (|(c₁ α' β' γ' : ℝ)| * house γ'))) := by
    calc
      1 ≤ (|(c₁ α' β' γ' : ℝ)| * |(c₁ α' β' γ' : ℝ)|) *
            ((|(c₁ α' β' γ' : ℝ)| * house α') * (|(c₁ α' β' γ' : ℝ)| * house γ')) := by
          refine one_le_mul_of_one_le_of_one_le
            (one_le_mul_of_one_le_of_one_le
              (by
                norm_cast
                exact one_le_abs_c₁ α' β' γ')
              (by
                norm_cast
                exact one_le_abs_c₁ α' β' γ'))
            (one_le_mul_of_one_le_of_one_le hα hγ)
      _ = |(c₁ α' β' γ' : ℝ)| * |(c₁ α' β' γ' : ℝ)| *
            (|(c₁ α' β' γ' : ℝ)| * (house α' * (|(c₁ α' β' γ' : ℝ)| * house γ'))) := by
          ring
  calc
    (1 : ℝ) = 1 ^ m K := by simp
    _ ≤ (|(c₁ α' β' γ' : ℝ)| * |(c₁ α' β' γ' : ℝ)| *
          (|(c₁ α' β' γ' : ℝ)| * (house α' * (|(c₁ α' β' γ' : ℝ)| * house γ')))) ^ m K := by
        refine pow_le_pow_left₀ (by positivity) hbase (m K)

include α β σ α' β' γ' hirr htriv habc in
lemma r_qt_0 : 0 < r α β σ α' β' γ' hirr htriv habc q hq0 h2mq :=
  Nat.zero_lt_of_ne_zero (r_ne_zero α β σ α' β' γ' hirr htriv habc q hq0 h2mq)

include α β σ α' β' γ' hirr htriv habc in
lemma one_le_r : 1 ≤  r α β σ α' β' γ' hirr htriv habc q hq0 h2mq :=
  Nat.zero_lt_of_ne_zero (r_ne_zero α β σ α' β' γ' hirr htriv habc q hq0 h2mq)

include α β σ α' β' γ' hirr htriv habc in
lemma cρ_abs_eq : |c₁ α' β' γ' ^ r α β σ α' β' γ' hirr htriv habc q hq0 h2mq * c₁ α' β' γ' ^ (2 * m
    K * q)| =
  c₁ α' β' γ' ^ r α β σ α' β' γ' hirr htriv habc q hq0 h2mq * c₁ α' β' γ' ^ (2 * m K * q) := by
    rw [abs_eq_self]
    apply mul_nonneg (pow_nonneg (le_trans Int.one_nonneg (one_le_c₁ α' β' γ')) _)
    · apply pow_nonneg (le_trans Int.one_nonneg (one_le_c₁ α' β' γ'))

include α β σ α' β' γ' hirr htriv habc in
lemma eq6a : house (rho α β σ α' β' γ' hirr htriv habc q hq0 h2mq) ≤
  (q*q) *(c₄ α' β' γ' ^ (n K q : ℝ) * ((n K q : ℝ) ^ (((n K q : ℝ)+ 1)/2)) *
        (c₆ α' β' γ'* q) ^(r α β σ α' β' γ' hirr htriv habc q hq0 h2mq) * (c₇ α' β' γ')^(q :
            ℤ)) := by
  calc _ ≤ norm (cρ α β σ α' β' γ' hirr htriv habc q hq0 h2mq : ℝ) * house (rho α β σ α' β' γ' hirr
      htriv habc q hq0 h2mq) := ?_
       _ ≤ (norm (cρ α β σ α' β' γ' hirr htriv habc q hq0 h2mq : ℝ))  *
          house (∑ t, ( ((algebraMap (𝓞 K) K) ((η (K := K) α β σ α' β' γ' hirr htriv habc q hq0
              h2mq) t)) *
        ((systemCoeffsR α β σ α' β' γ' hirr htriv habc q hq0 t h2mq)))) := ?_
       _ ≤ (norm (cρ α β σ α' β' γ' hirr htriv habc q hq0 h2mq : ℝ)) *
         ∑ t, house ( ((algebraMap (𝓞 K) K) ((η (K := K) α β σ α' β' γ' hirr htriv habc q hq0 h2mq)
             t)) *
       ((systemCoeffsR α β σ α' β' γ' hirr htriv habc q hq0 t h2mq))) := ?_
       _ = (∑ t, house ((cρ α β σ α' β' γ' hirr htriv habc q hq0 h2mq) *
         (algebraMap (𝓞 K) K ((η (K := K) α β σ α' β' γ' hirr htriv habc q hq0 h2mq) t) *
          systemCoeffsR α β σ α' β' γ' hirr htriv habc q hq0 t h2mq))) := ?_
       _ = ∑ t, house ((algebraMap (𝓞 K) K) (η (K := K) α β σ α' β' γ' hirr htriv habc q hq0 h2mq t)
           *
        (↑(c₁ α' β' γ') ^ (m K * q - a q t * (↑(l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq) + 1))
            *
          (↑(c₁ α' β' γ') ^ (m K * q - b q t * (↑(l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq) +
              1)) *
            (c₁ α' β' γ' ^ r α β σ α' β' γ' hirr htriv habc q hq0 h2mq • (↑(a q t) + b q t • β') ^ r
                α β σ α' β' γ' hirr htriv habc q hq0 h2mq *
              (c₁ α' β' γ' ^ (a q t * (↑(l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq) + 1)) •
                  α' ^ (a q t * (↑(l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq) + 1)) *
                c₁ α' β' γ' ^ (b q t * (↑(l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq) + 1)) •
                  γ' ^ (b q t * (↑(l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq) + 1))))))) := ?_
       _ ≤ ∑ t, house ((algebraMap (𝓞 K) K) (η (K := K) α β σ α' β' γ' hirr htriv habc q hq0 h2mq
           t)) *
        (house (((c₁ α' β' γ' : K) ^ (m K * q - a q t * (↑(l₀' α β σ α' β' γ' hirr htriv habc q hq0
            h2mq) + 1)))) *
          (house (((c₁ α' β' γ' : K) ^
              (m K * q - b q t * (↑(l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq) + 1)))) *
            (house (((c₁ α' β' γ' : K) ^ r α β σ α' β' γ' hirr htriv habc q hq0 h2mq •
              (↑(a q t) + b q t • β') ^ r α β σ α' β' γ' hirr htriv habc q hq0 h2mq)) *
              (house (((c₁ α' β' γ' : K) ^ (a q t * (↑(l₀' α β σ α' β' γ' hirr htriv habc q hq0
                  h2mq) + 1)) •
                  α' ^ (a q t * (↑(l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq) + 1)))) *
                (house ((c₁ α' β' γ' : K) ^ (b q t * (↑(l₀' α β σ α' β' γ' hirr htriv habc q hq0
                    h2mq) + 1)) •
                  γ' ^ (b q t * (↑(l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq) + 1)))
                  ))))) := ?_
       _ ≤ (∑ t, c₄ α' β' γ' ^ (n K q : ℝ) * ((n K q : ℝ) ^ (((n K q : ℝ)+ 1)/2)) *
        (↑|c₁ α' β' γ' ^ (m K * q - a q t * (↑(l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq) + 1))|
            *
        (↑|c₁ α' β' γ' ^ (m K * q - b q t * (↑(l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq) + 1))|
            *
          (((|c₁ α' β' γ'| * (|(q : ℤ)| * (1 + house (β')))) ^ (r α β σ α' β' γ' hirr htriv habc q
              hq0 h2mq)) *
             house ((c₁ α' β' γ' • α')) ^ (m K * q) *
             house ((c₁ α' β' γ' • γ')) ^ (m K * q))))) := ?_
       _ ≤ ∑ (t : Fin (q * q)), c₄ α' β' γ' ^ (n K q : ℝ) * ((n K q : ℝ) ^ (((n K q : ℝ)+ 1)/2)) *
          (↑|c₁ α' β' γ'| ^ (m K * q) *
          (↑|c₁ α' β' γ'| ^ (m K * q) *
          ((|c₁ α' β' γ'|^ (r α β σ α' β' γ' hirr htriv habc q hq0 h2mq) *
            (|(q : ℤ)|^ (r α β σ α' β' γ' hirr htriv habc q hq0 h2mq) * (1 + house (β')) ^ (r α β σ
                α' β' γ' hirr htriv habc q hq0 h2mq)) *
             ((|c₁ α' β' γ'|^ (m K * q) * house (α') ^ (m K * q)) *
             (|c₁ α' β' γ'|^ (m K * q)  * house γ' ^ (m K * q))))))) := ?_
       _ ≤  (q*q) *(c₄ α' β' γ' ^ (n K q : ℝ) * ((n K q : ℝ) ^ (((n K q : ℝ)+ 1)/2)) *
        (c₆ α' β' γ'* q) ^(r α β σ α' β' γ' hirr htriv habc q hq0 h2mq) * (c₇ α' β' γ')^(q :
            ℤ)) := ?_
  · rw [← one_mul (house (rho α β σ α' β' γ' hirr htriv habc q hq0 h2mq))]
    apply mul_le_mul
    · exact one_le_norm_c1rho α β σ α' β' γ' hirr htriv habc q hq0 h2mq
    · simp only [one_mul, le_refl]
    · exact house_nonneg (rho α β σ α' β' γ' hirr htriv habc q hq0 h2mq)
    · simp only [norm_nonneg]
  · unfold rho
    simp only [le_refl]
  · apply mul_le_mul (le_refl _)
    · exact
      house_sum_le_sum_house Finset.univ fun i ↦
        (algebraMap (𝓞 K) K) (η (K := K) α β σ α' β' γ' hirr htriv habc q hq0 h2mq i)
        * systemCoeffsR α β σ α' β' γ' hirr htriv habc q hq0 i h2mq
    · exact
      house_nonneg (∑ t, (algebraMap (𝓞 K) K)
        (η (K := K) α β σ α' β' γ' hirr htriv habc q hq0 h2mq
            t) * systemCoeffsR α β σ α' β' γ' hirr htriv habc q hq0 t h2mq)
    · exact norm_nonneg (cρ α β σ α' β' γ' hirr htriv habc q hq0 h2mq)
  · rw [mul_sum]
    apply Finset.sum_congr rfl
    intros i hi
    have  house_num_mul_int (α : K) (c' : ℤ) (hc : 0 ≤ c') :
    house ((c' : K) * α) = |(c' : ℝ)| * house (α) := by
        lift c' to ℕ using hc
        simpa using house_nat_mul α c'
    rw [house_num_mul_int
    (α := ((algebraMap (𝓞 K) K)
    (η (K := K) α β σ α' β' γ' hirr htriv habc q hq0 h2mq
        i) * systemCoeffsR α β σ α' β' γ' hirr htriv habc q hq0 i h2mq))]
    · simp only [Real.norm_eq_abs]
    · exact zero_le_c1rho α β σ α' β' γ' hirr htriv habc q hq0 h2mq
  · apply Finset.sum_congr rfl
    intros t ht
    rw [Algebra.left_comm (↑(cρ α β σ α' β' γ' hirr htriv habc q hq0 h2mq))
      (η (K := K) α β σ α' β' γ' hirr htriv habc q hq0 h2mq t) (systemCoeffsR α β σ α' β' γ' hirr
          htriv habc q hq0 t h2mq)]
    simp only [← zsmul_eq_mul]
    unfold systemCoeffsR
    unfold cρ
    rw [cρ_abs_eq]
    have : c₁ α' β' γ' ^ (2 * m K * q) = c₁ α' β' γ' ^ (m K * q)
     * c₁ α' β' γ' ^ (m K * q) := by
       rw [← pow_add]; ring
    rw [this]; clear this
    have := c_coeffspow_r α β σ α' β' γ' hirr htriv habc q hq0 t h2mq
    simp only [mul_assoc] at this
    rw [this]; clear this
    rw [Int.mul_comm (c₁ α' β' γ' ^ r α β σ α' β' γ' hirr htriv habc q hq0 h2mq)
     (c₁ α' β' γ' ^ (m K * q - a q t * (↑(l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq) + 1)) *
    c₁ α' β' γ' ^ (m K * q - b q t * (↑(l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq) + 1)))]
    simp only [mul_assoc]
    simp only [nsmul_eq_mul, zsmul_eq_mul,
     Int.cast_mul, Int.cast_pow]
    simp only [mul_assoc]
    simp only [Int.cast_eq]
    ring_nf
  · refine Finset.sum_le_sum ?_
    intro t ht
    trans
    · exact house_mul_le _ _
    refine mul_le_mul_of_nonneg (le_refl _) ?_ (house_nonneg _) (by positivity)

    trans
    · exact house_mul_le _ _
    refine mul_le_mul_of_nonneg (le_refl _) ?_ (house_nonneg _) (by positivity)

    trans
    · exact house_mul_le _ _
    refine mul_le_mul_of_nonneg (le_refl _) ?_ (house_nonneg _) (by positivity)

    trans
    · exact house_mul_le _ _
    refine mul_le_mul_of_nonneg ?_ ?_ (house_nonneg _) (by positivity)
    · simp [nsmul_eq_mul, zsmul_eq_mul, smul_eq_mul, Int.cast_pow]
    · trans
      · exact house_mul_le _ _
      ·
        refine mul_le_mul_of_nonneg ?_ ?_ (by positivity) (by positivity) <;>
          simp [house]
  · apply Finset.sum_le_sum
    intros t ht
    apply mul_le_mul
    · apply house_eta_le_c₄_pow α β σ α' β' γ' hirr htriv habc q hq0 t h2mq
    · simp only [mul_assoc]
      apply mul_le_mul
      · norm_cast
        rw [house_intCast]
      · apply mul_le_mul
        · norm_cast
          rw [house_intCast]
        · apply mul_le_mul
          · simp only [nsmul_eq_mul, smul_eq_mul]
            rw [← mul_pow]
            rw [mul_add]
            calc _ ≤  house ((↑(c₁ α' β' γ') * ↑(a q t) + ↑(c₁ α' β' γ') *
                  (↑(b q t) * β'))) ^ r α β σ α' β' γ' hirr htriv habc q hq0 h2mq :=?_
                 _ ≤  (↑|c₁ α' β' γ'| * (↑|↑q| * (1 + house
                     β'))) ^ r α β σ α' β' γ' hirr htriv habc q hq0 h2mq := ?_
            · apply house_pow_le _ _
            · rw [← mul_add]
              rw [pow_le_pow_iff_left₀]
              · have := house_add_mul_le α' β' γ' q t
                simp only [mul_assoc] at *
                norm_cast at *
                simp only [nsmul_eq_mul, zsmul_eq_mul] at this
                exact this
              · apply house_nonneg
              · unfold house
                positivity
              · exact r_ne_zero α β σ α' β' γ' hirr htriv habc q hq0 h2mq
            · simp only [Int.cast_abs, Nat.abs_cast, Int.cast_natCast, le_refl]
          · apply mul_le_mul
            · simp only [smul_eq_mul, zsmul_eq_mul]
              rw [← mul_pow]
              trans
              · apply house_pow_le _ _
              apply Bound.pow_le_pow_right_of_le_one_or_one_le
                (Or.inl ⟨one_le_house_of_isIntegral ?_ ?_, ?_⟩)
              · rw [← smul_eq_mul]
                exact mod_cast isIntegral_c₁α α' β' γ'
              · rw [← smul_eq_mul]
                exact mod_cast c₁α_ne_zero α β σ α' β' γ' hirr htriv habc
              · rw [mul_comm (m K) q]
                apply mul_le_mul (((finProdFinEquiv.symm.toFun t).1).isLt) ?_ (Nat.zero_le
                    _) (Nat.zero_le _)
                · exact (l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq).isLt
            · simp only [smul_eq_mul, zsmul_eq_mul]
              rw [← mul_pow]
              trans
              · apply house_pow_le _ _
              apply Bound.pow_le_pow_right_of_le_one_or_one_le
                (Or.inl ⟨one_le_house_of_isIntegral ?_ ?_, ?_⟩)
              · rw [← smul_eq_mul]
                exact mod_cast isIntegral_c₁γ α' β' γ'
              · rw [← smul_eq_mul]
                exact mod_cast c₁γ_ne_zero α β σ α' β' γ' hirr htriv habc
              · rw [mul_comm (m K) q]
                apply mul_le_mul (((finProdFinEquiv.symm.toFun t).2).isLt) ?_ (Nat.zero_le
                    _) (Nat.zero_le _)
                · exact (l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq).isLt
            · apply house_nonneg
            · unfold house; positivity
          · unfold house; positivity
          · unfold house; positivity
        · unfold house; positivity
        · positivity
      · unfold house; positivity
      · positivity
    · unfold house; positivity
    · apply mul_nonneg
      · simp only [Real.rpow_natCast]
        apply pow_nonneg
        · exact le_trans zero_le_one (one_le_c₄ α β σ α' β' γ' hirr htriv habc)
      · positivity
  · apply Finset.sum_le_sum
    intros t ht
    apply mul_le_mul
    · simp only [Real.rpow_natCast, le_refl]
    · apply mul_le_mul
      · simp only [abs_pow, Int.cast_pow, Int.cast_abs]
        refine pow_le_pow_right₀ ?_ ?_
        · norm_cast; exact one_le_abs_c₁ α' β' γ'
        · exact Nat.sub_le (m K * q) (a q t * (↑(l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq) +
            1))
      · apply mul_le_mul
        · simp only [abs_pow, Int.cast_pow, Int.cast_abs]
          refine pow_le_pow_right₀ ?_ ?_
          · norm_cast; exact one_le_abs_c₁ α' β' γ'
          · exact Nat.sub_le (m K * q) (b q t * (↑(l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq) +
              1))
        · nth_rw 1 [mul_assoc]
          apply mul_le_mul
          · rw [← mul_pow]; rw [← mul_pow]
          · apply mul_le_mul
            · simp only [zsmul_eq_mul, Int.cast_abs]
              rw [← mul_pow]
              refine pow_le_pow_left₀ ?_ ?_ (m K * q)
              · apply house_nonneg
              · trans
                · apply house_mul_le
                · simp only [house_intCast, Int.cast_abs, le_refl]
            · simp only [zsmul_eq_mul, Int.cast_abs]
              rw [← mul_pow]
              refine pow_le_pow_left₀ ?_ ?_ (m K * q)
              · apply house_nonneg
              · trans
                · apply house_mul_le
                · simp only [house_intCast, Int.cast_abs, le_refl]
            · unfold house; positivity
            · unfold house; positivity
          · unfold house; positivity
          · unfold house; positivity
        · unfold house; positivity
        · positivity
      · unfold house; positivity
      · positivity
    · unfold house; positivity
    · apply mul_nonneg
      · simp only [Real.rpow_natCast]
        apply pow_nonneg
        · exact le_trans zero_le_one (one_le_c₄ α β σ α' β' γ' hirr htriv habc)
      · positivity
  · simp only [ sum_const, card_univ, Fintype.card_fin]
    simp only [nsmul_eq_mul]
    apply mul_le_mul
    · simp only [Nat.cast_mul, le_refl]
    · nth_rw 4 [mul_assoc]
      apply mul_le_mul
      · simp only [Real.rpow_natCast, le_refl]
      · simp only [← mul_assoc]
        rw [← mul_pow]
        simp only [mul_assoc]
        rw [← mul_pow]
        rw [← mul_pow]
        rw [← mul_pow]
        simp only [Int.cast_abs,
        Nat.abs_cast, Int.cast_natCast, zpow_natCast]
        rw [mul_comm ((1 + house β') ^ r α β σ α' β' γ' hirr htriv habc q hq0 h2mq)
          ((|↑(c₁ α' β' γ')| * (house α' * (|↑(c₁ α' β' γ')| * house γ'))) ^ (m K * q))]
        nth_rw 3 [← mul_assoc]
        rw [mul_comm ((q:ℝ) ^ r α β σ α' β' γ' hirr htriv habc q hq0 h2mq)
         ((|↑(c₁ α' β' γ')| * (house α' * (|↑(c₁ α' β' γ')| * house γ'))) ^ (m K * q))]
        nth_rw 2 [← mul_assoc]
        rw [mul_comm  (|(c₁ α' β' γ' : ℝ)| ^ r α β σ α' β' γ' hirr htriv habc q hq0 h2mq)
          ((|(c₁ α' β' γ' : ℝ)| * (house α' * (|(c₁ α' β' γ' : ℝ)| *
           house γ'))) ^ (m K * q) * (q : ℝ) ^ r α β σ α' β' γ' hirr htriv habc q hq0 h2mq)]
        nth_rw 1 [← mul_assoc]
        rw [mul_comm  ((c₆ α' β' γ' * ↑q) ^ r α β σ α' β' γ' hirr htriv habc q hq0 h2mq) (c₇ α' β'
            γ' ^ q)]
        simp only [mul_assoc]
        rw [← mul_pow]
        rw [← mul_pow]
        nth_rw 1 [← mul_assoc]
        rw [← mul_pow]
        rw [pow_mul]
        rw [← mul_comm (q : ℝ) (c₆ α' β' γ')]
        unfold c₇ c₆
        simp only [mul_assoc]
        rfl
      · unfold house; positivity
      · apply mul_nonneg
        · simp only [Real.rpow_natCast]
          apply pow_nonneg
          · exact le_trans zero_le_one (one_le_c₄ α β σ α' β' γ' hirr htriv habc)
        · positivity
    · apply mul_nonneg
      · apply mul_nonneg
        · simp only [Real.rpow_natCast]
          apply pow_nonneg
          · exact le_trans zero_le_one (one_le_c₄ α β σ α' β' γ' hirr htriv habc)
        · positivity
      · unfold house; positivity
    · positivity

include α β σ α' β' γ' hirr htriv habc in
theorem bound_n_le_r' : ((n K q : ℝ) ^ (((n K q : ℝ)+ 1)/2)) ≤
     ((r α β σ α' β' γ' hirr htriv habc q hq0 h2mq : ℝ)^((1/2) * ((r α β σ α' β' γ' hirr htriv habc
         q hq0 h2mq : ℝ) + 1))) := by
      calc _ ≤ ((r α β σ α' β' γ' hirr htriv habc q hq0 h2mq : ℝ) ^ (((n K q : ℝ)+ 1)/2)) := ?_
           _ ≤ ((r α β σ α' β' γ' hirr htriv habc q hq0 h2mq : ℝ)^((1/2)* ((r α β σ α' β' γ' hirr
               htriv habc q hq0 h2mq : ℝ) + 1))) := ?_
      · refine Real.rpow_le_rpow ?_ ?_ ?_
        · simp only [Nat.cast_nonneg]
        · simp only [Nat.cast_le]; exact n_le_r α β σ α' β' γ' hirr htriv habc q hq0 h2mq
        · refine div_nonneg ?_ ?_
          · norm_cast
            exact Nat.le_add_left 0 (n K q + 1)
          · simp only [Nat.ofNat_nonneg]
      · apply Real.rpow_le_rpow_of_exponent_le_or_ge
        left
        · simp only [Nat.one_le_cast, one_div]
          refine ⟨r_qt_0 α β σ α' β' γ' hirr htriv habc q hq0 h2mq, ?_⟩
          · ring_nf
            simp only [one_div, add_le_add_iff_left,
             inv_pos, Nat.ofNat_pos, mul_le_mul_iff_left₀, Nat.cast_le]
            exact n_le_r α β σ α' β' γ' hirr htriv habc q hq0 h2mq

include α β σ α' β' γ' hirr htriv habc in
lemma bound_n_le_r :
  (c₄ α' β' γ' ^ (n K q : ℝ) * ((n K q : ℝ) ^ (((n K q : ℝ)+ 1)/2)) ≤
  ((c₄ α' β' γ' ^ (r α β σ α' β' γ' hirr htriv habc q hq0 h2mq : ℝ)) *
    ((r α β σ α' β' γ' hirr htriv habc q hq0 h2mq : ℝ)^((1/2)* ((r α β σ α' β' γ' hirr htriv habc q
        hq0 h2mq : ℝ) + 1))))) := by
    apply mul_le_mul
    · simp only [Real.rpow_natCast]
      refine pow_le_pow_right₀ (one_le_c₄ α β σ α' β' γ' hirr htriv habc) (n_le_r α β σ α' β' γ'
          hirr htriv habc q hq0 h2mq)
    · exact bound_n_le_r' α β σ α' β' γ' hirr htriv habc q hq0 h2mq
    · apply Real.rpow_nonneg
      simp only [Nat.cast_nonneg]
    · apply Real.rpow_nonneg
      exact le_trans zero_le_one (one_le_c₄ α β σ α' β' γ' hirr htriv habc)

include α β σ α' β' γ' hirr htriv habc in
lemma q_le_2sqrtmr : q^2 ≤ 2*m K*r α β σ α' β' γ' hirr htriv habc q hq0 h2mq := by
  trans
  · apply q_sq_le_two_mn q h2mq
  refine Nat.mul_le_mul (le_refl _) (n_le_r α β σ α' β' γ' hirr htriv habc q hq0 h2mq)

include α β σ α' β' γ' hirr htriv habc in
lemma sqt_etc : Real.sqrt (2*m K*(r α β σ α' β' γ' hirr htriv habc q hq0 h2mq)) =
  Real.sqrt (2*m K) * (r α β σ α' β' γ' hirr htriv habc q hq0 h2mq : ℝ)^(1/2 : ℝ) := by
    rw [Real.sqrt_mul]
    · congr
      exact Real.sqrt_eq_rpow ↑(r α β σ α' β' γ' hirr htriv habc q hq0 h2mq)
    · positivity

/-- The constant combining `c₆`, `√(2m)` and `c₇`, bounding `house ρ`. -/
def c₈ : ℝ := (c₆ α' β' γ' * √(2 * ↑(m K)) * c₇ α' β' γ' ^ (2 * m K) * c₄ α' β' γ' * (2 * ↑(m K)))

include α β σ α' β' γ' hirr htriv habc in
@[nolint unusedArguments]
lemma c7_nonneg : 0 ≤ c₇ α' β' γ' := by
  unfold c₇ house
  positivity

include α β σ α' β' γ' hirr htriv habc in
lemma c8_nonneg : 0 ≤ c₈ α' β' γ' := by
  unfold c₈
  apply mul_nonneg ?_ (by positivity)
  · apply mul_nonneg ?_ (le_trans zero_le_one (one_le_c₄ α β σ α' β' γ' hirr htriv habc))
    · apply mul_nonneg (mul_nonneg (c₆_nonneg α β σ α' β' γ' hirr htriv habc) (by simp)) (pow_nonneg (c7_nonneg α β σ α' β' γ' hirr htriv habc) _)

include α β σ α' β' γ' hirr htriv habc in
lemma c8_geq_one : 1 ≤ c₈ α' β' γ' := by
  unfold c₈
  have : 1 ≤ c₆ α' β' γ' := one_le_c₆ α β σ α' β' γ' hirr htriv habc
  have : 1 ≤ c₇ α' β' γ' := one_le_c₇ α β σ α' β' γ' hirr htriv habc
  have := one_le_c₄ α β σ α' β' γ' hirr htriv habc
  apply one_le_mul_of_one_le_of_one_le
  · apply one_le_mul_of_one_le_of_one_le
    · apply one_le_mul_of_one_le_of_one_le
      · apply one_le_mul_of_one_le_of_one_le
        · (expose_names; exact this_1)
        · rw [Real.one_le_sqrt]
          apply one_le_mul_of_one_le_of_one_le (by grind) ?_
          · simp only [Nat.one_le_cast]
            exact Nat.le_of_ble_eq_true rfl
      · (expose_names; exact one_le_pow₀ this_2)
    · exact this
  · apply one_le_mul_of_one_le_of_one_le (by grind) ?_
    · simp only [Nat.one_le_cast]
      exact Nat.le_of_ble_eq_true rfl

include α β σ α' β' γ' hirr htriv habc in
lemma zero_lt_r : 0 < r α β σ α' β' γ' hirr htriv habc q hq0 h2mq :=
  r_qt_0 α β σ α' β' γ' hirr htriv habc q hq0 h2mq

include α β σ α' β' γ' hirr htriv habc in
@[nolint unusedArguments]
theorem q_sq2_neq_1 (m q : ℕ) (_ : 0 < q)
    (h2mq : 2 * m ∣ q ^ 2) : q ^ 2 ≠ 1 := by
  intro hq2eq1
  have hdiv1 : 2 * m ∣ 1 := by
    exact (Nat.ModEq.dvd_iff
     (congrFun (congrArg HMod.hMod hq2eq1) (q ^ 2)) h2mq).mp h2mq
  cases m with
  | zero => simp [*] at hdiv1
  | succ m' =>
    have h_two_eq_one : 2 * (m'.succ) = 1 := Nat.eq_one_of_dvd_one hdiv1
    have h_ge_two : 2 * (m'.succ) ≥ 2 := by
      calc
        2 * (m'.succ) = 2 + 2 * m' := by
          simp only [Nat.succ_eq_add_one]
          ring_nf
        _ ≥ 2 := Nat.le_add_right _ _
    have absurd_le : 1 ≥ 2 := by rwa [h_two_eq_one] at h_ge_two
    have gt21 : 2 > 1 := by decide
    exact (Nat.not_le_of_gt gt21) absurd_le

include α β σ α' β' γ' hirr htriv habc in
theorem eq6b.extracted_1_1 :
  q * q ≤ (2 * m K : ℝ) ^ (r α β σ α' β' γ' hirr htriv habc q hq0 h2mq: ℝ) * (r α β σ α' β' γ' hirr
      htriv habc q hq0 h2mq: ℝ) := by
    calc _ = (q^2: ℝ) := ?_
         _ ≤ (2 * ↑(m K): ℝ) * (n K q: ℝ) := ?_
         _ ≤ (2 * ↑(m K): ℝ) ^ (n K q: ℝ) := ?_
         _ ≤ ((2*m K: ℝ)^(r α β σ α' β' γ' hirr htriv habc q hq0 h2mq: ℝ)) := ?_
         _ ≤ (2 * ↑(m K) : ℝ) ^ (r α β σ α' β' γ' hirr htriv habc q hq0 h2mq: ℝ) * (r α β σ α' β' γ'
             hirr htriv habc q hq0 h2mq: ℝ) := ?_
    · grind
    · norm_cast; exact q_sq_le_two_mn q h2mq
    · have : (2 * ↑(m K)) * n K q ≤ (2 * ↑(m K)) ^n K q := by
        refine Nat.mul_le_pow ?_ (n K q)
        simp only [ne_eq, mul_eq_one,
          OfNat.ofNat_ne_one, false_and, not_false_eq_true]
      simp only [Real.rpow_natCast, ge_iff_le]
      exact mod_cast this
    · apply Real.rpow_le_rpow_of_exponent_le
      · have : 1 ≤ 2 * (m K : ℝ) := by
              unfold m
              simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
              ring_nf
              refine le_add_of_le_of_nonneg ?_ ?_
              · simp only [Nat.one_le_ofNat]
              · positivity
        exact this
      · norm_cast; exact n_le_r α β σ α' β' γ' hirr htriv habc q hq0 h2mq
    · nth_rw 1 [← mul_one (a:= (2 * (m K : ℝ)) ^ (r α β σ α' β' γ' hirr htriv habc q hq0 h2mq : ℝ))]
      apply mul_le_mul (by grind) (mod_cast (one_le_r α β σ α' β' γ' hirr htriv habc q hq0 h2mq)) (by grind) (by positivity)

include α β σ α' β' γ' hirr htriv habc in
theorem eq6b.extracted_1_2 :
  q * q ≤ (2 * m K : ℝ) ^ (r α β σ α' β' γ' hirr htriv habc q hq0 h2mq: ℝ) := by
    calc _ = (q^2: ℝ) := ?_
         _ ≤ (2 * ↑(m K): ℝ) * (n K q: ℝ) := ?_
         _ ≤ (2 * ↑(m K): ℝ) ^ (n K q: ℝ) := ?_
         _ ≤ ((2*m K: ℝ)^(r α β σ α' β' γ' hirr htriv habc q hq0 h2mq: ℝ)) := ?_
    · grind
    · norm_cast; exact q_sq_le_two_mn q h2mq
    · have : (2 * ↑(m K)) * n K q ≤ (2 * ↑(m K)) ^n K q := by
        refine Nat.mul_le_pow ?_ (n K q)
        simp only [ne_eq, mul_eq_one,
          OfNat.ofNat_ne_one, false_and, not_false_eq_true]
      simp only [Real.rpow_natCast, ge_iff_le]
      exact mod_cast this
    · apply Real.rpow_le_rpow_of_exponent_le
      · have : 1 ≤ 2 * (m K : ℝ) := by
              unfold m
              simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
              ring_nf
              refine le_add_of_le_of_nonneg ?_ ?_
              · simp only [Nat.one_le_ofNat]
              · positivity
        exact this
      · norm_cast
        exact n_le_r α β σ α' β' γ' hirr htriv habc q hq0 h2mq

open Real

include h2mq in
include α β σ α' β' γ' hirr htriv habc in
@[nolint unusedArguments]
lemma q_eq_sqrtmn : q = sqrt (2 * m K* n K q) := by
  norm_cast
  rw [← q_sq_eq_two_mn q h2mq]
  simp only [Nat.cast_pow, Nat.cast_nonneg, sqrt_sq]

set_option linter.style.multiGoal false in
include α β σ α' β' γ' hirr htriv habc in
lemma eq6b : (q*q) * ((((c₄ α' β' γ' ^ (n K q : ℝ) *
  ((n K q : ℝ) ^ (((n K q : ℝ)+ 1)/2)))) *
  (c₆ α' β' γ'* q) ^(r α β σ α' β' γ' hirr htriv habc q hq0 h2mq) * (c₇ α' β' γ')^q)) ≤
  c₈ α' β' γ'^(r α β σ α' β' γ' hirr htriv habc q hq0 h2mq : ℝ) *
   (r α β σ α' β' γ' hirr htriv habc q hq0 h2mq : ℝ) ^ ((r α β σ α' β' γ' hirr htriv habc q hq0 h2mq
       : ℝ) + 3/2) := by
  calc
       _ ≤ (((2*m K)^(r α β σ α' β' γ' hirr htriv habc q hq0 h2mq : ℝ))* ((r α β σ α' β' γ' hirr
           htriv habc q hq0 h2mq)) *
           ((((c₄ α' β' γ' ^ (r α β σ α' β' γ' hirr htriv habc q hq0 h2mq : ℝ)) *
           ((r α β σ α' β' γ' hirr htriv habc q hq0 h2mq : ℝ)^((1/2)* ((r α β σ α' β' γ' hirr htriv
               habc q hq0 h2mq : ℝ) + 1))))) *
           (((c₆ α' β' γ'* Real.sqrt (2*m K) *
           (r α β σ α' β' γ' hirr htriv habc q hq0 h2mq: ℝ)^(1/2 :
               ℝ)) ^(r α β σ α' β' γ' hirr htriv habc q hq0 h2mq: ℝ)) *
           ((c₇ α' β' γ')^(2*m K))^(r α β σ α' β' γ' hirr htriv habc q hq0 h2mq: ℝ)))) := ?_
       _ ≤ c₈ α' β' γ'^(r α β σ α' β' γ' hirr htriv habc q hq0 h2mq : ℝ) *
         (r α β σ α' β' γ' hirr htriv habc q hq0 h2mq : ℝ)^((r α β σ α' β' γ' hirr htriv habc q hq0
             h2mq : ℝ) + 3/2) := ?_
  · -- keep your existing first block unchanged
    apply mul_le_mul (eq6b.extracted_1_1 α β σ α' β' γ' hirr htriv habc q hq0 h2mq)
    · simp only [mul_assoc]
      apply mul_le_mul
      · simp only [Real.rpow_natCast]
        refine pow_le_pow_right₀ (one_le_c₄ α β σ α' β' γ' hirr htriv habc) (n_le_r α β σ α' β' γ'
            hirr htriv habc q hq0 h2mq)
      · apply mul_le_mul
        · exact bound_n_le_r' α β σ α' β' γ' hirr htriv habc q hq0 h2mq
        · apply mul_le_mul
          · simp only [Real.rpow_natCast]
            refine pow_le_pow_left₀ ?_ ?_ (r α β σ α' β' γ' hirr htriv habc q hq0 h2mq)
            · unfold c₆ house; positivity
            · refine mul_le_mul_of_nonneg_left ?_ ?_
              · have := q_eq_sqrtmn α β σ α' β' γ' hirr htriv habc q h2mq
                calc _ ≤ √(2 * ↑(m K)) * ↑(n K q) ^ (1 / 2 : ℝ) := ?_
                     _ ≤ √(2 * ↑(m K)) * ↑(r α β σ α' β' γ' hirr htriv habc q hq0 h2mq) ^ (1 / 2 :
                         ℝ) := ?_
                · rw [this]
                  rw [Real.sqrt_mul]
                  refine mul_le_mul_of_nonneg_left ?_ ?_
                  · rw [le_iff_lt_or_eq]
                    right
                    exact Real.sqrt_eq_rpow ↑(n K q)
                  · simp only [Nat.ofNat_nonneg, Real.sqrt_nonneg]
                  grind
                · refine mul_le_mul_of_nonneg_left ?_ ?_
                  · apply Real.rpow_le_rpow
                    · simp only [Nat.cast_nonneg]
                    · simp only [Nat.cast_le]
                      exact n_le_r α β σ α' β' γ' hirr htriv habc q hq0 h2mq
                    · simp only [one_div, inv_nonneg, Nat.ofNat_nonneg]
                  · simp only [Nat.ofNat_nonneg, Real.sqrt_nonneg]
              · unfold c₆ house; positivity
          · simp only [Real.rpow_natCast]
            rw [← pow_mul]
            refine pow_le_pow_right₀ ?_ ?_
            · exact one_le_c₇ α β σ α' β' γ' hirr htriv habc
            · trans
              · apply q_le_two_mn q h2mq
              apply mul_le_mul (le_refl _) (n_le_r α β σ α' β' γ' hirr htriv habc q hq0 h2mq)
                (by positivity) (by positivity)
          · unfold c₇ house; positivity
          · unfold c₆ house; positivity
        · unfold c₇ c₆ house; positivity
        · positivity
      · unfold c₆ c₇ house; positivity
      · simp only [Real.rpow_natCast]
        unfold c₄
        apply pow_nonneg
        simp only [lt_sup_iff, zero_lt_one, true_or,
          mul_nonneg_iff_of_pos_left]
        exact le_trans zero_le_one (one_le_c₃ α' β' γ')
    · unfold c₆ c₇ house
      · apply mul_nonneg
        · apply mul_nonneg
          · simp only [Real.rpow_natCast]
            · apply mul_nonneg
              · apply pow_nonneg
                exact le_trans zero_le_one (one_le_c₄ α β σ α' β' γ' hirr htriv habc)
              · positivity
          · positivity
        · positivity
    · positivity
  · -- keep your existing second block unchanged
    nth_rw 2 [Real.mul_rpow]
    nth_rw 4 [mul_comm]
    nth_rw 2 [mul_assoc]
    simp only [← mul_assoc]
    nth_rw 3 [mul_assoc]
    nth_rw 1 [← mul_comm]
    rw [mul_comm ((2 * (m K : ℝ)) ^ (r α β σ α' β' γ' hirr htriv habc q hq0 h2mq : ℝ)) (r α β σ α'
        β' γ' hirr htriv habc q hq0 h2mq : ℝ)]
    nth_rw 3 [← Real.rpow_one ((r α β σ α' β' γ' hirr htriv habc q hq0 h2mq))]
    simp only [← mul_assoc]
    nth_rw 1  [← Real.rpow_add]
    simp only [mul_assoc]
    rw [← Real.mul_rpow]
    rw [← mul_assoc]
    rw [← mul_assoc]
    nth_rw 8 [mul_comm]
    rw [mul_rotate]
    nth_rw 1 [← mul_assoc]
    nth_rw 1 [← mul_assoc]
    rw [← Real.mul_rpow]
    nth_rw 1 [mul_assoc]
    nth_rw 1 [mul_assoc]
    nth_rw 3 [← mul_assoc]
    nth_rw 1  [← Real.rpow_mul]
    nth_rw 1  [← Real.rpow_add]
    nth_rw 7 [mul_comm]
    simp only [← mul_assoc]
    nth_rw 1 [← Real.mul_rpow]
    apply mul_le_mul
    · unfold c₈
      simp only [Nat.ofNat_nonneg, Real.sqrt_mul,
        Real.rpow_natCast, le_refl]
    · ring_nf
      simp only [le_refl]
    · positivity
    · simp only [Real.rpow_natCast]
      apply pow_nonneg
      · apply c8_nonneg α β σ α' β' γ' hirr htriv habc
    · apply mul_nonneg
      · apply mul_nonneg
        · apply mul_nonneg
          · apply c₆_nonneg α β σ α' β' γ' hirr htriv habc
          · simp only [Nat.ofNat_nonneg,
            Real.sqrt_mul, Real.sqrt_pos, Nat.ofNat_pos,
            mul_nonneg_iff_of_pos_left, Real.sqrt_nonneg]
        · apply pow_nonneg
          · apply c7_nonneg α β σ α' β' γ' hirr htriv habc
      · exact le_trans zero_le_one (one_le_c₄ α β σ α' β' γ' hirr htriv habc)
    · positivity
    · simp only [Nat.cast_pos]
      apply zero_lt_r α β σ α' β' γ' hirr htriv habc
    · simp only [Nat.cast_nonneg]
    · apply mul_nonneg
      · exact c₆_nonneg α β σ α' β' γ' hirr htriv habc
      · simp only [Nat.ofNat_nonneg, Real.sqrt_mul,
        Real.sqrt_pos, Nat.ofNat_pos,
        mul_nonneg_iff_of_pos_left, Real.sqrt_nonneg]
    · apply mul_nonneg
      · apply pow_nonneg
        · exact c7_nonneg α β σ α' β' γ' hirr htriv habc
      · exact le_trans zero_le_one (one_le_c₄ α β σ α' β' γ' hirr htriv habc)
    · apply pow_nonneg
      · exact c7_nonneg α β σ α' β' γ' hirr htriv habc
    · exact le_trans zero_le_one (one_le_c₄ α β σ α' β' γ' hirr htriv habc)
    · simp only [Nat.cast_pos]
      exact r_qt_0 α β σ α' β' γ' hirr htriv habc q hq0 h2mq
    · apply mul_nonneg
      · exact c₆_nonneg α β σ α' β' γ' hirr htriv habc
      · simp only [Nat.ofNat_nonneg, Real.sqrt_mul,
        Real.sqrt_pos, Nat.ofNat_pos,
        mul_nonneg_iff_of_pos_left, Real.sqrt_nonneg]
    · positivity

include α β σ α' β' γ' hirr htriv habc in
lemma eq6 : house (rho α β σ α' β' γ' hirr htriv habc q hq0 h2mq) ≤ c₈ α' β' γ'^(r α β σ α' β' γ'
    hirr htriv habc q hq0 h2mq : ℝ) *
(r α β σ α' β' γ' hirr htriv habc q hq0 h2mq : ℝ)^((r α β σ α' β' γ' hirr htriv habc q hq0 h2mq : ℝ)
    + 3/2) := by
  trans
  · apply eq6a α β σ α' β' γ' hirr htriv habc q hq0 h2mq
  exact eq6b α β σ α' β' γ' hirr htriv habc q hq0 h2mq


end GelfondSchneider

end
