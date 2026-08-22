/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/

module

--public import Mathlib.NumberTheory.Transcendental.GelfondSchneider.MainAnalytic
public import Mathlib.NumberTheory.Transcendental.GelfondSchneider.MainHol
public import Mathlib.Analysis.Calculus.IteratedDeriv.Analytic

/-!
# Gelfond-Schneider: the analytic upper bound

Cauchy's estimate bounds `‖N ρ‖` above by `c₁₅ ^ (-r)`; with the algebraic lower bound of
`MainPostAnalytic` this is the contradiction proving the theorem.

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

/-- The constant `exp (|1 + ‖β‖| * ‖log α‖ * m)`. -/
def c₉ (K : Type) [Field K] [NumberField K] : ℝ := Real.exp (|1 + ‖β‖| *  ‖Complex.log α‖ * (↑(m K)
    : ℝ))

include α β σ α' β' γ' hirr htriv habc in
@[nolint unusedArguments]
lemma c9_pos : 0 < (c₉ α β K) := Real.exp_pos _

include α β σ α' β' γ' hirr htriv habc in
@[nolint unusedArguments]
lemma c9_nonneg : 0 ≤ (c₉ α β K) := by
  rw [le_iff_lt_or_eq]
  left
  exact Real.exp_pos _

include α β σ α' β' γ' hirr htriv habc in
@[nolint unusedArguments]
lemma c9_gt_1 : 1 ≤ (c₉ α β K) := by
  apply Real.one_le_exp
  positivity

/-- The constant `m ^ (m - 1)`. -/
def c₁₁ (K : Type) [Field K] [NumberField K] : ℝ := (↑(m K) ^ ((m K) - 1))

include α β σ α' β' γ' hirr htriv habc in
@[nolint unusedArguments]
lemma one_le_c11 : 1 ≤ (c₁₁ K) :=
  (one_le_pow_iff_of_nonneg (by simp) (by unfold m; grind)).mpr (mod_cast (one_le_m K))

include α β σ α' β' γ' hirr htriv habc in
lemma c11_nonneg : 0 ≤ (c₁₁ K) := le_trans zero_le_one (one_le_c11 α β σ α' β' γ' hirr htriv habc)

variable [DecidableEq (K →+* ℂ)]

variable {z : ℂ} {l₀ : ℝ} (hz : (z : ℂ) ∈ Metric.sphere 0 ((m K) * (1 + ((r α β σ α' β' γ' hirr
    htriv habc) q hq0 h2mq / q))))
  (hl0 : (l₀ : ℝ) < ((m K) : ℝ) * (1 + (r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq / q))

include α β σ α' β' γ' hirr htriv habc in
@[nolint unusedArguments]
lemma norm_hz (hz : z ∈ Metric.sphere 0 (((m K) : ℝ) * (1 + ((r α β σ α' β' γ' hirr htriv habc) q
    hq0 h2mq : ℝ) / (q : ℝ)))) :
    ‖z‖ ≤ ‖((m K) : ℝ)‖ * ‖1 + ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) / (q: ℝ)‖ := by
  simp only [mem_sphere_iff_norm, sub_zero] at hz
  rw [hz, ← norm_mul, Real.norm_eq_abs]
  exact le_abs_self _



include hz in
include α β σ α' β' γ' hirr htriv habc in
@[nolint unusedArguments]
lemma abs_Rb : norm (((R α β σ α' β' γ' hirr htriv habc) q hq0 h2mq) z) ≤ (q * q) * (((c₄ α' β' γ')
    ^ ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) *
    ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq) ^ ((((r α β σ α' β' γ' hirr htriv habc) q hq0
        h2mq : ℝ ) + 1) / 2)) *
    ((c₉ α β K)) ^ ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq + q : ℝ)) := by
  calc _ ≤ ∑ t, ((house ((((algebraMap (𝓞 K) K)
             (((η (K := K) α β σ α' β' γ' hirr htriv habc) q hq0 h2mq)
                 t))))) * ‖cexp ((ρ α β) q t * z)‖) := ?_
       _ ≤ ∑ t : Fin (q*q), ((c₄ α' β' γ') ^ ((n K) q : ℝ)) * ((n K) q : ℝ) ^ ((((n K) q : ℝ) + 1) /
           2)
           * Real.exp ‖((ρ α β) q t * z)‖ := ?_
       _ ≤ ∑ t : Fin (q*q), ((c₄ α' β' γ') ^ ((n K) q : ℝ)) * ((n K) q : ℝ) ^ ((((n K) q : ℝ) + 1) /
           2) *
           Real.exp (norm ((q : ℝ) * (1 + norm β) * ‖Complex.log α‖ * ((m K) : ℝ) *
           ((1 + ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) / (q : ℝ))))) := ?_
       _ ≤ (q * q) * (((c₄ α' β' γ') ^ ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) * ((r α β
           σ α' β' γ' hirr htriv habc) q hq0 h2mq) ^
           ((((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ ) + 1) / 2)) * ((c₉ α β K)) ^ ((r α
               β σ α' β' γ' hirr htriv habc) q hq0 h2mq + q : ℝ)) := ?_
  · unfold R
    simp only [canonicalEmbedding.apply_at]
    trans
    · apply norm_sum_le
    simp only [Complex.norm_mul]
    apply Finset.sum_le_sum
    intros i hi
    simp only [norm_pos_iff, ne_eq, exp_ne_zero, not_false_eq_true, mul_le_mul_iff_left₀]
    apply norm_embedding_le_house
  · refine sum_le_sum ?_
    intro i hi
    refine mul_le_mul ?_ ?_ ?_ ?_
    · simpa using (house_eta_le_c₄_pow α β σ α' β' γ' hirr htriv habc q hq0 i h2mq)
    · simpa using (Complex.norm_exp_le_exp_norm ((ρ α β) q i * z))
    · simp
    · apply mul_nonneg
      · exact Real.rpow_nonneg (le_trans zero_le_one ((one_le_c₄ α β σ α' β' γ' hirr htriv habc))) _
      · exact Real.rpow_nonneg (by simpa using (Nat.cast_nonneg ((n K) q))) _
  · apply sum_le_sum
    intros i hi
    apply mul_le_mul
    · have lemma82 := house_eta_le_c₄_pow α β σ α' β' γ' hirr htriv habc q hq0 i h2mq
      unfold house at lemma82
      apply Preorder.le_refl _
    · unfold ρ
      simp only [nsmul_eq_mul, norm_mul, Real.exp_le_exp]
      calc
           _ ≤  (‖↑(a q i : ℂ)‖ + ‖↑(b q i) * β‖) * ‖Complex.log α‖ * ‖z‖ := ?_

           _ ≤  (‖(q : ℤ)‖ + ‖q * β‖) * ‖Complex.log α‖ * ‖z‖ := ?_

           _ ≤ (‖(q : ℤ)‖ + ((‖↑(q : ℤ)‖ * ‖β‖))) * ‖Complex.log α‖ * ‖z‖ := ?_

           _ = (‖(q : ℤ)‖ * ((1 + ‖β‖))) * ‖Complex.log α‖ * ‖z‖ := ?_

           _ ≤ ‖(q : ℤ)‖ * ‖1 + ‖β‖‖ * ‖Complex.log α‖* ‖(↑(m K) : ℝ)‖ *
               ‖(1 + ↑((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) / (q : ℝ))‖ := ?_

           _ ≤ ‖(q : ℝ)‖ * ‖1 + ‖β‖‖ * ‖Complex.log α‖ * ‖(↑(m K) : ℝ)‖ *
               ‖(1 + ↑((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) / (q : ℝ))‖ := by
                simp only [mul_assoc]; simp_all
      · gcongr; apply norm_add_le
      · gcongr
        · simp only [RCLike.norm_natCast, _root_.norm_natCast, Nat.cast_le]
          exact ((finProdFinEquiv.symm.toFun i).1).isLt
        · simp only [Complex.norm_mul, RCLike.norm_natCast]
          apply mul_le_mul ?_ (by rfl) (by simp) (by simp)
          · simp only [Nat.cast_le]
            exact ((finProdFinEquiv.symm.toFun i).2).isLt
      · gcongr; simp
      · congr
        nth_rw 1 [← mul_one (a:=(‖(q : ℤ)‖))]
        rw [mul_add]
      · simp only [mul_assoc]
        apply mul_le_mul
        · simp only [le_refl]
        · gcongr
          · exact le_abs_self (1 + ‖β‖)
          · exact (norm_hz α β σ α' β' γ' hirr htriv habc) q hq0 h2mq hz
        · positivity
        · simp only [Int.norm_natCast, Nat.cast_nonneg]
      simp only [Real.norm_eq_abs]
      simp only [Nat.abs_cast, abs_norm, le_refl]
    · exact Real.exp_nonneg ‖(ρ α β) q i * z‖
    · apply mul_nonneg
      · simp only [Real.rpow_natCast]
        apply pow_nonneg
        exact le_trans zero_le_one ((one_le_c₄ α β σ α' β' γ' hirr htriv habc))
      · apply Real.rpow_nonneg
        simp only [Nat.cast_nonneg]
  · simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]
    apply mul_le_mul (by rfl) ?_ ?_ (by positivity)
    · apply mul_le_mul
      · apply mul_le_mul
        · simp only [Real.rpow_natCast]
          refine Bound.pow_le_pow_right_of_le_one_or_one_le ?_
          left
          exact ⟨one_le_c₄ α β σ α' β' γ' hirr htriv habc, n_le_r α β σ α' β' γ' hirr htriv habc q
              hq0 h2mq⟩
        · calc _ ≤ ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) ^ ((((n K) q : ℝ) + 1) /
            2) := ?_
               _ ≤ ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) ^ ((((r α β σ α' β' γ' hirr
                   htriv habc) q hq0 h2mq :ℝ) + 1) / 2) := ?_
          · apply Real.rpow_le_rpow
            · simp only [Nat.cast_nonneg]
            · simp only [Nat.cast_le]; exact n_le_r α β σ α' β' γ' hirr htriv habc q hq0 h2mq
            · refine div_nonneg ?_ ?_
              · norm_cast
                simp
              · simp only [Nat.ofNat_nonneg]
          · apply Real.rpow_le_rpow_of_exponent_le
            · simp only [Nat.one_le_cast]
              trans
              · apply n_one_le q hq0 h2mq
              exact n_le_r α β σ α' β' γ' hirr htriv habc q hq0 h2mq
            · refine (div_le_div_iff_of_pos_right ?_).mpr ?_
              · simp only [Nat.ofNat_pos]
              · simp only [add_le_add_iff_right, Nat.cast_le]
                exact n_le_r α β σ α' β' γ' hirr htriv habc q hq0 h2mq
        · apply Real.rpow_nonneg; simp only [Nat.cast_nonneg]
        · apply Real.rpow_nonneg; exact le_trans zero_le_one ((one_le_c₄ α β σ α' β' γ' hirr htriv
            habc))
      · rw [Real.rpow_def_of_pos (x:= (c₉ α β K))]
        · calc _ ≤ Real.exp ( |1 + ‖β‖| *  ‖Complex.log α‖ * (↑(m K)) *
                   |(q : ℝ) * (1 + ↑((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq) / ↑q)|) := ?_
               _ ≤ Real.exp (Real.log (c₉ α β K) * (↑((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq)
                   + ↑q)) := ?_

          · simp only [Real.exp_le_exp]
            rw [norm_mul];rw [norm_mul];rw [norm_mul];rw [norm_mul]
            have : ‖(q : ℝ)‖ * ‖1 + ‖β‖‖ *  ‖‖Complex.log α‖‖ * ‖((m K) : ℝ)‖ *
                   ‖(1 + ↑((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) / (q : ℝ))‖ =
                   ‖1 + ‖β‖‖ *  ‖‖Complex.log α‖‖ * ‖((m K) : ℝ)‖ *
                   ‖(q : ℝ)‖ * ‖(1 + ↑((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) / (q :
                       ℝ))‖ := by
                simp only [Real.norm_eq_abs, mul_eq_mul_right_iff, abs_eq_zero]
                left
                rw [mul_assoc, mul_assoc, mul_comm]
                simp only [mul_assoc]
            simp only [mul_assoc] at this
            simp only [mul_assoc]
            rw [this]
            simp only [Real.norm_eq_abs]
            rw [← abs_mul]
            have : (q : ℝ) * (1 + ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) / q) =
                       (((q : ℝ) + ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ))) := by
                        ring_nf
                        simp only [mul_assoc]
                        nth_rw 2 [mul_comm]
                        simp only [← mul_assoc]
                        simp only [add_right_inj]
                        rw [mul_inv_cancel₀]
                        simp only [one_mul]
                        simp only [ne_eq, Nat.cast_eq_zero]
                        rw [← ne_eq]
                        exact Nat.ne_zero_of_lt hq0
            rw [this]
            simp
          · simp only [mul_assoc, Real.exp_le_exp]
            have : |(((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq) + q : ℝ)| = (↑((r α β σ α' β'
                γ' hirr htriv habc) q hq0 h2mq) + ↑q) := by
              simp only [abs_eq_self]; positivity
            rw [← this]
            simp only [c₉, Real.log_exp, mul_assoc]
            gcongr
            have : (q : ℝ) * (1 + ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) / q) =
                       (((q : ℝ) + ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ))) := by
                        ring_nf
                        simp only [mul_assoc]
                        nth_rw 2 [mul_comm]
                        simp only [← mul_assoc]
                        simp only [add_right_inj]
                        rw [mul_inv_cancel₀]
                        · simp only [one_mul]
                        simp only [ne_eq, Nat.cast_eq_zero]
                        rw [← ne_eq]
                        exact Nat.ne_zero_of_lt hq0
            rw [this]
            rw [add_comm]
        · unfold c₉; apply Real.exp_pos
      · positivity
      · apply mul_nonneg (Real.rpow_nonneg _ _) (Real.rpow_nonneg (by positivity) _)
        exact le_trans zero_le_one ((one_le_c₄ α β σ α' β' γ' hirr htriv habc))
    · simp only [Real.rpow_natCast, norm_mul, Real.norm_eq_abs]
      apply mul_nonneg
        (mul_nonneg (pow_nonneg (le_trans zero_le_one ((one_le_c₄ α β σ α' β' γ' hirr htriv habc))) _) (by positivity))
        (Real.exp_nonneg _)

/-- The constant `2 * m * c₄ * c₉ * c₉ ^ (2 * m)`. -/
def c₁₀ : ℝ := (2*(m K)* (c₄ α' β' γ')* (c₉ α β K)* (c₉ α β K)^(2*(m K) : ℝ))

include α β σ α' β' γ' hirr htriv habc in
@[nolint unusedArguments]
lemma c10_nonneg : 0 ≤ (c₁₀ α β α' β' γ') := by
  unfold c₁₀
  apply mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
      (le_trans zero_le_one ((one_le_c₄ α β σ α' β' γ' hirr htriv
          habc)))) (c9_nonneg α β σ α' β' γ' hirr htriv habc))
  · apply Real.rpow_nonneg; exact c9_nonneg α β σ α' β' γ' hirr htriv habc

include α β σ α' β' γ' hirr htriv habc in
@[nolint unusedArguments]
lemma one_le_c10 : 1 ≤ (c₁₀ α β α' β' γ') := by
  unfold c₁₀
  have hm : (1 : ℝ) ≤ (m K) := by exact_mod_cast (one_le_m K)
  have h1 : (1 : ℝ) ≤ (2 : ℝ) * (m K) := by nlinarith
  have h2 : 1 ≤ (2 : ℝ) * (m K) * (c₄ α' β' γ') := by
    simpa [mul_assoc] using one_le_mul_of_one_le_of_one_le h1 (one_le_c₄ α β σ α' β' γ' hirr htriv
        habc)
  have h3 : 1 ≤ (2 : ℝ) * (m K) * (c₄ α' β' γ') * (c₉ α β K) := by
    simpa [mul_assoc] using one_le_mul_of_one_le_of_one_le h2 (c9_gt_1 α β σ α' β' γ' hirr htriv
        habc)
  have h4 : 1 ≤ (c₉ α β K) ^ (2 * (m K) : ℝ) := by
    exact Real.one_le_rpow ((c9_gt_1 α β σ α' β' γ' hirr htriv habc)) (by positivity)
  simpa [mul_assoc] using one_le_mul_of_one_le_of_one_le h3 h4

include α β σ α' β' γ' hirr htriv habc in
@[nolint unusedArguments]
lemma abs_R : (q * q) * (((c₄ α' β' γ') ^ ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) * ((r
    α β σ α' β' γ' hirr htriv habc) q hq0 h2mq) ^
      ((((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ ) + 1) / 2)) * ((c₉ α β K)) ^ ((r α β σ
          α' β' γ' hirr htriv habc) q hq0 h2mq + q : ℝ)) ≤
      ((c₁₀ α β α' β' γ'))^ ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) * ((r α β σ α' β' γ'
          hirr htriv habc) q hq0 h2mq : ℝ) ^
      (1/2 * (((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq) + 3 : ℝ)) := by
    calc _ ≤ (2 * (m K) : ℝ )^((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) *((r α β σ α' β'
        γ' hirr htriv habc) q hq0 h2mq : ℝ)*
             (((c₄ α' β' γ') ^ ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) * ((r α β σ α' β'
                 γ' hirr htriv habc) q hq0 h2mq : ℝ) ^
             ((((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) + 1) / 2)) * ((c₉ α β K)) ^ ((r α
                 β σ α' β' γ' hirr htriv habc) q hq0 h2mq + q : ℝ)) := ?_
         _ ≤ ((c₁₀ α β α' β' γ') ^ ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ)) * ((r α β σ
             α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) ^
             (1/2 * ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq + 3) : ℝ) := ?_
    · apply mul_le_mul (eq6b.extracted_1_1 α β σ α' β' γ' hirr htriv habc q hq0 h2mq) le_rfl ?_ (by positivity)
      (apply mul_nonneg (mul_nonneg (Real.rpow_nonneg (le_trans zero_le_one (one_le_c₄ α β σ α' β'
          γ' hirr htriv habc)) _)
        (by positivity)) (Real.rpow_nonneg (c9_nonneg α β σ α' β' γ' hirr htriv habc) _))
    · unfold c₁₀
      nth_rw 2 [Real.mul_rpow _ (by apply Real.rpow_nonneg (c9_nonneg α β σ α' β' γ' hirr htriv habc) ((2 * ↑(m K) : ℝ)))]
      · nth_rw 2 [Real.mul_rpow _ (by grind [c9_nonneg α β σ α' β' γ' hirr htriv habc])]
        · nth_rw 2 [Real.mul_rpow (by positivity) (by apply le_trans zero_le_one ((one_le_c₄ α β σ α' β' γ' hirr htriv habc)))]
          · simp only [← mul_assoc, mul_assoc ((2*(m K) : ℝ) ^ ((r α β σ α' β' γ' hirr htriv habc) q
              hq0 h2mq : ℝ))
                ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) ((c₄ α' β' γ') ^ ((r α β σ α' β'
                    γ' hirr htriv habc) q hq0 h2mq : ℝ)),
                mul_comm ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) ((c₄ α' β' γ') ^ ((r α
                    β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ))]
            simp only [mul_assoc]; nth_rw 3 [← mul_assoc]
            apply mul_le_mul (by rfl) ?_ ?_ (by positivity)
            · apply mul_le_mul (by simp) ?_
                (mul_nonneg (by positivity) (Real.rpow_nonneg (c9_nonneg α β σ α' β' γ' hirr htriv habc) _))
                (Real.rpow_nonneg (le_trans zero_le_one ((one_le_c₄ α β σ α' β' γ' hirr htriv
                    habc))) _)
              · rw [Real.rpow_add (by grind [c9_pos α β σ α' β' γ' hirr htriv habc]), mul_comm, mul_assoc]
                · apply mul_le_mul (by rfl) ?_ ?_ (Real.rpow_nonneg (c9_nonneg α β σ α' β' γ' hirr htriv habc) _)
                  · apply mul_le_mul ?_ ?_ (by positivity)
                      (by apply Real.rpow_nonneg (Real.rpow_nonneg (c9_nonneg α β σ α' β' γ' hirr htriv habc) _) _)
                    · rw [← Real.rpow_mul (c9_nonneg α β σ α' β' γ' hirr htriv habc)]
                      · apply Real.rpow_le_rpow_of_exponent_le (c9_gt_1 α β σ α' β' γ' hirr htriv
                          habc)
                        · exact mod_cast le_trans (q_le_two_mn q h2mq)
                           (mul_le_mul (by rfl) (n_le_r α β σ α' β' γ' hirr htriv habc q hq0 h2mq) (by positivity)
                           (by positivity))
                    · nth_rw 1 [← Real.rpow_one (((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq))]
                      rw [← Real.rpow_add]
                      · exact Real.rpow_le_rpow_of_exponent_le
                          (by simp; grind [r_qt_0 α β σ α' β' γ' hirr htriv habc q hq0 h2mq]) (by ring_nf; simp)
                      · simp; grind [r_qt_0 α β σ α' β' γ' hirr htriv habc q hq0 h2mq]
                  · apply mul_nonneg (Real.rpow_nonneg (c9_nonneg α β σ α' β' γ' hirr htriv habc) _) (mul_nonneg (by simp)
                      (by apply Real.rpow_nonneg (by simp)))
            · apply mul_nonneg (Real.rpow_nonneg (le_trans zero_le_one ((one_le_c₄ α β σ α' β' γ'
                hirr htriv habc))) _)
               (mul_nonneg (by positivity) (Real.rpow_nonneg (c9_nonneg α β σ α' β' γ' hirr htriv habc) _))
        · apply mul_nonneg (by positivity) (le_trans zero_le_one ((one_le_c₄ α β σ α' β' γ' hirr htriv habc)))
      · apply mul_nonneg (mul_nonneg (by positivity) (le_trans zero_le_one ((one_le_c₄ α β σ α' β' γ' hirr htriv habc))))
          (c9_nonneg α β σ α' β' γ' hirr htriv habc)

include α β σ α' β' γ' hirr htriv habc in
@[nolint unusedArguments]
lemma norm_sub_l0_lower_bound_on_sphere
    (hz : z ∈ Metric.sphere 0 (((m K) : ℝ) * (1 + ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq :
        ℝ) / (q : ℝ)))) :
    ((m K) * ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ)) / (q : ℝ) ≤ ‖z - (((l₀' α β σ α'
        β' γ' hirr htriv habc) q hq0 h2mq : ℂ) + 1)‖ := by
  calc ((m K) * ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ)) / (q : ℝ)
    _ = ((m K) * (1 + ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) / (q : ℝ)) - (m K) :
        ℝ) := ?_
    _ ≤ ‖z‖ - ‖((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℂ) + 1‖ := ?_
    _ ≤ ‖z - (((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℂ) + 1)‖ := ?_
  · ring
  · simp only [mem_sphere_iff_norm, sub_zero] at hz
    rw [hz]
    simp only [tsub_le_iff_right]
    have : (m K) * (1 + ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) / (q : ℝ))
            - (((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) + 1) =
           (m K) * (1 + ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) / (q : ℝ))
            + (- (((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) + 1)) := rfl
    norm_cast
    simp only [Nat.cast_add, Nat.cast_one, ge_iff_le]
    rw [this, add_assoc]
    simp only [le_add_iff_nonneg_right, le_neg_add_iff_add_le, add_zero]
    exact_mod_cast Fin.isLt _
  · apply norm_sub_norm_le z

include hz in
include α β σ α' β' γ' hirr htriv habc in
@[nolint unusedArguments]
lemma norm_z_minus_km_lower_bound_on_sphere (km : Fin ((m K))) :
  (m K) * (r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq / q ≤ ‖z - ((km: ℂ) + 1)‖  := by
  have hz' : ‖z‖ = (m K) * (1 + ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) / (q : ℝ)) := by
    simpa [mem_sphere_iff_norm, sub_zero] using hz
  have hkm' : (km : ℝ) ≤ (m K) := le_of_lt (by simp [Nat.cast_lt])
  have hkm : ‖(km : ℂ)‖ ≤ ((m K) : ℝ) := by simp
  calc _ = ((m K) * (1 + ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) / (q : ℝ)) - (m K) : ℝ) := by ring
       _ = ‖z‖ - norm ((m K) : ℂ) := by simp [hz', sub_eq_add_neg]
       _ ≤ ‖z‖ - ‖(km : ℂ) + 1‖ := ?_
       _ ≤ ‖z - ((km : ℂ) + 1)‖ := by simp [norm_sub_norm_le z ((km : ℂ) + 1)]
  · simp only [tsub_le_iff_right]
    · rw [sub_eq_add_neg, ← tsub_le_iff_left, sub_eq_add_neg]
      simp only [neg_add_rev, neg_neg, add_neg_cancel_comm_assoc, RCLike.norm_natCast]
      exact_mod_cast Fin.isLt _

lemma prod_bound {ι} (f : ι → ℝ) (s : Finset ι) (C : ℝ) (hC : ∀ x ∈ s, 0 ≤ f x)
   (h : ∀ x ∈ s, f x ≤ C) :  ∏ x ∈ s, f x ≤ C ^ s.card := by
  rw [← Finset.prod_const]
  exact Finset.prod_le_prod hC h

include hz h2mq in
include α β σ α' β' γ' hirr htriv habc in
@[nolint unusedArguments]
lemma abs_denom : norm (((z - ((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq + 1 : ℂ)) ^ (-((r α β
    σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℤ))) *
  ∏ km ∈ (Finset.range ((m K)) \ {((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℕ)}),
    ((((((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℂ) + 1 - ((km + 1 : ℂ))) / ((z - ((km + 1
        : ℂ))))) ^
      ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq))))
    ≤ ((c₁₁ K)) ^ ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) *
      (q / ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq)) ^ ((m K) * (r α β σ α' β' γ' hirr htriv
          habc) q hq0 h2mq : ℝ) := by
  let C : ℝ := ((m K) * (↑q / (↑(m K) * ↑((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq)))) ^ (r α β
      σ α' β' γ' hirr htriv habc) q hq0 h2mq
  calc
    _ ≤ norm (z - ((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq + 1 : ℂ)) ^ (-((r α β σ α' β' γ'
        hirr htriv habc) q hq0 h2mq : ℤ)) *
        norm (∏ km ∈ Finset.range ((m K)) \ {((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℕ)},
          ((((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℕ) + 1 - ((km : ℕ) + 1)) / (z - ((km
              : ℕ) + 1))) ^
            ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq)) := by
          simp only [zpow_neg, zpow_natCast, Complex.norm_mul, norm_inv, norm_pow, norm_prod,
            Complex.norm_div, add_sub_add_right_eq_sub, le_refl]
    _ ≤ ((m K) * ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) / (q : ℝ)) ^ (-((r α β σ α' β'
        γ' hirr htriv habc) q hq0 h2mq : ℤ)) *
        norm (∏ km ∈ Finset.range ((m K)) \ {((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℕ)},
          ((((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℕ) + 1 - ((km : ℕ) + 1)) / (z - ((km
              : ℕ) + 1))) ^
            ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq)) := by
          apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
          · simp only [zpow_neg, zpow_natCast]
            refine inv_anti₀ ?_ ?_
            · refine pow_pos ?_ ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq)
              refine Real.sqrt_ne_zero'.mp ?_
              refine (Real.sqrt_ne_zero (by positivity)).mpr ?_
              refine div_ne_zero ?_ ?_
              · simp only [ne_eq, mul_eq_zero, Nat.cast_eq_zero, not_or]
                refine ⟨?_, ?_⟩
                · rw [← ne_eq]
                  exact Ne.symm (Nat.zero_ne_add_one (2 * (h K) + 1))
                · simp_rw [(r_ne_zero α β σ α' β' γ' hirr htriv habc)]
                  aesop
              · have : 0 < (q : ℝ) := by exact_mod_cast hq0
                exact Ne.symm (ne_of_lt this)
            · refine (pow_le_pow_iff_left₀ (by positivity) (by positivity)
                (r_ne_zero α β σ α' β' γ' hirr htriv habc q hq0 h2mq)).mpr ?_
              · grind [(norm_z_minus_km_lower_bound_on_sphere α β σ α' β' γ' hirr htriv habc) q hq0
                  h2mq hz]
          · rw [norm_prod]
    _ ≤ (((m K) * ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) / (q : ℝ))⁻¹) ^ (((r α β σ α'
        β' γ' hirr htriv habc) q hq0 h2mq : ℤ)) *
         ∏ x ∈ Finset.range (m K) \ {↑((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq)},
      (‖((((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℕ) + 1 - ((x : ℕ) + 1)) : ℂ)‖ *
       (↑q / (↑(m K) * ↑((r α β σ α' β' γ' hirr htriv habc) q hq0
           h2mq)))) ^ (r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq := by
          apply mul_le_mul
          · simp only [zpow_neg, zpow_natCast]
            rw [le_iff_eq_or_lt]
            left
            ring
          · rw [norm_prod]
            apply Finset.prod_le_prod
            · intro x hx
              rw [norm_pow, ← norm_pow]
              positivity
            · intro x hx
              simp only [norm_pow]
              rw [div_eq_mul_inv]
              refine (pow_le_pow_iff_left₀ ?_ ?_ (r_ne_zero α β σ α' β' γ' hirr htriv habc q hq0
                  h2mq)).mpr ?_
              · positivity
              · positivity
              · simp only [Complex.norm_mul]
                apply mul_le_mul
                · simp
                · simp only [norm_inv]
                  simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton] at hx
                  let x' : Fin (m K) := ⟨x, hx.1⟩
                  have hxnorm := norm_z_minus_km_lower_bound_on_sphere α β σ α' β' γ' hirr htriv
                      habc q hq0 h2mq hz x'
                  unfold x' at hxnorm
                  simp only at hxnorm
                  rw [← one_div_le_one_div]
                  · simp only [one_div, inv_div, div_inv_eq_mul, one_mul]
                    exact hxnorm
                  · refine div_pos ?_ ?_
                    · norm_cast
                    · apply mul_pos
                      · unfold m
                        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
                        apply add_pos
                        · simp only [Nat.ofNat_pos, mul_pos_iff_of_pos_left, Nat.cast_pos]
                          unfold h
                          exact Module.finrank_pos
                        · simp only [Nat.ofNat_pos]
                      · simp only [Nat.cast_pos]
                        exact r_qt_0 α β σ α' β' γ' hirr htriv habc q hq0 h2mq
                  · simp only [mem_sphere_iff_norm, sub_zero] at hz
                    simp only [inv_pos]
                    calc
                      _ < ↑(m K) * ↑((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq) / ↑q := by
                            apply mul_pos
                            · apply mul_pos
                              · unfold m
                                simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
                                apply add_pos
                                · simp only [Nat.ofNat_pos, mul_pos_iff_of_pos_left, Nat.cast_pos]
                                  unfold h
                                  exact Module.finrank_pos
                                · simp only [Nat.ofNat_pos]
                              · simp only [Nat.cast_pos]
                                exact r_qt_0 α β σ α' β' γ' hirr htriv habc q hq0 h2mq
                            · simp only [inv_pos, Nat.cast_pos]
                              exact hq0
                      _ ≤ ‖z - (↑x + 1)‖ := hxnorm
                · positivity
                · positivity
          · apply norm_nonneg
          · simp only [zpow_natCast]
            apply pow_nonneg
            simp only [inv_div]
            positivity
    _ ≤ (((m K) * ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) / (q : ℝ))⁻¹) ^ (((r α β σ α'
        β' γ' hirr htriv habc) q hq0 h2mq : ℝ)) *
        C ^ Finset.card (Finset.range (m K) \ {↑((l₀' α β σ α' β' γ' hirr htriv habc) q hq0
            h2mq)}) := by
          simp only [zpow_natCast, inv_div]
          apply mul_le_mul (by simp only [Real.rpow_natCast, le_refl]) ?_ (by positivity) (by positivity)
          apply prod_bound
          · intro x hx
            positivity
          · intro x hx
            unfold C
            refine (pow_le_pow_iff_left₀ (by positivity) (by positivity)
              (r_ne_zero α β σ α' β' γ' hirr htriv habc q hq0 h2mq)).mpr ?_
            simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton] at hx
            have : ‖((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℂ) + 1 - (↑x + 1)‖ ≤ ((m K) :
                ℝ) := by
              simp only [add_sub_add_right_eq_sub]
              rw [← Complex.norm_natCast]
              obtain ⟨y, hy⟩ := ((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq)
              obtain ⟨hx1, hx2⟩ := hx
              simp only [RCLike.norm_natCast]
              by_cases H : x ≤ y
              · have : ‖(y : ℂ) - (x : ℂ)‖ = ((y - x) : ℕ) := by
                  rw [← Complex.norm_natCast]
                  norm_cast
                rw [this]
                simp only [Nat.cast_le, tsub_le_iff_right, ge_iff_le]
                linarith
              · have : ‖(y : ℂ) - (x : ℂ)‖ = ((x - y) : ℕ) := by
                  calc
                    _ = ‖(x : ℂ) - (y : ℂ)‖ := by rw [← norm_neg]; simp only [neg_sub]
                    _ = ((x - y) : ℕ) := by
                          rw [← Complex.norm_natCast]
                          norm_cast
                          grind
                rw [this]
                simp only [Nat.cast_le, tsub_le_iff_right, ge_iff_le]
                linarith
            exact mul_le_mul this (le_refl _) (by positivity) (by positivity)
    _ ≤ ((c₁₁ K)) ^ ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) *
        (q / ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq)) ^ ((m K) * (r α β σ α' β' γ' hirr
            htriv habc) q hq0 h2mq : ℝ) := by
          simp only [inv_div, Real.rpow_natCast]
          have : #(Finset.range (m K) \ {↑((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq)}) = ((m K) - 1) := by grind
          rw [this]
          unfold C
          rw [← pow_mul]
          nth_rw 5 [mul_comm]
          rw [mul_pow, pow_mul]
          simp only [← mul_assoc]
          nth_rw 2 [mul_comm]
          simp only [mul_assoc]
          rw [← pow_add]
          unfold c₁₁
          have H1 : ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq + ((((m K) : ℝ) - 1) : ℝ) * (r α
              β σ α' β' γ' hirr htriv habc) q hq0 h2mq) =
              ((m K) * (r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) := by ring_nf
          apply mul_le_mul (le_refl _) ?_ (by positivity) (by positivity)
          simp only [← Real.rpow_natCast]
          have : ↑((m K) - 1) = ((((m K) : ℝ) - 1) : ℝ) := Nat.cast_pred (by grind)
          simp only [Nat.cast_add, Nat.cast_mul]
          rw [this, H1]
          apply Real.rpow_le_rpow (by positivity) ?_ (by positivity)
          refine (div_le_div_iff_of_pos_left (by simp only [Nat.cast_pos]; exact hq0)
            (mul_pos (by simp only [Nat.cast_pos]; exact Nat.zero_lt_succ (2 * (h K) + 1))
              (by simp only [Nat.cast_pos]; exact r_qt_0 α β σ α' β' γ' hirr htriv habc q hq0 h2mq))
            (by simp only [Nat.cast_pos]; exact r_qt_0 α β σ α' β' γ' hirr htriv habc q hq0 h2mq)).mpr ?_
          norm_cast
          nth_rw 1 [← one_mul (a := (r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq)]
          exact mul_le_mul (one_le_m K) (le_refl _) (Nat.zero_le _) (Nat.zero_le _)









/-- A constant bounding the sup-norm of `S` on the circle of integration. -/
def c₁₂ : ℝ := (2*(m K) : ℝ)^((m K)/2 : ℝ) * (c₁₀ α β α' β' γ') * (c₁₁ K)

include α β σ α' β' γ' hirr htriv habc in
@[nolint unusedArguments]
lemma one_le_c12 : 1 ≤ (c₁₂ α β α' β' γ') := by
  unfold c₁₂
  refine one_le_mul_of_one_le_of_one_le ?_ ((one_le_c11 α β σ α' β' γ' hirr htriv habc))
  apply one_le_mul_of_one_le_of_one_le ?_ ((one_le_c10 α β σ α' β' γ' hirr htriv habc))
  · refine Real.one_le_rpow ?_ (by positivity)
    · apply one_le_mul_of_one_le_of_one_le (by aesop) ?_
      · simp only [Nat.one_le_cast]; exact (one_le_m K)

include α β σ α' β' γ' hirr htriv habc in
@[nolint unusedArguments]
lemma c12_nonneg : 0 ≤ (c₁₂ α β α' β' γ') := by
  simpa [c₁₂] using
    mul_nonneg (mul_nonneg (by positivity) (c10_nonneg α β σ α' β' γ' hirr htriv habc)) (c11_nonneg α β σ α' β' γ' hirr htriv habc)




include α β σ α' β' γ' hirr htriv habc in
@[nolint unusedArguments]
lemma S_norm_bound : ∀ (hz : z ∈ Metric.sphere 0 ((m K) * (1 + ((r α β σ α' β' γ' hirr htriv habc) q
    hq0 h2mq : ℝ) / (q : ℝ)))),
  norm ((S α β σ α' β' γ' hirr htriv habc) q hq0 h2mq z) ≤ ((c₁₂ α β α' β' γ'))^((r α β σ α' β' γ'
      hirr htriv habc) q hq0 h2mq : ℝ)*
    ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) ^
              (((((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ)* ( ( (3 : ℝ) - ((m K): ℝ))/2 :
                  ℝ)) + (3 / 2 : ℝ))) := by
  intros hz
  calc
    _ = norm (((R α β σ α' β' γ' hirr htriv habc) q hq0 h2mq z) * (((r α β σ α' β' γ' hirr htriv
        habc) q hq0 h2mq).factorial) *
        (((z - ((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq + 1 : ℂ)) ^ (-((r α β σ α' β' γ'
            hirr htriv habc) q hq0 h2mq) : ℤ)) *
        ∏ k' ∈ Finset.range ((m K)) \ {↑((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq)},
         ((((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq + 1) - (k' + 1)) / (z - (k' + 1 :
             ℂ))) ^ ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq)) : ℂ) := ?_

    _ = ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq).factorial *
        (norm (((R α β σ α' β' γ' hirr htriv habc) q hq0 h2mq) z) *
        norm ( (1/(z - ((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq + 1 : ℂ)) ^ ((r α β σ α' β'
            γ' hirr htriv habc) q hq0 h2mq))) *
        norm ( (∏ k' ∈ Finset.range ((m K)) \ {↑((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq)},
         ((((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq + 1)- (k' + 1)) / (z - (k' + 1 :
             ℂ))) ^ ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq)) : ℂ)) := ?_

    _ ≤ ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq).factorial *
        (((c₁₀ α β α' β' γ'))^((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) *
        ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ)^(1/2*((r α β σ α' β' γ' hirr htriv habc)
            q hq0 h2mq + 3 : ℝ)) *
        ((c₁₁ K))^((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) *
        (q / (r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ)^((m K) * (r α β σ α' β' γ' hirr
            htriv habc) q hq0 h2mq : ℝ)) := ?_

    _ ≤ ((c₁₂ α β α' β' γ'))^((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ)*((r α β σ α' β' γ'
        hirr htriv habc) q hq0 h2mq : ℝ) ^
        (((((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ)* ( ( (3 : ℝ) - ((m K): ℝ))/2 : ℝ)) +
            (3 / 2 : ℝ))) := ?_

  · rw [(S_eq_SR_on_circle α β σ α' β' γ' hirr htriv habc) q hq0 h2mq z hz]
    unfold SR
    simp only [mul_assoc]
  · nth_rewrite 2 [mul_assoc]
    nth_rewrite 2 [← mul_assoc]
    rw [mul_comm  ↑((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq).factorial  ‖(R α β σ α' β' γ'
        hirr htriv habc) q hq0 h2mq z‖]
    simp only [mul_assoc, zpow_neg, zpow_natCast,
    Complex.norm_mul, norm_natCast, norm_inv, norm_pow,
      norm_prod, Complex.norm_div, one_div]
  · apply mul_le_mul (le_refl _) ?_ (by positivity) (by positivity)
    · rw [mul_assoc, mul_assoc]
      · apply mul_le_mul (le_trans ((abs_Rb α β σ α' β' γ' hirr htriv habc) q hq0 h2mq hz) (abs_R α
          β σ α' β' γ' hirr htriv habc q hq0 h2mq)) ?_
            (by positivity) ?_
        · simp only [one_div, norm_inv, norm_pow, norm_prod, Complex.norm_div]
          have := abs_denom α β σ α' β' γ' hirr htriv habc q hq0 h2mq hz
          simp only [zpow_neg, zpow_natCast, Complex.norm_mul, norm_inv, norm_pow, norm_prod,
            Complex.norm_div, Real.rpow_natCast] at this
          simp only [Real.rpow_natCast, ge_iff_le]
          exact this
        · apply mul_nonneg (Real.rpow_nonneg (c10_nonneg α β σ α' β' γ' hirr htriv habc) _) (by positivity)
  · simp only [← mul_assoc]
    rw [mul_comm]
    unfold c₁₂
    rw [Real.mul_rpow]
    rw [Real.mul_rpow]
    nth_rw 7 [mul_comm]
    simp only [← mul_assoc]
    rw [mul_comm]
    nth_rw 3 [mul_comm]
    ring_nf
    simp only [mul_assoc]
    apply mul_le_mul
    · simp only [Real.rpow_natCast, le_refl]

    · apply mul_le_mul
      · simp only [Real.rpow_natCast, le_refl]
      · calc _ ≤ (Real.sqrt (2*(m K) * (r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ))^((r α β σ
          α' β' γ' hirr htriv habc) q hq0 h2mq * (m K) : ℝ) *
                 ((↑((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ))⁻¹ ^ ((m K) * (r α β σ α' β'
                     γ' hirr htriv habc) q hq0 h2mq : ℝ) *
                ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq).factorial *
                ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ)^((1/2 : ℝ)*((r α β σ α' β' γ'
                    hirr htriv habc) q hq0 h2mq + 3 : ℝ))) := ?_

             _≤ (Real.sqrt (2*(m K) : ℝ)^(((m K) * (r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq :
                 ℝ)) *
                (((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ)^(1/2 : ℝ))^(((m K) * (r α β σ
                    α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ)))*
                (((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ)^((r α β σ α' β' γ' hirr htriv
                    habc) q hq0 h2mq : ℝ) *
                (↑((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ))⁻¹ ^ ((m K) * (r α β σ α' β'
                    γ' hirr htriv habc) q hq0 h2mq : ℝ) *
                ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ)^((1/2 : ℝ)*((r α β σ α' β' γ'
                    hirr htriv habc) q hq0 h2mq + 3 : ℝ))) :=?_

             _= ((↑(m K) * 2 : ℝ) ^ (((m K) : ℝ) * (1 / 2: ℝ))) ^ ((r α β σ α' β' γ' hirr htriv
                 habc) q hq0 h2mq : ℝ)*

              ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) ^
              (((((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ)* ( ( (3 : ℝ) - ((m K): ℝ))/2 :
                  ℝ)) + (3 / 2 : ℝ))) := ?_

        · rw [Real.mul_rpow]
          simp only [mul_assoc]
          apply mul_le_mul
          have := (sqt_etc α β σ α' β' γ' hirr htriv habc) q hq0 h2mq
          have := (q_le_2sqrtmr α β σ α' β' γ' hirr htriv habc) q hq0 h2mq
          apply Real.rpow_le_rpow
          · simp only [Nat.cast_nonneg]
          · rw [(q_eq_sqrtmn α β σ α' β' γ' hirr htriv habc) q h2mq]
            simp only [Nat.ofNat_pos, mul_nonneg_iff_of_pos_left, Nat.cast_nonneg,
              Real.sqrt_mul, Nat.ofNat_nonneg]
            simp only [mul_assoc]
            apply mul_le_mul
            · simp only [le_refl]
            · apply mul_le_mul
              · simp only [le_refl]
              · simp only [Nat.cast_nonneg, Real.sqrt_le_sqrt_iff, Nat.cast_le]
                exact n_le_r α β σ α' β' γ' hirr htriv habc q hq0 h2mq
              · positivity
              · positivity
            · positivity
            · positivity
          · positivity
          · ring_nf
            simp only [one_div, le_refl]
          · positivity
          · positivity
          · positivity
          · positivity
        · rw [(sqt_etc α β σ α' β' γ' hirr htriv habc) q hq0 h2mq]
          rw [Real.mul_rpow]
          apply mul_le_mul
          · rw [mul_comm ((m K) : ℝ) ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ)]
          · rw [mul_comm]
            nth_rw 5 [mul_comm]
            apply mul_le_mul
            · simp only [le_refl]
            · rw [mul_comm]
              apply mul_le_mul
              · norm_cast
                exact Nat.factorial_le_pow ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq)
              · simp only [le_refl]
              · positivity
              · positivity
            · positivity
            · positivity
          · positivity
          · positivity
          · positivity
          · positivity
        · rw [← Real.rpow_mul]
          rw [← Real.rpow_mul]
          rw [Real.sqrt_eq_rpow]
          rw [← Real.rpow_mul]
          rw [mul_comm ((m K) : ℝ) (1/2)]
          rw [mul_comm ((m K) : ℝ) 2]
          simp only [mul_assoc]
          congr
          rw [Real.inv_rpow]
          rw [← mul_assoc]
          rw [← Real.rpow_add]
          rw [← Real.rpow_neg]
          rw [← Real.rpow_add]
          rw [← Real.rpow_add]
          · ring_nf
          · simp only [Nat.cast_pos]; exact r_qt_0 α β σ α' β' γ' hirr htriv habc q hq0 h2mq
          · simp only [Nat.cast_pos]; exact r_qt_0 α β σ α' β' γ' hirr htriv habc q hq0 h2mq
          · simp only [Nat.cast_nonneg]
          · simp only [Nat.cast_pos]; exact r_qt_0 α β σ α' β' γ' hirr htriv habc q hq0 h2mq
          · simp only [Nat.cast_nonneg]
          · simp only [Nat.ofNat_pos, mul_nonneg_iff_of_pos_left, Nat.cast_nonneg]
          · positivity
          · simp only [Nat.cast_nonneg]
        · ring_nf
          simp only [one_div, Real.rpow_natCast, le_refl]
      · positivity
      · apply Real.rpow_nonneg
        apply (c10_nonneg α β σ α' β' γ' hirr htriv habc)
    · apply mul_nonneg
      · apply Real.rpow_nonneg
        exact c10_nonneg α β σ α' β' γ' hirr htriv habc
      · positivity
    · apply Real.rpow_nonneg
      exact (c11_nonneg α β σ α' β' γ' hirr htriv habc)
    · positivity
    · exact c10_nonneg α β σ α' β' γ' hirr htriv habc
    · apply mul_nonneg
      · positivity
      · exact c10_nonneg α β σ α' β' γ' hirr htriv habc
    · exact c11_nonneg α β σ α' β' γ' hirr htriv habc

/-- `ρᵣ` as the `η`-weighted sum of the system coefficients. -/
@[nolint unusedArguments]
theorem systemCoeffsff_foo_S : ρᵣ α β σ α' β' γ' hirr htriv habc q hq0 h2mq =
  Complex.log (α) ^ (-((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℤ)) *
   ((S α β σ α' β' γ' hirr htriv habc) q hq0 h2mq) (↑↑((l₀' α β σ α' β' γ' hirr htriv habc) q hq0
       h2mq) + 1) := by
  dsimp [ρᵣ]
  congr
  have HAE : ∀ (z : ℂ), AnalyticAt ℂ ((R α β σ α' β' γ' hirr htriv habc) q hq0 h2mq) z := by
    intros z
    fun_prop
  let R₁ : ℂ → ℂ := R' α β σ α' β' γ' hirr htriv habc q hq0 h2mq (((l₀' α β σ α' β' γ' hirr htriv
      habc) q hq0 h2mq))
  have HR1 : ∀ (z : ℂ), AnalyticAt ℂ R₁ z := by
    unfold R₁
    intros z
    apply R'_analyticAt α β σ α' β' γ' hirr htriv habc q hq0 h2mq ((l₀' α β σ α' β' γ' hirr htriv
        habc) q hq0 h2mq) z
  have hR₁ : ∀ (z : ℂ), ((R α β σ α' β' γ' hirr htriv habc) q hq0 h2mq) z =
    ((z - ((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq + 1)) ^ ((r α β σ α' β' γ' hirr htriv
        habc) q hq0 h2mq)) * (R₁ z) := by
    intros z
    rw [(R_eq_pow_mul_R' α β σ α' β' γ' hirr htriv habc)]
  have hr : (r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq ≤ (r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq := by rfl
  have :
   ∃ R₂ : ℂ → ℂ, (∀ z : ℂ, AnalyticAt ℂ R₂ z) ∧
    (∀ z, deriv^[((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq)] (R α β σ α' β' γ' hirr htriv habc
        q hq0 h2mq) z =
   (z - ( l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq + 1))^(((r α β σ α' β' γ' hirr htriv habc) q
       hq0 h2mq)-((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq)) *
    (((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq).factorial/(((r α β σ α' β' γ' hirr htriv habc)
        q hq0 h2mq)-((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq)).factorial * R₁ z +
       (z - ( l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq + 1))* R₂ z)) := by
    simp only [← iteratedDeriv_eq_iterate, tsub_self]
    apply iteratedDeriv_mul_pow_sub_of_analytic (z₀ := ((l₀' α β σ α' β' γ' hirr htriv habc q hq0
        h2mq : ℂ) + 1))
        --HAE
        HR1 hR₁ (t := 0) (k := r α β σ α' β' γ' hirr htriv habc q hq0 h2mq)
  simp only [tsub_self, pow_zero, Nat.factorial_zero,
  Nat.cast_one, div_one, one_mul] at this
  have := this
  obtain ⟨R2,hR⟩ := this
  clear this
  obtain ⟨hR1, hR2⟩ := hR
  rw [hR2]
  unfold R₁
  symm
  dsimp [S]
  simp only [add_left_inj, Nat.cast_inj, exists_apply_eq_apply', ↓reduceDIte]
  dsimp
  · unfold SRl0
    simp only [add_sub_add_right_eq_sub]
    rw [mul_comm   ↑((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq).factorial
      ((R' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq ((l₀' α β σ α' β' γ' hirr htriv habc) q hq0
          h2mq) (↑↑((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq) + 1))]
    nth_rw 2 [← mul_one
      (a := ((R' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq ((l₀' α β σ α' β' γ' hirr htriv habc) q
          hq0 h2mq) (↑↑((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq) + 1)) *
      ↑((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq).factorial) ]
    congr
    simp only [mul_one, sub_self, zero_mul, add_zero]
    nth_rw 2 [← mul_one (a:= (R' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq ((l₀' α β σ α' β' γ'
        hirr htriv habc) q hq0 h2mq)
      (((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℂ) + 1) * ↑((r α β σ α' β' γ' hirr htriv
          habc) q hq0 h2mq).factorial)]
    congr
    have H1 :  ∏ x ∈ Finset.range (m K) \ {↑((l₀' α β σ α' β' γ' hirr htriv habc) q hq0
        h2mq)}, 1 = (1 : ℂ) := by
      simp only [prod_const_one]
    congr
    rw [← H1]
    apply Finset.prod_congr
    rfl
    intros x hx
    rw [div_self]
    simp only [one_pow]
    have : ∀ x ∈ Finset.range (m K) \ {↑((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq)},
      ↑↑((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq) ≠ x := by
        intros x hx
        grind only [= Finset.mem_sdiff, = Finset.mem_singleton]
    have := this x hx
    intros HC
    rw [sub_eq_zero] at HC
    norm_cast at HC

include α β σ α' β' γ' hirr htriv habc in
@[nolint unusedArguments]
lemma eq7 (l' : Fin ((m K))) :
    ρᵣ α β σ α' β' γ' hirr htriv habc q hq0 h2mq = Complex.log (α) ^ (-((r α β σ α' β' γ' hirr htriv
        habc) q hq0 h2mq) : ℤ) * ((2 * ↑Real.pi * I)⁻¹ *
    (∮ z in C(0, (m K) * (1 + ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq / q))), (z - ((l₀' α β
        σ α' β' γ' hirr htriv habc) q hq0 h2mq + 1))⁻¹ *
    ((S α β σ α' β' γ' hirr htriv habc) q hq0 h2mq) z)) :=
  (hcauchy α β σ α' β' γ' hirr htriv
      habc) q hq0 h2mq ▸ systemCoeffsff_foo_S α β σ α' β' γ' hirr htriv habc q hq0 h2mq

/-- A constant bounding `‖ρ‖` via Cauchy's estimate. -/
def c₁₃ : ℝ :=((‖Complex.log α‖⁻¹ + 1)*(m K)*(2 + 1/(m K))*(c₁₂ α β α' β' γ'))

include α β σ α' β' γ' hirr htriv habc in
@[nolint unusedArguments]
lemma c13_nonneg : 0 ≤ (c₁₃ α β α' β' γ') := by
  unfold c₁₃
  apply mul_nonneg (by positivity) ((c12_nonneg α β σ α' β' γ' hirr htriv habc))

include α β σ α' β' γ' hirr htriv habc in
@[nolint unusedArguments]
lemma one_le_c13 : 1 ≤ (c₁₃ α β α' β' γ') := by
  unfold c₁₃
  refine one_le_mul_of_one_le_of_one_le ?_ ((one_le_c12 α β σ α' β' γ' hirr htriv habc))
  apply one_le_mul_of_one_le_of_one_le
  · apply one_le_mul_of_one_le_of_one_le
    · rw [add_comm]
      refine le_add_of_le_of_nonneg (le_refl _) (by positivity)
    · simp only [Nat.one_le_cast]; exact Nat.le_of_ble_eq_true rfl
  · simp only [one_div]
    refine le_add_of_le_of_nonneg (by aesop) (by positivity)

/-- The numerator appearing in the Cauchy estimate for `S`. -/
def Cnum : ℝ := (((m K) * ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ)) / (q : ℝ))⁻¹ * ((c₁₂
    α β α' β' γ') ^ ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ)*
  ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) ^ (((((r α β σ α' β' γ' hirr htriv habc) q hq0
      h2mq : ℝ)* (((3 : ℝ) - (m K)) / 2 : ℝ)) + (3 / 2 : ℝ))))

include α β σ α' β' γ' hirr htriv habc in
@[nolint unusedArguments]
lemma hf : ∀ z ∈ Metric.sphere 0 ((m K) * (1 + ↑((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ)
    / ↑q)),
    ‖(z - ((↑((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq) : ℂ) + 1))⁻¹ * ((S α β σ α' β' γ'
        hirr htriv habc) q hq0 h2mq z)‖ ≤ (Cnum α β σ α' β' γ' hirr htriv habc) q hq0 h2mq := by
  intros z hz
  simp only [Complex.norm_mul, norm_inv, Cnum]
  apply mul_le_mul ?_ (S_norm_bound α β σ α' β' γ' hirr htriv habc q hq0 h2mq hz) (by positivity) (by positivity)
  · apply inv_anti₀ ?_ ((norm_sub_l0_lower_bound_on_sphere α β σ α' β' γ' hirr htriv habc) q hq0
      h2mq hz)
    · refine Real.sqrt_ne_zero'.mp ?_
      · refine (Real.sqrt_ne_zero (by positivity)).mpr ?_
        refine div_ne_zero ?_ (Ne.symm (ne_of_lt (mod_cast hq0)))
        · simp only [ne_eq, mul_eq_zero, Nat.cast_eq_zero, not_or]
          refine ⟨by simp [m], by simp_rw [(r_ne_zero α β σ α' β' γ' hirr htriv habc)]; simp only [not_false_eq_true]⟩

include α β σ α' β' γ' hirr htriv habc in
@[nolint unusedArguments]
lemma eq8 :
    norm (ρᵣ α β σ α' β' γ' hirr htriv habc q hq0 h2mq) ≤ ((c₁₃ α β α' β' γ')) ^ ((r α β σ α' β' γ'
        hirr htriv habc) q hq0 h2mq : ℝ) *
    (((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) ^ (((r α β σ α' β' γ' hirr htriv habc) q
        hq0 h2mq : ℝ) * ((3 - ((m K) : ℝ))) / 2 + 3 / 2)) := by

  have hR : 0 ≤ ((m K) * (1 + ↑((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq) / ↑q) : ℝ) := by
    apply mul_nonneg (Nat.cast_nonneg _)
    apply add_nonneg zero_le_one
    apply div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

  have H := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hR
    ((hf α β σ α' β' γ' hirr htriv habc) q hq0 h2mq)

  calc _ = norm (Complex.log α ^ (-((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℤ)) * ((2 *
      Real.pi) * I)⁻¹ * ∮ (z : ℂ) in
           C(0, (m K) * (1 + ↑((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq) / ↑q)), (z - ↑(((l₀' α
               β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℂ) + 1))⁻¹ *
           ((S α β σ α' β' γ' hirr htriv habc) q hq0 h2mq z)) := ?_

       _ = norm (Complex.log (α) ^ (-((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℤ))) *
           norm ((2 * Real.pi * I)⁻¹) * norm (∮ (z : ℂ) in
           C(0, (m K) * (1 + ↑((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq) / ↑q)),
           (z - ↑(((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℂ) + 1))⁻¹ * ((S α β σ α' β' γ'
               hirr htriv habc) q hq0 h2mq z)) := ?_

       _ ≤ ((norm ((Complex.log α))^ (-((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℤ)))) * ((m
           K) : ℝ) *
           (1 + ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) / (q : ℝ)) * ((c₁₂ α β α' β'
               γ')) ^ ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) *
           (((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) ^ (((r α β σ α' β' γ' hirr htriv
               habc) q hq0 h2mq : ℝ) * (3 - (m K) : ℝ) / 2 + 3 / 2) *
           ((q : ℝ) / ((((m K) : ℝ) * ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ))))) := ?_

       _ ≤ ((c₁₃ α β α' β' γ')) ^ ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) * (((r α β σ
           α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) ^ (((r α β σ α' β' γ' hirr htriv
               habc) q hq0 h2mq : ℝ) *
           ((3 - ((m K) : ℝ))) / 2 + 3 / 2)) := ?_

  · rw [(eq7 α β σ α' β' γ' hirr htriv habc) q hq0 h2mq]
    · simp only [mul_assoc]
    exact ((l₀' α β σ α' β' γ' hirr htriv habc) q hq0 h2mq)
  · simp only [zpow_neg, zpow_natCast, _root_.mul_inv_rev,
    norm_inv, norm_pow, norm_real, Real.norm_eq_abs, norm_ofNat, norm_mul]
  · simp only [mul_assoc]
    simp only [zpow_neg, zpow_natCast, norm_inv, norm_pow, _root_.mul_inv_rev, inv_I, neg_mul,
      norm_neg, Complex.norm_mul, norm_I, norm_real, Real.norm_eq_abs, one_mul, norm_ofNat]
    · apply mul_le_mul
      · simp only [le_refl]
      · simp only [_root_.mul_inv_rev, inv_I, neg_mul, smul_eq_mul, norm_neg, Complex.norm_mul,
          norm_I, norm_inv, norm_real, Real.norm_eq_abs, norm_ofNat, one_mul] at H
        simp only [mul_assoc] at *
        trans
        · apply H
        simp only [Real.rpow_natCast]
        apply mul_le_mul
        · simp only [le_refl]
        · unfold Cnum
          --simp only [← mul_assoc]
          nth_rw 2 [mul_comm]
          simp only [mul_assoc]
          simp only [Real.rpow_natCast, inv_div]
          ring_nf;
          simp only [le_refl]
        · unfold Cnum
          apply mul_nonneg
          · positivity
          · apply mul_nonneg
            · positivity
            · apply mul_nonneg
              · apply Real.rpow_nonneg
                · exact c12_nonneg α β σ α' β' γ' hirr htriv habc
              · positivity
        · simp only [Nat.cast_nonneg]
      · positivity
      · simp only [inv_nonneg, norm_nonneg, pow_nonneg]
  · simp only [zpow_neg, zpow_natCast, mul_assoc]
    nth_rw 5 [← mul_comm]
    unfold c₁₃
    rw [Real.mul_rpow, Real.mul_rpow, Real.mul_rpow]
    simp only [mul_assoc]
    apply mul_le_mul
    · rw [← norm_inv, ← inv_pow, ← norm_inv]
      simp only [Real.rpow_natCast]
      apply pow_le_pow_left₀
      simp only [norm_inv, inv_nonneg, norm_nonneg]
      simp only [norm_inv, le_add_iff_nonneg_right, zero_le_one]
    · apply mul_le_mul
      · nth_rw 1 [← Real.rpow_one (x:= (m K))]
        apply Real.rpow_le_rpow_of_exponent_le
        · unfold m; simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
          rw [le_iff_lt_or_eq]
          left
          trans
          apply one_lt_two
          simp only [lt_add_iff_pos_left, Nat.ofNat_pos, mul_pos_iff_of_pos_left, Nat.cast_pos]
          unfold h; exact Module.finrank_pos
        · simp only [Nat.one_le_cast]
          exact one_le_r α β σ α' β' γ' hirr htriv habc q hq0 h2mq
      · simp only [← mul_assoc]
        nth_rw 1 [mul_comm]
        nth_rw 6 [mul_comm]
        apply mul_le_mul
        · simp only [le_refl]
        · simp only [mul_assoc]
          rw [mul_comm]
          nth_rw 4 [mul_comm]
          simp only [mul_assoc]
          apply mul_le_mul ?_ ?_ (by positivity) (Real.rpow_nonneg (c12_nonneg α β σ α' β' γ' hirr htriv habc) _)
          · simp only [Real.rpow_natCast, le_refl]
          · ring_nf
            rw [mul_rotate]
            simp only [mul_assoc]
            nth_rw 2 [← mul_assoc]
            rw [inv_mul_cancel₀]
            simp only [one_mul]
            nth_rw 1 [← mul_assoc]
            rw [inv_mul_cancel₀]
            simp only [one_mul]
            calc _ ≤ ((m K) : ℝ)⁻¹ + (2*((m K) : ℝ)*((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq :
                ℝ))
                      * (((m K) : ℝ)⁻¹ * ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ)⁻¹) :=?_
                 _ ≤ (2 + ((m K) : ℝ)⁻¹) ^ ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) := ?_
            · simp only [add_le_add_iff_left]
              apply mul_le_mul ?_ (le_refl _) (by positivity) (by positivity)
              · norm_cast
                trans
                apply q_le_two_mn q h2mq
                apply mul_le_mul (le_refl _) (n_le_r α β σ α' β' γ' hirr htriv habc q hq0 h2mq) (by positivity) (by positivity)
            · ring_nf
              rw [mul_inv_cancel₀]
              simp only [one_mul]
              rw [mul_inv_cancel₀]
              simp only [one_mul]
              nth_rw 1 [← Real.rpow_one (x:=(2 + ((m K) : ℝ)⁻¹))]
              apply Real.rpow_le_rpow_of_exponent_le
              · refine le_add_of_le_of_nonneg ?_ (by positivity)
                · simp only [Nat.one_le_ofNat]
              · simp only [Nat.one_le_cast]
                exact one_le_r α β σ α' β' γ' hirr htriv habc q hq0 h2mq
              · simp only [ne_eq,
                  Nat.cast_eq_zero]; exact r_ne_zero α β σ α' β' γ' hirr htriv habc q hq0 h2mq
              · simp only [ne_eq, Nat.cast_eq_zero]
                exact Nat.ne_zero_of_lt ((one_le_m K))
            · simp only [ne_eq,
                Nat.cast_eq_zero];exact r_ne_zero α β σ α' β' γ' hirr htriv habc q hq0 h2mq
            · simp only [ne_eq, Nat.cast_eq_zero]
              exact Nat.ne_zero_of_lt hq0
        · apply mul_nonneg
          · apply mul_nonneg
            · positivity
            · apply Real.rpow_nonneg (c12_nonneg α β σ α' β' γ' hirr htriv habc)
          · positivity
        · positivity
      · apply mul_nonneg
        · positivity
        · apply mul_nonneg
          · apply Real.rpow_nonneg (c12_nonneg α β σ α' β' γ' hirr htriv habc)
          · positivity
      · positivity
    · apply mul_nonneg (by positivity)
      · apply mul_nonneg (by positivity)
          (mul_nonneg (Real.rpow_nonneg (c12_nonneg α β σ α' β' γ' hirr htriv habc) _) (by positivity))
    · apply Real.rpow_nonneg
      rw [add_comm]
      trans
      apply zero_le_one
      refine le_add_of_le_of_nonneg ?_ ?_
      · simp only [le_refl]
      · simp only [inv_nonneg, norm_nonneg]
    · rw [add_comm]
      trans
      apply zero_le_one
      refine le_add_of_le_of_nonneg ?_ ?_
      · simp only [le_refl]
      · simp only [inv_nonneg, norm_nonneg]
    · simp only [Nat.cast_nonneg]
    · positivity
    · positivity
    · positivity
    · exact c12_nonneg α β σ α' β' γ' hirr htriv habc

/-- The constant `c₈ ^ (h - 1) * c₁₃`, bounding the norm of `ρ` from above. -/
def c₁₄ : ℝ := ((c₈ α' β' γ')^(((h K)-1)) * (c₁₃ α β α' β' γ'))

include α β σ α' β' γ' hirr htriv habc in
@[nolint unusedArguments]
lemma c14_nonneg : 1 ≤ (c₁₄ α β α' β' γ') :=
  one_le_mul_of_one_le_of_one_le (one_le_pow₀ (c8_geq_one α β σ α' β' γ' hirr htriv
      habc)) (one_le_c13 α β σ α' β' γ' hirr htriv habc)

include u t in
include α β σ α' β' γ' hirr htriv habc in
@[nolint unusedArguments]
lemma use6and8 : norm ((Algebra.norm ℚ (rho α β σ α' β' γ' hirr htriv habc q hq0 h2mq))) ≤ ((c₁₄ α β
    α' β' γ'))^((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) *
    ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ)^((-((r α β σ α' β' γ' hirr htriv habc) q hq0
        h2mq : ℝ))/2 + 3 * ((h K))/2) := by

  calc _ ≤  ‖ρᵣ α β σ α' β' γ' hirr htriv habc q hq0 h2mq‖ * (house (rho α β σ α' β' γ' hirr htriv
      habc q hq0 h2mq)) ^ ((((h K)) - 1 )) := ?_

       _ ≤ ((c₈ α' β' γ') ^ (r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq * ↑((r α β σ α' β' γ' hirr
           htriv habc) q hq0 h2mq :ℝ) ^
          (((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) + 3 / 2))^(((h K)) -1) *
          (((c₁₃ α β α' β' γ')) ^ ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) *
           (((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) ^ (((r α β σ α' β' γ' hirr htriv
               habc) q hq0 h2mq : ℝ) *
           ((3 - ((m K) : ℝ))) / 2 + 3 / 2))) := ?_

       _ ≤ (((c₁₄ α β α' β' γ'))^((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ)) * (↑((r α β σ
           α' β' γ' hirr htriv habc) q hq0 h2mq: ℝ))^(
         ((((h K): ℝ) - 1)) * (((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) + 3/2) +
         (((((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) * (3 - ((m K) : ℝ))) / 2) + 3 /
             2)) := ?_

       _ = (((c₁₄ α β α' β' γ'))^((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq: ℝ)) * (↑((r α β σ
           α' β' γ' hirr htriv habc) q hq0 h2mq: ℝ))^(
         ((-((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ))/2) + 3 * ((h K))/ 2) := ?_

  · have := norm_norm_le_norm_mul_house_pow (K := K) (α := ((rho α β σ α' β' γ' hirr htriv habc) q
      hq0 h2mq)) σ
    rw [← rho_eq_ρᵣ]
    unfold h
    simp only [← Real.rpow_natCast] at *
    exact this
  · nth_rw 2 [mul_comm]
    apply mul_le_mul
    · apply eq8 α β σ α' β' γ' hirr htriv habc q hq0 h2mq
    · have := (eq6 α β σ α' β' γ' hirr htriv habc) q hq0 h2mq
      simp only [← Real.rpow_natCast] at *
      apply Real.rpow_le_rpow
      · exact house_nonneg ((rho α β σ α' β' γ' hirr htriv habc) q hq0 h2mq)
      · exact this
      · simp only [Nat.cast_nonneg]
    · apply pow_nonneg; exact house_nonneg ((rho α β σ α' β' γ' hirr htriv habc) q hq0 h2mq)
    · apply mul_nonneg
      · apply Real.rpow_nonneg
        exact (c13_nonneg α β σ α' β' γ' hirr htriv habc)
      · positivity
  · unfold c₁₄
    simp only [← Real.rpow_natCast] at *
    rw [Real.mul_rpow]
    rw [← Real.rpow_mul]
    nth_rw 3 [mul_comm]
    nth_rw 1 [← Real.rpow_mul]
    nth_rw 5 [mul_comm]
    simp only [← mul_assoc]
    nth_rw  2 [mul_assoc]
    rw [← Real.rpow_add]
    rw [mul_comm]
    simp only [← mul_assoc]
    rw [Real.rpow_mul]
    rw [← Real.mul_rpow]
    nth_rw 7 [mul_comm]
    nth_rw 2 [mul_comm]
    apply mul_le_mul
    · simp only [Real.rpow_natCast]
      simp only [le_refl]
    · rw [le_iff_lt_or_eq]
      right
      congr
      refine Nat.cast_pred ?_
      unfold h; exact Module.finrank_pos
    · positivity
    · simp only [Real.rpow_natCast]
      apply pow_nonneg
      apply mul_nonneg
      · apply pow_nonneg
        exact c8_nonneg α β σ α' β' γ' hirr htriv habc
      · exact (c13_nonneg α β σ α' β' γ' hirr htriv habc)
    · exact (c13_nonneg α β σ α' β' γ' hirr htriv habc)
    · simp only [Real.rpow_natCast]
      apply pow_nonneg
      exact c8_nonneg α β σ α' β' γ' hirr htriv habc
    · exact c8_nonneg α β σ α' β' γ' hirr htriv habc
    · simp only [Nat.cast_pos]
      exact r_qt_0 α β σ α' β' γ' hirr htriv habc q hq0 h2mq
    · simp only [Nat.cast_nonneg]
    · exact c8_nonneg α β σ α' β' γ' hirr htriv habc
    · simp only [Real.rpow_natCast]
      apply pow_nonneg
      exact c8_nonneg α β σ α' β' γ' hirr htriv habc
    · apply Real.rpow_nonneg
      simp only [Nat.cast_nonneg]
  · unfold m
    simp only [mul_eq_mul_left_iff]
    left
    have : (((h K) : ℝ) - 1) * (((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) + 3/2) +
    (((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) * (3 - ((m K) : ℝ)) / 2 + 3 / 2) =
    (-((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ)) / 2 + 3 * ((h K)) / 2 := by
     unfold m
     push_cast
     ring
    rw [← this]
    unfold m
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]

/-- The constant `c₁₄ * c₅`, giving the final upper bound on `‖N ρ‖`. -/
def c₁₅ : ℝ := (c₁₄ α β α' β' γ') * (c₅ α' β' γ')

include α β σ α' β' γ' hirr htriv habc in
@[nolint unusedArguments]
lemma c15_nonneg : 0 ≤ (c₁₅ α β α' β' γ') := by
  unfold c₁₅; exact mul_nonneg (zero_le_one.trans (c14_nonneg α β σ α' β' γ' hirr htriv
      habc)) (c5nonneg α' β' γ').le

include α β σ α' β' γ' hirr htriv habc in
@[nolint unusedArguments]
lemma c15_geg_1 : 1 ≤ (c₁₅ α β α' β' γ') := by
  unfold c₁₅ c₅
  exact one_le_mul_of_one_le_of_one_le (c14_nonneg α β σ α' β' γ' hirr htriv habc) (one_le_pow₀ (by simp))

include α β σ α' β' γ' hirr htriv habc in
@[nolint unusedArguments]
theorem norm_pos_rho : 0 < ‖(Algebra.norm ℚ) ((rho α β σ α' β' γ' hirr htriv habc) q hq0
    h2mq)‖ := by
  rw [norm_pos_iff, ne_eq, Algebra.norm_eq_zero_iff]
  rintro H
  apply ρᵣ_nonzero α β σ α' β' γ' hirr htriv habc q hq0 h2mq
  simpa [← rho_eq_ρᵣ]

include α β σ α' β' γ' hirr htriv habc in
@[nolint unusedArguments]
lemma norm_algebraNorm_rho_gtinv :
    norm ((Algebra.norm ℚ) ((rho α β σ α' β' γ' hirr htriv habc) q hq0 h2mq)) ⁻¹ < (c₅ α' β'
        γ') ^ (((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ)) := by
  have h := eq5 α β σ α' β' γ' hirr htriv habc q hq0 h2mq
  rw [← inv_lt_inv₀] at h
  · simpa [← Real.rpow_neg] using h
  · exact norm_pos_rho α β σ α' β' γ' hirr htriv habc q hq0 h2mq
  · simp only [Real.rpow_neg_natCast, zpow_neg, zpow_natCast, inv_pos]
    apply pow_pos (c5nonneg α' β' γ')

include u t in
include α β σ α' β' γ' hirr htriv habc in
@[nolint unusedArguments]
lemma use5 : ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) ^ ((((r α β σ α' β' γ' hirr htriv
    habc) q hq0 h2mq : ℝ) - 3 * (h K)) / 2) <
  ((c₁₅ α β α' β' γ')) ^ ((r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) := by
  let r : ℝ := (r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq
  let N : ℝ := ‖(Algebra.norm ℚ) ((rho α β σ α' β' γ' hirr htriv habc) q hq0 h2mq)‖
  let B : ℝ := r ^ (-r / 2 + 3 * (h K) / 2)

  have hrpos : 0 < r := by
    dsimp [r]
    exact_mod_cast r_qt_0 α β σ α' β' γ' hirr htriv habc q hq0 h2mq
  have hNpos : 0 < N := by
    simpa [N] using norm_pos_rho α β σ α' β' γ' hirr htriv habc q hq0 h2mq
  have hBpos : 0 < B := by
    dsimp [B]
    exact Real.rpow_pos_of_pos hrpos _

  have h68 : N ≤ (c₁₄ α β α' β' γ') ^ r * B := by
    dsimp [N, r, B]
    simpa using (use6and8 α β σ α' β' γ' hirr htriv habc q hq0 u t h2mq)

  have htmp :
        N * B⁻¹ ≤ ((c₁₄ α β α' β' γ') ^ r * B) * B⁻¹ :=
      mul_le_mul_of_nonneg_right h68 (inv_nonneg.mpr (le_of_lt hBpos))

  have h1 : N * B⁻¹ ≤ (c₁₄ α β α' β' γ') ^ r := by
    simpa [mul_assoc, mul_inv_cancel₀ hBpos.ne', mul_one] using htmp

  have hle : B⁻¹ ≤ N⁻¹ * ((c₁₄ α β α' β' γ') ^ r) := by
    have htmp :
        N⁻¹ * (N * B⁻¹) ≤ N⁻¹ * ((c₁₄ α β α' β' γ') ^ r) :=by
      apply mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr (le_of_lt hNpos))
    grind [mul_assoc, inv_mul_cancel₀ hNpos.ne', one_mul]

  have hltN : N⁻¹ < (c₅ α' β' γ') ^ r := by
    dsimp [N, r]
    simpa using (norm_algebraNorm_rho_gtinv α β σ α' β' γ' hirr htriv habc q hq0 h2mq)

  have hApos : 0 < (c₁₄ α β α' β' γ') ^ r := by
    exact Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one (c14_nonneg α β σ α' β' γ' hirr htriv
        habc)) _

  have hmulrpow : ((c₁₅ α β α' β' γ')) ^ r = ((c₁₄ α β α' β' γ') ^ r) * ((c₅ α' β' γ') ^ r) := by
    unfold c₁₅
    rw [Real.mul_rpow (le_trans zero_le_one (c14_nonneg α β σ α' β' γ' hirr htriv habc)) (c5nonneg
        α' β' γ').le]

  calc
    ((GelfondSchneider.r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) ^ ((((GelfondSchneider.r α
        β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) - 3 * (h K)) / 2)
        = B⁻¹ := by
            dsimp [B, r]
            rw [show ((((GelfondSchneider.r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) - 3 * (h
                K)) / 2) =
                - (-((GelfondSchneider.r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) / 2 + 3 * (h K) / 2) by ring]
            rw [Real.rpow_neg (le_of_lt (by
              exact_mod_cast r_qt_0 α β σ α' β' γ' hirr htriv habc q hq0 h2mq))]
    _ ≤ N⁻¹ * ((c₁₄ α β α' β' γ') ^ r) := hle
    _ = ((c₁₄ α β α' β' γ') ^ r) * N⁻¹ := by ring
    _ < ((c₁₄ α β α' β' γ') ^ r) * ((c₅ α' β' γ') ^ r) := mul_lt_mul_of_pos_left hltN hApos
    _ = ((c₁₅ α β α' β' γ')) ^ r := hmulrpow.symm
    _ = ((c₁₅ α β α' β' γ')) ^ ((GelfondSchneider.r α β σ α' β' γ' hirr htriv habc) q hq0 h2mq : ℝ) := by rfl

end GelfondSchneider


end
