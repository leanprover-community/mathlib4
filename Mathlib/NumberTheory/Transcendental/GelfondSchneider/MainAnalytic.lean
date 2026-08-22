/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/

module

public import Mathlib.NumberTheory.Transcendental.GelfondSchneider.MainOrder
public import Mathlib.Analysis.Analytic.Order

/-! The goal of this file is to establish the critical lower bound for the proof of the
Gelfond-Schneider Theorem. Having constructed an auxiliary exponential polynomial
`R(x)` that vanishes to high order at specific points, we now isolate the first non-vanishing
derivative of `R(x)` and use its algebraic properties to bound it away from zero.

## Main Objective

To derive a contradiction, we need two opposing bounds on the size of the derivatives of `R(x)`.
This file is entirely dedicated to constructing the lower bound.
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

include α β σ α' β' γ' hirr htriv habc in
lemma iteratedkDeriv_R_eq_zero (k' : Fin (n K q)) (l' : Fin (m K)) :
    deriv^[k'] (R α β σ α' β' γ' hirr htriv habc q hq0 h2mq) (l' + 1) = 0 := by
  let u : Fin (m K * n K q) := (finProdFinEquiv.toFun ⟨l',k'⟩)
  have h1 := coeffs_mul_deriv_eq_zero α β σ α' β' γ' hirr htriv habc q hq0 u h2mq
  unfold k at *
  unfold l at *
  unfold u at *
  simp only [Equiv.toFun_as_coe,
    Equiv.symm_apply_apply] at *
  have : (σ (cCoeffs α' β' γ' q) *
   (Complex.log α)^(-k' : ℤ)) * deriv^[k'] (R α β σ α' β' γ' hirr htriv habc q hq0 h2mq) (l'+1) =
    (σ (cCoeffs α' β' γ' q) *
    (Complex.log α)^(-k' :
        ℤ)) * 0 → deriv^[k'] (R α β σ α' β' γ' hirr htriv habc q hq0 h2mq) (l' + 1) = 0 := by
      apply mul_left_cancel₀
      by_contra H
      simp only [Int.cast_mul, Int.cast_pow, map_mul, map_pow,
        map_intCast, zpow_neg, zpow_natCast,
        mul_eq_zero, pow_eq_zero_iff', Int.cast_eq_zero, ne_eq, not_or, inv_eq_zero] at H
      rcases H with ⟨h1, h2⟩
      · apply c₁_ne_zero α' β' γ'; assumption
      ·  apply c₁_ne_zero α' β' γ'; rename_i h2; exact h2.1
      · apply c₁_ne_zero α' β' γ'; rename_i h2; exact h2.1
      · have : Complex.log α ≠ 0 :=
         mt (fun h ↦ by simpa [exp_log htriv.1, exp_zero] using congrArg exp h) htriv.2
        apply this; rename_i h2; exact h2.1
  rw [this]
  rw [mul_zero]
  rw [mul_assoc]
  simp only [mul_assoc] at *
  rw [← h1]
  simp only [Int.cast_mul, Int.cast_pow, map_mul, map_pow, map_intCast, zpow_neg, zpow_natCast,
    Nat.cast_add, Nat.cast_one]

open AnalyticOnNhd

include α β σ α' β' γ' hirr htriv habc in
lemma order_neq_top : ∀ (l' : Fin (m K)), analyticOrderAt (R α β σ α' β' γ' hirr htriv habc q hq0
    h2mq) (l' + 1) ≠ ⊤ := by
  intros l' H
  rw [analyticOrderAt_eq_top_iff_eq_zero] at H
  · apply R_ne_zero α β σ α' β' γ' hirr htriv habc q hq0 h2mq (by aesop)
  fun_prop

include α β σ α' β' γ' hirr htriv habc in
lemma order_neq_top_min_one : ∀ z : ℂ, analyticOrderAt (R α β σ α' β' γ' hirr htriv habc q hq0
    h2mq) z ≠ ⊤ := by
  intros l' H
  rw [analyticOrderAt_eq_top_iff_eq_zero] at H
  · apply R_ne_zero α β σ α' β' γ' hirr htriv habc
    · rw [funext_iff]
      intros z
      rw [funext_iff] at H
      apply H z
  intros z
  fun_prop

include α β σ α' β' γ' hirr htriv habc in
lemma Rorder_exists (z : ℂ) :
    ∃ r, (analyticOrderAt (R α β σ α' β' γ' hirr htriv habc q hq0 h2mq) z) = some r := by
  have : (analyticOrderAt (R α β σ α' β' γ' hirr htriv habc q hq0 h2mq) z) ≠ ⊤ :=
    order_neq_top_min_one α β σ α' β' γ' hirr htriv habc q hq0 h2mq z
  revert this
  cases (analyticOrderAt (R α β σ α' β' γ' hirr htriv habc q hq0 h2mq) z) with
  | top => grind
  | coe => aesop

include α β σ α' β' γ' hirr htriv habc in
/-- The order of vanishing of `R` at `z`, as a natural number. -/
def rOrder (z : ℂ) : ℕ := (Rorder_exists α β σ α' β' γ' hirr htriv habc q hq0 h2mq z).choose

include α β σ α' β' γ' hirr htriv habc in
theorem R_order_prop {z : ℂ} :
    analyticOrderAt (R α β σ α' β' γ' hirr htriv habc q hq0 h2mq) z =
      some (rOrder α β σ α' β' γ' hirr htriv habc q hq0 h2mq z) :=
  (Rorder_exists α β σ α' β' γ' hirr htriv habc q hq0 h2mq z).choose_spec

include α β σ α' β' γ' hirr htriv habc in
lemma R_order_eq (z) : (analyticOrderAt (R α β σ α' β' γ' hirr htriv habc q hq0 h2mq)
    z) = rOrder α β σ α' β' γ' hirr htriv habc q hq0 h2mq z :=
  (Rorder_exists α β σ α' β' γ' hirr htriv habc q hq0 h2mq z).choose_spec

include α β σ α' β' γ' hirr htriv habc in
lemma r_exists : ∃ r, r' α β σ α' β' γ' hirr htriv habc q hq0 h2mq = some r := by
  have H := order_neq_top_min_one α β σ α' β' γ' hirr htriv habc q hq0 h2mq (l₀' α β σ α' β' γ' hirr
      htriv habc q hq0 h2mq + 1)
  have : r' α β σ α' β' γ' hirr htriv habc q hq0 h2mq ≠ ⊤ := by
    rw [(r'_spec α β σ α' β' γ' hirr htriv habc q hq0 h2mq).1] at H; exact H
  revert this
  cases r' α β σ α' β' γ' hirr htriv habc q hq0 h2mq with
  | top => grind
  | coe => aesop

include α β σ α' β' γ' hirr htriv habc in
/-- The minimal order of vanishing `r` of `R` among the points `1, …, m`. -/
def r := (r_exists α β σ α' β' γ' hirr htriv habc q hq0 h2mq).choose

include α β σ α' β' γ' hirr htriv habc in
/-- `r'` is the natural number `r`. -/
abbrev rSpec : r' α β σ α' β' γ' hirr htriv habc q hq0 h2mq = ↑(r α β σ α' β' γ' hirr htriv habc q
    hq0 h2mq) :=
  (r_exists α β σ α' β' γ' hirr htriv habc q hq0 h2mq).choose_spec

include α β σ α' β' γ' hirr htriv habc in
/-- The defining properties of `r`: it is the order of `R` at `l₀' + 1`, and it is minimal. -/
abbrev rProp :
  let s : Finset (Fin (m K)) := Finset.univ
  analyticOrderAt (R α β σ α' β' γ' hirr htriv habc q hq0 h2mq) (l₀' α β σ α' β' γ' hirr htriv habc
      q hq0 h2mq + 1) = r α β σ α' β' γ' hirr htriv habc q hq0 h2mq ∧
  ∀ l' ∈ s, r α β σ α' β' γ' hirr htriv habc q hq0 h2mq ≤ analyticOrderAt (R α β σ α' β' γ' hirr
      htriv habc q hq0 h2mq) (↑↑l' + 1) := by
  intros s
  rw [← rSpec α β σ α' β' γ' hirr htriv habc q hq0 h2mq]
  apply r'_spec α β σ α' β' γ' hirr htriv habc q hq0 h2mq

include α β σ α' β' γ' hirr htriv habc in
lemma r_div_q_geq_0 : 0 ≤ (r α β σ α' β' γ' hirr htriv habc q hq0 h2mq) / q := by
  simp_all only [zero_le]


include α β σ α' β' γ' hirr htriv habc in
/-- The integer factor `|c₁ ^ r * c₁ ^ (2 * m * q)|` that clears the denominators of `ρ`. -/
def cρ : ℤ := abs (c₁ α' β' γ' ^ (r α β σ α' β' γ' hirr htriv habc q hq0 h2mq) * c₁ α' β' γ'^(2*m K
    * q))

include α β σ α' β' γ' hirr htriv habc in
/-- The system coefficient at the minimal order `r` and the point `l₀' + 1`. -/
abbrev systemCoeffsR : K := (a q t + b q t • β')^(r α β σ α' β' γ' hirr htriv habc q hq0 h2mq) *
 α' ^(a q t * (l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq + 1)) * γ' ^(b q t * (l₀' α β σ α' β'
     γ' hirr htriv habc q hq0 h2mq + 1))

include α β σ α' β' γ' hirr htriv habc in
lemma systemCoeffs_ne_zero_r : systemCoeffsR α β σ α' β' γ' hirr htriv habc q hq0 t h2mq ≠ 0 := by
  unfold systemCoeffsR
  intros H
  simp only [mul_eq_zero, pow_eq_zero_iff'] at H
  cases H with
  | inl H1 =>
    cases H1 with
    | inl H1 =>
      rcases H1 with ⟨h1, h2⟩
      exact β'_ne_zero α β σ α' β' γ' hirr habc q t h1
    | inr H2 => exact (alpha'_beta'_gamma'_ne_zero α β σ α' β' γ' hirr htriv habc).1 H2.1
  | inr H2 =>
    exfalso
    exact (alpha'_beta'_gamma'_ne_zero α β σ α' β' γ' hirr htriv habc).2.2 H2.1

include α β σ α' β' γ' hirr htriv habc in
/-- The normalised evaluation `(log α) ^ (-r) * R⁽ʳ⁾(l₀' + 1)`. -/
def ρᵣ : ℂ := (Complex.log α)^(-(r α β σ α' β' γ' hirr htriv habc q hq0 h2mq) : ℤ) *
 deriv^[r α β σ α' β' γ' hirr htriv habc q hq0 h2mq] (R α β σ α' β' γ' hirr htriv habc q hq0
     h2mq) (l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq + 1)

include α β σ α' β' γ' hirr htriv habc in
lemma systemCoeffs_map_eq_exp_mul_r :
  exp (ρ α β q t * (l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq + 1)) *
  ρ α β q t ^ (r α β σ α' β' γ' hirr htriv habc q hq0 h2mq : ℕ) *
  Complex.log α ^ (-(r α β σ α' β' γ' hirr htriv habc q hq0 h2mq) : ℤ) = σ (systemCoeffsR α β σ α'
      β' γ' hirr htriv habc q hq0 t h2mq) := by
    nth_rw 2 [ρ]
    rw [mul_pow, mul_assoc, mul_assoc]
    have : (Complex.log α ^ (r α β σ α' β' γ' hirr htriv habc q hq0 h2mq : ℕ) *
      Complex.log α ^ (-r α β σ α' β' γ' hirr htriv habc q hq0 h2mq : ℤ)) = 1 := by
      simp only [zpow_neg, zpow_natCast]
      refine Complex.mul_inv_cancel ?_
      by_contra! H
      have : Complex.log α ≠ 0 :=
         mt (fun h ↦ by simpa [exp_log htriv.1, exp_zero] using congrArg exp h) htriv.2
      apply this
      simp only [pow_eq_zero_iff', ne_eq] at H
      apply H.1
    rw [this]; clear this
    rw [mul_one]
    unfold systemCoeffsR
    rw [mul_comm]
    change _ = σ ((↑(a q t) + b q t • β') ^ (r α β σ α' β' γ' hirr htriv habc q hq0 h2mq : ℕ)
        * (α' ^ (a q t * (l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq + 1)))
        * (γ' ^ (b q t * (l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq + 1))))
    rw [map_mul]
    rw [map_mul]
    nth_rw 1 [mul_assoc]
    have : σ ((↑(a q t) + (b q t) • β') ^ (r α β σ α' β' γ' hirr htriv habc q hq0 h2mq)) =
        (↑(a q t) + ↑(b q t) * β) ^ ((r α β σ α' β' γ' hirr htriv habc q hq0 h2mq)) := by
      simp only [nsmul_eq_mul, map_pow, map_add, map_natCast, map_mul]
      simp_all only [a, b]
    rw [this]; clear this
    rw [map_pow, map_pow]
    have : (↑(a q t) + (b q t) • β) ^
      (r α β σ α' β' γ' hirr htriv habc q hq0 h2mq) * cexp (ρ α β q t * (l₀' α β σ α' β' γ' hirr
          htriv habc q hq0 h2mq + 1)) =
        (↑(a q t) + ↑(b q t) * β)^(r α β σ α' β' γ' hirr htriv habc q hq0 h2mq) *
          cexp (ρ α β q t * (l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq + 1)) := by
      simp_all only [Equiv.toFun_as_coe, finProdFinEquiv_symm_apply,
        Fin.coe_modNat,
        Fin.coe_divNat, Nat.cast_add, Nat.cast_one, nsmul_eq_mul,b, a]
    rw [this]; clear this
    simp only [mul_eq_mul_left_iff, pow_eq_zero_iff']
    left
    rw [ρ]
    have : cexp (( ↑(a q t) + (b q t) • β) * Complex.log α * (l₀' α β σ α' β' γ' hirr htriv habc q
        hq0 h2mq + 1)
        ) =
        cexp ((↑(a q t) + ↑(b q t) • β) * Complex.log α * (l₀' α β σ α' β' γ' hirr htriv habc q hq0
            h2mq +1)) := by
          simp_all only [Equiv.toFun_as_coe, finProdFinEquiv_symm_apply,
          Fin.coe_modNat,
            Fin.coe_divNat, Nat.cast_add, Nat.cast_one,
            nsmul_eq_mul, b, a]
    rw [this];clear this
    have : σ α' ^ ((a q t) * (l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq + 1)) *
       σ γ' ^ ((b q t) * (l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq + 1)) =
       α ^ ((a q t) * (l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq + 1)) *
       (σ γ')^ ((b q t) * (l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq + 1)) := by
      simp only [mul_eq_mul_right_iff, pow_eq_zero_iff',
        map_eq_zero, ne_eq, mul_eq_zero, not_or]
      left
      congr
      rw [← habc.1]
    rw [← habc.1]
    have : σ γ' = α^β := by rw [habc.2.2]
    rw [this]; clear this
    have : Complex.exp (Complex.log α) = α :=
      Complex.exp_log htriv.1
    clear this
    rw [← cpow_nat_mul]
    have : cexp ((↑(a q t) + (b q t) • β) *
      Complex.log α * (l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq +1)) =
        α ^ ((a q t) * (l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq + 1)) *
        α ^ (↑((b q t) * (l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq +1 )) * β) ↔
      cexp ((↑(a q t) + (b q t) • β) *
      Complex.log α * (l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq + 1)) =
        α ^ (((a q t) * (l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq +1)) +
         ((↑(b q t) * (l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq + 1)) * β)) := by
        rw [cpow_add]
        · simp only [nsmul_eq_mul, Nat.cast_mul]
          norm_cast
        exact htriv.1
    rw [this]; clear this
    rw [cpow_def_of_ne_zero]
    · have : Complex.log α * (↑(a q t) * (l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq +1) +
       ((b q t) * (l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq + 1)) * β) =
        (↑(a q t) + (b q t) • β) * Complex.log α * (l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq +
            1) := by
        nth_rw 4 [mul_comm]
        have : ( ((l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq + 1) * (b q t)) * β) =
        ( (((b q t) * β) * (l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq + 1))) := by
          exact mul_rotate (↑↑(l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq) + 1) (↑(b q t)) β
        rw [this];clear this
        have H : (↑(a q t) * (l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq + 1) +
        (((b q t) * β) * (l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq +1))) =
        (((a q t)  + ((b q t) * β)) *  ↑((↑(l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq : ℕ) + 1
            :ℂ))) :=
        Eq.symm (RightDistribClass.right_distrib
          (↑(a q t)) (↑(b q t) * β) (l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq + 1))
        rw [H, mul_comm, mul_assoc]
        nth_rw 3 [mul_comm]
        rw [← mul_assoc, nsmul_eq_mul]
      rw [this]
    · exact htriv.1

include α β σ α' β' γ' hirr htriv habc in
theorem deriv_R_k_eval_at_l0' :
  deriv^[r α β σ α' β' γ' hirr htriv habc q hq0 h2mq] (R α β σ α' β' γ' hirr htriv habc q hq0
      h2mq) (l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq + 1) =
  ∑ t, σ ((η (K := K) α β σ α' β' γ' hirr htriv habc q hq0 h2mq) t) *
  cexp (ρ α β q t * (l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq + 1)) * (ρ α β q t) ^ (r α β σ α'
      β' γ' hirr htriv habc q hq0 h2mq) := by
  rw [iteratedDeriv_R]

include α β σ α' β' γ' hirr htriv habc in
lemma systemCoeffs_deriv_r :
 (Complex.log α)^(-r α β σ α' β' γ' hirr htriv habc q hq0 h2mq : ℤ) * deriv^[r α β σ α' β' γ' hirr
     htriv habc q hq0 h2mq]
 (R α β σ α' β' γ' hirr htriv habc q hq0 h2mq) (l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq + 1) =
 ∑ t, σ ↑((η (K := K) α β σ α' β' γ' hirr htriv habc q hq0 h2mq) t) * σ (systemCoeffsR α β σ α' β'
     γ' hirr htriv habc q hq0 t h2mq) := by
  rw [deriv_R_k_eval_at_l0' α β σ α' β' γ' hirr htriv habc q hq0 h2mq, mul_sum, Finset.sum_congr
      rfl]
  intros t ht
  rw [mul_assoc, mul_comm, mul_assoc]
  unfold η
  simp only [mul_eq_mul_left_iff, map_eq_zero,
    FaithfulSMul.algebraMap_eq_zero_iff]
  left
  have := systemCoeffs_map_eq_exp_mul_r α β σ α' β' γ' hirr htriv habc q hq0 t h2mq
  rw [← this]

include α β σ α' β' γ' hirr htriv habc in
/-- The algebraic number `ρ`, the `η`-weighted sum of the system coefficients at order `r`. -/
def rho := ∑ t : Fin (q * q), (η (K := K) α β σ α' β' γ' hirr htriv habc q hq0 h2mq
    t) * (systemCoeffsR α β σ α' β' γ' hirr htriv habc q hq0 t h2mq)

include α β σ α' β' γ' hirr htriv habc in
theorem rho_eq_ρᵣ : σ (rho α β σ α' β' γ' hirr htriv habc q hq0
    h2mq) = ρᵣ α β σ α' β' γ' hirr htriv habc q hq0 h2mq := by
  unfold rho ρᵣ
  rw [systemCoeffs_deriv_r]
  simp only [map_sum, map_mul, nsmul_eq_mul, map_pow, map_add, map_natCast]

include α β σ α' β' γ' hirr htriv habc in
lemma cρ_ne_zero : cρ α β σ α' β' γ' hirr htriv habc q hq0 h2mq ≠ 0 := by
  apply abs_ne_zero.mpr <| mul_ne_zero _ _
  all_goals apply pow_ne_zero _ (c₁_ne_zero α' β' γ')

/-!
This number lies in $K,$ and ${c_1}^{r+2mq}\rho$ is an integer in $K$
-/

include α β σ α' β' γ' hirr htriv habc in
lemma ρ_is_int :
  IsIntegral ℤ (cρ α β σ α' β' γ' hirr htriv habc q hq0 h2mq • rho α β σ α' β' γ' hirr htriv habc q
      hq0 h2mq) := by
  unfold rho cρ systemCoeffsR
  have : c₁ α' β' γ' ^ (2 * m K * q) = c₁ α' β' γ' ^ (m K * q)
  * c₁ α' β' γ' ^ (m K * q) := by
      rw [← pow_add]; ring
  rw [this]
  rcases abs_choice (c₁ α' β' γ' ^ r α β σ α' β' γ' hirr htriv habc q hq0 h2mq * c₁ α' β' γ' ^ (m K
      * q) * c₁ α' β' γ' ^ (m K * q)) with H1 | H2
  · rw [← mul_assoc, H1, Finset.smul_sum]
    apply IsIntegral.sum
    intros x hx
    rw [zsmul_eq_mul]
    nth_rw 1 [mul_comm]
    rw [mul_assoc]
    apply IsIntegral.mul
    · exact RingOfIntegers.isIntegral_coe ((η (K := K) α β σ α' β' γ' hirr htriv habc q hq0 h2mq) x)
    · rw [mul_comm, ← zsmul_eq_mul]
      have triple_comm (K : Type) [Field K] (a b c : ℤ) (x y z : K) :
         ((a*b)*c) • ((x*y)*z) = a•x * b•y * c•z := by
        simp only [zsmul_eq_mul, Int.cast_mul]; ring
      have := triple_comm K
        (c₁ α' β' γ'^(r α β σ α' β' γ' hirr htriv habc q hq0 h2mq) : ℤ)
        (c₁ α' β' γ'^(m K * q) : ℤ)
        (c₁ α' β' γ'^(m K * q) : ℤ)
        (((a q x : ℕ) + b q x • β')^(r α β σ α' β' γ' hirr htriv habc q hq0 h2mq))
        (α' ^ (a q x * (l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq + 1)))
        (γ' ^ (b q x * (l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq + 1)))
      have : IsIntegral ℤ
         ((c₁ α' β' γ' ^ (r α β σ α' β' γ' hirr htriv habc q hq0 h2mq) * c₁ α' β' γ' ^ (m K * q) *
             c₁ α' β' γ' ^ (m K * q)) •
        ((↑(a q x) + b q x • β') ^ (r α β σ α' β' γ' hirr htriv habc q hq0 h2mq) *
          α' ^ (a q x * (l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq + 1)) *
          γ' ^ (b q x * (l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq + 1)))) =
       IsIntegral ℤ
         (c₁ α' β' γ' ^ (r α β σ α' β' γ' hirr htriv habc q hq0 h2mq) • (↑(a q x) + b q x • β') ^ (r
             α β σ α' β' γ' hirr htriv habc q hq0 h2mq) *
          c₁ α' β' γ' ^ (m K * q) • α' ^ (a q x * (l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq +
              1)) *
          c₁ α' β' γ' ^ (m K * q) • γ' ^ (b q x * (l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq +
              1))) := by
        rw [← this]
      simp_rw [this]
      apply IsIntegral.mul
      · apply IsIntegral.mul
        · simp only [nsmul_eq_mul, zsmul_eq_mul, Int.cast_pow]
          rw [← mul_pow]
          apply IsIntegral.pow
          rw [mul_add]
          apply IsIntegral.add
          · apply IsIntegral.mul <| isIntegral_intCast _
            · apply isIntegral_natCast
          · rw [mul_comm, mul_assoc]
            apply IsIntegral.mul
            · apply isIntegral_natCast
            · rw [mul_comm];
              have := isIntegral_c₁β α' β' γ'
              simp only [zsmul_eq_mul] at this
              exact this
        · apply isIntegral_c₁_pow_smul_pow α' β' γ'
          · rw [mul_comm]
            apply Nat.mul_le_mul ((l₀' α β σ α' β' γ' hirr htriv habc q hq0
                h2mq).isLt) ((finProdFinEquiv.symm.toFun x).1.isLt)
          · rw [← zsmul_eq_mul]; exact isIntegral_c₁α α' β' γ'
      · have : c₁ α' β' γ' ^ (m K * q - ((b q x) * (l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq +
          1))) *
           (c₁ α' β' γ' ^ ((b q x) * (l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq + 1))) =
              (c₁ α' β' γ' ^ ((m K * q))) := by
          rw [← pow_add,Nat.sub_add_cancel]
          nth_rw 1 [mul_comm]
          apply mul_le_mul
          · exact (l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq).isLt
          · exact (finProdFinEquiv.symm.toFun x).2.isLt
          · simp only [zero_le]
          · simp only [zero_le]
        rw [← this]
        simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_pow]
        rw [mul_assoc]
        apply IsIntegral.mul
        · apply IsIntegral.pow
          · apply isIntegral_intCast
        · rw [← mul_pow]
          apply IsIntegral.pow
          · rw [← zsmul_eq_mul]; exact isIntegral_c₁γ α' β' γ'
  · rw [Finset.smul_sum]
    apply IsIntegral.sum
    intros x hx
    rw [← mul_assoc, H2]
    rw [zsmul_eq_mul]
    nth_rw 1 [mul_comm]
    rw [mul_assoc]
    apply IsIntegral.mul
    · exact RingOfIntegers.isIntegral_coe ((η (K := K) α β σ α' β' γ' hirr htriv habc q hq0 h2mq) x)
    · rw [mul_comm]
      rw [← zsmul_eq_mul]
      have triple_comm (K : Type) [Field K] (a b c : ℤ) (x y z : K) :
         ((a*b)*c) • ((x*y)*z) = a•x * b•y * c•z := by
        simp only [zsmul_eq_mul, Int.cast_mul]; ring
      have H := triple_comm K
        (c₁ α' β' γ'^(r α β σ α' β' γ' hirr htriv habc q hq0 h2mq))
        (c₁ α' β' γ'^(m K * q) : ℤ)
        (c₁ α' β' γ'^(m K * q) : ℤ)
        (((a q x : ℕ) + (b q x) • β')^(r α β σ α' β' γ' hirr htriv habc q hq0 h2mq))
        (α' ^ ((a q x) * ((l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq + 1))))
        (γ' ^ ((b q x) * ((l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq + 1))))
      have : IsIntegral ℤ (-(c₁ α' β' γ' ^ r α β σ α' β' γ' hirr htriv habc q hq0 h2mq * c₁ α' β' γ'
          ^ (m K * q) * c₁ α' β' γ' ^ (m K * q)) •
    ((↑(a q x) + b q x • β') ^ r α β σ α' β' γ' hirr htriv habc q hq0 h2mq * α' ^ (a q x * (l₀' α β
        σ α' β' γ' hirr htriv habc q hq0 h2mq + 1)) *
      γ' ^ (b q x * (l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq + 1)))) =
         IsIntegral ℤ ((c₁ α' β' γ' ^ (r α β σ α' β' γ' hirr htriv habc q hq0 h2mq) •
          (↑(a q x) + (b q x) • β') ^ (r α β σ α' β' γ' hirr htriv habc q hq0 h2mq)
           * c₁ α' β' γ' ^ (m K * q) • α' ^ ((a q x) *
           (l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq + 1)) * c₁ α' β' γ' ^ (m K * q) •
             γ' ^ ((b q x) * (l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq + 1)))) := by
          rw [← H]
          rw [neg_smul]
          simp only [nsmul_eq_mul, zsmul_eq_mul, Int.cast_mul, Int.cast_pow,
            IsIntegral.neg_iff]
      clear H
      rw [this]
      apply IsIntegral.mul
      · apply IsIntegral.mul
        · simp only [nsmul_eq_mul, zsmul_eq_mul, Int.cast_pow]
          rw [← mul_pow]
          apply IsIntegral.pow
          rw [mul_add]
          · apply IsIntegral.add
            · apply IsIntegral.mul <| isIntegral_intCast _
              · apply isIntegral_natCast
            ·rw [mul_comm, mul_assoc]
             apply IsIntegral.mul <| isIntegral_natCast _
             rw [mul_comm, ← zsmul_eq_mul]
             exact isIntegral_c₁β α' β' γ'
        · apply isIntegral_c₁_pow_smul_pow α' β' γ'
          · rw [mul_comm]
            apply Nat.mul_le_mul
            · exact (l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq).isLt
            exact (finProdFinEquiv.symm.toFun x).1.isLt
          · rw [← zsmul_eq_mul]; exact isIntegral_c₁α α' β' γ'
      · have : c₁ α' β' γ' ^ (m K * q - (b q x * (l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq +
          1))) *
           (c₁ α' β' γ' ^ ((b q x) * (l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq + 1))) = (c₁ α'
               β' γ' ^ ((m K * q))) := by
          rw [← pow_add, Nat.sub_add_cancel]
          nth_rw 1 [mul_comm]
          apply mul_le_mul
          · exact (l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq).isLt
          · exact (finProdFinEquiv.symm.toFun x).2.isLt
          · simp only [zero_le]
          · simp only [zero_le]
        rw [← this]
        simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_pow]
        rw [mul_assoc]
        apply IsIntegral.mul
        · apply IsIntegral.pow
          · apply isIntegral_intCast
        · rw [← mul_pow]
          apply IsIntegral.pow
          · rw [← zsmul_eq_mul]; exact isIntegral_c₁γ α' β' γ'

include α β σ α' β' γ' hirr htriv habc in
/-- The algebraic integer `cρ • ρ` of `𝓞 K`. -/
def c1ρ : 𝓞 K := RingOfIntegers.restrict _
  (fun _ => (ρ_is_int α β σ α' β' γ' hirr htriv habc q hq0 h2mq)) ℤ

include α β σ α' β' γ' hirr htriv habc in
lemma one_le_c1rho : 1 ≤ ↑(cρ α β σ α' β' γ' hirr htriv habc q hq0 h2mq) := by
  apply Int.one_le_abs
  by_contra H
  simp only [mul_eq_zero, pow_eq_zero_iff', ne_eq,
    OfNat.ofNat_ne_zero, false_or, not_or] at H
  cases H with
  | inl h1 => apply (c₁_ne_zero α' β' γ'); exact h1.1
  | inr h2 => apply (c₁_ne_zero α' β' γ'); exact h2.1

include α β σ α' β' γ' hirr htriv habc in
lemma one_le_norm_c1rho : 1 ≤ norm (cρ α β σ α' β' γ' hirr htriv habc q hq0 h2mq) := by
  have := one_le_c1rho α β σ α' β' γ' hirr htriv habc q hq0 h2mq
  have : |(cρ α β σ α' β' γ' hirr htriv habc q hq0 h2mq)| = ‖(cρ α β σ α' β' γ' hirr htriv habc q
      hq0 h2mq : ℤ)‖ := by
    simp only [Int.cast_abs]
    exact rfl
  rw [← this]
  simp only [Int.cast_abs, ge_iff_le]
  have := Int.one_le_abs (z := cρ α β σ α' β' γ' hirr htriv habc q hq0 h2mq)
  norm_cast
  apply this
  exact cρ_ne_zero α β σ α' β' γ' hirr htriv habc q hq0 h2mq

include α β σ α' β' γ' hirr htriv habc in
lemma zero_le_c1rho : 0 ≤ ↑(cρ α β σ α' β' γ' hirr htriv habc q hq0 h2mq) :=
  Int.le_of_lt (one_le_c1rho α β σ α' β' γ' hirr htriv habc q hq0 h2mq)

include α β σ α' β' γ' hirr htriv habc in
lemma crho_le_abs_crho :
    (cρ α β σ α' β' γ' hirr htriv habc q hq0 h2mq) ≤ abs (cρ α β σ α' β' γ' hirr htriv habc q hq0
        h2mq):= le_abs_self _

include α β σ α' β' γ' hirr htriv habc in
lemma abs_crho_le_norm_crho :
    abs (cρ α β σ α' β' γ' hirr htriv habc q hq0 h2mq) ≤ norm (cρ α β σ α' β' γ' hirr htriv habc q
        hq0 h2mq) := by
  simp only [Int.cast_abs]
  rfl

include α β σ α' β' γ' hirr htriv habc in
lemma norm_crho_le_house_crho : norm (cρ α β σ α' β' γ' hirr htriv habc q hq0 h2mq) ≤
  house (cρ α β σ α' β' γ' hirr htriv habc q hq0 h2mq : K) := by
  rw [house_intCast]
  simp only [Int.cast_abs]
  exact Preorder.le_refl ‖cρ α β σ α' β' γ' hirr htriv habc q hq0 h2mq‖

include α β σ α' β' γ' hirr htriv habc in
lemma norm_cρ_pos : 0 < ‖cρ α β σ α' β' γ' hirr htriv habc q hq0 h2mq‖ := by
  rw [norm_pos_iff]
  have := cρ_ne_zero α β σ α' β' γ' hirr htriv habc q hq0 h2mq
  unfold cρ at this
  exact this

include α β σ α' β' γ' hirr htriv habc in
lemma h1 : 1 ≤ ‖cρ α β σ α' β' γ' hirr htriv habc q hq0 h2mq‖ ^ Module.finrank ℚ K := by
      rw [one_le_pow_iff_of_nonneg]
      · rw [Int.norm_eq_abs]
        have := (norm_cρ_pos α β σ α' β' γ' hirr htriv habc q hq0 h2mq)
        rw [Int.norm_eq_abs] at this
        unfold cρ
        simp only [Int.cast_abs, Int.cast_mul, Int.cast_pow, abs_abs]
        rw [← pow_add]
        simp only [abs_pow]
        have : 1 ≤ |↑(c₁ α' β' γ')| := by
          rw [le_abs']
          right
          exact one_le_c₁ α' β' γ'
        refine one_le_pow₀ ?_
        exact mod_cast this
      · apply norm_nonneg
      · have : 0 < Module.finrank ℚ K  := Module.finrank_pos
        simp_all only [ne_eq]
        intro a
        simp_all only [lt_self_iff_false]

end GelfondSchneider

end
