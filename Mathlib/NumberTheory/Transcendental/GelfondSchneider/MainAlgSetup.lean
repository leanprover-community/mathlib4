/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/

module

public import Mathlib.NumberTheory.Transcendental.GelfondSchneider.MainAlg
public import Mathlib.Tactic

/-!
# Gelfond-Schneider Theorem: Matrix Coefficient Bounds and Siegel's Lemma

This file is the second component in the formalization of the Gelfond–Schneider Theorem
  (Hilbert's Seventh Problem), establishing the transcendence of `α ^ β`.

## Main results
Following the construction of the algebraic setup and linear system matrix in `MainAlg.lean`,
this file establishes strict analytical bounds on the coefficients of the matrix `A` and
applies Siegel's Lemma to guarantee a small, non-trivial integer solution.

Specifically, we prove:
1. `house_matrixA_le`**: The maximum absolute value of the conjugates (the "house") of the
  entries of `A` is strictly bounded by `c₃^n * n^((n - 1) / 2)`.
2. `η`**: The existence of a non-trivial vector of algebraic integers `η₁ ... η_t` in the kernel
  of `A`.
3. `house_eta_le_c₄_pow`**: An explicit upper bound on the house of the solution vector `η`,
  showing `‖ηₖ‖ ≤ c₄ⁿ * n^((n + 1) / 2)`.

These bounded coefficients `η` will be used in subsequent files to explicitly construct the
auxiliary integer function `R(x)`.

## References
* Loo-Keng Hua, Introduction to Number Theory, Springer, 1982. Chapter 17.9.
-/

@[expose] public section

open BigOperators Module.Free Fintype NumberField Embeddings FiniteDimensional
   Matrix Set Polynomial Finset IntermediateField Complex AnalyticAt

noncomputable section

variable (h7 : Setup) (q : ℕ) (hq0 : 0 < q) (u : Fin (h7.m * h7.n q)) (t : Fin (q * q))
  (h2mq : 2 * h7.m ∣ q ^ 2)

namespace Setup


/-!
In this file we bound the house of the coefficients of the auxiliary function `R`;
  `‖ηₖ‖ ≤ c₄ⁿ * n^((n - 1) / 2)`, for `1 ≤ k ≤ t`.
-/

open Real

/-- A real-valued bounding constant encompassing `c₂` and the houses of `α'`, `β'`, and `γ'`.
Used to establish a strict upper bound on the entries of the linear system matrix `A`. -/
def c₃ : ℝ := h7.c₂ * (1 + house h7.β') * sqrt (2 * h7.m) *
  (max 1 (((house h7.α' ^ (2 * h7.m ^ 2)) * house h7.γ' ^(2 * h7.m ^ 2))))

lemma one_le_c₃ : 1 ≤ h7.c₃ := by
  simp only [c₃]
  refine one_le_mul_of_one_le_of_one_le ?_ (le_max_left 1 _)
  refine one_le_mul_of_one_le_of_one_le ?_ ?_
  · exact one_le_mul_of_one_le_of_one_le (by exact_mod_cast h7.one_le_c₂)
      (le_add_of_nonneg_right (house_nonneg _))
  · rw [one_le_sqrt]
    have := h7.one_le_m
    exact_mod_cast (by omega : 1 ≤ 2 * h7.m)

lemma c₃_pow : h7.c₃ ^ ↑(h7.n q : ℝ) = h7.c₂ ^ ↑(h7.n q) * ((1 + house (h7.β')) ^ ↑(h7.n q)) *
    (sqrt ((2 * h7.m)) ^ ↑(h7.n q)) * (max 1 ((house (h7.α') ^ (2 * h7.m ^ 2)) * house (h7.γ') ^
    (2*h7.m^ 2)))^ ↑(h7.n q) := by
  simp only [c₃, rpow_natCast]; rw [mul_pow, mul_pow, mul_pow]

include h2mq in
lemma q_sq_eq_two_mn : q ^ 2 = 2 * h7.m * h7.n q := Eq.symm (Nat.mul_div_cancel' h2mq)

include h2mq in
lemma q_sq_le_two_mn : q ^ 2 ≤ 2 * h7.m * h7.n q := by
  simpa using le_of_eq (h7.q_sq_eq_two_mn q h2mq)

include h2mq in
lemma q_eq_n_etc : q ^ (h7.n q - 1) ≤ (sqrt (2 * h7.m) ^ (h7.n q - 1)) * (sqrt (h7.n q)) ^
    (h7.n q - 1) := by
  rw [← mul_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ (h7.n q - 1)
  have hq : (q : ℝ) ≤ sqrt (2 * h7.m * h7.n q) := by
    refine (le_sqrt (by positivity) (by positivity)).2 (mod_cast h7.q_sq_le_two_mn q h2mq)
  simpa [mul_assoc, sqrt_mul] using hq

include h2mq in
lemma q_le_two_mn : q ≤ 2 * h7.m * h7.n q :=
  le_trans (Nat.le_pow (Nat.zero_lt_two)) ((by simpa using le_of_eq (h7.q_sq_eq_two_mn q h2mq)))

include hq0 h2mq in
lemma m_mul_n_pos : 0 < h7.m * h7.n q :=
  Nat.mul_pos h7.one_le_m <| by simpa [n, Nat.div_pos_iff] using
    ⟨Nat.zero_lt_succ (2 * h7.h + 1), Nat.le_of_dvd (Nat.pow_pos hq0) h2mq⟩

include h2mq hq0 in
lemma mul_div_sub_eq_one : ((h7.m : ℝ) * (h7.n q : ℝ) / (2 * (h7.m : ℝ) * (h7.n q : ℝ) -
    (h7.m * (h7.n q : ℝ))) : ℝ) = 1 := by
  have : 2 * (h7.m : ℝ) * (h7.n q : ℝ) - (h7.m : ℝ) * (h7.n q : ℝ) = (h7.m : ℝ) * (h7.n q : ℝ) :=
    by ring
  rw [this]
  exact div_self (by exact_mod_cast (h7.m_mul_n_pos q hq0 h2mq).ne')

include hq0 h2mq in
lemma mul_rpow_sub_one_div_two : (h7.n q : ℝ) * (h7.n q : ℝ) ^ (((h7.n q : ℝ) - 1) / 2) =
    (h7.n q : ℝ) ^ (((h7.n q : ℝ) + 1) / 2) := by
  have h_exp : (((h7.n q : ℝ) + 1) / 2) = 1 + (((h7.n q : ℝ) - 1) / 2) := by ring
  rw [h_exp, Real.rpow_add (by
   norm_cast; refine Nat.ne_zero_iff_zero_lt.mp
     (Nat.ne_zero_of_lt (one_le_n h7 q hq0 h2mq))), Real.rpow_one]

include h2mq hq0 in
lemma abs_q_pow_mul_house_le_c₃_pow : |↑q| ^ (h7.n q - 1) * ((1 + house h7.β') ^ (h7.n q - 1) *
    (house h7.α' ^ (h7.m * (2 * (h7.m * h7.n q))) * house h7.γ' ^ (h7.m * (2 * (h7.m * h7.n q))))) ≤
    (1 + house h7.β') ^ h7.n q * (√(2 * ↑h7.m) ^ h7.n q * (max 1 (house h7.α' ^ (2 * h7.m ^ 2) *
    house h7.γ' ^ (2 * h7.m ^ 2)) ^ h7.n q * √↑(h7.n q) ^ (↑(h7.n q : ℝ) - 1))) := by
  calc _ ≤ (sqrt (2 * h7.m) ^ (h7.n q -1))* (sqrt (h7.n q)) ^ ((h7.n q) -1) *
                 ((1 + house h7.β') ^ (h7.n q - 1) * (house h7.α' ^ (h7.m * (2 * (h7.m * h7.n q))) *
                 house h7.γ' ^ (h7.m * (2 * (h7.m * h7.n q))))) := ?_
       _ ≤ (sqrt (2 * h7.m) ^ (h7.n q -1)) * ((1 + house h7.β') ^ (h7.n q - 1) *
                 (house h7.α' ^ (h7.m * (2 * (h7.m * h7.n q))) * house h7.γ' ^
                 (h7.m * (2 * (h7.m * h7.n q))))) * sqrt (h7.n q) ^ (((h7.n q) : ℝ) - 1) := ?_
       _ ≤ √(2 * ↑(h7.m)) ^ ((h7.n q)) * ((1 + house h7.β') ^ ((h7.n q)) * (house h7.α' ^
                 (h7.m * 2 * h7.m)) ^ (h7.n q) * (house h7.γ' ^ (h7.m * 2 * h7.m)) ^ (h7.n q)) *
                 (sqrt (h7.n q )) ^ (((h7.n q) : ℝ)-1) := ?_
  · apply mul_le_mul (by simpa using (h7.q_eq_n_etc q h2mq)) (by rfl) (by dsimp [house];positivity)
      (by positivity)
  · have hsqrt : (sqrt (h7.n q) ^ (h7.n q - 1)) = (sqrt (h7.n q) ^ ((h7.n q : ℝ) - 1)) := by
      simpa [(Nat.cast_sub (h7.one_le_n q hq0 h2mq))] using
        (rpow_natCast (x := sqrt (h7.n q)) (n := h7.n q - 1)).symm
    refine le_of_eq ?_; simp [hsqrt]; ac_rfl
  · simp only [mul_assoc]
    apply mul_le_mul ?_ ?_ (by dsimp [house];positivity) (by positivity)
    · refine Bound.pow_le_pow_right_of_le_one_or_one_le (Or.inl ⟨?_, by simp⟩)
      have hm1 : (1 : ℝ) ≤ (h7.m : ℝ) := by exact_mod_cast h7.one_le_m
      have : (1 : ℝ) ≤ (2 : ℝ) * (h7.m : ℝ) := by nlinarith
      simpa [Nat.cast_mul, Nat.cast_ofNat] using (one_le_sqrt).2 this
    · apply mul_le_mul ?_ ?_ (by dsimp [house];positivity) (by dsimp [house];positivity)
      · refine Bound.pow_le_pow_right_of_le_one_or_one_le (Or.inl (by dsimp [house];simp))
      · apply mul_le_mul (by simp [pow_mul]) (by simp [pow_mul]) (by dsimp [house];positivity)
                (pow_nonneg (pow_nonneg (house_nonneg _) _) _)
  · nth_rw 2 [← mul_assoc]
    rw [mul_comm  ((1 + house h7.β') ^ (h7.n q)) (((sqrt ((2*h7.m)))) ^ (h7.n q))]
    simp only [mul_assoc]
    apply mul_le_mul ?_ ?_ (by dsimp [house];positivity) (by positivity)
    · refine pow_le_pow_left₀ (sqrt_nonneg _) (by rfl) (h7.n q)
    · apply mul_le_mul (by rfl) ?_ (by dsimp [house];positivity) (by dsimp [house];positivity)
      · simp only [← mul_assoc]
        apply mul_le_mul ?_ (by rfl) (by positivity) (by positivity)
        · rw [← mul_pow]
          refine pow_le_pow_left₀ (by dsimp [house];positivity) ?_ (h7.n q)
          · have : ((h7.m * 2) * h7.m) = (2 * h7.m ^ 2) := by grind
            rw [this]; clear this
            calc _ ≤ house h7.α' ^ (2 * h7.m ^ 2) * house h7.γ' ^ (2 * h7.m ^ 2) := ?_
                 _ ≤ max 1 ((house h7.α' ^ (2 * h7.m ^ 2) * house h7.γ' ^ (2 * h7.m ^ 2))) := ?_
            · apply Preorder.le_refl
            · simp only [le_sup_right]

lemma c₁_pow_sub_one_mul_c₁_pow_mul_c₁_pow_eq :
    ((h7.c₁ : ℤ) ^ (h7.n q - 1) * (h7.c₁ : ℤ) ^ (h7.m * q) * (h7.c₁ : ℤ) ^ (h7.m * q)) =
    ((h7.c₁ : ℤ) ^ (h7.n q - 1 - h7.k q u) * (h7.c₁ : ℤ) ^ (h7.m * q - a q t * h7.l q u) *
    (h7.c₁ : ℤ) ^ (h7.m * q - b q t * h7.l q u)) * ((h7.c₁ : ℤ) ^ h7.k q u *
    (h7.c₁ : ℤ) ^ (a q t * h7.l q u) * (h7.c₁ : ℤ) ^ (b q t * h7.l q u)) := by
  symm
  calc _ = ((h7.c₁ : ℤ) ^ (h7.n q - 1 - h7.k q u) * (h7.c₁ : ℤ) ^ h7.k q u) *
          ((h7.c₁ : ℤ) ^ (h7.m * q - a q t * h7.l q u) * (h7.c₁ : ℤ) ^ (a q t * h7.l q u)) *
          ((h7.c₁ : ℤ) ^ (h7.m * q - b q t * h7.l q u) * (h7.c₁ : ℤ) ^ (b q t * h7.l q u)) := ?_
       _ = _ := ?_
  · ring
  · simp_rw [← pow_add]
    have intCast_k_le_intCast_n_sub_one : (h7.k q u : ℤ) ≤ (h7.n q - 1 : ℤ) := by
      have := (finProdFinEquiv.symm u).2.isLt
      aesop
    rw [Nat.sub_add_cancel (by grind), Nat.sub_add_cancel
       (by simpa [mul_comm] using (Nat.mul_le_mul (((finProdFinEquiv.symm.toFun t).1).isLt)
         (((finProdFinEquiv.symm.toFun u).1).isLt))), Nat.sub_add_cancel (by simpa [mul_comm] using
        (Nat.mul_le_mul (((finProdFinEquiv.symm.toFun t).2).isLt)
        (((finProdFinEquiv.symm.toFun u).1).isLt)))]

lemma house_add_mul_le :
    house (h7.c₁ • (↑(a q t) + b q t • h7.β')) ≤ (|h7.c₁| * |(q : ℤ)|) * (1 + house (h7.β')) := by
  calc _ ≤ house (h7.c₁ • ((a q t : ℤ) : h7.K)) + house (h7.c₁ • ((b q t : ℤ) • h7.β')) := ?_
       _ ≤ house (h7.c₁ : h7.K) * house ((a q t : ℤ) : h7.K) + house (h7.c₁ : h7.K) *
           house ((b q t : ℤ) • h7.β') := ?_
       _ ≤ house (h7.c₁ : h7.K) * house ((a q t : ℤ) : h7.K) + house (h7.c₁ : h7.K) *
           (house ((b q t : ℤ) : h7.K) * house ( h7.β')) := ?_
       _ = |h7.c₁| * |(a q t : ℤ)| + |h7.c₁| * |(b q t : ℤ)| * house (h7.β') := ?_
       _ ≤ |h7.c₁| * |(q : ℤ)| + |h7.c₁| * |(q : ℤ)| * house h7.β' := ?_
       _ = |h7.c₁| * |(q : ℤ)| * (1 + house h7.β') := ?_
  · norm_cast; rw [smul_add]; apply house_add_le
  · refine add_le_add (by grind [house_mul_le]) (by grind [house_mul_le])
  · refine add_le_add (by grind)
      (mul_le_mul (le_refl _) (by grind [house_mul_le]) (house_nonneg _) (house_nonneg _))
  · rw [house_intCast]; rw [house_intCast]; rw [house_intCast]; rw [mul_assoc]
  · refine add_le_add (mul_le_mul (le_refl _) (mod_cast ((finProdFinEquiv.symm.toFun t).1).isLt)
      (Int.cast_nonneg (Int.zero_le_ofNat (a q t))) (Int.cast_nonneg  (abs_nonneg (h7.c₁)))) ?_
    · rw [mul_assoc, mul_assoc]
      apply mul_le_mul (by rfl) ?_ (mul_nonneg (by positivity) (house_nonneg _)) (by simp)
      · apply mul_le_mul (mod_cast ((finProdFinEquiv.symm.toFun t).2).isLt) (le_refl _)
          (house_nonneg _) (by simp)
  · rw [mul_add]; simp only [Int.cast_abs, mul_one]

/-! Moreover, the absolute value of the conjugates of the various coefficients is at most
  `c₂^n (q + q * |β|) ^ (n - 1) * |α| ^ (m q) * |γ| ^ (m q) ≤ c₃^n * n^((n - 1) / 2)`.
-/
include hq0 h2mq in
lemma house_matrixA_le : house ((algebraMap (𝓞 h7.K) h7.K) ((h7.A q) u t)) ≤
    (h7.c₃ ^ (h7.n q : ℝ) * (h7.n q : ℝ) ^ (((h7.n q : ℝ) - 1) / 2))  := by
  simp only [A, systemCoeffs, RingOfIntegers.restrict, RingOfIntegers.map_mk]
  calc _ = house (((h7.c₁ ^ (h7.n q - 1 - h7.k q u) * h7.c₁ ^ (h7.m * q - a q t * h7.l q u) *
           h7.c₁ ^ (h7.m * q - b q t * h7.l q u)) • (h7.c₁ ^ h7.k q u * h7.c₁ ^ (a q t * h7.l q u) *
           h7.c₁ ^ (b q t * h7.l q u))) • ((↑(a q t) + b q t • h7.β') ^ h7.k q u * h7.α' ^
           (a q t * h7.l q u) * h7.γ' ^ (b q t * h7.l q u))) := ?_
       _ = house ((h7.c₁ ^ ((h7.n q - 1) - h7.k q u) * h7.c₁ ^ (h7.m * q - a q t * h7.l q u) *
           (h7.c₁ : h7.K) ^ (h7.m * q - b q t * h7.l q u)) • (((h7.c₁ : h7.K) ^ h7.k q u) *
           ((a q t : h7.K) + (b q t) * h7.β') ^ h7.k q u * ((h7.c₁ : h7.K) ^ (a q t * h7.l q u)) *
           h7.α' ^ (a q t * h7.l q u) * ((h7.c₁ : h7.K) ^ (b q t * h7.l q u)) *
           h7.γ' ^ (b q t * h7.l q u))) := ?_
       _ ≤ house (((h7.c₁ : h7.K) ^ (h7.n q - 1 - h7.k q u) * (h7.c₁ : h7.K) ^
           (h7.m * q - a q t * h7.l q u) * (h7.c₁ : h7.K) ^ (h7.m * q - b q t * h7.l q u))) *
           house (h7.c₁ ^ (h7.k q u) • (↑(a q t) + (b q t) • h7.β') ^ (h7.k q u)) *
           house (h7.c₁ ^ (a q t * h7.l q u) • h7.α' ^ (a q t * h7.l q u)) *
           house (h7.c₁ ^ (b q t * h7.l q u) • h7.γ' ^ (b q t * h7.l q u)) := ?_
       _ ≤ house (((h7.c₁ : h7.K) ^ (h7.n q - 1 - h7.k q u) * (h7.c₁ : h7.K) ^
           (h7.m * q - a q t * h7.l q u) * (h7.c₁ : h7.K) ^ (h7.m * q - b q t * h7.l q u))) *
           house (h7.c₁ • (↑(a q t) + (b q t) • h7.β')) ^ (h7.k q u) * house (h7.c₁ • h7.α') ^
           (a q t * h7.l q u) * house (h7.c₁ • h7.γ') ^ (b q t * h7.l q u) := ?_
       _ ≤ house (((h7.c₁ : h7.K) ^ (h7.n q - 1 - h7.k q u) * (h7.c₁ : h7.K) ^
           (h7.m * q - a q t * h7.l q u) * (h7.c₁ : h7.K) ^ (h7.m * q - b q t * h7.l q u))) *
           house (h7.c₁ • (↑(a q t) + b q t • h7.β')) ^ (h7.n q - 1) *
           house (h7.c₁ • h7.α') ^ (h7.m * q) * house (h7.c₁ • h7.γ') ^ (h7.m * q) := ?_
       _ ≤ |(((h7.c₁) ^ (h7.n q - 1 - h7.k q u) * (h7.c₁) ^ (h7.m * q - a q t * h7.l q u) *
           (h7.c₁) ^ (h7.m * q - b q t * h7.l q u)))| * (|h7.c₁| *
           (|(q : ℤ)| * (1 + house (h7.β')))) ^ (h7.n q - 1) * (|h7.c₁| * house (h7.α')) ^
           (h7.m * (2 * (h7.m * h7.n q))) * (|h7.c₁| * house (h7.γ')) ^
           (h7.m * (2 * (h7.m * h7.n q))) := ?_
       _ = |(((h7.c₁) ^ (h7.n q - 1 - h7.k q u) * (h7.c₁) ^ (h7.m * q - a q t * h7.l q u) *
           (h7.c₁) ^ (h7.m * q - b q t * h7.l q u)))| * |h7.c₁ ^ (h7.n q - 1)| •
           (↑|↑q| * (1 + house h7.β')) ^ (h7.n q - 1) * |h7.c₁ ^ (h7.m * (2 * (h7.m * h7.n q)))| •
           house h7.α' ^ (h7.m * (2 * (h7.m * h7.n q))) * |h7.c₁ ^ (h7.m * (2 * (h7.m * h7.n q)))|
           • house h7.γ' ^ (h7.m * (2 * (h7.m * h7.n q))) := ?_
       _ ≤ |(((h7.c₁) ^ (h7.n q - 1 - h7.k q u) * (h7.c₁) ^ (h7.m * q - a q t * h7.l q u) *
           (h7.c₁) ^ (h7.m * q - b q t * h7.l q u)))| * ↑|h7.c₁| ^ ((h7.n q - 1) +
           (2 * h7.m * (2 * (h7.m * h7.n q)))) * (↑|↑q| ^ ((h7.n q ) - 1) * (1 + house h7.β') ^
           (h7.n q - 1) * house h7.α' ^ (h7.m * (2 * (h7.m * h7.n q))) *
           house h7.γ' ^ (h7.m * (2 * (h7.m * h7.n q)))) := ?_
       _ = |(h7.c₁) ^ (h7.n q - 1 - h7.k q u)| * |(h7.c₁) ^ (h7.m * q - a q t * h7.l q u)| *
           |(h7.c₁) ^ (h7.m * q - b q t * h7.l q u)| * ↑|h7.c₁| ^ ((h7.n q - 1) +
           (2 * h7.m * (2 * (h7.m * h7.n q)))) * (↑|↑q| ^ ((h7.n q)- 1) * (1 + house h7.β')
           ^ (h7.n q - 1) * house h7.α' ^ (h7.m * (2 * (h7.m * h7.n q))) * house h7.γ' ^
           (h7.m * (2 * (h7.m * h7.n q)))) := ?_
       _ = |(h7.c₁)| ^ (h7.n q - 1 - h7.k q u) * |(h7.c₁)| ^ (h7.m * q - a q t * h7.l q u) *
           |(h7.c₁)| ^ (h7.m * q - b q t * h7.l q u) * ↑|h7.c₁| ^ ((h7.n q - 1) +  (2 * h7.m *
           (2 * (h7.m * h7.n q)))) * (↑|↑q| ^ ((h7.n q) - 1) * (1 + house h7.β') ^ (h7.n q - 1) *
           house h7.α' ^ (h7.m * (2 * (h7.m * h7.n q))) *
           house h7.γ' ^ (h7.m * (2 * (h7.m * h7.n q)))) := ?_
       _ ≤ ↑(h7.c₂) ^ (h7.n q) * (↑|↑q| ^ ((h7.n q ) - 1) * (1 + house h7.β') ^ (h7.n q - 1) *
           house h7.α' ^ (h7.m * (2 * (h7.m * h7.n q))) *
           house h7.γ' ^ (h7.m * (2 * (h7.m * h7.n q)))) := ?_
       _ ≤ h7.c₃ ^ (h7.n q : ℝ) * ((sqrt (h7.n q)) ^ ((h7.n q : ℝ)- 1)) := ?_
       _ ≤ (h7.c₃ ^ (h7.n q : ℝ) * (h7.n q : ℝ) ^ (((h7.n q : ℝ) - 1) / 2)) := ?_
  · rw [c_coeffs]
    conv => enter [2, 1]; simp only [Int.zsmul_eq_mul];
    rw [← c₁_pow_sub_one_mul_c₁_pow_mul_c₁_pow_eq]
  · rw [smul_assoc]; simp; grind
  · simp only [nsmul_eq_mul, zsmul_eq_mul, Int.cast_pow,mul_assoc]
    apply le_trans (house_mul_le _ _) (mul_le_mul (by rfl) ?_ (house_nonneg _) (house_nonneg _))
    · rw [← mul_assoc, ← mul_assoc, ← mul_assoc]
      apply le_trans (house_mul_le _ _)
      rw [← mul_assoc]
      apply mul_le_mul (by grind [mul_assoc, house_mul_le]) (by rfl) (house_nonneg _)
        (mul_nonneg (house_nonneg _) (house_nonneg _))
  · simp only [mul_assoc]
    apply mul_le_mul (by rfl) ?_ (by dsimp [house];positivity) (by dsimp [house];positivity)
    · simp only [nsmul_eq_mul, zsmul_eq_mul, Int.cast_pow, ← mul_pow]
      apply mul_le_mul (house_pow_le _ _) ?_ (by dsimp [house];positivity)
        (by dsimp [house];positivity)
      · apply mul_le_mul (house_pow_le _ _) (house_pow_le _ _) (house_nonneg _)
          (pow_nonneg (house_nonneg _) _)
  · apply mul_le_mul ?_ ?_ (by dsimp [house];positivity) (by dsimp [house];positivity)
    · apply mul_le_mul ?_ ?_ (by dsimp [house];positivity) (by dsimp [house];positivity)
      · apply mul_le_mul (by rfl) ?_ (by dsimp [house];positivity) (house_nonneg _)
        · refine Bound.pow_le_pow_right_of_le_one_or_one_le
            (Or.inl ⟨one_le_house_of_isIntegral (isInt_β_bound_low _ _ _) (fun H ↦ ?_), ?_⟩)
          · simp only [zsmul_eq_mul, mul_eq_zero, Int.cast_eq_zero] at H
            cases H with
            | inl hp => apply h7.c₁_ne_zero; exact hp
            | inr hq => apply h7.β'_ne_zero q t 1; rw [pow_one]; exact hq
          · refine (Nat.le_sub_iff_add_le' (h7.one_le_n q hq0 h2mq)).mpr ?_
            · rw [add_comm]; exact (finProdFinEquiv.symm.toFun u).2.isLt
      · apply Bound.pow_le_pow_right_of_le_one_or_one_le
            (Or.inl ⟨one_le_house_of_isIntegral h7.isIntegral_c₁α h7.c₁α_ne_zero, ?_⟩)
        · rw [mul_comm h7.m q]
          apply mul_le_mul (((finProdFinEquiv.symm.toFun t).1).isLt)
           (((finProdFinEquiv.symm.toFun u).1).isLt) (zero_le _) (zero_le _)
    · apply Bound.pow_le_pow_right_of_le_one_or_one_le
        (Or.inl ⟨one_le_house_of_isIntegral h7.isIntegral_c₁γ h7.c₁γ_ne_zero, ?_⟩)
      · rw [mul_comm h7.m q]
        apply (mul_le_mul (((finProdFinEquiv.symm.toFun t).2).isLt)
          (((finProdFinEquiv.symm.toFun u).1).isLt) (zero_le _) (zero_le _))
  · apply mul_le_mul ?_ ?_ (by dsimp [house];positivity) (by dsimp [house];positivity)
    · apply mul_le_mul ?_ ?_ (by dsimp [house];positivity) (by dsimp [house];positivity)
      · apply mul_le_mul ?_ ?_ (by dsimp [house];positivity)
          (by simp only [abs_mul, abs_pow, Int.cast_mul, Int.cast_pow, Int.cast_abs]; positivity)
        ·  rw [← house_intCast (K := h7.K)];  simp
        · refine pow_le_pow_left₀ (house_nonneg _) ?_ (h7.n q - 1)
          · rw [← mul_assoc]; apply h7.house_add_mul_le q t
      · calc _ ≤ house (h7.c₁ • h7.α') ^ (h7.m * (2 * (h7.m * h7.n q))) := ?_
             _ ≤ (↑|h7.c₁| * house h7.α') ^ (h7.m * (2 * (h7.m * h7.n q))) := ?_
        · refine Bound.pow_le_pow_right_of_le_one_or_one_le
            (Or.inl ⟨one_le_house_of_isIntegral h7.isIntegral_c₁α h7.c₁α_ne_zero, ?_⟩)
          · apply mul_le_mul (by rfl) ?_ (by simp) (by simp)
            · exact (by have H := h7.q_le_two_mn q h2mq; rw [mul_assoc] at H; exact H )
        · refine pow_le_pow_left₀ (house_nonneg _) ?_ (h7.m * (2 * (h7.m * h7.n q)))
          · calc _ ≤ house (h7.c₁ : h7.K) * house (h7.α') := ?_
                 _ ≤ _ := ?_
            · grind [house_mul_le]
            · simp
    · calc _ ≤ house (h7.c₁ • h7.γ') ^ (h7.m * (2 * (h7.m * h7.n q))) := ?_
           _ ≤ (↑|h7.c₁| * house h7.γ') ^ (h7.m * (2 * (h7.m * h7.n q))) := ?_
      · refine Bound.pow_le_pow_right_of_le_one_or_one_le
          (Or.inl ⟨one_le_house_of_isIntegral h7.isIntegral_c₁γ h7.c₁γ_ne_zero, ?_⟩)
        · apply mul_le_mul (by rfl) (by grind [h7.q_le_two_mn q h2mq]) (by simp) (by simp)
      refine pow_le_pow_left₀ (house_nonneg _) ?_ (h7.m * (2 * (h7.m * h7.n q)))
      · calc _ ≤ house (h7.c₁ : h7.K)  * house (h7.γ') := ?_
             _ ≤ _ := ?_
        · grind [house_mul_le]
        · simp only [house_intCast, Int.cast_abs, le_refl]
  · rw [zsmul_eq_mul, zsmul_eq_mul, zsmul_eq_mul, mul_pow, mul_pow, mul_pow, mul_pow, mul_pow,
        abs_pow, abs_pow]; congr; all_goals simp
  · have := zsmul_mul_mul_distrib |(h7.c₁ ^ (h7.n q - 1))|
         |(h7.c₁ ^ (h7.m * (2 * (h7.m * h7.n q))))|
         |(h7.c₁ ^ (h7.m * (2 * (h7.m * h7.n q))))| ((↑|↑q| * (1 + house (h7.β'))) ^ (h7.n q - 1))
         ((house h7.α') ^ (h7.m * (2 * (h7.m * h7.n q))))
         ((house h7.γ') ^ (h7.m * (2 * (h7.m * h7.n q))))
    simp only [mul_assoc, zsmul_eq_mul] at *
    rw [← this, abs_pow, abs_pow, ← pow_add, ← pow_add]
    apply mul_le_mul (by simp) ?_ (by dsimp [house];positivity) (by simp)
    · apply mul_le_mul ?_ ?_ (by dsimp [house];positivity) (by simp)
      · rw [← pow_add, ← pow_add, Eq.symm (Nat.two_mul (h7.m * (2 * (h7.m * h7.n q))))]
        simp only [Int.cast_pow, Int.cast_abs, le_refl]
      · rw [mul_pow]; simp only [mul_assoc]; simp only [Nat.abs_cast, le_refl]
  · simp only [← pow_add, ← pow_add, Int.cast_abs, Int.cast_pow, Nat.abs_cast, abs_pow,
      ← pow_add, ← pow_add, ← pow_add, ← pow_add]
  · rw [abs_pow, abs_pow, abs_pow]; simp
  · apply mul_le_mul ?_ (by rfl) (by dsimp [house];positivity) (?_)
    · rw [← pow_add, ← pow_add, ← pow_add, Int.cast_abs, c₂, Int.cast_pow, Int.cast_abs, ← pow_mul]
      refine pow_le_pow_right₀ (mod_cast h7.one_le_abs_c₁) ?_
      · simp only [add_mul, add_mul, one_mul, mul_assoc,
          (Nat.two_mul (h7.m * (2 * (h7.m * h7.n q)))), add_assoc]
        refine Nat.add_le_add ?_ (Nat.add_le_add ((Nat.sub_le _ _).trans <| by
          simpa [mul_assoc] using Nat.mul_le_mul_left h7.m (h7.q_le_two_mn q h2mq))
            (Nat.add_le_add ((Nat.sub_le _ _).trans <| by
          simpa [mul_assoc] using Nat.mul_le_mul_left h7.m (h7.q_le_two_mn q h2mq)) (by simp)))
        · grind
    · apply pow_nonneg; exact mod_cast (le_trans Int.one_nonneg (h7.one_le_c₂))
  · simp_rw [h7.c₃_pow q, mul_assoc]
    apply mul_le_mul (by rfl) (h7.abs_q_pow_mul_house_le_c₃_pow q hq0 h2mq)
       (by dsimp [house];positivity) ?_
    · apply pow_nonneg; norm_cast; apply le_trans Int.one_nonneg (h7.one_le_c₂)
  · rw [le_iff_eq_or_lt]; left;
    have : sqrt (h7.n q) ^ ((h7.n q : ℝ) - 1) = (h7.n q : ℝ) ^ (((h7.n q : ℝ) - 1) / 2) := by
      nth_rw 1 [sqrt_eq_rpow, ← rpow_mul, mul_comm, mul_div]
      · simp only [mul_one]
      · simp only [Nat.cast_nonneg]
    rw [← this]

open NumberField

include hq0 h2mq in
lemma hM_ne_zero : h7.A q ≠ 0 := by
  intro H
  let u : Fin _ := ⟨0, h7.m_mul_n_pos q hq0 h2mq⟩
  let t : Fin _ := ⟨0, mul_pos hq0 hq0⟩
  have H_eval : (h7.A q u t).val = 0 := by rw [H]; rfl
  simp only [A, RingOfIntegers.restrict, zsmul_eq_mul, Int.cast_mul, Int.cast_pow] at H_eval
  have hβ : (↑(a q t) + b q t • h7.β' : h7.K) ≠ 0 := fun h ↦ h7.β'_ne_zero q t 1 (by grind)
  revert H_eval
  simp [h7.c₁_ne_zero, h7.alpha'_beta'_gamma'_ne_zero.1, h7.alpha'_beta'_gamma'_ne_zero.2.2]
  grind

include hq0 h2mq in
lemma m_mul_n_lt_q_mul_q : h7.m * h7.n q < q * q :=
  lt_of_lt_of_eq (by grind [h7.m_mul_n_pos q hq0 h2mq]) <|
  (h7.q_sq_eq_two_mn q h2mq).symm.trans (pow_two q)

variable [DecidableEq (h7.K →+* ℂ)]

/-- A non-trivial integer vector (in `𝓞 K`) residing in the kernel of the matrix `A`.
Its existence is guaranteed by Siegel's lemma (`exists_ne_zero_int_vec_house_le`). -/
abbrev η : Fin (q * q) → 𝓞 h7.K := (house.exists_ne_zero_int_vec_house_le h7.K (h7.A q)
  (h7.hM_ne_zero q hq0 h2mq) (mul_pos (Nat.zero_lt_succ (2 * h7.h + 1))
  (h7.one_le_n q hq0 h2mq)) (h7.m_mul_n_lt_q_mul_q q hq0 h2mq) (Fintype.card_fin _)
  (fun u t ↦ h7.house_matrixA_le q hq0 u t h2mq) (Fintype.card_fin _)).choose

/-- A real-valued bounding constant used to bound the norm (house) of the
solution vector `η`. -/
def c₄ : ℝ := (max 1 ((house.c₁ h7.K) * house.c₁ h7.K * 2 * h7.m)) * h7.c₃

/-!
`‖ηₖ‖ ≤ c₄ⁿ * n^((n - 1) / 2)`, for `1 ≤ k ≤ t`.
-/
open house in
include hq0 h2mq in
lemma house_eta_le_c₄_pow : house (algebraMap (𝓞 h7.K) h7.K (h7.η q hq0 h2mq t)) ≤
    h7.c₄ ^ (h7.n q : ℝ) * ((h7.n q : ℝ) ^ (((h7.n q : ℝ) + 1)/2)) := by
  calc _ ≤ house.c₁ h7.K * (house.c₁ h7.K * ↑(q * q) *
           (h7.c₃ ^ (h7.n q : ℝ) * (h7.n q : ℝ) ^ (((h7.n q : ℝ) - 1) / 2))) ^
           ((h7.m * h7.n q : ℝ) / (↑(q * q : ℝ) - ↑(h7.m * h7.n q ))) := ?_
       _ = (house.c₁ h7.K * (house.c₁ h7.K * 2 * h7.m * (h7.c₃ ^ (h7.n q : ℝ)) * ((h7.n q : ℝ) *
           (h7.n q : ℝ) ^ (((h7.n q : ℝ) - 1) / 2)))) := ?_
       _ ≤ h7.c₄ ^ (h7.n q : ℝ) * ((h7.n q : ℝ) ^ (((h7.n q : ℝ) + 1) / 2) : ℝ) := ?_
  · exact mod_cast ((house.exists_ne_zero_int_vec_house_le
    h7.K (h7.A q) (h7.hM_ne_zero q hq0 h2mq) (mul_pos (Nat.zero_lt_succ (2 * h7.h + 1))
    (h7.one_le_n q hq0 h2mq)) (h7.m_mul_n_lt_q_mul_q q hq0 h2mq) (Fintype.card_fin _)
    (fun u t ↦ h7.house_matrixA_le q hq0 u t h2mq) (Fintype.card_fin _)).choose_spec).2.2 t
  · have : (q * q : ℝ) = q^2 := mod_cast (pow_two ↑q).symm
    rw [← pow_two q, this, h7.q_sq_eq_two_mn q h2mq]
    have : (q ^ 2 : ℝ) = 2 * h7.m * h7.n q := mod_cast (h7.q_sq_eq_two_mn q h2mq)
    rw [this]
    have mul_div_sub_eq_one := h7.mul_div_sub_eq_one q hq0 h2mq
    nth_rw 2 [← Nat.cast_mul] at mul_div_sub_eq_one
    rw [mul_div_sub_eq_one, rpow_one, h7.mul_rpow_sub_one_div_two q hq0 h2mq, mul_eq_mul_left_iff]
    left
    rw [mul_assoc, mul_assoc, mul_assoc, mul_assoc, mul_assoc]
    have one_le_house_c₁ : 1 ≤ house.c₁ h7.K := one_le_mul_of_one_le_of_one_le (Nat.one_le_cast.mpr
      (Module.finrank_pos)) (one_le_mul_of_one_le_of_one_le (le_max_left _ _) (le_max_left _ _))
    refine (mul_right_inj' (by grind)).mpr ?_
    · grind [h7.mul_rpow_sub_one_div_two q hq0 h2mq, ← mul_assoc, ← mul_assoc, ← mul_assoc]
  · rw [h7.mul_rpow_sub_one_div_two q hq0 h2mq, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ ?_
    · rw [c₄, mul_rpow (le_of_lt (lt_of_lt_of_le (by norm_num) (le_max_left _ _)))
        (le_of_lt (lt_of_lt_of_le (by norm_num) h7.one_le_c₃))]
      refine mul_le_mul_of_nonneg_right ?_ ?_
      · have hn : (1 : ℝ) ≤ (h7.n q : ℝ) := mod_cast h7.one_le_n q hq0 h2mq
        have hpow : (max 1 (house.c₁ h7.K * house.c₁ h7.K * 2 * ↑h7.m) : ℝ) ≤
          (max 1 (house.c₁ h7.K * house.c₁ h7.K * 2 * ↑h7.m)) ^ (h7.n q : ℝ) := by
          simpa [Real.rpow_one] using (rpow_le_rpow_of_exponent_le (le_max_left (1 : ℝ) _) hn)
        exact (le_max_right (1 : ℝ) _).trans hpow
      · apply rpow_nonneg (le_trans zero_le_one h7.one_le_c₃)
    · apply rpow_nonneg; simp only [Nat.cast_nonneg]

end Setup
