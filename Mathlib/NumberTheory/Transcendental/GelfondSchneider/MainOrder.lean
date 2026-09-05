/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/

module

public import Mathlib.NumberTheory.Transcendental.GelfondSchneider.MainAlgSetup
public import Mathlib.Analysis.Analytic.Order

/-!
This PR is the third component in the formalization of the Gelfond-Schneider Theorem
(Hilbert's Seventh Problem). It connects the algebraically constructed auxiliary function `R(x)`
to its analytical properties, establishing the exact order of vanishing and the fundamental lower
bound on the norm of its non-zero derivative evaluation.

Following the argument in Loo-Keng Hua's "Introduction to Number Theory"
Chapter 17.9, equations (4) and (5)), we define the minimal non-vanishing derivative
order $r$ and scale the evaluation to an algebraic integer to compute its norm.
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

/-!
Since the numbers `ρ₁, ..., ρₜ` are distinct, the function `R(x)`
is not identically zero. For suppose otherwise, then on expanding the right
hand side of `R` we have `η₁ρ₁ + η₂ρ₂ᵏ + ... + ηₜρₜᵏ = 0`, a contradiction.
-/

lemma eq_iff_finProdFinEquiv_symm_ext (i j : Fin (q * q)) : i = j ↔
    (finProdFinEquiv.symm.1 i).1 = (finProdFinEquiv.symm.1 j).1 ∧
    ((finProdFinEquiv.symm.1 i).2 : Fin q) = (finProdFinEquiv.symm.1 j).2 := by
  rw [← Prod.ext_iff, Equiv.toFun_as_coe, EmbeddingLike.apply_eq_iff_eq]

include hirr htriv in
lemma rho_injective (i j : Fin (q * q)) (hij : i ≠ j) : ρ α β q i ≠ ρ α β q j := by
  rw [ne_eq, eq_iff_finProdFinEquiv_symm_ext q, not_and'] at hij
  simp only [ρ, not_or, ne_eq, mul_eq_mul_right_iff, not_or]
  constructor
  · by_cases Heq : (finProdFinEquiv.symm.1 i).2 = (finProdFinEquiv.symm.1 j).2
    · unfold a b
      rw [Heq]
      intro H
      apply (hij Heq)
      simp only [Equiv.toFun_as_coe, nsmul_eq_mul, add_left_inj, Nat.cast_inj] at H
      exact Fin.eq_of_val_eq H
    · let i2 : ℕ := (finProdFinEquiv.symm.toFun i).2 + 1
      let j2 : ℕ := (finProdFinEquiv.symm.toFun j).2 + 1
      let i1 : ℕ := (finProdFinEquiv.symm.toFun i).1 + 1
      let j1 : ℕ := (finProdFinEquiv.symm.toFun j).1 + 1
      rw [← ne_eq]
      change i1 + i2 • β ≠ j1 + j2 • β
      intros H
      apply hirr (i1 - j1) (j2 - i2)
      have : i1 + i2 • β = j1 + j2 • β ↔ (↑i1 - ↑j1) /(↑j2 - ↑i2 : ℂ) = β := by
        calc _ ↔ ↑i1 - ↑j1 + ↑i2 • β - ↑j2 • β = 0 := ?_
             _ ↔ ↑i1 - ↑j1 + (i2 - ↑j2 : ℂ) • β = 0 := ?_
             _ ↔ ↑i1 - ↑j1 = - ((i2 - ↑j2 : ℂ) • β) := ?_
             _ ↔ ↑i1 - ↑j1 = (↑j2 - ↑i2 : ℂ) • β := ?_
             _ ↔ (↑i1 - ↑j1) /(↑j2 - ↑i2 : ℂ) = β := ?_
        · grind
        · rw [sub_eq_add_neg]; simp only [nsmul_eq_mul]; rw [← neg_mul, add_assoc, ← add_mul]
          simp only [smul_eq_mul];rw [← sub_eq_add_neg]
        · rw [add_eq_zero_iff_eq_neg]
        · refine Eq.congr_right (?_); simp only [smul_eq_mul]; rw [← neg_mul];simp only [neg_sub]
        · rw [div_eq_iff, mul_comm,smul_eq_mul]
          intros HC
          apply (fun HC ↦ Heq (Fin.eq_of_val_eq (Nat.succ_inj.mp HC)))
          rw [sub_eq_zero] at HC; simp only [Nat.cast_inj] at HC; exact HC.symm
      rw [this] at H
      rw [H.symm]
      simp only [Int.cast_sub, Int.cast_natCast]
  · exact mt
      (fun h ↦ by simpa [exp_log htriv.1, exp_zero] using congrArg exp h) htriv.2

/-- The Vandermonde matrix of the exponents `ρ t` appearing in the auxiliary function `R`. -/
abbrev V := vandermonde (fun t ↦ ρ α β q t)

include hirr htriv in
lemma vandermonde_det_ne_zero : det (V α β q) ≠ 0 := by
  by_contra H
  rw [V, det_vandermonde_eq_zero_iff] at H
  obtain ⟨i, j, ⟨hij, hij'⟩⟩ := H
  apply rho_injective α β hirr htriv q i j hij' hij

open Differentiable Complex

/-- The auxiliary exponential function `R x = ∑ t, σ (η t) * exp (ρ t * x)`. -/
abbrev R : ℂ → ℂ := fun x ↦ ∑ t, (canonicalEmbedding K)
  ((algebraMap (𝓞 K) K) ((η (K := K) α β σ α' β' γ' hirr htriv habc q hq0 h2mq) t)) σ *
    exp (ρ α β q t * x)

/-!
We introduce the integral function
  `R(x) = η₁ e^(ρ₁ x) + … + ηₜ e^(ρₜ x)` (2)
where the coefficients `η₁, …, ηₜ` are determined by the following conditions.


Thus, we see from (2) that

  `R(x) = a_{n,ℓ}(x - ℓ)ⁿ + a_{n+1,ℓ}(x - ℓ)ⁿ⁺¹ + ⋯,    1 ≤ ℓ ≤ m,` (3)

where `a_{n,ℓ}, a_{n+1,ℓ}, ...` are not all zero. Hence, there must be a natural
number `r` such that `R⁽ᵏ⁾(ℓ) = 0, 0 ≤ k ≤ r - 1, 1 ≤ ℓ ≤ m`. But for
`1 ≤ ℓ₀ ≤ m` we have `R⁽ʳ⁾(ℓ₀) ≠ 0` so that we see from (3) that `r ≥ n`.
-/

lemma cexp_mul (c x : ℂ) : deriv (fun x ↦ cexp (c * x)) x = c * cexp (c * x) := by
  rw [deriv_cexp (by fun_prop), deriv_fun_mul (by fun_prop) (by fun_prop)]
  simp [deriv_const', deriv_id'', mul_comm]

theorem iteratedDeriv_R (k' : ℕ) :
    deriv^[k'] (fun x ↦ (R α β σ α' β' γ' hirr htriv habc q hq0 h2mq) x) =
    fun x ↦ ∑ t, (σ ((η (K := K) α β σ α' β' γ' hirr htriv habc q hq0 h2mq) t)) *
      exp (ρ α β q t * x) * (ρ α β q t)^k' := by
  induction k' with
  | zero => simp only [pow_zero, mul_one]; rfl
  | succ k hk =>
    rw [← iteratedDeriv_eq_iterate] at *
    simp only [iteratedDeriv_succ]
    conv => enter [1]; rw [hk]
    ext x
    rw [_root_.deriv, fderiv_fun_sum]
    · simp only [FunLike.coe_sum, Finset.sum_apply, fderiv_eq_smul_deriv,
      deriv_mul_const_field', deriv_const_mul_field', smul_eq_mul, one_mul]
      rw [Finset.sum_congr rfl]
      intros t ht
      · rw [mul_assoc, mul_assoc, mul_eq_mul_left_iff, map_eq_zero]; left
        rw [cexp_mul, mul_assoc, (pow_succ' (ρ α β q t) k)]
        · rw [mul_comm, mul_assoc, mul_eq_mul_left_iff, Eq.symm (pow_succ' (ρ α β q t) k)]
          left; rfl
    · intros i hi
      apply mul (by fun_prop) (differentiable_const (ρ α β q i ^ k))

lemma iteratedDeriv_R_eq_zero (hR : R α β σ α' β' γ' hirr htriv habc q hq0 h2mq = 0) (z : ℂ)
    (k' : ℕ) :
    deriv^[k'] (fun z ↦ R α β σ α' β' γ' hirr htriv habc q hq0 h2mq z) z = 0 := by
  rw [hR, ← iteratedDeriv_eq_iterate, iteratedDeriv]
  simp

lemma vecMul_V_eq_zero (hR : R α β σ α' β' γ' hirr htriv habc q hq0 h2mq = 0) :
    (V α β q).vecMul
      (fun t ↦ σ ((η (K := K) α β σ α' β' γ' hirr htriv habc q hq0 h2mq) t)) = 0 := by
  ext k
  have hk : deriv^[k] (fun x ↦ R α β σ α' β' γ' hirr htriv habc q hq0 h2mq x) 0 = 0 :=
    iteratedDeriv_R_eq_zero α β σ α' β' γ' hirr htriv habc q hq0 h2mq (hR := hR) _ _
  rw [iteratedDeriv_R α β σ α' β' γ' hirr htriv habc q hq0 h2mq k] at hk
  simpa [V, vecMul, dotProduct, vandermonde_apply, of_apply] using hk

include hirr htriv in
lemma ηvec_eq_zero (hVecMulEq0 : (V α β q).vecMul
      (fun t ↦ σ ((η (K := K) α β σ α' β' γ' hirr htriv habc q hq0 h2mq) t)) = 0) :
    (fun t ↦ σ ((η (K := K) α β σ α' β' γ' hirr htriv habc q hq0 h2mq) t)) = 0 := by
  apply eq_zero_of_vecMul_eq_zero
    (vandermonde_det_ne_zero α β hirr htriv q) hVecMulEq0

lemma hbound_sigma : η (K := K) α β σ α' β' γ' hirr htriv habc q hq0 h2mq ≠ 0 :=
  (house.exists_ne_zero_int_vec_house_le K (A α' β' γ' q)
    (A_ne_zero α β σ α' β' γ' hirr htriv habc q hq0 h2mq)
    (Nat.mul_pos (one_le_m K) (n_one_le q hq0 h2mq))
    ((mul_assoc 2 _ _).symm ▸ lt_mul_of_one_lt_left
      (Nat.mul_pos (one_le_m K) (n_one_le q hq0 h2mq)) Nat.one_lt_two
      |>.trans_eq ((Nat.mul_div_cancel' h2mq).trans (pow_two q))) (Fintype.card_fin _)
    (fun u t ↦ house_matrixA_le α β σ α' β' γ' hirr htriv habc q hq0 u t h2mq)
    (Fintype.card_fin _)).choose_spec.1

include hirr htriv in
lemma R_ne_zero : R α β σ α' β' γ' hirr htriv habc q hq0 h2mq ≠ 0 := by
  intro H
  have HC := ηvec_eq_zero α β σ α' β' γ' hirr htriv habc q hq0 h2mq
    (vecMul_V_eq_zero α β σ α' β' γ' hirr htriv habc q hq0 h2mq H)
  apply hbound_sigma α β σ α' β' γ' hirr htriv habc q hq0 h2mq
  ext t
  simpa [η, FaithfulSMul.algebraMap_eq_zero_iff] using congr_fun HC t

omit [DecidableEq (K →+* ℂ)] in
include htriv habc in
lemma systemCoeffs_map_eq_exp_mul :
  Complex.exp (ρ α β q t * l q u) * ((ρ α β q t) ^ (k q u : ℕ) *
  Complex.log α ^ (-(k q u) : ℤ)) = σ (systemCoeffs α' β' γ' q u t) := by
  calc _ = cexp (ρ α β q t * l q u) * (((↑(a q t) + ↑(b q t) • β) *
          Complex.log α) ^ (k q u : ℕ) * Complex.log α ^ (-↑(k q u) : ℤ)) := ?_
       _ = cexp (ρ α β q t * l q u) * ((↑(a q t) + ↑(b q t) • β) ^ (k q u : ℕ) *
          ((Complex.log α) ^ (k q u : ℕ) * Complex.log α ^ (-(k q u) : ℤ))) := ?_
       _ = cexp (ρ α β q t * l q u) * ((↑(a q t) + ↑(b q t) • β) ^ (k q u : ℕ)) := ?_
       _ = σ (systemCoeffs α' β' γ' q u t) := ?_
  · nth_rw 2 [ρ]
  · rw [mul_pow, mul_assoc]
  ·  have h_log_ne : Complex.log α ≠ 0 :=
      mt (fun h ↦ by simpa [exp_log htriv.1, exp_zero] using congrArg Complex.exp h) htriv.2
     aesop
  · rw [habc.2.1, mul_comm, systemCoeffs, mul_assoc]
    simp only [nsmul_eq_mul, map_pow, map_add, map_natCast, map_mul, mul_eq_mul_left_iff,
      pow_eq_zero_iff', ne_eq]; left
    rw [← habc.1, ← habc.2.2, ρ, ← cpow_nat_mul]
    have : α ^ ((a q t * l q u)) * α ^ (↑(b q t * l q u) * β) =
           α ^ ((a q t * l q u) + (↑(b q t * l q u) * β)) := by
      rw [cpow_add _ _ htriv.1]
      · rw [cpow_nat_mul]
        simp only [mul_eq_mul_right_iff, pow_eq_zero_iff', cpow_eq_zero_iff, ne_eq, mul_eq_zero,
          not_or]; left; rw [cpow_nat_mul, cpow_natCast]; exact pow_mul' α (a q t) (l q u)
    rw [this]; clear this
    · rw [cpow_def_of_ne_zero htriv.1 _]
      · congr 1; rw [mul_rotate, mul_assoc]; simp only [nsmul_eq_mul, Nat.cast_mul]
        nth_rw 3 [mul_comm]; rw [mul_assoc]; grind

include hq0 h2mq htriv habc in
lemma systemCoeffs_deriv :
    (Complex.log α)^(-(k q u) : ℤ) *
      deriv^[k q u] (R α β σ α' β' γ' hirr htriv habc q hq0 h2mq) (l q u) =
    ∑ t, σ ↑((η (K := K) α β σ α' β' γ' hirr htriv habc q hq0 h2mq) t) *
      σ (systemCoeffs α' β' γ' q u t) := by
  rw [iteratedDeriv_R, mul_sum, Finset.sum_congr rfl]
  intros t ht
  rw [mul_assoc, mul_comm, mul_assoc]
  simp only [mul_eq_mul_left_iff, map_eq_zero, FaithfulSMul.algebraMap_eq_zero_iff]
  left
  have := systemCoeffs_map_eq_exp_mul α β σ α' β' γ' htriv habc q u t
  unfold l at this
  rw [mul_assoc]
  unfold l
  exact this

include htriv habc in
lemma coeffs_mulVec_A_eq : σ (cCoeffs α' β' γ' q) * ((Complex.log α)^ (-(k q u) : ℤ) *
    deriv^[k q u] (R α β σ α' β' γ' hirr htriv habc q hq0 h2mq) (l q u)) =
    σ ((A α' β' γ' q *ᵥ (η (K := K) α β σ α' β' γ' hirr htriv habc q hq0 h2mq)) u) := by
  rw [systemCoeffs_deriv α β σ α' β' γ' hirr htriv habc q hq0 u h2mq]
  unfold Matrix.mulVec dotProduct
  simp only [← map_mul, ← map_sum]
  congr 1
  rw [Finset.mul_sum]
  simp only [Int.cast_mul, Int.cast_pow, map_sum, map_mul]
  apply Finset.sum_congr rfl
  intros x hx
  rw [map_A]
  ring

include htriv habc in
lemma coeffs_mul_deriv_eq_zero : σ (cCoeffs α' β' γ' q) * ((Complex.log α)^ (-(k q u) : ℤ) *
    deriv^[k q u] (R α β σ α' β' γ' hirr htriv habc q hq0 h2mq) (l q u)) = 0 := by
  rw [coeffs_mulVec_A_eq]
  have hMt0 := (house.exists_ne_zero_int_vec_house_le K (A α' β' γ' q)
    (A_ne_zero α β σ α' β' γ' hirr htriv habc q hq0 h2mq)
    (Nat.mul_pos (one_le_m K) (n_one_le q hq0 h2mq))
    ((mul_assoc 2 _ _).symm ▸ lt_mul_of_one_lt_left
      (Nat.mul_pos (one_le_m K) (n_one_le q hq0 h2mq)) Nat.one_lt_two
      |>.trans_eq ((Nat.mul_div_cancel' h2mq).trans (pow_two q))) (Fintype.card_fin _)
    (fun u t ↦ house_matrixA_le α β σ α' β' γ' hirr htriv habc q hq0 u t h2mq)
    (Fintype.card_fin _)).choose_spec.2.1
  simp [η, FaithfulSMul.algebraMap_eq_zero_iff]
  aesop

/-!After defining the auxiliary function R we consider the
first nonzero derivative at an integer ℓ₀.

  `(log α)⁻ʳ R⁽ʳ⁾(ℓ₀) = ρ`.

where r is the smallest integer such that `R⁽ʳ⁾(ℓ₀) ≠ 0`.-/

lemma exists_min_analyticOrderAt :
  let s : Finset (Fin (m K)) := Finset.univ
  ∃ l₀' ∈ s, (∃ y,
    (analyticOrderAt (R α β σ α' β' γ' hirr htriv habc q hq0 h2mq) (l₀' + 1)) = y ∧
  (∀ (l' : Fin (m K)), l' ∈ s → y ≤
    (analyticOrderAt (R α β σ α' β' γ' hirr htriv habc q hq0 h2mq) (l' + 1)))) := by
  intro s
  obtain ⟨x, hx, hmin⟩ := Finset.exists_min_image s
   (fun x ↦ analyticOrderAt (R α β σ α' β' γ' hirr htriv habc q hq0 h2mq) (x + 1))
   ⟨⟨0, one_le_m K⟩, Finset.mem_univ _⟩
  exact ⟨x, hx, _, rfl, hmin⟩

/-- A point of `Fin m` at which `R` vanishes to minimal order. -/
abbrev l₀' : Fin (m K) :=
  (exists_min_analyticOrderAt α β σ α' β' γ' hirr htriv habc q hq0 h2mq).choose

/-- The defining property of `l₀'`: the order of `R` at `l₀' + 1` is minimal among
`1, …, m`. -/
abbrev l₀Prop :=
  (exists_min_analyticOrderAt α β σ α' β' γ' hirr htriv habc q hq0 h2mq).choose_spec.2

/-- The order of vanishing of `R` at `l₀' + 1`, as an element of `ℕ∞`. -/
abbrev r' := (l₀Prop α β σ α' β' γ' hirr htriv habc q hq0 h2mq).choose

lemma r'_spec :
    let s : Finset (Fin (m K)) := Finset.univ
    analyticOrderAt (R α β σ α' β' γ' hirr htriv habc q hq0 h2mq)
        ↑↑(l₀' α β σ α' β' γ' hirr htriv habc q hq0 h2mq + 1 : ℂ) =
      r' α β σ α' β' γ' hirr htriv habc q hq0 h2mq ∧
    ∀ l' ∈ s, r' α β σ α' β' γ' hirr htriv habc q hq0 h2mq ≤
      analyticOrderAt (R α β σ α' β' γ' hirr htriv habc q hq0 h2mq) (↑↑l' + 1) :=
  (l₀Prop α β σ α' β' γ' hirr htriv habc q hq0 h2mq).choose_spec

end GelfondSchneider
