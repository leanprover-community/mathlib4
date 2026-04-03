/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.NumberTheory.NumberField.House

/-!
# Hilbert's Seventh Problem (Gelfond–Schneider Theorem)
The goal of this file is to formalize a proof of the **Gelfond–Schneider Theorem**, which solves
Hilbert’s Seventh Problem: namely, that for algebraic numbers `α ≠ 0, 1` and irrational algebraic
`β`, the number `α ^ β` is transcendental.

## Main results
* `gelfondSchneider`: If `α` and `β` are algebraic, `α ≠ 0`, `α ≠ 1`, and `β` is irrational, then
  `α ^ β` is transcendental.

## Implementation details
We follow the proof in Keng’s *Introduction to Number Theory*, Chapter 17, Section 5, p.488 - 493.

The argument proceeds by contradiction. The core of the proof is an auxiliary function lemma, where
we construct a nonzero integer linear combination of exponential functions that vanishes to high
order at several algebraic points.

This specific file handles the foundational algebraic setup:
1. Constructing a common number field `K` of degree `h` containing `α, β, γ`.
2. Defining the structural parameters `m = 2h + 2` and `n = q^2 / (2m)`.
3. Establishing the common denominator scaling factor `c₁` such that `c₁α`, `c₁β`, and `c₁γ`
   are all algebraic integers in `K`.
4. Formulating the homogeneous linear system matrix `A` with scaled entries residing strictly
   in the ring of integers `𝓞 K`, ready for Siegel's Lemma.

## References
Loo-Keng Hua, Introduction to Number Theory, Springer, 1982. Chapter XII (§13).
A. O. Gelfond (1934), *Sur le septième Problème de Hilbert
T. Schneider (1935), *Transzendenzuntersuchungen periodischer Funktionen*
-/

@[expose] public section

open BigOperators Module.Free Fintype NumberField Embeddings FiniteDimensional
   Matrix Set Polynomial Finset IntermediateField Complex AnalyticAt

noncomputable section

/-!
Suppose that `α, β, γ` lie in an algebraic field `K` with degree `h`.
-/

lemma isNumberField_adjoin_of_isAlgebraic (α β γ : ℂ) (hα : IsAlgebraic ℚ α) (hβ : IsAlgebraic ℚ β)
    (hγ : IsAlgebraic ℚ γ) : NumberField (adjoin ℚ {α, β, γ}) where
  to_charZero := charZero_of_injective_algebraMap (algebraMap ℚ _).injective
  to_finiteDimensional := finiteDimensional_adjoin fun _ hx ↦ by
    rcases hx with rfl | rfl | rfl
    exacts [isAlgebraic_iff_isIntegral.1 hα, isAlgebraic_iff_isIntegral.1 hβ,
      isAlgebraic_iff_isIntegral.1 hγ]

lemma exists_common_field_of_isAlgebraic (α β γ : ℂ) (hα : IsAlgebraic ℚ α) (hβ : IsAlgebraic ℚ β)
    (hγ : IsAlgebraic ℚ γ) : ∃ (K : Type) (_ : Field K) (_ : NumberField K) (σ : K →+* ℂ)
    (_ : DecidableEq (K →+* ℂ)), ∃ (α' β' γ' : K), α = σ α' ∧ β = σ β' ∧ γ = σ γ' := by
  refine ⟨adjoin ℚ {α, β, γ}, ?_⟩
  let σ : ↥(adjoin ℚ {α, β, γ}) →+* ℂ :=
    { toFun := fun x ↦ x.1, map_one' := rfl, map_mul' := fun _ _ ↦ rfl,
      map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
  refine ⟨inferInstance, isNumberField_adjoin_of_isAlgebraic α β γ hα hβ hγ, σ,
    Classical.typeDecidableEq _, ⟨⟨α, ?_⟩, ⟨β, ?_⟩, ⟨γ, ?_⟩, ?_⟩⟩
  · apply subset_adjoin
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or]
  · apply subset_adjoin
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true]
  · apply subset_adjoin
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_true]
  · dsimp [σ]
    exact ⟨rfl, ⟨rfl, rfl⟩⟩

namespace GelfondSchneider

/-!
Let `α` and `β` be algebraic numbers with `α ≠ 0, 1` and `β` irrational. We prove that `αᵇ` is
transcendental by contradiction. Suppose `γ = αᵇ = e^(β log α)` is also algebraic.
-/

variable {K : Type} [Field K] (α : ℂ) (β : ℂ) (σ : K →+* ℂ) (α' : K)
  (β' : K) (γ' : K) (hirr : ∀ i j : ℤ, β ≠ i / j) (htriv : α ≠ 0 ∧ α ≠ 1) (hα : IsAlgebraic ℚ α)
  (hβ : IsAlgebraic ℚ β) (habc : α = σ α' ∧ β = σ β' ∧ α ^ β = σ γ') (hd : DecidableEq (K →+* ℂ))

include htriv habc in
lemma alpha'_ne_one : α' ≠ 1 := fun h ↦
  htriv.2 <| by simpa [habc.1, map_one] using congrArg σ h

include htriv in
lemma alpha_gamma_pow_beta_ne_zero : α ^ β ≠ 0 :=
  fun H ↦ htriv.1 ((cpow_eq_zero_iff α β).mp H).1

include hirr in
lemma beta_ne_zero : β ≠ 0 :=
  fun H ↦ hirr 0 1 (by simpa [div_one] using H)

include htriv habc hirr in
lemma alpha'_beta'_gamma'_ne_zero : α' ≠ 0 ∧ β' ≠ 0 ∧ γ' ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> intro H
  · exact htriv.1 (by simp [habc.1, H, map_zero σ])
  · exact beta_ne_zero β hirr (by simp [habc.2.1, H, map_zero σ])
  · exact alpha_gamma_pow_beta_ne_zero α β htriv (by simp [habc.2.2, H, map_zero σ])

include htriv habc hirr in
lemma beta'_ne_zero : β' ≠ 0 := (alpha'_beta'_gamma'_ne_zero α β σ α' β' γ' hirr htriv habc).2.1


include htriv in
lemma log_α_ne_zero : log α ≠ 0 :=
  mt (fun h ↦ by simpa [exp_log htriv.1, exp_zero] using congrArg exp h) htriv.2

open Complex

lemma IsIntegral_assoc {x y : ℤ} (z : ℤ) (α : K) (ha : IsIntegral ℤ (z • α)) :
    IsIntegral ℤ ((x * y * z : ℤ) • α) := by
  simpa [Int.cast_mul, zsmul_eq_mul, mul_assoc] using IsIntegral.smul (x * y) ha

variable [NumberField K]

lemma exists_int_smul_isIntegral (α : K) :
    ∃ k : ℤ, k ≠ 0 ∧ IsIntegral ℤ (k • α) := by
  obtain ⟨y, hy, hf⟩ := exists_integral_multiples ℤ ℚ (L := K) {α}
  refine ⟨y, hy, hf α (mem_singleton_self _)⟩

/-- A choice of a non-zero integer `c` such that `c • α` is an algebraic integer.
The existence of such an integer is guaranteed for any algebraic number. -/
def c₀ (α : K) :
    {c : ℤ // c ≠ 0 ∧ IsIntegral ℤ (c • α)} :=
  ⟨(exists_int_smul_isIntegral α).choose, (exists_int_smul_isIntegral α).choose_spec⟩

/-- An abbreviation for the explicit integer value extracted from `c₀ α`. -/
abbrev c₀Coeff (α : K) : ℤ := (c₀ α : ℤ)

lemma c₀Coeff_ne_zero (α : K) : c₀Coeff α ≠ 0 := (c₀ α).2.1

/-- c₁ is a positive integer such that c₁ • α', c₁ • β', c₁ • γ' are algebraic integers -/
def c₁ : ℤ := abs (c₀ α' * c₀ β' * c₀ γ')

include α' β' γ' in
lemma one_le_c₁ : 1 ≤ (c₁ α' β' γ') := by
  simpa [c₁] using Int.one_le_abs <| mul_ne_zero (mul_ne_zero (c₀Coeff_ne_zero α')
    (c₀Coeff_ne_zero β')) (c₀Coeff_ne_zero γ')

lemma one_le_abs_c₁ : 1 ≤ |c₁ α' β' γ'| :=
  Int.one_le_abs (Ne.symm (Int.ne_of_lt (one_le_c₁ α' β' γ')))

lemma isIntegral_c₁α : IsIntegral ℤ (c₁ α' β' γ' • α') := by
  have h := IsIntegral_assoc (x := c₀Coeff γ') (y := c₀Coeff β') (c₀Coeff α') α'
    ((c₀ α').2.2)
  conv => enter [2]; rw [c₁, mul_comm, mul_comm (c₀Coeff α')
    (c₀Coeff β'), ← mul_assoc]
  rcases abs_choice (c₀Coeff γ' * c₀Coeff β' * c₀Coeff α') with H1 | H2
  · rw [H1]; exact h
  · rw [H2]; rw [← IsIntegral.neg_iff, neg_smul, neg_neg]; exact h

lemma isIntegral_c₁β : IsIntegral ℤ (c₁ α' β' γ' • β') := by
  have h := IsIntegral_assoc (x := c₀Coeff γ') (y := c₀Coeff α') (c₀Coeff β') β'
    ((c₀ β').2.2)
  rw [c₁, mul_comm, ← mul_assoc]
  rcases abs_choice (c₀Coeff γ' * c₀Coeff α' * c₀Coeff β') with H1 | H2
  · rw [H1]; exact h
  · rw [H2]; rw [← IsIntegral.neg_iff, neg_smul, neg_neg]; exact h

lemma isIntegral_c₁γ : IsIntegral ℤ (c₁ α' β' γ' • γ') := by
  have h := IsIntegral_assoc (x := c₀Coeff α') (y := c₀Coeff β') (c₀Coeff γ') γ'
    ((c₀ γ').2.2)
  rw [c₁]
  rcases abs_choice (c₀Coeff α' * c₀Coeff β' *
    c₀Coeff γ') with H1 | H2
  · rw [H1]; exact h
  · rw [H2]; rw [← IsIntegral.neg_iff, neg_smul, neg_neg]; exact h

/-!
Let `m = 2h + 2`, and `n = q^ 2 / (2 * m)`, where $q^2 = t $ is a square of a natural number
and is a multiple of $2m.$  -/

/-- The finrank of the field extension `K` -/
def h : ℕ := Module.finrank ℚ K

/-- A parameter `m` dependent on the degree `h = [K : ℚ]`. -/
def m : ℕ := 2 * h (K := K) + 2

lemma one_le_m : 1 ≤ m (K := K) := Nat.succ_le_succ (Nat.zero_le (2 * h (K := K) + 1))

variable (q : ℕ) (hq0 : 0 < q)

/-- A target bound parameter `n` dependent on a free parameter `q`. -/
def n : ℕ := q ^ 2 / (2 * m (K := K))

variable (u : Fin (m (K := K) * n (K := K) q)) (t : Fin (q * q))

-- `a, b, k, l` are values that depend on the context variables `t` and `u`.

/-- A variable `a` that satisfies `1 ≤ a ≤ q`. -/
def a : ℕ := (finProdFinEquiv.symm.toFun t).1 + 1

/-- A variable `b` that satisfies `1 ≤ b ≤ q`. -/
def b : ℕ := (finProdFinEquiv.symm.toFun t).2 + 1

/-- Also, let `ρ₁, ρ₂, …, ρₜ` represent the `t` numbers
  `(a + bβ) log α,  1 ≤ a ≤ q, 1 ≤ b ≤ q.` -/
def ρ : ℂ := (a q t + (b q t • β)) * Complex.log α

/-!
We introduce the integral function
  `R(x) = η₁ e^(ρ₁ x) + … + ηₜ e^(ρₜ x)`
where the coefficients `η₁, …, ηₜ` are determined by the following conditions.
The function `R` is defined in the next file.

We solve the system of `mn` homogeneous linear equations
  `(log α)⁻ᵏ R⁽ᵏ⁾(l) = 0,  0 ≤ k ≤ n - 1, 1 ≤ l ≤ m`
in the `t = 2mn` unknowns `η₁, …, ηₜ`. It follows from
`house.exists_ne_zero_int_vec_house_le` that there is a non-trivial set of integer
solutions `η₁, …, η₂` in `K`.
-/

/-!
The coefficients are in `K` and
  `(log α)⁻ᵏ ((a + bβ) log α)ᵏ e^(l(a + bβ) log α) = (a + bβ)ᵏ αᵃˡ γᵇˡ`
for `1 ≤ l ≤ m, 1 ≤ a, b ≤ q, 0 ≤ k ≤ n - 1`.-/

/-- A variable `k` that satisfies 0 ≤ k ≤ n - 1 -/
def k : ℕ := (finProdFinEquiv.symm.toFun u).2

/-- A variable `l` that satisfies 1 ≤ l ≤ m -/
def l : ℕ := (finProdFinEquiv.symm.toFun u).1 + 1

/-- The core algebraic coefficient appearing in the evaluation of the `k`-th derivative
of the auxiliary function at point `l`. Evaluates to `(a + bβ')^k * α'^(al) * γ'^(bl)`. -/
abbrev systemCoeffs : K :=
  (a q t + b q t • β') ^ (k q u) * α' ^ (a q t * l q u) * γ' ^ (b q t * l q u)

variable (h2mq : 2 * m (K := K) ∣ q ^ 2)

include hq0 h2mq in
lemma one_le_n : 1 ≤ n (K := K) q := by
  simp [n, (Nat.one_le_div_iff (by positivity [one_le_m (K := K)])).2
    (Nat.le_of_dvd (Nat.pow_pos hq0) h2mq)]

/-!
Let `c₁, c₂, …` be natural numbers independent of `n`. There exists `c₁` such that
`c₁ α, c₁ β, c₁ γ` are integers in `K`.
-/

/-- A combined integer scaling factor `c₁^(n-1 + 2mq)` applied to the linear system to clear
all denominators and ensure the resulting matrix entries are algebraic integers. -/
abbrev c_coeffs (q : ℕ) := c₁ α' β' γ' ^ (n (K := K) q - 1) * c₁ α' β' γ' ^ (m (K := K) * q) *
  c₁ α' β' γ' ^ (m (K := K) * q)

/-- An unscaled sub-component of the matrix coefficients, used to establish intermediate
integrality bounds during the construction of the auxiliary function. -/
abbrev c_coeffs0 (q : ℕ) (u : Fin (m (K := K) * n (K := K) q)) (t : Fin (q * q)) :=
  c₁ α' β' γ' ^ (k q u : ℕ) * c₁ α' β' γ' ^ (a q t * l q u)
  * c₁ α' β' γ' ^ (b q t * l q u)

lemma isIntegral_c₁_pow_smul_pow (u : K) (n k a l : ℕ) (hnk : a * l ≤ n * k)
    (H : IsIntegral ℤ (↑(c₁ α' β' γ') * u)) :
    IsIntegral ℤ (c₁ α' β' γ' ^ (n * k) • u ^ (a * l)) := by
  rw [zsmul_eq_mul, Int.cast_pow, ← Nat.sub_add_cancel hnk, pow_add, mul_assoc, ← mul_pow]
  exact IsIntegral.mul (IsIntegral.pow (IsIntegral.Cast (c₁ α' β' γ')) (n * k - a * l))
    (IsIntegral.pow H (a * l))

lemma isIntegral_c₁_pow_smul_α'_pow : IsIntegral ℤ
    (c₁ α' β' γ' ^ (a q t * l q u) • (α' ^ (a q t * l q u))) :=
  isIntegral_c₁_pow_smul_pow _ _ _ α' (a q t) (l q u) (a q t) (l q u) (by rfl)
    (by grind [isIntegral_c₁α])

lemma isIntegral_c₁_pow_smul_γ'_pow : IsIntegral ℤ (c₁ α' β' γ' ^ (b q t * l q u) •
    (γ'^ (b q t * (l q u)))) :=
  isIntegral_c₁_pow_smul_pow _ _ _ γ' (b q t) (l q u) (b q t) (l q u) (by rfl)
    (by grind [isIntegral_c₁γ])

lemma isIntegral_c₁_pow_smul_α'_pow' :
    IsIntegral ℤ (c₁ α' β' γ' ^ (m (K := K) * q) • (α' ^ (a q t * l q u))) :=
    isIntegral_c₁_pow_smul_pow _ _ _ α' (m (K := K)) q (a q t) (l q u)
  (by
    have h1 : a q t ≤ q := ((finProdFinEquiv.symm.toFun t).1).isLt
    have h2 : l q u ≤ m (K := K) := ((finProdFinEquiv.symm.toFun u).1).isLt
    exact mul_comm q (m (K := K)) ▸ Nat.mul_le_mul h1 h2) <| by grind [isIntegral_c₁α]

lemma isIntegral_c₁_pow_smul_γ'_pow' :
    IsIntegral ℤ (c₁ α' β' γ' ^ (m (K := K) * q) • (γ'^ (b q t * l q u))) :=
    isIntegral_c₁_pow_smul_pow _ _ _ γ' (m (K := K)) q (b q t) (l q u)
  (by
    have h1 : b q t ≤ q := ((finProdFinEquiv.symm.toFun t).2).isLt
    have h2 : l q u ≤ m (K := K) := ((finProdFinEquiv.symm.toFun u).1).isLt
    exact mul_comm q (m (K := K)) ▸ Nat.mul_le_mul h1 h2) <| by grind [isIntegral_c₁γ]

include α' β' γ' in
lemma c_coeffs_neq_zero : c_coeffs α' β' γ' q ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero  _ (Ne.symm (Int.ne_of_lt (one_le_c₁ α' β' γ'))))
  (pow_ne_zero _ (Ne.symm (Int.ne_of_lt (one_le_c₁ α' β' γ')))))
  (pow_ne_zero _ (Ne.symm (Int.ne_of_lt (one_le_c₁ α' β' γ'))))

lemma isIntegral_c₁_pow_smul_add_smul_pow (n : ℕ) (k : ℕ) (hkn : k ≤ n - 1) (a : ℕ) (b : ℕ) :
    IsIntegral ℤ (c₁ α' β' γ' ^ (n - 1) • (↑a + ↑b • β') ^ k) := by
  rw [zsmul_eq_mul, Int.cast_pow, ← Nat.sub_add_cancel hkn, pow_add, mul_assoc, ← mul_pow, mul_add]
  refine IsIntegral.mul (IsIntegral.pow (IsIntegral.Cast _ ) _)
    (IsIntegral.pow (IsIntegral.add ?_ ?_) _)
  · exact IsIntegral.mul (IsIntegral.Cast _) (IsIntegral.Nat _)
  · rw [nsmul_eq_mul, ← mul_assoc, mul_comm (c₁ α' β' γ' : K), mul_assoc]
    exact IsIntegral.mul (IsIntegral.Nat _) (by grind [isIntegral_c₁β])

/-!
Multiplying the system by
`c₁^(n-1) c₁^(mq) c₁^ (mq) = c₁^(n-1+2mq) ≤ (c₂^n)` ensures the coefficients are integers in `K`. -/

lemma zsmul_mul_mul_distrib {K : Type} [Field K] (a b c : ℤ) (x y z : K) :
    ((a * b) * c) • ((x * y) * z) = a • x * b • y * c • z := by
  simp [zsmul_eq_mul]; ring

open Nat in
lemma c₁IsInt : IsIntegral ℤ (c_coeffs α' β' γ' q • systemCoeffs α' β' γ' q u t) := by
  rw [zsmul_mul_mul_distrib, mul_assoc]
  refine IsIntegral.mul ?_ (IsIntegral.mul (isIntegral_c₁_pow_smul_α'_pow' α' β' γ' q u t)
    (isIntegral_c₁_pow_smul_γ'_pow' α' β' γ' q u t))
  · exact isIntegral_c₁_pow_smul_add_smul_pow _ _ _ (n (K := K) q) (k q u)
      (le_sub_one_of_lt (finProdFinEquiv.symm.1 u).2.isLt) (a q t) (b q t)

/-- The matrix representing the homogeneous linear system of `mn` equations in `q^2` unknowns.
Its entries are scaled to strictly reside in the ring of integers `𝓞 K`. -/
def A : Matrix (Fin (m (K := K) * n (K := K) q)) (Fin (q * q)) (𝓞 K) :=
  fun i j ↦ RingOfIntegers.restrict _ (fun _ ↦ (c₁IsInt α' β' γ' q i j)) ℤ

lemma c₁_ne_zero : c₁ α' β' γ' ≠ 0 := Ne.symm (Int.ne_of_lt (one_le_c₁ α' β' γ'))

include α β σ hirr htriv habc in
lemma c₁α_ne_zero : c₁ α' β' γ' • α' ≠ 0 := by
  simpa using ⟨Ne.symm (Int.ne_of_lt (one_le_c₁ α' β' γ')),
   (alpha'_beta'_gamma'_ne_zero α β σ α' β' γ' hirr htriv habc ).1⟩

include α β σ hirr htriv habc in
lemma c₁γ_ne_zero : c₁ α' β' γ' • γ' ≠ 0 := by
  simpa using ⟨Ne.symm (Int.ne_of_lt (one_le_c₁ α' β' γ')),
   (alpha'_beta'_gamma'_ne_zero α β σ α' β' γ' hirr htriv habc ).2.2⟩

include α β σ hirr htriv habc in
lemma house_bound_c₁α :
    house (c₁ α' β' γ' • α') ^ (a q t * l q u) ≤ house (c₁ α' β' γ' • α') ^ (m (K := K) * q) := by
  refine Bound.pow_le_pow_right_of_le_one_or_one_le (Or.inl ⟨one_le_house_of_isIntegral
    (isIntegral_c₁α α' β' γ') (c₁α_ne_zero α β σ α' β' γ' hirr htriv habc), ?_⟩)
  simpa [mul_comm] using mul_le_mul (((finProdFinEquiv.symm.toFun t).1).isLt)
    (((finProdFinEquiv.symm.toFun u).1).isLt) (zero_le _) (zero_le _)

lemma isInt_β_bound : IsIntegral ℤ (c₁ α' β' γ' • (↑q + q • β')) := by
  simpa [smul_add, zsmul_eq_mul, nsmul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
    (IsIntegral.add ((IsIntegral.Cast (c₁ α' β' γ')).mul (IsIntegral.Nat q))
    ((IsIntegral.Nat q).mul (isIntegral_c₁β α' β' γ')))

lemma isInt_β_bound_low (q : ℕ) (t : Fin (q * q)) :
    IsIntegral ℤ (c₁ α' β' γ' • (↑(a q t) + b q t • β')) := by
  simpa [smul_add, zsmul_eq_mul, nsmul_eq_mul, mul_add,
    mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm] using
  (IsIntegral.add
    ((IsIntegral.Cast (c₁ α' β' γ')).mul (IsIntegral.Nat (a q t)))
    ((IsIntegral.Nat (b q t)).mul (isIntegral_c₁β  α' β' γ')))

include hirr σ habc in
lemma β'_ne_zero (y : ℕ) : (↑↑(a q t) + (↑(b q t)) • β') ^ y ≠ 0 := fun H ↦
  hirr (-(a q t : ℤ)) (b q t) <| by
    have hEq : (a q t : ℂ) + b q t * β = 0 := by
      simpa [nsmul_eq_mul, map_add, map_mul, ← habc.2.1] using
        congrArg σ (eq_zero_of_pow_eq_zero H)
    push_cast
    exact eq_div_iff_mul_eq (by unfold b; norm_cast) |>.mpr (by grind)

include hq0 hirr habc in
lemma b_sum_ne_zero : (↑q : K) + q • β' ≠ 0 := fun H ↦
    hirr (-1) 1 <| by
  have hEq : (q : ℂ) + q * β = 0 := by
    simpa [nsmul_eq_mul, ← habc.2.1] using congrArg σ H
  have hqC : (q : ℂ) ≠ 0 := mod_cast Nat.ne_zero_of_lt hq0
  exact mul_left_cancel₀ hqC (by linear_combination hEq)

include α β σ hirr habc in
lemma bound_c₁β (q : ℕ) (hq0 : 0 < q) : 1 ≤ house ((c₁ α' β' γ' • (q + q • β'))) :=
  one_le_house_of_isIntegral (isInt_β_bound α' β' γ' q) <|
  smul_ne_zero (Int.ne_of_lt (one_le_c₁ α' β' γ')).symm
  (b_sum_ne_zero α β σ α' β' γ' hirr habc q hq0)

include α β σ hirr htriv habc in
lemma one_le_house_c₁γ : 1 ≤ house (c₁ α' β' γ' • γ') :=
  one_le_house_of_isIntegral (isIntegral_c₁γ α' β' γ') <|
  smul_ne_zero (Int.ne_of_lt (one_le_c₁ α' β' γ')).symm
  (alpha'_beta'_gamma'_ne_zero α β σ α' β' γ' hirr htriv habc).2.2

/-- A large integer constant independent of `n` and `q`, used as a foundational base
to bound the houses (maximum absolute values of conjugates) of the algebraic coefficients. -/
def c₂ : ℤ := (|c₁ α' β' γ'| ^ (((1 + 2 * (m (K := K)) *
  (2 * (m (K := K))))) + (1 + 2 * (m (K := K)) * (2 * (m (K := K))))))

lemma one_le_c₂ : 1 ≤ c₂ α' β' γ' :=
  one_le_pow₀ <| Int.cast_one_le_of_pos (one_le_abs_c₁ α' β' γ')

open Real

/-- A real-valued bounding constant encompassing `c₂` and the houses of `α'`, `β'`, and `γ'`.
Used to establish a strict upper bound on the entries of the linear system matrix `A`. -/
def c₃ : ℝ := c₂ α' β' γ' * (1 + house β') * sqrt (2 * m (K := K)) *
  (max 1 (((house α' ^ (2 * m (K := K) ^ 2)) * house γ' ^(2 * m (K := K) ^ 2))))

lemma one_le_c₃ : 1 ≤ c₃ α' β' γ' :=
  one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
  (one_le_mul_of_one_le_of_one_le (mod_cast one_le_c₂ α' β' γ') <|
  le_add_of_nonneg_right <| house_nonneg _) <|
  one_le_sqrt.mpr <| mod_cast (by have := one_le_m (K := K); lia)) <| le_max_left 1 _

include h2mq hq0 in
lemma abs_q_pow_mul_house_le_c₃_pow : |↑q| ^ (n (K := K) q - 1) *
      ((1 + house β') ^ (n (K := K) q - 1) *
      (house α' ^ (m (K := K) * (2 * (m (K := K) * n (K := K) q))) *
      house γ' ^ (m (K := K) * (2 * (m (K := K) * n (K := K) q))))) ≤
    (1 + house β') ^ n (K := K) q * (√(2 * m (K := K)) ^ n (K := K) q *
    (max 1 (house α' ^ (2 * m (K := K) ^ 2) *
    house γ' ^ (2 * m (K := K) ^ 2)) ^ n (K := K) q * √↑(n (K := K) q) ^
      (↑(n (K := K) q : ℝ) - 1))) := by
  calc _ ≤ (sqrt (2 * m (K := K)) ^ (n (K := K) q -1))*
    (sqrt (n (K := K) q)) ^ ((n (K := K) q) -1) *
                 ((1 + house β') ^ (n (K := K) q - 1) * (house α' ^ (m (K := K) * (2 * (m (K := K) *
                  n (K := K) q))) *
                 house γ' ^ (m (K := K) * (2 * (m (K := K) * n (K := K) q))))) := ?_
       _ ≤ (sqrt (2 * m (K := K)) ^ (n (K := K) q -1)) * ((1 + house β') ^ (n (K := K) q - 1) *
                 (house α' ^ (m (K := K) * (2 * (m (K := K) * n (K := K) q))) * house γ' ^
                 (m (K := K) * (2 * (m (K := K) * n (K := K) q))))) * sqrt (n (K := K) q) ^
                 (((n (K := K) q) : ℝ) - 1) := ?_
       _ ≤ √(2 * ↑(m (K := K))) ^ ((n (K := K) q)) * ((1 + house β') ^ ((n (K := K) q)) *
         (house α' ^ (m (K := K) * 2 * m (K := K))) ^ (n (K := K) q) * (house γ' ^ (m (K := K) *
                 2 * m (K := K))) ^
                 (n (K := K) q) * √(n (K := K) q) ^ ((n (K := K) q : ℝ) - 1)) := ?_
  · have q_eq_n_etc : q ^ (n (K := K) q - 1) ≤ (sqrt (2 * m (K := K)) ^ (n (K := K) q - 1)) *
      (sqrt (n (K := K) q)) ^ (n (K := K) q - 1) := by
     rw [← mul_pow]
     refine pow_le_pow_left₀ (by positivity) ?_ (n (K := K) q - 1)
     have hq : (q : ℝ) ≤ sqrt (2 * m (K := K) * n (K := K) q) :=
        (le_sqrt (by positivity) (by positivity)).2
        (mod_cast le_of_eq (Eq.symm (Nat.mul_div_cancel' h2mq)))
     simpa [mul_assoc, sqrt_mul] using hq
    apply mul_le_mul (by simpa using (q_eq_n_etc )) (by rfl) (by positivity) (by positivity)
  · have hsqrt : (sqrt (n (K := K) q) ^ (n (K := K) q - 1)) =
     (sqrt (n (K := K) q) ^ ((n (K := K) q : ℝ) - 1)) := by
      simpa [(Nat.cast_sub (one_le_n (K := K) q hq0 h2mq))] using
        (rpow_natCast (x := sqrt (n (K := K) q)) (n := n (K := K) q - 1)).symm
    refine le_of_eq ?_; simp [hsqrt]; ac_rfl
  · simp only [mul_assoc]
    apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
    · refine Bound.pow_le_pow_right_of_le_one_or_one_le
        (Or.inl ⟨one_le_sqrt.mpr (by exact_mod_cast (by grind [one_le_m])), by simp⟩)
    · apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
      · refine Bound.pow_le_pow_right_of_le_one_or_one_le (Or.inl (by simp))
      · apply mul_le_mul (by simp [pow_mul]) (by simp [pow_mul]) (by positivity)
                (pow_nonneg (pow_nonneg (house_nonneg _) _) _)
  · nth_rw 2 [← mul_assoc]
    rw [mul_comm  ((1 + house β') ^ (n (K := K) q)) (((sqrt ((2*m (K := K))))) ^ (n (K := K) q))]
    simp only [mul_assoc]
    apply mul_le_mul (pow_le_pow_left₀ (sqrt_nonneg _) (by rfl) (n (K := K) q)) ?_
      (by positivity) (by positivity)
    · apply mul_le_mul (by rfl) ?_ (by positivity) (by positivity)
      · simp only [← mul_assoc]
        apply mul_le_mul ?_ (by rfl) (by positivity) (by positivity)
        · rw [← mul_pow]
          refine pow_le_pow_left₀ (by positivity) ?_ (n (K := K) q)
          · have : ((m (K := K) * 2) * m (K := K)) = (2 * m (K := K) ^ 2) := by
              rw [pow_two, mul_assoc, mul_comm, mul_assoc]
            rw [this]; clear this
            calc _ ≤ house α' ^ (2 * m (K := K) ^ 2) * house γ' ^ (2 * m (K := K) ^ 2) := ?_
                 _ ≤ max 1 ((house α' ^ (2 * m (K := K) ^ 2) *
                     house γ' ^ (2 * m (K := K) ^ 2))) := ?_
            · apply Preorder.le_refl
            · simp only [le_sup_right]

lemma house_add_mul_le :
    house (c₁ α' β' γ' • (↑(a q t) + b q t • β')) ≤
      (|c₁ α' β' γ'| * |(q : ℤ)|) * (1 + house (β')) := by
  calc _ ≤ house (c₁ α' β' γ' • ((a q t : ℤ) : K)) +
           house (c₁ α' β' γ' • ((b q t : ℤ) • β')) := ?_
       _ ≤ house (c₁ α' β' γ' : K) * house ((a q t : ℤ) : K) + house (c₁ α' β' γ' : K) *
           house ((b q t : ℤ) • β') := ?_
       _ ≤ house (c₁ α' β' γ' : K) * house ((a q t : ℤ) : K) + house (c₁ α' β' γ' : K) *
           (house ((b q t : ℤ) : K) * house ( β')) := ?_
       _ = |c₁ α' β' γ'| * |(a q t : ℤ)| + |c₁ α' β' γ'| * |(b q t : ℤ)| * house (β') := ?_
       _ ≤ |c₁ α' β' γ'| * |(q : ℤ)| + |c₁ α' β' γ'| * |(q : ℤ)| * house β' := ?_
       _ = |c₁ α' β' γ'| * |(q : ℤ)| * (1 + house β') := ?_
  · norm_cast; rw [smul_add]; apply house_add_le
  · refine add_le_add (by grind [house_mul_le]) (by grind [house_mul_le])
  · refine add_le_add (by grind)
      (mul_le_mul (le_refl _) (by grind [house_mul_le]) (house_nonneg _) (house_nonneg _))
  · rw [house_intCast]; rw [house_intCast]; rw [house_intCast]; rw [mul_assoc]
  · refine add_le_add (mul_le_mul (le_refl _) (mod_cast ((finProdFinEquiv.symm.toFun t).1).isLt)
      (Int.cast_nonneg (Int.zero_le_ofNat (a q t)))
      (Int.cast_nonneg  (abs_nonneg (c₁ α' β' γ' )))) ?_
    · rw [mul_assoc, mul_assoc]
      apply mul_le_mul (by rfl) ?_ (mul_nonneg (by positivity) (house_nonneg _)) (by simp)
      · apply mul_le_mul (mod_cast ((finProdFinEquiv.symm.toFun t).2).isLt) (le_refl _)
          (house_nonneg _) (by simp)
  · rw [mul_add]; simp only [Int.cast_abs, mul_one]

lemma c₁_pow_sub_one_mul_c₁_pow_mul_c₁_pow_eq :
    ((c₁ α' β' γ' : ℤ) ^ (n (K := K) q - 1) * (c₁ α' β' γ' : ℤ) ^ (m (K := K) * q) *
       (c₁ α' β' γ' : ℤ) ^ (m (K := K) * q)) =
    ((c₁ α' β' γ' : ℤ) ^ (n (K := K) q - 1 - k q u) *
       (c₁ α' β' γ' : ℤ) ^ (m (K := K) * q - a q t * l q u) *
    (c₁ α' β' γ' : ℤ) ^ (m (K := K) * q - b q t * l q u)) * ((c₁ α' β' γ' : ℤ) ^ k q u *
    (c₁ α' β' γ' : ℤ) ^ (a q t * l q u) * (c₁ α' β' γ' : ℤ) ^ (b q t * l q u)) := by
  symm
  calc
    _ = ((c₁ α' β' γ' : ℤ) ^ (n (K := K) q - 1 - k q u) * (c₁ α' β' γ' : ℤ) ^ k q u) *
        ((c₁ α' β' γ' : ℤ) ^ (m (K := K) * q - a q t * l q u) *
            (c₁ α' β' γ' : ℤ) ^ (a q t * l q u)) *
        ((c₁ α' β' γ' : ℤ) ^ (m (K := K) * q - b q t * l q u) *
            (c₁ α' β' γ' : ℤ) ^ (b q t * l q u)) := by ring
    _ = _ := by
      simp_rw [← pow_add]
      have intCast_k_le_intCast_n_sub_one : (k q u : ℤ) ≤ (n (K := K) q - 1 : ℤ) := by
        have := (finProdFinEquiv.symm u).2.isLt
        aesop
      rw [
        Nat.sub_add_cancel (by grind),
        Nat.sub_add_cancel (by
          have h := Nat.mul_le_mul (finProdFinEquiv.symm.toFun t).1.isLt
            (finProdFinEquiv.symm.toFun u).1.isLt
          rw [mul_comm (m (K := K)) q]
          exact h),
        Nat.sub_add_cancel (by
          have h := Nat.mul_le_mul (finProdFinEquiv.symm.toFun t).2.isLt
            (finProdFinEquiv.symm.toFun u).1.isLt
          rw [mul_comm (m (K := K)) q]
          exact h)]

/-! Moreover, the absolute value of the conjugates of the various coefficients is at most
  `c₂^n (q + q * |β|) ^ (n - 1) * |α| ^ (m q) * |γ| ^ (m q) ≤ c₃^n * n^((n - 1) / 2)`.
-/
include α β K σ α' β' γ' hirr htriv habc hq0 h2mq in
lemma house_matrixA_le : house ((algebraMap (𝓞 K) K) ((A α' β' γ' q) u t)) ≤
    (c₃ α' β' γ' ^ (n (K := K) q : ℝ) * (n (K := K) q : ℝ) ^ (((n (K := K) q : ℝ) - 1) / 2))  := by
  simp only [A, systemCoeffs, RingOfIntegers.restrict, RingOfIntegers.map_mk]
  calc _ = house (((c₁ α' β' γ' ^ (n (K := K) q - 1 - k q u) *
     c₁ α' β' γ' ^ (m (K := K) * q - a q t * l q u) *
           c₁ α' β' γ' ^ (m (K := K) * q - b q t * l q u)) •
           (c₁ α' β' γ' ^ k q u * c₁ α' β' γ' ^ (a q t * l q u) *
           c₁ α' β' γ' ^ (b q t * l q u))) • ((↑(a q t) + b q t • β') ^ k q u * α' ^
           (a q t * l q u) * γ' ^ (b q t * l q u))) := ?_
       _ = house ((c₁ α' β' γ' ^ ((n (K := K) q - 1) - k q u) *
            c₁ α' β' γ' ^ (m (K := K) * q - a q t * l q u) *
           (c₁ α' β' γ' : K) ^ (m (K := K) * q - b q t * l q u)) • (((c₁ α' β' γ' : K) ^ k q u) *
           ((a q t : K) + (b q t) * β') ^ k q u * ((c₁ α' β' γ' : K) ^ (a q t * l q u)) *
           α' ^ (a q t * l q u) * ((c₁ α' β' γ' : K) ^ (b q t * l q u)) *
           γ' ^ (b q t * l q u))) := ?_
       _ ≤ house (((c₁ α' β' γ' : K) ^ (n (K := K) q - 1 - k q u) * (c₁ α' β' γ' : K) ^
           (m (K := K) * q - a q t * l q u) *
           (c₁ α' β' γ' : K) ^ (m (K := K) * q - b q t * l q u))) *
           house (c₁ α' β' γ' ^ (k q u) • (↑(a q t) + (b q t) • β') ^ (k q u)) *
           house (c₁ α' β' γ' ^ (a q t * l q u) • α' ^ (a q t * l q u)) *
           house (c₁ α' β' γ' ^ (b q t * l q u) • γ' ^ (b q t * l q u)) := ?_
       _ ≤ house (((c₁ α' β' γ' : K) ^ (n (K := K) q - 1 - k q u) * (c₁ α' β' γ' : K) ^
           (m (K := K) * q - a q t * l q u) *
           (c₁ α' β' γ' : K) ^ (m (K := K) * q - b q t * l q u))) *
           house (c₁ α' β' γ' • (↑(a q t) + (b q t) • β')) ^ (k q u) * house (c₁ α' β' γ' • α') ^
           (a q t * l q u) * house (c₁ α' β' γ' • γ') ^ (b q t * l q u) := ?_
       _ ≤ house (((c₁ α' β' γ' : K) ^ (n (K := K) q - 1 - k q u) * (c₁ α' β' γ' : K) ^
           (m (K := K) * q - a q t * l q u) *
           (c₁ α' β' γ' : K) ^ (m (K := K) * q - b q t * l q u))) *
           house (c₁ α' β' γ' • (↑(a q t) + b q t • β')) ^ (n (K := K) q - 1) *
           house (c₁ α' β' γ' • α') ^ (m (K := K) * q) *
           house (c₁ α' β' γ' • γ') ^ (m (K := K) * q) := ?_
       _ ≤ |(((c₁ α' β' γ') ^ (n (K := K) q - 1 - k q u) *
           (c₁ α' β' γ') ^ (m (K := K) * q - a q t * l q u) *
           (c₁ α' β' γ') ^ (m (K := K) * q - b q t * l q u)))| * (|c₁ α' β' γ'| *
           (|(q : ℤ)| * (1 + house (β')))) ^ (n (K := K) q - 1) * (|c₁ α' β' γ'| * house (α')) ^
           (m (K := K) * (2 * (m (K := K) * n (K := K) q))) * (|c₁ α' β' γ'| * house (γ')) ^
           (m (K := K) * (2 * (m (K := K) * n (K := K) q))) := ?_
       _ = |(((c₁ α' β' γ') ^ (n (K := K) q - 1 - k q u) *
           (c₁ α' β' γ') ^ (m (K := K) * q - a q t * l q u) *
           (c₁ α' β' γ') ^ (m (K := K) * q - b q t * l q u)))| *
           |c₁ α' β' γ' ^ (n (K := K) q - 1)| •
           (↑|↑q| * (1 + house β')) ^ (n (K := K) q - 1) *
           |c₁ α' β' γ' ^ (m (K := K) * (2 * (m (K := K) * n (K := K) q)))| •
           house α' ^ (m (K := K) * (2 * (m (K := K) * n (K := K) q))) *
           |c₁ α' β' γ' ^ (m (K := K) * (2 * (m (K := K) * n (K := K) q)))|
           • house γ' ^ (m (K := K) * (2 * (m (K := K) * n (K := K) q))) := ?_
       _ ≤ |(((c₁ α' β' γ') ^ (n (K := K) q - 1 - k q u) *
           (c₁ α' β' γ') ^ (m (K := K) * q - a q t * l q u) *
           (c₁ α' β' γ') ^ (m (K := K) * q - b q t * l q u)))| *
           ↑|c₁ α' β' γ'| ^ ((n (K := K) q - 1) +
           (2 * m (K := K) * (2 * (m (K := K) * n (K := K) q)))) *
           (↑|↑q| ^ ((n (K := K) q ) - 1) * (1 + house β') ^
           (n (K := K) q - 1) * house α' ^ (m (K := K) * (2 * (m (K := K) * n (K := K) q))) *
           house γ' ^ (m (K := K) * (2 * (m (K := K) * n (K := K) q)))) := ?_
       _ = |(c₁ α' β' γ') ^ (n (K := K) q - 1 - k q u)| *
           |(c₁ α' β' γ') ^ (m (K := K) * q - a q t * l q u)| *
           |(c₁ α' β' γ') ^ (m (K := K) * q - b q t * l q u)| *
           ↑|c₁ α' β' γ'| ^ ((n (K := K) q - 1) +
           (2 * m (K := K) * (2 * (m (K := K) * n (K := K) q)))) *
           (↑|↑q| ^ ((n (K := K) q)- 1) * (1 + house β')
           ^ (n (K := K) q - 1) * house α' ^ (m (K := K) *
           (2 * (m (K := K) * n (K := K) q))) * house γ' ^
           (m (K := K) * (2 * (m (K := K) * n (K := K) q)))) := ?_
       _ = |(c₁ α' β' γ')| ^ (n (K := K) q - 1 - k q u) *
           |(c₁ α' β' γ')| ^ (m (K := K) * q - a q t * l q u) *
           |(c₁ α' β' γ')| ^ (m (K := K) * q - b q t * l q u) *
           ↑|c₁ α' β' γ'| ^ ((n (K := K) q - 1) +  (2 * m (K := K) *
           (2 * (m (K := K) * n (K := K) q)))) *
           (↑|↑q| ^ ((n (K := K) q) - 1) * (1 + house β') ^ (n (K := K) q - 1) *
           house α' ^ (m (K := K) * (2 * (m (K := K) * n (K := K) q))) *
           house γ' ^ (m (K := K) * (2 * (m (K := K) * n (K := K) q)))) := ?_
       _ ≤ ↑(c₂ α' β' γ') ^ (n (K := K) q) *
           (↑|↑q| ^ ((n (K := K) q ) - 1) * (1 + house β') ^ (n (K := K) q - 1) *
           house α' ^ (m (K := K) * (2 * (m (K := K) * n (K := K) q))) *
           house γ' ^ (m (K := K) * (2 * (m (K := K) * n (K := K) q)))) := ?_
       _ ≤ c₃ α' β' γ' ^ (n (K := K) q : ℝ) *
           ((sqrt (n (K := K) q)) ^ ((n (K := K) q : ℝ)- 1)) := ?_
       _ ≤ (c₃ α' β' γ' ^ (n (K := K) q : ℝ) *
           (n (K := K) q : ℝ) ^ (((n (K := K) q : ℝ) - 1) / 2)) := ?_
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
    apply mul_le_mul (by rfl) ?_ (by positivity) (by positivity)
    · simp only [nsmul_eq_mul, zsmul_eq_mul, Int.cast_pow, ← mul_pow]
      apply mul_le_mul (house_pow_le _ _) ?_ (by positivity) (by positivity)
      · apply mul_le_mul (house_pow_le _ _) (house_pow_le _ _) (house_nonneg _)
          (pow_nonneg (house_nonneg _) _)
  · apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
    · apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
      · apply mul_le_mul (by rfl) ?_ (by positivity) (house_nonneg _)
        · refine Bound.pow_le_pow_right_of_le_one_or_one_le
            (Or.inl ⟨one_le_house_of_isIntegral (isInt_β_bound_low _ _ _ q t) (fun H ↦ ?_), ?_⟩)
          · simp only [zsmul_eq_mul, mul_eq_zero, Int.cast_eq_zero] at H
            cases H with
            | inl hp => apply c₁_ne_zero α' β' γ'; exact hp
            | inr hq => apply β'_ne_zero α β σ α' β' γ' hirr habc q t 1; rw [pow_one]; exact hq
          · refine (Nat.le_sub_iff_add_le' (one_le_n (K := K) q hq0 h2mq)).mpr ?_
            · rw [add_comm]; exact (finProdFinEquiv.symm.toFun u).2.isLt
      · apply Bound.pow_le_pow_right_of_le_one_or_one_le
            (Or.inl ⟨one_le_house_of_isIntegral (isIntegral_c₁α α' β' γ')
            (c₁α_ne_zero α β σ α' β' γ' hirr htriv habc) , ?_⟩)
        · rw [mul_comm (m (K := K)) q]
          apply mul_le_mul (((finProdFinEquiv.symm.toFun t).1).isLt)
           (((finProdFinEquiv.symm.toFun u).1).isLt) (zero_le _) (zero_le _)
    · apply Bound.pow_le_pow_right_of_le_one_or_one_le
        (Or.inl ⟨one_le_house_of_isIntegral (isIntegral_c₁γ α' β' γ')
          (c₁γ_ne_zero α β σ α' β' γ' hirr htriv habc), ?_⟩)
      · rw [mul_comm (m (K := K)) q]
        apply (mul_le_mul (((finProdFinEquiv.symm.toFun t).2).isLt)
          (((finProdFinEquiv.symm.toFun u).1).isLt) (zero_le _) (zero_le _))
  · apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
    · apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
      · apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
        · rw [← house_intCast (K := K)]; simp
        · refine pow_le_pow_left₀ (house_nonneg _) ?_ (n (K := K) q - 1)
          · rw [← mul_assoc]; apply house_add_mul_le α' β' γ' q t
      · calc _ ≤ house (c₁ α' β' γ' • α') ^ (m (K := K) * (2 * (m (K := K) * n (K := K) q))) := ?_
             _ ≤ (↑|c₁ α' β' γ'| * house α') ^ (m (K := K) *
                 (2 * (m (K := K) * n (K := K) q))) := ?_
        · refine Bound.pow_le_pow_right_of_le_one_or_one_le
            (Or.inl ⟨one_le_house_of_isIntegral (isIntegral_c₁α α' β' γ')
             (c₁α_ne_zero α β σ α' β' γ' hirr htriv habc), ?_⟩)
          · apply mul_le_mul (by rfl) ?_ (by simp) (by simp)
            · exact (by
              have H := le_trans (Nat.le_pow (Nat.zero_lt_two))
                ((le_of_eq (Eq.symm (Nat.mul_div_cancel' h2mq)))); rw [mul_assoc] at H; exact H )
        · refine pow_le_pow_left₀ (house_nonneg _) ?_
            (m (K := K) * (2 * (m (K := K) * n (K := K) q)))
          · calc _ ≤ house (c₁ α' β' γ' : K) * house (α') := ?_
                 _ ≤ _ := ?_
            · grind [house_mul_le]
            · simp
    · calc _ ≤ house (c₁ α' β' γ' • γ') ^ (m (K := K) * (2 * (m (K := K) * n (K := K) q))) := ?_
           _ ≤ (↑|c₁ α' β' γ'| * house γ') ^ (m (K := K) * (2 * (m (K := K) * n (K := K) q))) := ?_
      · refine Bound.pow_le_pow_right_of_le_one_or_one_le
          (Or.inl ⟨one_le_house_of_isIntegral (isIntegral_c₁γ α' β' γ')
           (c₁γ_ne_zero α β σ α' β' γ' hirr htriv habc), ?_⟩)
        · have q_le_two_mn : q ≤ 2 * m (K := K) * n (K := K) q :=
            le_trans (Nat.le_pow (Nat.zero_lt_two))
            ((le_of_eq (Eq.symm (Nat.mul_div_cancel' h2mq))))
          apply mul_le_mul (by rfl) (by grind) (by simp) (by simp)
      refine pow_le_pow_left₀ (house_nonneg _) ?_ (m (K := K) * (2 * (m (K := K) * n (K := K) q)))
      · calc _ ≤ house (c₁ α' β' γ' : K)  * house (γ') := ?_
             _ ≤ _ := ?_
        · grind [house_mul_le]
        · simp only [house_intCast, Int.cast_abs, le_refl]
  · rw [zsmul_eq_mul, zsmul_eq_mul, zsmul_eq_mul, mul_pow, mul_pow, mul_pow, mul_pow, mul_pow,
        abs_pow, abs_pow]; congr; all_goals simp
  · have := zsmul_mul_mul_distrib |(c₁ α' β' γ' ^ (n (K := K) q - 1))|
         |(c₁ α' β' γ' ^ (m (K := K) * (2 * (m (K := K) * n (K := K) q))))|
         |(c₁ α' β' γ' ^
           (m (K := K) * (2 * (m (K := K) * n (K := K) q))))|
           ((↑|↑q| * (1 + house (β'))) ^ (n (K := K) q - 1))
         ((house α') ^ (m (K := K) * (2 * (m (K := K) * n (K := K) q))))
         ((house γ') ^ (m (K := K) * (2 * (m (K := K) * n (K := K) q))))
    simp only [mul_assoc, zsmul_eq_mul] at *
    rw [← this, abs_pow, abs_pow, ← pow_add, ← pow_add]
    apply mul_le_mul (by simp) ?_ (by positivity) (by positivity)
    · apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
      · rw [← pow_add, ← pow_add, Eq.symm
         (Nat.two_mul (m (K := K) * (2 * (m (K := K) * n (K := K) q))))]
        simp only [Int.cast_pow, Int.cast_abs, le_refl]
      · rw [mul_pow]; simp only [mul_assoc]; simp only [Nat.abs_cast, le_refl]
  · simp only [← pow_add, ← pow_add, Int.cast_abs, Int.cast_pow, Nat.abs_cast, abs_pow,
      ← pow_add, ← pow_add, ← pow_add, ← pow_add]
  · rw [abs_pow, abs_pow, abs_pow]; simp
  · apply mul_le_mul ?_ (by rfl) (by positivity) (?_)
    · rw [← pow_add, ← pow_add, ← pow_add, Int.cast_abs, c₂, Int.cast_pow, Int.cast_abs, ← pow_mul]
      refine pow_le_pow_right₀ (mod_cast (one_le_abs_c₁ α' β' γ')) ?_
      · simp only [add_mul, add_mul, one_mul, mul_assoc,
          (Nat.two_mul (m (K := K) * (2 * (m (K := K) * n (K := K) q)))), add_assoc]
        refine Nat.add_le_add ?_ (Nat.add_le_add ((Nat.sub_le _ _).trans <| by
          simpa [mul_assoc] using
              Nat.mul_le_mul_left (m (K := K)) (le_trans (Nat.le_pow (Nat.zero_lt_two))
              ((le_of_eq (Eq.symm (Nat.mul_div_cancel' h2mq))))))
            (Nat.add_le_add ((Nat.sub_le _ _).trans <| by
          simpa [mul_assoc] using
             Nat.mul_le_mul_left (m (K := K)) (le_trans (Nat.le_pow (Nat.zero_lt_two))
             ((le_of_eq (Eq.symm (Nat.mul_div_cancel' h2mq)))))) (by simp)))
        · grind
    · apply pow_nonneg; exact mod_cast (le_trans Int.one_nonneg (one_le_c₂ α' β' γ'))
  · simp_rw [c₃, rpow_natCast, mul_pow, mul_assoc]
    apply mul_le_mul (by rfl)
       (abs_q_pow_mul_house_le_c₃_pow α' β' γ' q hq0 h2mq) (by positivity) ?_
    · apply pow_nonneg; norm_cast; apply le_trans Int.one_nonneg (one_le_c₂ α' β' γ')
  · rw [le_iff_eq_or_lt]; left;
    have : sqrt (n (K := K) q) ^ ((n (K := K) q : ℝ) - 1) =
        (n (K := K) q : ℝ) ^ (((n (K := K) q : ℝ) - 1) / 2) := by
      nth_rw 1 [sqrt_eq_rpow, ← rpow_mul, mul_comm, mul_div]
      · simp only [mul_one]
      · simp only [Nat.cast_nonneg]
    rw [← this]

open NumberField

include α β σ α' β' γ' hirr htriv habc q hq0 h2mq in
lemma hM_ne_zero : A α' β' γ' q ≠ 0 := by
  intro H
  let u : Fin _ := ⟨0, Nat.mul_pos (one_le_m (K := K)) <| Nat.div_pos_iff.mpr
    ⟨Nat.zero_lt_succ (Nat.mul 2 (2 * h (K := K) + 1) + 1), Nat.le_of_dvd (Nat.pow_pos hq0) h2mq⟩⟩
  let t : Fin _ := ⟨0, mul_pos hq0 hq0⟩
  have H_eval : (A α' β' γ' q u t).val = 0 := by rw [H]; rfl
  simp only [A, RingOfIntegers.restrict, zsmul_eq_mul, Int.cast_mul, Int.cast_pow] at H_eval
  have hβ : (↑(a q t) + b q t • β' : K) ≠ 0 := fun h ↦
    (β'_ne_zero α β σ α' β' γ' hirr habc q t 1) (by grind)
  revert H_eval
  simp [c₁_ne_zero,
    (alpha'_beta'_gamma'_ne_zero α β σ α' β' γ' hirr htriv habc).1,
    (alpha'_beta'_gamma'_ne_zero α β σ α' β' γ' hirr htriv habc).2.2]
  grind

variable [DecidableEq (K →+* ℂ)]

include α β σ α' β' γ' hirr htriv habc in
/-- A non-trivial integer vector (in `𝓞 K`) residing in the kernel of the matrix `A`.
Its existence is guaranteed by Siegel's lemma (`exists_ne_zero_int_vec_house_le`). -/
abbrev η : Fin (q * q) → 𝓞 K := (house.exists_ne_zero_int_vec_house_le K (A α' β' γ' q)
  (hM_ne_zero α β σ α' β' γ' hirr htriv habc q hq0 h2mq)
  (mul_pos (Nat.zero_lt_succ (2 * h (K := K) + 1)) (one_le_n (K := K) q hq0 h2mq))
  (lt_of_lt_of_eq (  (mul_assoc 2 _ _).symm ▸ lt_mul_of_one_lt_left
    (Nat.mul_pos (one_le_m (K := K))<| Nat.div_pos_iff.mpr
    ⟨Nat.zero_lt_succ (Nat.mul 2 (2 * h (K := K) + 1) + 1),
    Nat.le_of_dvd (Nat.pow_pos hq0) h2mq⟩) <|
    (Nat.one_lt_two)) ((Nat.mul_div_cancel' h2mq).trans (pow_two q))) (Fintype.card_fin _)
  (fun u t ↦ house_matrixA_le α β σ α' β' γ' hirr htriv habc q hq0 u t h2mq)
    (Fintype.card_fin _)).choose

/-- A real-valued bounding constant used to bound the norm (house) of the
solution vector `η`. -/
def c₄ : ℝ := (max 1 ((house.c₁ K) * house.c₁ K * 2 * (m (K := K)))) * (c₃ α' β' γ' : ℝ)

/-!
`‖ηₖ‖ ≤ c₄ⁿ * n^((n - 1) / 2)`, for `1 ≤ k ≤ t`.
-/
open house in
include hq0 h2mq in
lemma house_eta_le_c₄_pow :
    house (algebraMap (𝓞 K) K (η (K := K) α β σ  α' β' γ' hirr htriv habc q hq0 h2mq t)) ≤
    c₄  α' β' γ' ^ (n (K := K) q : ℝ) * ((n (K := K) q : ℝ) ^ (((n (K := K) q : ℝ) + 1)/2)) := by
  have  mul_rpow_sub_one_div_two : (n (K := K) q : ℝ) *
    (n (K := K) q : ℝ) ^ (((n (K := K) q : ℝ) - 1) / 2) =
    (n (K := K) q : ℝ) ^ (((n (K := K) q : ℝ) + 1) / 2) := by
    nth_rw 1 [← Real.rpow_one (n (K := K) q : ℝ)];
    rw [← Real.rpow_add <| mod_cast (one_le_n (K := K) q hq0 h2mq)]; congr 1; ring
  calc _ ≤ house.c₁ K * (house.c₁ K * ↑(q * q) *
           (c₃  α' β' γ' ^ (n (K := K) q : ℝ) *
           (n (K := K) q : ℝ) ^ (((n (K := K) q : ℝ) - 1) / 2))) ^
           ((m (K := K) * n (K := K) q : ℝ) / (↑(q * q : ℝ) - ↑(m (K := K) * n (K := K) q ))) := ?_
       _ = (house.c₁ K * (house.c₁ K * 2 * m (K := K) *
           (c₃  α' β' γ' ^ (n (K := K) q : ℝ)) * ((n (K := K) q : ℝ) *
           (n (K := K) q : ℝ) ^ (((n (K := K) q : ℝ) - 1) / 2)))) := ?_
       _ ≤ c₄  α' β' γ' ^ (n (K := K) q : ℝ) *
           ((n (K := K) q : ℝ) ^ (((n (K := K) q : ℝ) + 1) / 2) : ℝ) := ?_
  · exact mod_cast ((house.exists_ne_zero_int_vec_house_le (K := K)
      (A α' β' γ' q) (hM_ne_zero α β σ  α' β' γ' hirr htriv habc q hq0 h2mq)
      (mul_pos (Nat.zero_lt_succ (2 * h (K := K) + 1))
      (one_le_n (K := K) q hq0 h2mq)) (lt_of_lt_of_eq (  (mul_assoc 2 _ _).symm ▸
      lt_mul_of_one_lt_left (Nat.mul_pos one_le_m <| Nat.div_pos_iff.mpr
      ⟨Nat.zero_lt_succ (Nat.mul 2 (2 * h (K := K) + 1) + 1),
      Nat.le_of_dvd (Nat.pow_pos hq0) h2mq⟩) <|
      (Nat.one_lt_two)) ((Nat.mul_div_cancel' h2mq).trans (pow_two q))) (Fintype.card_fin _)
      (fun u t ↦ house_matrixA_le α β σ  α' β' γ' hirr htriv habc q hq0 u t h2mq)
      (Fintype.card_fin _)).choose_spec).2.2 t
  · have q_sq_eq_two_mn : q ^ 2 = 2 * m * n (K := K) q := Eq.symm (Nat.mul_div_cancel' h2mq)
    have : (q * q : ℝ) = q^2 := mod_cast (pow_two ↑q).symm
    rw [← pow_two q, this, q_sq_eq_two_mn]
    have : (q ^ 2 : ℝ) = 2 * m * n (K := K) q := mod_cast (q_sq_eq_two_mn)
    rw [this]
    have mul_div_sub_eq_one :
      ((m (K := K) : ℝ) * (n (K := K) q : ℝ) / (2 * (m (K := K) : ℝ) * (n (K := K) q : ℝ) -
      (m (K := K) * (n (K := K) q : ℝ))) : ℝ) = 1 := by
     rw [mul_assoc, two_mul, add_sub_cancel_right]
     exact div_self <| mod_cast (Nat.mul_pos one_le_m <|
        Nat.div_pos_iff.mpr ⟨Nat.zero_lt_succ (Nat.mul 2 (2 * h (K := K) + 1) + 1),
        Nat.le_of_dvd (Nat.pow_pos hq0) h2mq⟩).ne'
    nth_rw 2 [← Nat.cast_mul] at mul_div_sub_eq_one
    rw [mul_div_sub_eq_one, rpow_one, mul_rpow_sub_one_div_two, mul_eq_mul_left_iff]
    left
    rw [mul_assoc, mul_assoc, mul_assoc, mul_assoc, mul_assoc]
    have one_le_house_c₁ : 1 ≤ house.c₁ K := one_le_mul_of_one_le_of_one_le (Nat.one_le_cast.mpr
      (Module.finrank_pos)) (one_le_mul_of_one_le_of_one_le (le_max_left _ _) (le_max_left _ _))
    refine (mul_right_inj' (by grind)).mpr ?_
    · grind [← mul_assoc, ← mul_assoc, ← mul_assoc]
  · rw [mul_rpow_sub_one_div_two, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ ?_
    · rw [c₄, mul_rpow (le_of_lt (lt_of_lt_of_le (by norm_num) (le_max_left _ _)))
        (le_of_lt (lt_of_lt_of_le (by norm_num) (one_le_c₃ α' β' γ')))]
      refine mul_le_mul_of_nonneg_right ?_ ?_
      · have hn : (1 : ℝ) ≤ (n (K := K) q : ℝ) := mod_cast one_le_n (K := K) q hq0 h2mq
        have hpow : (max 1 (house.c₁ K * house.c₁ K * 2 * (m (K := K)) ) : ℝ) ≤
          (max 1 (house.c₁ K * house.c₁ K * 2 * (m (K := K)))) ^ (n (K := K) q : ℝ) := by
          simpa [Real.rpow_one] using (rpow_le_rpow_of_exponent_le (le_max_left (1 : ℝ) _) hn)
        exact (le_max_right (1 : ℝ) _).trans hpow
      · apply rpow_nonneg (le_trans zero_le_one (one_le_c₃ α' β' γ'))
    · apply rpow_nonneg; simp only [Nat.cast_nonneg]

end GelfondSchneider
