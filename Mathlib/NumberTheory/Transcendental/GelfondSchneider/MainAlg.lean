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

variable {K} [Field K] [NumberField K]

namespace GelfondSchneider

lemma exists_int_smul_isIntegral {K : Type*} [Field K] [NumberField K] (α : K) :
    ∃ k : ℤ, k ≠ 0 ∧ IsIntegral ℤ (k • α) := by
  obtain ⟨y, hy, hf⟩ := exists_integral_multiples ℤ ℚ (L := K) {α}
  refine ⟨y, hy, hf α (mem_singleton_self _)⟩

/-- A choice of a non-zero integer `c` such that `c • α` is an algebraic integer.
The existence of such an integer is guaranteed for any algebraic number. -/
def c₀ {K : Type*} [Field K] [NumberField K] (α : K) : {c : ℤ // c ≠ 0 ∧ IsIntegral ℤ (c • α)} :=
  ⟨(exists_int_smul_isIntegral α).choose, (exists_int_smul_isIntegral α).choose_spec⟩

/-- An abbreviation for the explicit integer value extracted from `c₀ α`. -/
abbrev c₀Coeff {K : Type*} [Field K] [NumberField K] (α : K) : ℤ := (c₀ α : ℤ)

lemma c₀Coeff_ne_zero (α : K) : c₀Coeff α ≠ 0 := (c₀ α).2.1

/-!
Let `α` and `β` be algebraic numbers with `α ≠ 0, 1` and `β` irrational. We prove that `αᵇ` is
transcendental by contradiction. Suppose `γ = αᵇ = e^(β log α)` is also algebraic.
-/

/-- This structure encapsulates all the foundational data and hypotheses for the proof
of the Gelfond-Schneider theorem. It binds the complex numbers to their algebraic
counterparts in a common number field. -/
structure Setup where
  /-- The base of the exponentiation, assumed to be an algebraic complex number. -/
  α : ℂ
  /-- The exponent, assumed to be an irrational algebraic complex number. -/
  β : ℂ
  /-- A common abstract type representing the number field containing the preimages
  of `α`, `β`, and `α ^ β`. -/
  K : Type
  [isField : Field K]
  [isNumberField : NumberField K]
  /-- A fixed ring homomorphism embedding the abstract number field `K` into `ℂ`. -/
  σ : K →+* ℂ
  /-- The algebraic preimage of `α` in the number field `K`. -/
  α' : K
  /-- The algebraic preimage of `β` in the number field `K`. -/
  β' : K
  /-- The algebraic preimage of the assumed-algebraic `α ^ β` in the number field `K`. -/
  γ' : K
  hirr : ∀ i j : ℤ, β ≠ i / j
  htriv : α ≠ 0 ∧ α ≠ 1
  hα : IsAlgebraic ℚ α
  hβ : IsAlgebraic ℚ β
  habc : α = σ α' ∧ β = σ β' ∧ α ^ β = σ γ'
  /-- A decidable equality instance for the complex embeddings of `K`. -/
  hd : DecidableEq (K →+* ℂ)

namespace Setup

attribute [instance] isField isNumberField

variable (h7 : Setup)

open Setup

lemma alpha_gamma_pow_beta_ne_zero : h7.α ^ h7.β ≠ 0 :=
  fun H ↦ h7.htriv.1 ((cpow_eq_zero_iff h7.α h7.β).mp H).1

lemma beta_ne_zero : h7.β ≠ 0 :=
  fun H ↦ h7.hirr 0 1 (by simpa [div_one] using H)

lemma alpha'_beta'_gamma'_ne_zero : h7.α' ≠ 0 ∧ h7.β' ≠ 0 ∧ h7.γ' ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> intro H
  · exact h7.htriv.1 (by simp [h7.habc.1, H, map_zero h7.σ])
  · exact h7.beta_ne_zero (by simp [h7.habc.2.1, H, map_zero h7.σ])
  · exact h7.alpha_gamma_pow_beta_ne_zero (by simp [h7.habc.2.2, H, map_zero h7.σ])

lemma alpha'_ne_one : h7.α' ≠ 1 := fun h ↦
  h7.htriv.2 <| by simpa [h7.habc.1, map_one] using congrArg h7.σ h

lemma beta'_ne_zero : h7.β' ≠ 0 := h7.alpha'_beta'_gamma'_ne_zero.2.1

open Complex

lemma log_α_ne_zero : log h7.α ≠ 0 :=
  mt (fun h ↦ by simpa [exp_log h7.htriv.1, exp_zero] using congrArg exp h) h7.htriv.2

/-- c₁ is a positive integer such that c₁ • α', c₁ • β', c₁ • γ' are algebraic integers -/
def c₁ : ℤ := abs (c₀ h7.α' * c₀ h7.β' * c₀ h7.γ')

lemma one_le_c₁ : 1 ≤ h7.c₁ := by
  simpa [c₁] using Int.one_le_abs <| mul_ne_zero (mul_ne_zero (c₀Coeff_ne_zero h7.α')
    (c₀Coeff_ne_zero h7.β')) (c₀Coeff_ne_zero h7.γ')

lemma one_le_abs_c₁ : 1 ≤ |↑h7.c₁| := Int.one_le_abs (Ne.symm (Int.ne_of_lt h7.one_le_c₁))

lemma IsIntegral_assoc (K : Type) [Field K] {x y : ℤ} (z : ℤ) (α : K) (ha : IsIntegral ℤ (z • α)) :
    IsIntegral ℤ ((x * y * z : ℤ) • α) := by
  simpa [Int.cast_mul, zsmul_eq_mul, mul_assoc] using IsIntegral.smul (x * y) ha

lemma isIntegral_c₁α : IsIntegral ℤ (h7.c₁ • h7.α') := by
  have h := IsIntegral_assoc (x := c₀Coeff h7.γ') (y := c₀Coeff h7.β') h7.K (c₀Coeff h7.α') h7.α'
    ((c₀ h7.α').2.2)
  conv => enter [2]; rw [c₁, mul_comm, mul_comm (c₀Coeff h7.α') (c₀Coeff h7.β'), ← mul_assoc]
  rcases abs_choice (c₀Coeff h7.γ' * c₀Coeff h7.β' * c₀Coeff h7.α') with H1 | H2
  · rw [H1]; exact h
  · rw [H2]; rw [← IsIntegral.neg_iff, neg_smul, neg_neg]; exact h

lemma isIntegral_c₁β : IsIntegral ℤ (h7.c₁ • h7.β') := by
  have h := IsIntegral_assoc (x := c₀Coeff h7.γ') (y := c₀Coeff h7.α') h7.K (c₀Coeff h7.β') h7.β'
    ((c₀ h7.β').2.2)
  rw [c₁, mul_comm, ← mul_assoc]
  rcases abs_choice (c₀Coeff h7.γ' * c₀Coeff h7.α' * c₀Coeff h7.β') with H1 | H2
  · rw [H1]; exact h
  · rw [H2]; rw [← IsIntegral.neg_iff, neg_smul, neg_neg]; exact h

lemma isIntegral_c₁γ : IsIntegral ℤ (h7.c₁ • h7.γ') := by
  have h := IsIntegral_assoc (x := c₀Coeff h7.α') (y := c₀Coeff h7.β') h7.K (c₀Coeff h7.γ') h7.γ'
    ((c₀ h7.γ').2.2)
  rw [c₁]
  rcases abs_choice (c₀Coeff h7.α' * c₀Coeff h7.β' * c₀Coeff h7.γ') with H1 | H2
  · rw [H1]; exact h
  · rw [H2]; rw [← IsIntegral.neg_iff, neg_smul, neg_neg]; exact h

/-!
Let `m = 2h + 2`, and `n = q^ 2 / (2 * h7.m)`, where $q^2 = t $ is a square of a natural number
and is a multiple of $2m.$  -/

/-- The finrank of the field extension `h7.K` -/
def h : ℕ := Module.finrank ℚ h7.K

/-- A parameter `m` dependent on the degree `h = [K : ℚ]`. -/
def m : ℕ := 2 * h7.h + 2

lemma one_le_m : 1 ≤ h7.m := Nat.succ_le_succ (Nat.zero_le (2 * h7.h + 1))

variable (q : ℕ) (hq0 : 0 < q)

/-- A target bound parameter `n` dependent on a free parameter `q`. -/
def n : ℕ := q ^ 2 / (2 * h7.m)

variable (u : Fin (h7.m * h7.n q)) (t : Fin (q * q))

-- `a, b, k, l` are values that depend on the context variables `t` and `u`.

/-- A variable `a` that satisfies `1 ≤ a ≤ q`. -/
def a : ℕ := (finProdFinEquiv.symm.toFun t).1 + 1

/-- A variable `b` that satisfies `1 ≤ b ≤ q`. -/
def b : ℕ := (finProdFinEquiv.symm.toFun t).2 + 1

/-- Also, let `ρ₁, ρ₂, …, ρₜ` represent the `t` numbers
  `(a + bβ) log α,  1 ≤ a ≤ q, 1 ≤ b ≤ q.` -/
def ρ : ℂ := (a q t + (b q t • h7.β)) * Complex.log h7.α


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
abbrev systemCoeffs : h7.K :=
  (a q t + b q t • h7.β') ^ (h7.k q u) * h7.α' ^ (a q t * h7.l q u) * h7.γ' ^ (b q t * h7.l q u)

variable (h2mq : 2 * h7.m ∣ q ^ 2)

include hq0 h2mq in
lemma one_le_n : 1 ≤ h7.n q := by
  simp [n, (Nat.one_le_div_iff (by positivity [h7.one_le_m])).2
  (Nat.le_of_dvd (Nat.pow_pos hq0) h2mq)]

/-!
Let `c₁, c₂, …` be natural numbers independent of `n`. There exists `c₁` such that
`c₁ α, c₁ β, c₁ γ` are integers in `K`.
-/

/-- A combined integer scaling factor `c₁^(n-1 + 2mq)` applied to the linear system to clear
all denominators and ensure the resulting matrix entries are algebraic integers. -/
abbrev c_coeffs (q : ℕ) := h7.c₁ ^ (h7.n q - 1) * h7.c₁ ^ (h7.m * q) * h7.c₁ ^ (h7.m * q)

/-- An unscaled sub-component of the matrix coefficients, used to establish intermediate
integrality bounds during the construction of the auxiliary function. -/
abbrev c_coeffs0 (q : ℕ) (u : Fin (h7.m * h7.n q)) (t : Fin (q * q)) :=
  h7.c₁ ^ (h7.k q u : ℕ) * h7.c₁ ^ (a q t * h7.l q u) * h7.c₁ ^ (b q t * h7.l q u)

lemma IsIntegral.Cast (K : Type) [Field K] (a : ℤ) : IsIntegral ℤ (a : K) :=
  map_isIntegral_int (algebraMap ℤ K) (Algebra.IsIntegral.isIntegral _)

lemma isIntegral_c₁_pow_smul_pow (u : h7.K) (n k a l : ℕ) (hnk : a * l ≤ n * k)
    (H : IsIntegral ℤ (↑h7.c₁ * u)) : IsIntegral ℤ (h7.c₁ ^ (n * k) • u ^ (a * l)) := by
  rw [zsmul_eq_mul, Int.cast_pow, ← Nat.sub_add_cancel hnk, pow_add, mul_assoc, ← mul_pow]
  exact IsIntegral.mul (IsIntegral.pow (IsIntegral.Cast h7.K h7.c₁) _) (IsIntegral.pow H _)

lemma IsIntegral.Nat (K : Type) [Field K] (a : ℕ) : IsIntegral ℤ (a : K) := by
  have : (a : K) = ((a : ℤ) : K) := by simp only [Int.cast_natCast]
  rw [this]; apply IsIntegral.Cast

lemma isIntegral_c₁_pow_smul_α'_pow : IsIntegral ℤ
    (h7.c₁ ^ (a q t * h7.l q u) • (h7.α' ^ (a q t * h7.l q u))) := by
  apply h7.isIntegral_c₁_pow_smul_pow h7.α' (a q t) (h7.l q u) (a q t) (h7.l q u) (by rfl)
    (by grind [h7.isIntegral_c₁α])

lemma isIntegral_c₁_pow_smul_γ'_pow : IsIntegral ℤ (h7.c₁ ^ (b q t * h7.l q u) •
    (h7.γ'^ (b q t * (h7.l q u)))) := by
  apply h7.isIntegral_c₁_pow_smul_pow h7.γ' (b q t) (h7.l q u) (b q t) (h7.l q u) (by rfl)
    (by grind [h7.isIntegral_c₁γ])

lemma isIntegral_c₁_pow_smul_α'_pow' :
    IsIntegral ℤ (h7.c₁^(h7.m * q) • (h7.α' ^ (a q t * h7.l q u))) :=
    h7.isIntegral_c₁_pow_smul_pow h7.α' h7.m q (a q t) (h7.l q u)
  (by simpa [mul_comm] using Nat.mul_le_mul (((finProdFinEquiv.symm.toFun t).1).isLt)
       (((finProdFinEquiv.symm.toFun u).1).isLt)) <| by grind [h7.isIntegral_c₁α]

lemma isIntegral_c₁_pow_smul_γ'_pow' :
    IsIntegral ℤ (h7.c₁ ^ (h7.m * q) • (h7.γ'^ (b q t * h7.l q u))) :=
    h7.isIntegral_c₁_pow_smul_pow h7.γ' h7.m q (b q t) (h7.l q u)
  (by simpa [mul_comm] using Nat.mul_le_mul (((finProdFinEquiv.symm.toFun t).2).isLt)
       (((finProdFinEquiv.symm.toFun u).1).isLt)) <| by grind [h7.isIntegral_c₁γ]

lemma c_coeffs_neq_zero : h7.c_coeffs q ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ (Ne.symm (Int.ne_of_lt h7.one_le_c₁)))
  (pow_ne_zero _ (Ne.symm (Int.ne_of_lt h7.one_le_c₁))))
  (pow_ne_zero _ (Ne.symm (Int.ne_of_lt h7.one_le_c₁)))

lemma isIntegral_c₁_pow_smul_add_smul_pow (n : ℕ) (k : ℕ) (hkn : k ≤ n - 1) (a : ℕ) (b : ℕ) :
    IsIntegral ℤ (h7.c₁ ^ (n - 1) • (↑a + ↑b • h7.β') ^ k) := by
  rw [zsmul_eq_mul, Int.cast_pow, ← Nat.sub_add_cancel hkn, pow_add, mul_assoc, ← mul_pow, mul_add]
  refine IsIntegral.mul (IsIntegral.pow (IsIntegral.Cast _ _) _)
    (IsIntegral.pow (IsIntegral.add ?_ ?_) _)
  · exact IsIntegral.mul (IsIntegral.Cast _ _) (IsIntegral.Nat _ _)
  · rw [nsmul_eq_mul, ← mul_assoc, mul_comm (h7.c₁ : h7.K), mul_assoc]
    exact IsIntegral.mul (IsIntegral.Nat _ _) (by grind [h7.isIntegral_c₁β])

/-!
Multiplying the system by
`c₁^(n-1) c₁^(mq) c₁^ (mq) = c₁^(n-1+2mq) ≤ (c₂^n)` ensures the coefficients are integers in `K`. -/

lemma zsmul_mul_mul_distrib {K : Type*} [Field K] (a b c : ℤ) (x y z : K) :
    ((a * b) * c) • ((x * y) * z) = a • x * b • y * c • z := by
  simp [zsmul_eq_mul]; ring

open Nat in
lemma c₁IsInt : IsIntegral ℤ (h7.c_coeffs q • h7.systemCoeffs q u t) := by
  rw [zsmul_mul_mul_distrib, mul_assoc]
  refine IsIntegral.mul ?_
    (IsIntegral.mul (h7.isIntegral_c₁_pow_smul_α'_pow' q u t)
    (h7.isIntegral_c₁_pow_smul_γ'_pow' q u t))
  · exact h7.isIntegral_c₁_pow_smul_add_smul_pow (h7.n q) (h7.k q u)
      (le_sub_one_of_lt (finProdFinEquiv.symm.1 u).2.isLt) (a q t) (b q t)

/-- The matrix representing the homogeneous linear system of `mn` equations in `q^2` unknowns.
Its entries are scaled to strictly reside in the ring of integers `𝓞 K`. -/
def A : Matrix (Fin (h7.m * h7.n q)) (Fin (q * q)) (𝓞 h7.K) :=
  fun i j ↦ RingOfIntegers.restrict _ (fun _ ↦ (h7.c₁IsInt q i j)) ℤ

lemma c₁_ne_zero : h7.c₁ ≠ 0 := Ne.symm (Int.ne_of_lt h7.one_le_c₁)

lemma c₁α_ne_zero : h7.c₁ • h7.α' ≠ 0 := by
  simpa using ⟨Ne.symm (Int.ne_of_lt h7.one_le_c₁), (h7.alpha'_beta'_gamma'_ne_zero).1⟩

lemma c₁γ_ne_zero : h7.c₁ • h7.γ' ≠ 0 := by
  simpa using ⟨Ne.symm (Int.ne_of_lt h7.one_le_c₁), (h7.alpha'_beta'_gamma'_ne_zero).2.2⟩

lemma house_bound_c₁α :
    house (h7.c₁ • h7.α') ^ (a q t * h7.l q u) ≤ house (h7.c₁ • h7.α') ^ (h7.m * q) := by
  refine Bound.pow_le_pow_right_of_le_one_or_one_le (Or.inl ⟨one_le_house_of_isIntegral
    (h7.isIntegral_c₁α) h7.c₁α_ne_zero, ?_⟩)
  simpa [mul_comm] using mul_le_mul (((finProdFinEquiv.symm.toFun t).1).isLt)
    (((finProdFinEquiv.symm.toFun u).1).isLt) (zero_le _) (zero_le _)

lemma isInt_β_bound : IsIntegral ℤ (h7.c₁ • (↑q + q • h7.β')) := by
  simpa [smul_add, zsmul_eq_mul, nsmul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
    (IsIntegral.add ((IsIntegral.Cast h7.K h7.c₁).mul (IsIntegral.Nat h7.K q))
    ((IsIntegral.Nat h7.K q).mul h7.isIntegral_c₁β))

lemma isInt_β_bound_low (q : ℕ) (t : Fin (q * q)) :
    IsIntegral ℤ (h7.c₁ • (↑(a q t) + b q t • h7.β')) := by
  simpa [smul_add, zsmul_eq_mul, nsmul_eq_mul, mul_add,
  mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm] using
  (IsIntegral.add
    ((IsIntegral.Cast h7.K h7.c₁).mul (IsIntegral.Nat h7.K (a q t)))
    ((IsIntegral.Nat h7.K (b q t)).mul h7.isIntegral_c₁β))

lemma β'_ne_zero (y : ℕ) : (↑↑(a q t) + (↑(b q t)) • h7.β') ^ y ≠ 0 := fun H ↦
  h7.hirr (-(a q t : ℤ)) (b q t) <| by
    have hEq : (a q t : ℂ) + b q t * h7.β = 0 := by
      simpa [nsmul_eq_mul, map_add, map_mul, ← h7.habc.2.1] using
        congrArg h7.σ (eq_zero_of_pow_eq_zero H)
    push_cast
    exact eq_div_iff_mul_eq (by unfold b; norm_cast) |>.mpr (by grind)

include hq0 in
lemma b_sum_ne_zero : (↑q : h7.K) + q • h7.β' ≠ 0 := fun H ↦
  h7.hirr (-1) 1 <| by
    have hEq : (q : ℂ) + q * h7.β = 0 := by
      simpa [nsmul_eq_mul, ← h7.habc.2.1] using congrArg h7.σ H
    have hqC : (q : ℂ) ≠ 0 := mod_cast Nat.ne_zero_of_lt hq0
    norm_num
    exact mul_left_cancel₀ hqC (by linear_combination hEq)

lemma bound_c₁β (q : ℕ) (hq0 : 0 < q) : 1 ≤ house ((h7.c₁ • (q + q • h7.β'))) := by
  apply one_le_house_of_isIntegral (h7.isInt_β_bound q)
  simp only [zsmul_eq_mul, ne_eq, mul_eq_zero, Int.cast_eq_zero, not_or]
  refine ⟨Ne.symm (Int.ne_of_lt h7.one_le_c₁), h7.b_sum_ne_zero q hq0⟩

lemma one_le_house_c₁γ : 1 ≤ house (h7.c₁ • h7.γ') := by
  apply one_le_house_of_isIntegral h7.isIntegral_c₁γ
  simp only [zsmul_eq_mul, ne_eq, mul_eq_zero, Int.cast_eq_zero, not_or]
  refine ⟨Ne.symm (Int.ne_of_lt h7.one_le_c₁), (h7.alpha'_beta'_gamma'_ne_zero).2.2⟩

/-- A large integer constant independent of `n` and `q`, used as a foundational base
to bound the houses (maximum absolute values of conjugates) of the algebraic coefficients. -/
def c₂ : ℤ := (|h7.c₁| ^ (((1 + 2 * h7.m * (2 * h7.m))) + (1 + 2 * h7.m * (2 * h7.m))))

lemma one_le_c₂ : 1 ≤ h7.c₂ := by
  apply le_trans (Int.cast_one_le_of_pos (h7.one_le_abs_c₁))
  nth_rw 1 [← pow_one (a:= |h7.c₁|)]
  apply pow_le_pow_right₀ (h7.one_le_abs_c₁) (Nat.le_add_left 1
    ((1 + 2 * h7.m * (2 * h7.m)).add (Nat.add 1 (((2 * h7.m).mul
    (Nat.mul 2 (2 * h7.h + 1) + 1)).add (Nat.mul 2 (2 * h7.h + 1) + 1)))))


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
  · apply mul_le_mul (by simpa using (h7.q_eq_n_etc q h2mq)) (by rfl) (by positivity)
      (by positivity)
  · have hsqrt : (sqrt (h7.n q) ^ (h7.n q - 1)) = (sqrt (h7.n q) ^ ((h7.n q : ℝ) - 1)) := by
      simpa [(Nat.cast_sub (h7.one_le_n q hq0 h2mq))] using
        (rpow_natCast (x := sqrt (h7.n q)) (n := h7.n q - 1)).symm
    refine le_of_eq ?_; simp [hsqrt]; ac_rfl
  · simp only [mul_assoc]
    apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
    · refine Bound.pow_le_pow_right_of_le_one_or_one_le (Or.inl ⟨?_, by simp⟩)
      have hm1 : (1 : ℝ) ≤ (h7.m : ℝ) := by exact_mod_cast h7.one_le_m
      have : (1 : ℝ) ≤ (2 : ℝ) * (h7.m : ℝ) := by nlinarith
      simpa [Nat.cast_mul, Nat.cast_ofNat] using (one_le_sqrt).2 this
    · apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
      · refine Bound.pow_le_pow_right_of_le_one_or_one_le (Or.inl (by simp))
      · apply mul_le_mul (by simp [pow_mul]) (by simp [pow_mul]) (by positivity)
                (pow_nonneg (pow_nonneg (house_nonneg _) _) _)
  · nth_rw 2 [← mul_assoc]
    rw [mul_comm  ((1 + house h7.β') ^ (h7.n q)) (((sqrt ((2*h7.m)))) ^ (h7.n q))]
    simp only [mul_assoc]
    apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
    · refine pow_le_pow_left₀ (sqrt_nonneg _) (by rfl) (h7.n q)
    · apply mul_le_mul (by rfl) ?_ (by positivity) (by positivity)
      · simp only [← mul_assoc]
        apply mul_le_mul ?_ (by rfl) (by positivity) (by positivity)
        · rw [← mul_pow]
          refine pow_le_pow_left₀ (by positivity) ?_ (h7.n q)
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
    apply mul_le_mul (by rfl) ?_ (by positivity) (by positivity)
    · simp only [nsmul_eq_mul, zsmul_eq_mul, Int.cast_pow, ← mul_pow]
      apply mul_le_mul (house_pow_le _ _) ?_ (by positivity) (by positivity)
      · apply mul_le_mul (house_pow_le _ _) (house_pow_le _ _) (house_nonneg _)
          (pow_nonneg (house_nonneg _) _)
  · apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
    · apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
      · apply mul_le_mul (by rfl) ?_ (by positivity) (house_nonneg _)
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
  · apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
    · apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
      · apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
        · rw [← house_intCast (K := h7.K)]; simp
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
    apply mul_le_mul (by simp) ?_ (by positivity) (by positivity)
    · apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
      · rw [← pow_add, ← pow_add, Eq.symm (Nat.two_mul (h7.m * (2 * (h7.m * h7.n q))))]
        simp only [Int.cast_pow, Int.cast_abs, le_refl]
      · rw [mul_pow]; simp only [mul_assoc]; simp only [Nat.abs_cast, le_refl]
  · simp only [← pow_add, ← pow_add, Int.cast_abs, Int.cast_pow, Nat.abs_cast, abs_pow,
      ← pow_add, ← pow_add, ← pow_add, ← pow_add]
  · rw [abs_pow, abs_pow, abs_pow]; simp
  · apply mul_le_mul ?_ (by rfl) (by positivity) (?_)
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
    apply mul_le_mul (by rfl) (h7.abs_q_pow_mul_house_le_c₃_pow q hq0 h2mq) (by positivity) ?_
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

end GelfondSchneider.Setup
