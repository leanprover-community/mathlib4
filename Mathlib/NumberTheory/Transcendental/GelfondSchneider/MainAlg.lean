/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.NumberTheory.NumberField.House
public import Mathlib.RingTheory.Algebraic.NatDenominator

/-!
# Hilbert's Seventh Problem (Gelfond–Schneider Theorem)

This file develops the algebraic setup for a proof of the **Gelfond–Schneider Theorem**,
which resolves Hilbert's Seventh Problem: if `α` and `β` are algebraic with `α ≠ 0, 1` and `β`
irrational, then `α ^ β` is transcendental.

## Main results

- `gelfondSchneider`: `α ^ β` is transcendental under the hypotheses above (in a later file).
- `Setup`: bundled algebraic data for the Gelfond–Schneider proof.
- `Setup.A`: the scaled Siegel matrix over the ring of integers.

## Implementation note

We follow Keng's *Introduction to Number Theory*, Chapter 17, Section 5, pp. 488–493.
The argument proceeds by contradiction via an auxiliary exponential function.
This file constructs the common number field `K`, the parameters `m = 2h + 2` and `n = q² / (2m)`,
the denominator clearing factor `c₁`, and the scaled integer matrix `A`.

## References

* Loo-Keng Hua, *Introduction to Number Theory*, Springer, 1982, Chapter XII (§13).
* A. O. Gelfond (1934), *Sur le septième Problème de Hilbert*.
* T. Schneider (1935), *Transzendenzuntersuchungen periodischer Funktionen*.
-/

@[expose] public section

open BigOperators Module.Free Fintype NumberField Embeddings FiniteDimensional Matrix Set
  Polynomial Finset IntermediateField Complex AnalyticAt

noncomputable section

/-!
Suppose that `α, β, γ` lie in an algebraic field `K` with degree `h`.
-/

lemma isNumberField_adjoin_of_isAlgebraic (α β γ : ℂ) (hα : IsAlgebraic ℚ α)
    (hβ : IsAlgebraic ℚ β) (hγ : IsAlgebraic ℚ γ) :
    NumberField (adjoin ℚ {α, β, γ}) where
  to_charZero := charZero_of_injective_algebraMap (algebraMap ℚ _).injective
  to_finiteDimensional := finiteDimensional_adjoin fun _ hx ↦ by
    rcases hx with rfl | rfl | rfl
    exacts [isAlgebraic_iff_isIntegral.1 hα, isAlgebraic_iff_isIntegral.1 hβ,
      isAlgebraic_iff_isIntegral.1 hγ]

lemma exists_common_field_of_isAlgebraic (α β γ : ℂ) (hα : IsAlgebraic ℚ α)
    (hβ : IsAlgebraic ℚ β) (hγ : IsAlgebraic ℚ γ) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (σ : K →+* ℂ)
      (_ : DecidableEq (K →+* ℂ)),
      ∃ α' β' γ' : K, α = σ α' ∧ β = σ β' ∧ γ = σ γ' := by
  classical
  refine ⟨ℚ⟮α, β, γ⟯, inferInstance,
    isNumberField_adjoin_of_isAlgebraic α β γ hα hβ hγ,
    IntermediateField.val _ |>.toRingHom, inferInstance, ?_⟩
  exact ⟨⟨α, subset_adjoin _ _ (by simp)⟩, ⟨β, subset_adjoin _ _ (by simp)⟩,
    ⟨γ, subset_adjoin _ _ (by simp)⟩, by simp⟩



section intDenom
variable {K : Type} [Field K] [NumberField K]
open AlgebraicDenominator
lemma gs_isAlgebraic_int (α : K) : IsAlgebraic ℤ α := by
  obtain ⟨y, hy, hr⟩ := exists_integral_multiples ℤ ℚ (L := K) {α}
  exact IsAlgebraic.of_smul_isIntegral (by simp [hy]) (hr α (mem_singleton_self _))
def gs_intDenom (α : K) : ℤ := (natDenominator α).cast
lemma gs_intDenom_ne_zero (α : K) : gs_intDenom α ≠ 0 :=
  Int.natCast_ne_zero.mpr (natDenominator_ne_zero (gs_isAlgebraic_int α))
lemma isIntegral_gs_intDenom_smul (α : K) : IsIntegral ℤ (gs_intDenom α • α) := by
  simpa [gs_intDenom, zsmul_eq_mul, Int.cast_natCast] using
    isIntegral_natDenominator_smul (S := K) α
lemma IsIntegral_assoc (K : Type) [Field K] {x y : ℤ} (z : ℤ) (α : K)
    (ha : IsIntegral ℤ (z • α)) : IsIntegral ℤ ((x * y * z : ℤ) • α) := by
  simpa [Int.cast_mul, zsmul_eq_mul, mul_assoc] using IsIntegral.smul (x * y) ha
end intDenom

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
def c₁ : ℤ := abs (gs_intDenom (K := h7.K) h7.α' * gs_intDenom (K := h7.K) h7.β' * gs_intDenom (K := h7.K) h7.γ')

lemma one_le_c₁ : 1 ≤ h7.c₁ := by
  exact Int.one_le_abs <| mul_ne_zero (mul_ne_zero (gs_intDenom_ne_zero (K := h7.K) h7.α')
    (gs_intDenom_ne_zero (K := h7.K) h7.β')) (gs_intDenom_ne_zero (K := h7.K) h7.γ')

lemma one_le_abs_c₁ : 1 ≤ |↑h7.c₁| := Int.one_le_abs (Ne.symm (Int.ne_of_lt h7.one_le_c₁))

lemma isIntegral_c₁α : IsIntegral ℤ (h7.c₁ • h7.α') := by
  have h := IsIntegral_assoc (K := h7.K) (x := gs_intDenom (K := h7.K) h7.γ') (y := gs_intDenom (K := h7.K) h7.β')
    (gs_intDenom (K := h7.K) h7.α') h7.α' (isIntegral_gs_intDenom_smul (K := h7.K) h7.α')
  conv => enter [2]; rw [c₁, mul_comm, mul_comm (gs_intDenom (K := h7.K) h7.α') (gs_intDenom (K := h7.K) h7.β'), ← mul_assoc]
  rcases abs_choice (gs_intDenom (K := h7.K) h7.γ' * gs_intDenom (K := h7.K) h7.β' * gs_intDenom (K := h7.K) h7.α') with H1 | H2
  · rw [H1]; exact h
  · rw [H2]; rw [← IsIntegral.neg_iff, neg_smul, neg_neg]; exact h

lemma isIntegral_c₁β : IsIntegral ℤ (h7.c₁ • h7.β') := by
  have h := IsIntegral_assoc (K := h7.K) (x := gs_intDenom (K := h7.K) h7.γ') (y := gs_intDenom (K := h7.K) h7.α')
    (gs_intDenom (K := h7.K) h7.β') h7.β' (isIntegral_gs_intDenom_smul (K := h7.K) h7.β')
  conv => enter [2]; rw [c₁, mul_comm, ← mul_assoc]
  rcases abs_choice (gs_intDenom (K := h7.K) h7.γ' * gs_intDenom (K := h7.K) h7.α' * gs_intDenom (K := h7.K) h7.β') with H1 | H2
  · rw [H1]; exact h
  · rw [H2]; rw [← IsIntegral.neg_iff, neg_smul, neg_neg]; exact h

lemma isIntegral_c₁γ : IsIntegral ℤ (h7.c₁ • h7.γ') := by
  have h := IsIntegral_assoc (K := h7.K) (x := gs_intDenom (K := h7.K) h7.α') (y := gs_intDenom (K := h7.K) h7.β')
    (gs_intDenom (K := h7.K) h7.γ') h7.γ' (isIntegral_gs_intDenom_smul (K := h7.K) h7.γ')
  rw [c₁]
  rcases abs_choice (gs_intDenom (K := h7.K) h7.α' * gs_intDenom (K := h7.K) h7.β' * gs_intDenom (K := h7.K) h7.γ') with H1 | H2
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

lemma isIntegral_c₁_pow_smul_pow (u : h7.K) (n k a l : ℕ) (hnk : a * l ≤ n * k)
    (H : IsIntegral ℤ (↑h7.c₁ * u)) : IsIntegral ℤ (h7.c₁ ^ (n * k) • u ^ (a * l)) := by
  rw [zsmul_eq_mul, Int.cast_pow, ← Nat.sub_add_cancel hnk, pow_add, mul_assoc, ← mul_pow]
  exact IsIntegral.mul (IsIntegral.pow (isIntegral_intCast (B := h7.K) h7.c₁) _) (IsIntegral.pow H _)

lemma isIntegral_c₁_pow_smul_α'_pow : IsIntegral ℤ
    (h7.c₁ ^ (a q t * h7.l q u) • (h7.α' ^ (a q t * h7.l q u))) := by
  apply h7.isIntegral_c₁_pow_smul_pow h7.α' (a q t) (h7.l q u) (a q t) (h7.l q u) (by rfl)
    (by grind [h7.isIntegral_c₁α])

lemma isIntegral_c₁_pow_smul_γ'_pow : IsIntegral ℤ (h7.c₁ ^ (b q t * h7.l q u) •
    (h7.γ'^ (b q t * (h7.l q u)))) := by
  apply h7.isIntegral_c₁_pow_smul_pow h7.γ' (b q t) (h7.l q u) (b q t) (h7.l q u) (by rfl)
    (by grind [h7.isIntegral_c₁γ])

include hq0 h2mq in
lemma al_le_mq (u : Fin (h7.m * h7.n q)) (t : Fin (q * q)) :
    a q t * h7.l q u ≤ h7.m * q := by
  simp [a, l]
  simpa [mul_comm] using Nat.mul_le_mul (finProdFinEquiv.symm t).1.isLt
    (finProdFinEquiv.symm u).1.isLt

include hq0 h2mq in
lemma bl_le_mq (u : Fin (h7.m * h7.n q)) (t : Fin (q * q)) :
    b q t * h7.l q u ≤ h7.m * q := by
  simp [a, l, b]
  simpa [mul_comm] using Nat.mul_le_mul (finProdFinEquiv.symm t).2.isLt
    (finProdFinEquiv.symm u).1.isLt

lemma isIntegral_c₁_pow_smul_α'_pow' :
    IsIntegral ℤ (h7.c₁ ^ (h7.m * q) • (h7.α' ^ (a q t * h7.l q u))) :=
  h7.isIntegral_c₁_pow_smul_pow h7.α' h7.m q (a q t) (h7.l q u)
    (by
      simp [a, l]
      have ht := (finProdFinEquiv.symm t).1.isLt
      have hu := (finProdFinEquiv.symm u).1.isLt
      simpa [mul_comm] using Nat.mul_le_mul ht hu)
    (by grind [h7.isIntegral_c₁α])

lemma isIntegral_c₁_pow_smul_γ'_pow' :
    IsIntegral ℤ (h7.c₁ ^ (h7.m * q) • (h7.γ' ^ (b q t * h7.l q u))) :=
  h7.isIntegral_c₁_pow_smul_pow h7.γ' h7.m q (b q t) (h7.l q u)
    (by
      simp [a, l, b]
      have ht := (finProdFinEquiv.symm t).2.isLt
      have hu := (finProdFinEquiv.symm u).1.isLt
      simpa [mul_comm] using Nat.mul_le_mul ht hu)
    (by grind [h7.isIntegral_c₁γ])

lemma c_coeffs_neq_zero : h7.c_coeffs q ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ (Ne.symm (Int.ne_of_lt h7.one_le_c₁)))
  (pow_ne_zero _ (Ne.symm (Int.ne_of_lt h7.one_le_c₁))))
  (pow_ne_zero _ (Ne.symm (Int.ne_of_lt h7.one_le_c₁)))

lemma isIntegral_c₁_pow_smul_add_smul_pow (n : ℕ) (k : ℕ) (hkn : k ≤ n - 1) (a : ℕ) (b : ℕ) :
    IsIntegral ℤ (h7.c₁ ^ (n - 1) • (↑a + ↑b • h7.β') ^ k) := by
  rw [zsmul_eq_mul, Int.cast_pow, ← Nat.sub_add_cancel hkn, pow_add, mul_assoc, ← mul_pow, mul_add]
  refine IsIntegral.mul (IsIntegral.pow (isIntegral_intCast (B := h7.K) h7.c₁) _)
    (IsIntegral.pow (IsIntegral.add ?_ ?_) _)
  · exact IsIntegral.mul (isIntegral_intCast (B := h7.K) h7.c₁) (isIntegral_natCast (B := h7.K) a)
  · rw [nsmul_eq_mul, ← mul_assoc, mul_comm (h7.c₁ : h7.K), mul_assoc]
    exact IsIntegral.mul (isIntegral_natCast (B := h7.K) b) (by grind [h7.isIntegral_c₁β])

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
      (Nat.le_sub_one_of_lt (finProdFinEquiv.symm u).2.isLt) (a q t) (b q t)

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
  simpa [mul_comm] using mul_le_mul (finProdFinEquiv.symm t).1.isLt
    (finProdFinEquiv.symm u).1.isLt zero_le zero_le

lemma isInt_β_bound : IsIntegral ℤ (h7.c₁ • (↑q + q • h7.β')) := by
  simpa [smul_add, zsmul_eq_mul, nsmul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
    (IsIntegral.add ((isIntegral_intCast (B := h7.K) h7.c₁).mul (isIntegral_natCast (B := h7.K) q))
      ((isIntegral_natCast (B := h7.K) q).mul h7.isIntegral_c₁β))

lemma isInt_β_bound_low (q : ℕ) (t : Fin (q * q)) :
    IsIntegral ℤ (h7.c₁ • (↑(a q t) + b q t • h7.β')) := by
  simpa [smul_add, zsmul_eq_mul, nsmul_eq_mul, mul_add,
  mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm] using
  (IsIntegral.add
    ((isIntegral_intCast (B := h7.K) h7.c₁).mul (isIntegral_natCast (B := h7.K) (a q t)))
    ((isIntegral_natCast (B := h7.K) (b q t)).mul h7.isIntegral_c₁β))

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
def c₂ : ℤ := abs h7.c₁ ^ (((1 + 2 * h7.m * (2 * h7.m))) + (1 + 2 * h7.m * (2 * h7.m)))

lemma one_le_c₂ : 1 ≤ h7.c₂ := by
  apply le_trans (Int.cast_one_le_of_pos h7.one_le_abs_c₁)
  nth_rw 1 [← pow_one (a := abs h7.c₁)]
  apply pow_le_pow_right₀ (h7.one_le_abs_c₁) (Nat.le_add_left 1
    ((1 + 2 * h7.m * (2 * h7.m)).add (Nat.add 1 (((2 * h7.m).mul
    (Nat.mul 2 (2 * h7.h + 1) + 1)).add (Nat.mul 2 (2 * h7.h + 1) + 1)))))

end Setup
