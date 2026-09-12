/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.NumberTheory.NumberField.House
public import Mathlib.RingTheory.Algebraic.Denominator

/-!
# Hilbert's Seventh Problem (Gelfond–Schneider Theorem)

This file develops the algebraic setup for a proof of the **Gelfond–Schneider Theorem**,
which resolves Hilbert's Seventh Problem: if `α` and `β` are algebraic with `α ≠ 0, 1` and `β`
irrational, then `α ^ β` is transcendental.

The proof is by contradiction: assuming `γ = α ^ β` is algebraic, one builds an auxiliary
exponential function whose coefficients solve an underdetermined homogeneous linear system over
a common number field `K` containing `α`, `β` and `γ`. This file supplies the algebraic half of
that construction: the field `K`, the parameters `m = 2h + 2` and `n = q² / (2m)` where
`h = [K : ℚ]`, the denominator-clearing factor `c₁`, the integral matrix `A` of the system, and
the height bounds on `A` and on the solution vector `η` that Siegel's lemma returns.

## Main results

- `exists_common_field_of_isAlgebraic`: a number field `K` containing `α`, `β` and `γ`.
- `house_matrixA_le`: an upper bound on the house of the entries of the Siegel matrix `A`.
- `house_eta_le_c₄_pow`: the resulting bound on the house of the solution vector `η`.

## References

* [Hua, L.-K., *Introduction to number theory*][hua1982house], pp. 488-493.
* A. O. Gelfond, *Sur le septième Problème de Hilbert*, 1934.
* T. Schneider, *Transzendenzuntersuchungen periodischer Funktionen*, 1935.
-/

@[expose] public section

open NumberField Finset IntermediateField Complex

noncomputable section

/-!
Suppose that `α, β, γ` lie in an algebraic field `K` with degree `h`.
-/

lemma isNumberField_adjoin_of_isAlgebraic (α β γ : ℂ) (hα : IsAlgebraic ℚ α)
    (hβ : IsAlgebraic ℚ β) (hγ : IsAlgebraic ℚ γ) :
    NumberField (adjoin ℚ {α, β, γ}) :=
  have : FiniteDimensional ℚ (adjoin ℚ {α, β, γ}) := finiteDimensional_adjoin fun _ hx ↦ by
    rcases hx with rfl | rfl | rfl
    exacts [isAlgebraic_iff_isIntegral.1 hα, isAlgebraic_iff_isIntegral.1 hβ,
      isAlgebraic_iff_isIntegral.1 hγ]
  NumberField.of_module_finite (K := ℚ) _

lemma exists_common_field_of_isAlgebraic (α β γ : ℂ) (hα : IsAlgebraic ℚ α)
    (hβ : IsAlgebraic ℚ β) (hγ : IsAlgebraic ℚ γ) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (σ : K →+* ℂ)
      (_ : DecidableEq (K →+* ℂ)),
      ∃ α' β' γ' : K, α = σ α' ∧ β = σ β' ∧ γ = σ γ' := by
  classical
  refine ⟨ℚ⟮α, β, γ⟯, _,
    isNumberField_adjoin_of_isAlgebraic α β γ hα hβ hγ,
    IntermediateField.val _ |>.toRingHom, inferInstance, ?_⟩
  exact ⟨⟨α, subset_adjoin _ _ (by simp)⟩, ⟨β, subset_adjoin _ _ (by simp)⟩,
    ⟨γ, subset_adjoin _ _ (by simp)⟩, by simp⟩

namespace GelfondSchneider

/-!
Let `α` and `β` be algebraic numbers with `α ≠ 0, 1` and `β` irrational.
We prove that `α ^ β` is transcendental by contradiction, assuming `γ = α ^ β` is algebraic.
-/

variable {K : Type*} [Field K] (α : ℂ) (β : ℂ) (σ : K →+* ℂ) (α' : K) (β' : K) (γ' : K)
  (hirr : ∀ i j : ℤ, β ≠ i / j) (htriv : α ≠ 0 ∧ α ≠ 1)
  (habc : α = σ α' ∧ β = σ β' ∧ α ^ β = σ γ')

include htriv in
lemma alpha_cpow_beta_ne_zero : α ^ β ≠ 0 :=
  fun H ↦ htriv.1 ((cpow_eq_zero_iff α β).mp H).1

include hirr in
lemma beta_ne_zero : β ≠ 0 :=
  fun H ↦ hirr 0 1 (by simpa [div_one] using H)

include htriv habc hirr in
lemma alpha'_beta'_gamma'_ne_zero : α' ≠ 0 ∧ β' ≠ 0 ∧ γ' ≠ 0 :=
  ⟨fun H ↦ htriv.1 (by simp [habc.1, H, map_zero σ]),
   fun H ↦ beta_ne_zero β hirr (by simp [habc.2.1, H, map_zero σ]),
   fun H ↦ alpha_cpow_beta_ne_zero α β htriv (by simp [habc.2.2, H, map_zero σ])⟩

variable [NumberField K]

/-- The integer denominator of `α`, given by `Algebra.natDenominator`. -/
abbrev intDenom (α : K) : ℤ := (Algebra.natDenominator α).cast

lemma intDenom_ne_zero (α : K) : intDenom α ≠ 0 :=
  Int.natCast_ne_zero.mpr <| IsAlgebraic.natDenominator_ne_zero <|
    IsFractionRing.isAlgebraic_iff ℤ ℚ K |>.mpr (.of_finite ℚ α)

/-- `c₁` is a positive integer such that `c₁ • α'`, `c₁ • β'`, and `c₁ • γ'`
are algebraic integers. -/
def c₁ : ℤ := abs (intDenom α' * intDenom β' * intDenom γ')

include α' β' γ' in
lemma one_le_c₁ : 1 ≤ c₁ α' β' γ' := Int.one_le_abs <|
  mul_ne_zero (mul_ne_zero (intDenom_ne_zero _) (intDenom_ne_zero _)) (intDenom_ne_zero _)

lemma c₁_ne_zero : c₁ α' β' γ' ≠ 0 := (Int.zero_lt_one.trans_le (one_le_c₁ _ _ _)).ne'

lemma one_le_abs_c₁ : 1 ≤ |c₁ α' β' γ'| := (one_le_c₁ _ _ _).trans (le_abs_self _)

omit [NumberField K] in
private lemma isIntegral_zsmul_of_dvd {c d : ℤ} {x : K} (h : IsIntegral ℤ (d • x))
    (hdc : d ∣ c) : IsIntegral ℤ (c • x) := by
  obtain ⟨e, rfl⟩ := hdc
  rw [mul_comm, mul_smul]
  exact h.zsmul e

omit [NumberField K] in
private lemma isIntegral_intDenom_smul (x : K) : IsIntegral ℤ (intDenom x • x) := by
  simpa [intDenom, zsmul_eq_mul] using Algebra.isIntegral_natDenominator_smul x

omit [NumberField K] in
lemma isIntegral_c₁α : IsIntegral ℤ (c₁ α' β' γ' • α') :=
  isIntegral_zsmul_of_dvd (isIntegral_intDenom_smul α')
    ((dvd_abs _ _).mpr ((dvd_mul_right _ _).mul_right _))

omit [NumberField K] in
lemma isIntegral_c₁β : IsIntegral ℤ (c₁ α' β' γ' • β') :=
  isIntegral_zsmul_of_dvd (isIntegral_intDenom_smul β')
    ((dvd_abs _ _).mpr ((dvd_mul_left _ _).mul_right _))

omit [NumberField K] in
lemma isIntegral_c₁γ : IsIntegral ℤ (c₁ α' β' γ' • γ') :=
  isIntegral_zsmul_of_dvd (isIntegral_intDenom_smul γ') ((dvd_abs _ _).mpr (dvd_mul_left _ _))


/-!
Let `m = 2h + 2` and `n = q² / (2m)`, where `q²` is a perfect square divisible by `2m`.
-/

/-- The finrank of the field extension `K`. -/
def h (K : Type*) [Field K] [NumberField K] : ℕ := Module.finrank ℚ K

/-- A parameter `m` dependent on the degree `h = [K : ℚ]`. -/
def m (K : Type*) [Field K] [NumberField K] : ℕ := 2 * (h K) + 2

lemma one_le_m (K : Type*) [Field K] [NumberField K] : 1 ≤ m K :=
  Nat.succ_le_succ (Nat.zero_le (2 * (h K) + 1))

variable (q : ℕ) (hq0 : 0 < q)

/-- A target bound parameter `n` dependent on a free parameter `q`. -/
def n (K : Type*) [Field K] [NumberField K] (q : ℕ) : ℕ := q ^ 2 / (2 * (m K))

/-- House exponent `m K * (2 * (m K * n K q))`. -/
abbrev houseExponent (K : Type*) [Field K] [NumberField K] (q : ℕ) : ℕ :=
  m K * (2 * (m K * n K q))

variable (u : Fin (m K * n K q)) (t : Fin (q * q))

/-- A variable `a` that satisfies `1 ≤ a ≤ q`. -/
def a : ℕ := (finProdFinEquiv.symm t).1 + 1

/-- A variable `b` that satisfies `1 ≤ b ≤ q`. -/
def b : ℕ := (finProdFinEquiv.symm t).2 + 1

/-- The value `(a + bβ) log α` for `1 ≤ a, b ≤ q`. -/
def ρ : ℂ := (a q t + (b q t • β)) * Complex.log α

/-!
We introduce the integral function
  `R(x) = η₁ e^(ρ₁ x) + … + ηₜ e^(ρₜ x)`
where the coefficients `η₁, …, ηₜ` are determined by the following conditions.

We solve the system of `mn` homogeneous linear equations
  `(log α)⁻ᵏ R⁽ᵏ⁾(l) = 0,  0 ≤ k ≤ n - 1, 1 ≤ l ≤ m`
in the `t = 2mn` unknowns `η₁, …, ηₜ`. It follows from
`house.exists_ne_zero_int_vec_house_le` that there is a non-trivial set of integer
solutions `η₁, …, ηₜ` in `K`.
-/

/-!
The coefficients are in `K` and
  `(log α)⁻ᵏ ((a + bβ) log α)ᵏ e^(l(a + bβ) log α) = (a + bβ)ᵏ αᵃˡ γᵇˡ`
for `1 ≤ l ≤ m, 1 ≤ a, b ≤ q, 0 ≤ k ≤ n - 1`.-/

/-- A variable `k` that satisfies 0 ≤ k ≤ n - 1 -/
def k : ℕ := (finProdFinEquiv.symm u).2

/-- A variable `l` that satisfies 1 ≤ l ≤ m -/
def l : ℕ := (finProdFinEquiv.symm u).1 + 1

lemma a_le : a q t ≤ q := Nat.succ_le_of_lt (finProdFinEquiv.symm t).1.isLt

lemma one_le_b : 1 ≤ b q t := Nat.le_add_left 1 _

lemma b_le : b q t ≤ q := Nat.succ_le_of_lt (finProdFinEquiv.symm t).2.isLt

lemma k_lt : k q u < n K q := (finProdFinEquiv.symm u).2.isLt

lemma l_le : l q u ≤ m K := Nat.succ_le_of_lt (finProdFinEquiv.symm u).1.isLt

include u in
omit t in
lemma k_le_n_sub_one : k q u ≤ n K q - 1 :=
  Nat.le_sub_one_of_lt (k_lt q u)

include u t in
lemma al_le_mq : a q t * l q u ≤ m K * q :=
  (Nat.mul_le_mul (a_le q t) (l_le q u)).trans_eq (mul_comm _ _)

include u t in
lemma bl_le_mq : b q t * l q u ≤ m K * q :=
  (Nat.mul_le_mul (b_le q t) (l_le q u)).trans_eq (mul_comm _ _)

/-- The core algebraic coefficient appearing in the evaluation of the `k`-th derivative
of the auxiliary function at point `l`. Evaluates to `(a + bβ')^k * α'^(al) * γ'^(bl)`. -/
abbrev systemCoeffs : K :=
  (a q t + b q t • β') ^ (k q u) * α' ^ (a q t * l q u) * γ' ^ (b q t * l q u)

variable (h2mq : 2 * m K ∣ q ^ 2)

include h2mq in
lemma two_mul_m_mul_n_eq_sq : 2 * (m K * n K q) = q ^ 2 := by
  rw [← mul_assoc]; exact Nat.mul_div_cancel' h2mq

include hq0 h2mq in
lemma one_le_n : 1 ≤ n K q :=
  (Nat.one_le_div_iff (by positivity [one_le_m K])).2 (Nat.le_of_dvd (Nat.pow_pos hq0) h2mq)

include hq0 h2mq in
/-- The Siegel system has a positive number `m n` of equations. -/
lemma m_mul_n_pos : 0 < m K * n K q :=
  Nat.mul_pos (one_le_m K) (one_le_n q hq0 h2mq)

/-!
Let `c₁, c₂, …` be natural numbers independent of `n`. There exists `c₁` such that
`c₁ α, c₁ β, c₁ γ` are integers in `K`.
-/

/-- A combined integer scaling factor `c₁^(n-1 + 2mq)` applied to the linear system to clear
all denominators and ensure the resulting matrix entries are algebraic integers. -/
abbrev cCoeffs (q : ℕ) : ℤ :=
  c₁ α' β' γ' ^ (n K q - 1) * c₁ α' β' γ' ^ (m K * q) * c₁ α' β' γ' ^ (m K * q)

omit [NumberField K] in
/-- Re-pair a scalar power with the element it scales: `c ^ N • x ^ i` splits as the unmatched
factor `c ^ (N - i)` times the `i`-th power of `c • x`, whenever `i ≤ N`. -/
private lemma zsmul_pow_eq {c : ℤ} {x : K} {i N : ℕ} (hiN : i ≤ N) :
    c ^ N • x ^ i = c ^ (N - i) • (c • x) ^ i := by
  rw [smul_pow, ← mul_smul, ← pow_add, Nat.sub_add_cancel hiN]

omit [NumberField K] in
/-- If `c • x` is an algebraic integer and `i ≤ N`, then so is `c ^ N • x ^ i`. -/
lemma isIntegral_zsmul_pow {c : ℤ} {x : K} (h : IsIntegral ℤ (c • x)) {i N : ℕ}
    (hiN : i ≤ N) : IsIntegral ℤ (c ^ N • x ^ i) := by
  rw [zsmul_pow_eq hiN]
  exact (h.pow i).zsmul _

/-- Scaling `x ^ i` by `c ^ N` with `i ≤ N`: the unmatched factor `|c| ^ (N - i)` comes out,
and the paired part is bounded with any exponent `M ≥ i`. -/
private lemma house_zsmul_pow_le {c : ℤ} {x : K} (h : 1 ≤ house (c • x)) {i N M : ℕ}
    (hiN : i ≤ N) (hiM : i ≤ M) :
    house (c ^ N • x ^ i) ≤ |c| ^ (N - i) * (|c| * house x) ^ M := by
  rw [zsmul_pow_eq hiN, house_zsmul, abs_pow, Int.cast_pow]
  gcongr
  exact (house_pow_le_pow h hiM).trans_eq (by rw [house_zsmul])

/-!
Multiplying the system by `c₁^(n-1) c₁^(mq) c₁^(mq) = c₁^(n-1+2mq) ≤ c₂^n` ensures the
coefficients are integers in `K`.
-/

lemma zsmul_mul_mul_distrib {K : Type*} [Field K] (a b c : ℤ) (x y z : K) :
    ((a * b) * c) • ((x * y) * z) = a • x * b • y * c • z := by
  simp [zsmul_eq_mul]; ring

omit [NumberField K] in
private lemma isIntegral_c₁_smul_addNSMul (a b : ℕ) :
    IsIntegral ℤ (c₁ α' β' γ' • ((a : K) + b • β')) := by
  simpa [smul_add, zsmul_eq_mul, nsmul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
    ((isIntegral_intCast (c₁ α' β' γ')).mul (isIntegral_natCast a)).add
      ((isIntegral_natCast b).mul (isIntegral_c₁β α' β' γ'))

omit [NumberField K] in
/-- The scaled sum `c₁ • (a + b • β')` is an algebraic integer over `ℤ`. -/
lemma isIntegral_c₁_smul_a_b_β' :
    IsIntegral ℤ (c₁ α' β' γ' • ((a q t : K) + b q t • β')) := by
  simpa [smul_add, zsmul_eq_mul, nsmul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
    ((isIntegral_intCast (c₁ α' β' γ')).mul (isIntegral_natCast (a q t))).add
      ((isIntegral_natCast (b q t)).mul (isIntegral_c₁β α' β' γ'))

/-- The scaled system coefficient `cCoeffs • systemCoeffs` is an algebraic integer over `ℤ`. -/
lemma isIntegral_cCoeffs_smul_systemCoeffs :
    IsIntegral ℤ (cCoeffs α' β' γ' q • systemCoeffs α' β' γ' q u t) := by
  rw [zsmul_mul_mul_distrib, mul_assoc]
  exact (isIntegral_zsmul_pow (isIntegral_c₁_smul_a_b_β' α' β' γ' q t) (k_le_n_sub_one q u)).mul
    ((isIntegral_zsmul_pow (isIntegral_c₁α α' β' γ') (al_le_mq q u t)).mul
      (isIntegral_zsmul_pow (isIntegral_c₁γ α' β' γ') (bl_le_mq q u t)))

/-- The matrix representing the homogeneous linear system of `mn` equations in `q^2` unknowns.
Its entries are scaled to strictly reside in the ring of integers `𝓞 K`. -/
def A : Matrix (Fin (m K * n K q)) (Fin (q * q)) (𝓞 K) :=
  fun i j ↦ RingOfIntegers.restrict _
  (fun _ ↦ isIntegral_cCoeffs_smul_systemCoeffs α' β' γ' q i j) ℤ

lemma map_A : algebraMap (𝓞 K) K (A α' β' γ' q u t) =
    cCoeffs α' β' γ' q • systemCoeffs α' β' γ' q u t :=
  (rfl)

include hirr σ habc in
lemma a_add_b_smul_β'_ne_zero : ((a q t : K) + b q t • β') ≠ 0 := fun H ↦
  hirr (-(a q t : ℤ)) (b q t) <| by
    have hEq : (a q t : ℂ) + b q t * β = 0 := by
      simpa [nsmul_eq_mul, map_add, map_mul, ← habc.2.1] using congrArg σ H
    push_cast
    exact eq_div_iff_mul_eq
      (Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp (one_le_b q t))) |>.mpr
      (by linear_combination hEq)

include α β σ hirr htriv habc in
lemma c₁α_ne_zero : c₁ α' β' γ' • α' ≠ 0 :=
  smul_ne_zero (c₁_ne_zero _ _ _)
    (alpha'_beta'_gamma'_ne_zero α β σ α' β' γ' hirr htriv habc).1

include α β σ hirr htriv habc in
lemma c₁γ_ne_zero : c₁ α' β' γ' • γ' ≠ 0 :=
  smul_ne_zero (c₁_ne_zero _ _ _)
    (alpha'_beta'_gamma'_ne_zero α β σ α' β' γ' hirr htriv habc).2.2

/-- If `x ≠ 0` and `c₁ • x` is an algebraic integer, its house is at least `1`. -/
private lemma one_le_house_c₁_smul {x : K} (hx : IsIntegral ℤ (c₁ α' β' γ' • x))
    (hx0 : x ≠ 0) : 1 ≤ house (c₁ α' β' γ' • x) :=
  one_le_house_of_isIntegral hx (smul_ne_zero (c₁_ne_zero _ _ _) hx0)

/-- A large integer constant independent of `n` and `q`, used as a foundational base
to bound the houses (maximum absolute values of conjugates) of the algebraic coefficients. -/
def c₂ : ℤ := (|c₁ α' β' γ'| ^ (((1 + 2 * (m K) * (2 * (m K)))) + (1 + 2 * (m K) * (2 * (m K)))))

lemma one_le_c₂ : 1 ≤ c₂ α' β' γ' := one_le_pow₀ (one_le_abs_c₁ α' β' γ')

open Real

/-- A real-valued bounding constant encompassing `c₂` and the houses of `α'`, `β'`, and `γ'`.
Used to establish a strict upper bound on the entries of the linear system matrix `A`. -/
def c₃ : ℝ := c₂ α' β' γ' * (1 + house β') * sqrt (2 * m K) *
  (max 1 ((house α' ^ (2 * m K ^ 2)) * house γ' ^ (2 * m K ^ 2)))

/-- `√(2m)` is at least `1`, since `1 ≤ m`. -/
lemma one_le_sqrt_two_mul_m : (1 : ℝ) ≤ √(2 * m K) :=
  one_le_sqrt.mpr (mod_cast (by have := one_le_m K; linarith))

lemma one_le_c₃ : 1 ≤ c₃ α' β' γ' :=
  one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
  (one_le_mul_of_one_le_of_one_le (mod_cast one_le_c₂ α' β' γ') <|
  le_add_of_nonneg_right <| house_nonneg _) <|
  one_le_sqrt_two_mul_m) <| le_max_left 1 _

/-! Moreover, the absolute value of the conjugates of the various coefficients is at most
  `c₂^n (q + q * |β|) ^ (n - 1) * |α| ^ (m q) * |γ| ^ (m q) ≤ c₃^n * n^((n - 1) / 2)`.
-/

include h2mq in
lemma mq_le_m_two_mnq : (m K) * q ≤ (m K) * (2 * ((m K) * (n K q))) :=
  Nat.mul_le_mul_left _ <| (two_mul_m_mul_n_eq_sq q h2mq).symm ▸ Nat.le_self_pow two_ne_zero q

lemma house_a_add_b_smul_le :
    house ((a q t : K) + b q t • β') ≤ |(q : ℤ)| * (1 + house β') := by
  rw [mul_one_add]
  refine (house_add_le _ _).trans (add_le_add ?_ ((house_nsmul _ _).le.trans ?_))
  · rw [house_natCast]; exact_mod_cast a_le q t
  · gcongr; exact_mod_cast b_le q t

include α' β' γ' hq0 h2mq q in
/-- The `c₂`-level bound is at most `c₃ ^ n * n ^ ((n - 1) / 2)`. This step is pure arithmetic
in the constants: it needs neither `σ` nor the transcendence hypotheses. -/
lemma c₂_bound_le_c₃ :
    ↑(c₂ α' β' γ') ^ (n K q) *
      (↑|↑q| ^ ((n K q ) - 1) * (1 + house β') ^ (n K q - 1) *
      house α' ^ (houseExponent K q) *
      house γ' ^ (houseExponent K q)) ≤
    c₃ α' β' γ' ^ (n K q : ℝ) *
      (n K q : ℝ) ^ (((n K q : ℝ) - 1) / 2) := by
  have hpow : ∀ x : ℝ, x ^ houseExponent K q = (x ^ (2 * m K ^ 2)) ^ n K q := fun x ↦ by
    rw [← pow_mul]; congr 1; ring
  have hq : |(q : ℝ)| = √(2 * m K) * √(n K q) := by
    rw [← sqrt_mul (by positivity), show (2 * (m K : ℝ) * n K q) = (q : ℝ) ^ 2 from
      by exact_mod_cast (mul_assoc 2 (m K) (n K q)) ▸ two_mul_m_mul_n_eq_sq q h2mq,
      sqrt_sq_eq_abs]
  rw [show (n K q : ℝ) ^ (((n K q : ℝ) - 1) / 2) = √(n K q) ^ (n K q - 1) by
      rw [sqrt_eq_rpow, ← rpow_natCast _ (n K q - 1), ← rpow_mul (Nat.cast_nonneg _),
        Nat.cast_sub (one_le_n q hq0 h2mq), Nat.cast_one]
      ring_nf,
    rpow_natCast, hq, hpow, hpow, show c₃ α' β' γ' ^ n K q = ↑(c₂ α' β' γ') ^ n K q *
      (1 + house β') ^ n K q * √(2 * m K) ^ n K q *
      max 1 (house α' ^ (2 * m K ^ 2) * house γ' ^ (2 * m K ^ 2)) ^ n K q by
      rw [c₃, mul_pow, mul_pow, mul_pow]]
  calc
    _ = ↑(c₂ α' β' γ') ^ n K q * (1 + house β') ^ (n K q - 1) * √(2 * m K) ^ (n K q - 1) *
          (house α' ^ (2 * m K ^ 2) * house γ' ^ (2 * m K ^ 2)) ^ n K q *
          √(n K q) ^ (n K q - 1) := by ring
    _ ≤ _ := by
      gcongr
      any_goals (unfold c₂; positivity)
      · exact le_add_of_nonneg_right (house_nonneg _)
      · exact Nat.sub_le _ 1
      · exact one_le_sqrt_two_mul_m
      · exact Nat.sub_le _ 1
      · exact le_max_right _ _

include α β σ hirr htriv habc hq0 h2mq in
lemma house_cCoeffs_smul_le_c₃ :
    house (cCoeffs α' β' γ' q • systemCoeffs α' β' γ' q u t) ≤
      c₃ α' β' γ' ^ (n K q : ℝ) * (n K q : ℝ) ^ (((n K q : ℝ) - 1) / 2) := by
  have hE := mq_le_m_two_mnq (K := K) q h2mq
  have hexp : (n K q - 1 - k q u) + (m K * q - a q t * l q u) + (m K * q - b q t * l q u) +
      ((n K q - 1) + (houseExponent K q + houseExponent K q)) ≤
      ((1 + 2 * m K * (2 * m K)) + (1 + 2 * m K * (2 * m K))) * n K q := by
    grind [k_le_n_sub_one q u, al_le_mq q u t, bl_le_mq q u t]
  rw [zsmul_mul_mul_distrib]
  calc _ ≤ |c₁ α' β' γ'| ^ (n K q - 1 - k q u) *
            (|c₁ α' β' γ'| * (|(q : ℤ)| * (1 + house β'))) ^ (n K q - 1) *
          (|c₁ α' β' γ'| ^ (m K * q - a q t * l q u) *
            (|c₁ α' β' γ'| * house α') ^ houseExponent K q) *
          (|c₁ α' β' γ'| ^ (m K * q - b q t * l q u) *
            (|c₁ α' β' γ'| * house γ') ^ houseExponent K q) := ?_
    _ = (|c₁ α' β' γ'| : ℝ) ^ ((n K q - 1 - k q u) + (m K * q - a q t * l q u) +
          (m K * q - b q t * l q u) + ((n K q - 1) +
            (houseExponent K q + houseExponent K q))) *
          (↑|↑q| ^ ((n K q) - 1) * (1 + house β') ^ (n K q - 1) *
            house α' ^ (houseExponent K q) * house γ' ^ (houseExponent K q)) := ?_
    _ ≤ ↑(c₂ α' β' γ') ^ (n K q) *
          (↑|↑q| ^ ((n K q ) - 1) * (1 + house β') ^ (n K q - 1) *
          house α' ^ (houseExponent K q) *
          house γ' ^ (houseExponent K q)) := ?_
    _ ≤ _ := ?_
  · obtain ⟨hα, -, hγ⟩ := alpha'_beta'_gamma'_ne_zero α β σ α' β' γ' hirr htriv habc
    refine ((house_mul_le _ _).trans (mul_le_mul_of_nonneg_right (house_mul_le _ _)
      (house_nonneg _))).trans ?_
    gcongr
    · exact (house_zsmul_pow_le (one_le_house_c₁_smul _ _ _
        (isIntegral_c₁_smul_a_b_β' α' β' γ' q t)
        (a_add_b_smul_β'_ne_zero α β σ α' β' γ' hirr habc q t))
        (k_le_n_sub_one q u) (k_le_n_sub_one q u)).trans
        (by gcongr; exact house_a_add_b_smul_le β' q t)
    · exact house_zsmul_pow_le (one_le_house_c₁_smul _ _ _ (isIntegral_c₁α α' β' γ') hα)
        (al_le_mq q u t) ((al_le_mq q u t).trans hE)
    · exact house_zsmul_pow_le (one_le_house_c₁_smul _ _ _ (isIntegral_c₁γ α' β' γ') hγ)
        (bl_le_mq q u t) ((bl_le_mq q u t).trans hE)
  · push_cast [abs_mul, abs_pow, mul_pow]
    ring
  · rw [c₂]
    push_cast [← pow_mul]
    gcongr
    exact mod_cast one_le_abs_c₁ α' β' γ'
  · exact c₂_bound_le_c₃ α' β' γ' q hq0 h2mq

include α β σ hirr htriv habc hq0 h2mq in
lemma house_matrixA_le :
    house ((algebraMap (𝓞 K) K) ((A α' β' γ' q) u t)) ≤
      (c₃ α' β' γ' ^ (n K q : ℝ) * (n K q : ℝ) ^ (((n K q : ℝ) - 1) / 2)) :=
  map_A α' β' γ' q u t ▸
    house_cCoeffs_smul_le_c₃ α β σ α' β' γ' hirr htriv habc q hq0 u t h2mq

include α β σ α' β' γ' hirr htriv habc q hq0 h2mq in
/-- The matrix `A` is nonzero, ensuring Siegel's lemma yields a nontrivial solution. -/
lemma A_ne_zero : A α' β' γ' q ≠ 0 := by
  intro H
  let u : Fin _ := ⟨0, m_mul_n_pos q hq0 h2mq⟩
  let t : Fin _ := ⟨0, mul_pos hq0 hq0⟩
  have H_eval : (A α' β' γ' q u t).val = 0 := by rw [H]; rfl
  simp only [A, RingOfIntegers.restrict, zsmul_eq_mul, Int.cast_mul, Int.cast_pow] at H_eval
  obtain ⟨hα, _, hγ⟩ := alpha'_beta'_gamma'_ne_zero α β σ α' β' γ' hirr htriv habc
  have := a_add_b_smul_β'_ne_zero α β σ α' β' γ' hirr habc q t
  revert H_eval; simp [c₁_ne_zero, hα, hγ]; grind

include hq0 h2mq in
/-- The Siegel system is underdetermined: there are fewer equations `m n` than unknowns `q²`. -/
lemma m_mul_n_lt_sq : m K * n K q < q * q :=
  (lt_two_mul_self (m_mul_n_pos q hq0 h2mq)).trans_eq
    ((two_mul_m_mul_n_eq_sq q h2mq).trans (pow_two q))

variable [DecidableEq (K →+* ℂ)]

include α β σ α' β' γ' hirr htriv habc hq0 h2mq in
/-- Siegel's lemma applied to the scaled matrix `A`: a non-zero integral kernel vector whose
entries have controlled house. -/
theorem exists_eta :
    ∃ ξ : Fin (q * q) → 𝓞 K, ξ ≠ 0 ∧ (A α' β' γ' q).mulVec ξ = 0 ∧
      ∀ l, house (ξ l).1 ≤ house.c₁ K * ((house.c₁ K * ↑(q * q) *
        (c₃ α' β' γ' ^ (n K q : ℝ) * (n K q : ℝ) ^ (((n K q : ℝ) - 1) / 2))) ^
        ((↑(m K * n K q) : ℝ) / (↑(q * q) - ↑(m K * n K q)))) :=
  house.exists_ne_zero_int_vec_house_le K (A α' β' γ' q)
    (A_ne_zero α β σ α' β' γ' hirr htriv habc q hq0 h2mq)
    (m_mul_n_pos q hq0 h2mq) (m_mul_n_lt_sq q hq0 h2mq) (Fintype.card_fin _)
    (fun u t ↦ house_matrixA_le α β σ α' β' γ' hirr htriv habc q hq0 u t h2mq)
    (Fintype.card_fin _)

/-- A non-trivial integer vector (in `𝓞 K`) residing in the kernel of the matrix `A`.
Its existence is guaranteed by Siegel's lemma (`exists_ne_zero_int_vec_house_le`). -/
def η : Fin (q * q) → 𝓞 K :=
  (exists_eta α β σ α' β' γ' hirr htriv habc q hq0 h2mq).choose

/-- The Siegel factor `c₁(K)² · 2m` is at least `1`. -/
lemma one_le_houseC₁_sq_mul : (1 : ℝ) ≤ house.c₁ K * house.c₁ K * 2 * m K := by
  have h1 := house.one_le_c₁ K
  have hm : (1 : ℝ) ≤ (m K : ℝ) := mod_cast one_le_m K
  nlinarith

/-- A real-valued bounding constant used to bound the norm (house) of the
solution vector `η`. -/
def c₄ : ℝ := house.c₁ K * house.c₁ K * 2 * m K * c₃ α' β' γ'

include hq0 h2mq in
/-- The bound on the entries of `η` supplied by Siegel's lemma. -/
lemma η_spec (t : Fin (q * q)) :
    house (algebraMap (𝓞 K) K
        (η (K := K) α β σ α' β' γ' hirr htriv habc q hq0 h2mq t)) ≤
      house.c₁ K * (house.c₁ K * ↑(q * q) *
        (c₃ α' β' γ' ^ (n K q : ℝ) * (n K q : ℝ) ^ (((n K q : ℝ) - 1) / 2))) ^
        ((↑(m K * n K q) : ℝ) / (↑(q * q) - ↑(m K * n K q))) :=
  (exists_eta α β σ α' β' γ' hirr htriv habc q hq0 h2mq).choose_spec.2.2 t

/--
`‖ηₖ‖ ≤ c₄ⁿ * n^((n + 1) / 2)`, for `1 ≤ k ≤ t`.
-/
lemma house_eta_le_c₄_pow :
    house (algebraMap (𝓞 K) K
        (η (K := K) α β σ α' β' γ' hirr htriv habc q hq0 h2mq t)) ≤
      c₄ α' β' γ' ^ (n K q : ℝ) * (n K q : ℝ) ^ (((n K q : ℝ) + 1) / 2) := by
  have hn : (1 : ℝ) ≤ (n K q : ℝ) := mod_cast one_le_n q hq0 h2mq
  have hA := one_le_houseC₁_sq_mul (K := K)
  have hN : (n K q : ℝ) * (n K q : ℝ) ^ (((n K q : ℝ) - 1) / 2) =
      (n K q : ℝ) ^ (((n K q : ℝ) + 1) / 2) := by
    rw [show ((n K q : ℝ) + 1) / 2 = 1 + ((n K q : ℝ) - 1) / 2 from by ring,
      rpow_one_add' (by positivity) (ne_of_gt (by linarith))]
  calc _ ≤ house.c₁ K * (house.c₁ K * ↑(q * q) *
            (c₃ α' β' γ' ^ (n K q : ℝ) *
            (n K q : ℝ) ^ (((n K q : ℝ) - 1) / 2))) ^
            ((↑(m K * n K q) : ℝ) / (↑(q * q) - ↑(m K * n K q))) := ?_
      _ = house.c₁ K * house.c₁ K * 2 * m K *
            c₃ α' β' γ' ^ (n K q : ℝ) * ((n K q : ℝ) *
            (n K q : ℝ) ^ (((n K q : ℝ) - 1) / 2)) := ?_
      _ ≤ c₄ α' β' γ' ^ (n K q : ℝ) *
            (n K q : ℝ) ^ (((n K q : ℝ) + 1) / 2) := ?_
  · exact η_spec α β σ α' β' γ' hirr htriv habc q hq0 h2mq t
  · push_cast
    rw [show (q : ℝ) * q = 2 * ((m K : ℝ) * n K q) from mod_cast
          (pow_two q).symm.trans (two_mul_m_mul_n_eq_sq q h2mq).symm,
        show (2 : ℝ) * ((m K : ℝ) * n K q) - (m K : ℝ) * n K q = (m K : ℝ) * n K q by ring,
        div_self (mod_cast (m_mul_n_pos q hq0 h2mq).ne'), rpow_one]
    ring
  · rw [hN, c₄, mul_rpow (by linarith) (zero_le_one.trans (one_le_c₃ _ _ _))]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (Real.self_le_rpow_of_one_le hA hn)
        (rpow_nonneg (zero_le_one.trans (one_le_c₃ _ _ _)) _)) (by positivity)

end GelfondSchneider
