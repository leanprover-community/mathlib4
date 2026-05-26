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
- `house_matrixA_le`: an upper bound on the house norm of entries of the Siegel matrix `A`.
- `house_eta_le_c₄_pow`: the resulting bound on the house norm of the solution vector `η`.

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

namespace GelfondSchneider

/-!
Let `α` and `β` be algebraic numbers with `α ≠ 0, 1` and `β` irrational.
We prove that `α ^ β` is transcendental by contradiction, assuming `γ = α ^ β` is algebraic.
-/

variable {K : Type} [Field K] (α : ℂ) (β : ℂ) (σ : K →+* ℂ) (α' : K) (β' : K) (γ' : K)
  (hirr : ∀ i j : ℤ, β ≠ i / j) (htriv : α ≠ 0 ∧ α ≠ 1) (hα : IsAlgebraic ℚ α)
  (hβ : IsAlgebraic ℚ β) (habc : α = σ α' ∧ β = σ β' ∧ α ^ β = σ γ')
  (hd : DecidableEq (K →+* ℂ))

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
lemma alpha'_beta'_gamma'_ne_zero : α' ≠ 0 ∧ β' ≠ 0 ∧ γ' ≠ 0 :=
  ⟨fun H ↦ htriv.1 (by simp [habc.1, H, map_zero σ]),
   fun H ↦ beta_ne_zero β hirr (by simp [habc.2.1, H, map_zero σ]),
   fun H ↦ alpha_gamma_pow_beta_ne_zero α β htriv (by simp [habc.2.2, H, map_zero σ])⟩

include htriv habc hirr in
lemma beta'_ne_zero : β' ≠ 0 :=
  (alpha'_beta'_gamma'_ne_zero α β σ α' β' γ' hirr htriv habc).2.1

include htriv in
lemma log_α_ne_zero : log α ≠ 0 :=
  mt (fun h ↦ by simpa [exp_log htriv.1] using congrArg exp h) htriv.2

variable [NumberField K]

open AlgebraicDenominator

/-- Every element of a number field is algebraic over `ℤ`. -/
lemma isAlgebraic_int (α : K) : IsAlgebraic ℤ α := by
  obtain ⟨y, hy, hr⟩ := exists_integral_multiples ℤ ℚ (L := K) {α}
  exact IsAlgebraic.of_smul_isIntegral (by simp [hy]) (hr α (mem_singleton_self _))

/-- The integer denominator of `α`, given by `natDenominator`. -/
abbrev intDenom (α : K) : ℤ := (natDenominator α).cast

lemma intDenom_ne_zero (α : K) : intDenom α ≠ 0 :=
  Int.natCast_ne_zero.mpr (natDenominator_ne_zero (isAlgebraic_int α))

/-- `c₁` is a positive integer such that `c₁ • α'`, `c₁ • β'`, and `c₁ • γ'`
are algebraic integers. -/
def c₁ : ℤ := abs (intDenom α' * intDenom β' * intDenom γ')

include α' β' γ' in
lemma one_le_c₁ : 1 ≤ c₁ α' β' γ' := Int.one_le_abs <|
  mul_ne_zero (mul_ne_zero (intDenom_ne_zero _) (intDenom_ne_zero _)) (intDenom_ne_zero _)

lemma c₁_ne_zero : c₁ α' β' γ' ≠ 0 := (Int.zero_lt_one.trans_le (one_le_c₁ _ _ _)).ne'

lemma one_le_abs_c₁ : 1 ≤ |c₁ α' β' γ'| := (one_le_c₁ _ _ _).trans (le_abs_self _)

omit [NumberField K] in
private lemma isIntegral_zsmul_of_abs {x : ℤ} {u : K} (h : IsIntegral ℤ (x • u)) :
    IsIntegral ℤ (|x| • u) :=
  (abs_choice x).elim (·.symm ▸ h) fun hx ↦ hx.symm ▸ (neg_smul x u).symm ▸ h.neg

omit [NumberField K] in
private lemma isIntegral_c₁_smul_aux (x : K) (a b : ℤ)
    (he : a * b * intDenom x = intDenom α' * intDenom β' * intDenom γ') :
    IsIntegral ℤ (c₁ α' β' γ' • x) := by
  rw [c₁, ← he]
  exact isIntegral_zsmul_of_abs <| by
    simpa [zsmul_eq_mul, mul_assoc, intDenom] using
      IsIntegral.smul (a * b) (isIntegral_natDenominator_smul x)

omit [NumberField K] in
lemma isIntegral_c₁α : IsIntegral ℤ (c₁ α' β' γ' • α') :=
  isIntegral_c₁_smul_aux _ _ _ α' (intDenom γ') (intDenom β') (by ring)

omit [NumberField K] in
lemma isIntegral_c₁β : IsIntegral ℤ (c₁ α' β' γ' • β') :=
  isIntegral_c₁_smul_aux _ _ _ β' (intDenom γ') (intDenom α') (by ring)

omit [NumberField K] in
lemma isIntegral_c₁γ : IsIntegral ℤ (c₁ α' β' γ' • γ') :=
  isIntegral_c₁_smul_aux _ _ _ γ' (intDenom α') (intDenom β') (by ring)

/-!
Let `m = 2h + 2` and `n = q² / (2m)`, where `q²` is a perfect square divisible by `2m`.
-/

/-- The finrank of the field extension `K`. -/
def h (K : Type) [Field K] [NumberField K] : ℕ := Module.finrank ℚ K

/-- A parameter `m` dependent on the degree `h = [K : ℚ]`. -/
def m (K : Type) [Field K] [NumberField K] : ℕ := 2 * h K + 2

lemma one_le_m (K : Type) [Field K] [NumberField K] : 1 ≤ m K :=
  Nat.succ_le_succ (Nat.zero_le (2 * h K + 1))

variable (q : ℕ) (hq0 : 0 < q)

/-- A target bound parameter `n` dependent on a free parameter `q`. -/
def n (K : Type) [Field K] [NumberField K] (q : ℕ) : ℕ := q ^ 2 / (2 * m K)

/-- House exponent `m K * (2 * (m K * n K q))`. -/
def mTwoMnq (K : Type) [Field K] [NumberField K] (q : ℕ) : ℕ :=
  m K * (2 * (m K * n K q))

variable (u : Fin (m K * n K q)) (t : Fin (q * q))

/-- A variable `a` that satisfies `1 ≤ a ≤ q`. -/
def a : ℕ := (finProdFinEquiv.symm.toFun t).1 + 1

/-- A variable `b` that satisfies `1 ≤ b ≤ q`. -/
def b : ℕ := (finProdFinEquiv.symm.toFun t).2 + 1

/-- The value `(a + bβ) log α` for `1 ≤ a, b ≤ q`. -/
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

variable (h2mq : 2 * m K ∣ q ^ 2)

include hq0 h2mq in
lemma n_one_le : 1 ≤ n K q := by
  simp only [n, m, h]
  exact (Nat.one_le_div_iff (by positivity [one_le_m K])).2
    (Nat.le_of_dvd (Nat.pow_pos hq0) h2mq)

/-!
Let `c₁, c₂, …` be natural numbers independent of `n`. There exists `c₁` such that
`c₁ α, c₁ β, c₁ γ` are integers in `K`.
-/

/-- A combined integer scaling factor `c₁^(n-1 + 2mq)` applied to the linear system to clear
all denominators and ensure the resulting matrix entries are algebraic integers. -/
abbrev cCoeffs (q : ℕ) : ℤ :=
  c₁ α' β' γ' ^ (n K q - 1) * c₁ α' β' γ' ^ (m K * q) * c₁ α' β' γ' ^ (m K * q)

omit [NumberField K] in
lemma isIntegral_c₁_pow_smul_pow (u : K) (n k a l : ℕ) (hnk : a * l ≤ n * k)
    (H : IsIntegral ℤ (↑(c₁ α' β' γ') * u)) :
    IsIntegral ℤ (c₁ α' β' γ' ^ (n * k) • u ^ (a * l)) := by
  rw [zsmul_eq_mul, Int.cast_pow, ← Nat.sub_add_cancel hnk, pow_add, mul_assoc, ← mul_pow]
  exact ((IsIntegral.Cast (c₁ α' β' γ')).pow _).mul (H.pow _)

lemma isIntegral_c₁_pow_smul_α'_pow' :
    IsIntegral ℤ (c₁ α' β' γ' ^ (m K * q) • α' ^ (a q t * l q u)) :=
  isIntegral_c₁_pow_smul_pow _ _ _ α' (m K) q (a q t) (l q u)
    (mul_comm q _ ▸ Nat.mul_le_mul (finProdFinEquiv.symm t).1.isLt
      (finProdFinEquiv.symm u).1.isLt) (by grind [isIntegral_c₁α])

lemma isIntegral_c₁_pow_smul_γ'_pow' :
    IsIntegral ℤ (c₁ α' β' γ' ^ (m K * q) • γ' ^ (b q t * l q u)) :=
  isIntegral_c₁_pow_smul_pow _ _ _ γ' (m K) q (b q t) (l q u)
    (mul_comm q _ ▸ Nat.mul_le_mul (finProdFinEquiv.symm t).2.isLt
      (finProdFinEquiv.symm u).1.isLt) (by grind [isIntegral_c₁γ])

include α' β' γ' in
/-- The combined scaling factor `cCoeffs` is nonzero. -/
lemma cCoeffs_ne_zero : cCoeffs α' β' γ' q ≠ 0 := by simp [cCoeffs, c₁_ne_zero]

omit [NumberField K] in
lemma isIntegral_c₁_pow_smul_add_smul_pow (n k : ℕ) (hkn : k ≤ n - 1) (a b : ℕ) :
    IsIntegral ℤ (c₁ α' β' γ' ^ (n - 1) • (↑a + ↑b • β') ^ k) := by
  rw [zsmul_eq_mul, Int.cast_pow, ← Nat.sub_add_cancel hkn, pow_add, mul_assoc, ← mul_pow,
    mul_add]
  refine ((IsIntegral.Cast _).pow _).mul ((IsIntegral.add ?_ ?_).pow _)
  · exact (IsIntegral.Cast _).mul (IsIntegral.Nat _)
  · rw [nsmul_eq_mul, ← mul_assoc, mul_comm (c₁ α' β' γ' : K), mul_assoc]
    exact (IsIntegral.Nat _).mul (by grind [isIntegral_c₁β])

/-!
Multiplying the system by `c₁^(n-1) c₁^(mq) c₁^(mq) = c₁^(n-1+2mq) ≤ c₂^n` ensures the
coefficients are integers in `K`.
-/

lemma zsmul_mul_mul_distrib {K : Type} [Field K] (a b c : ℤ) (x y z : K) :
    ((a * b) * c) • ((x * y) * z) = a • x * b • y * c • z := by
  simp [zsmul_eq_mul]; ring

/-- The scaled system coefficient `cCoeffs • systemCoeffs` is an algebraic integer over `ℤ`. -/
lemma isIntegral_cCoeffs_smul_systemCoeffs :
    IsIntegral ℤ (cCoeffs α' β' γ' q • systemCoeffs α' β' γ' q u t) := by
  rw [zsmul_mul_mul_distrib, mul_assoc]
  exact (isIntegral_c₁_pow_smul_add_smul_pow _ _ _ (n K q) (k q u)
      (Nat.le_sub_one_of_lt (finProdFinEquiv.symm u).2.isLt) (a q t) (b q t)).mul
    ((isIntegral_c₁_pow_smul_α'_pow' α' β' γ' q u t).mul
      (isIntegral_c₁_pow_smul_γ'_pow' α' β' γ' q u t))

/-- The matrix representing the homogeneous linear system of `mn` equations in `q^2` unknowns.
Its entries are scaled to strictly reside in the ring of integers `𝓞 K`. -/
def A : Matrix (Fin (m K * n K q)) (Fin (q * q)) (𝓞 K) :=
  fun i j ↦ RingOfIntegers.restrict _
  (fun _ ↦ isIntegral_cCoeffs_smul_systemCoeffs α' β' γ' q i j) ℤ

include α β σ hirr htriv habc in
lemma c₁α_ne_zero : c₁ α' β' γ' • α' ≠ 0 :=
  smul_ne_zero (c₁_ne_zero _ _ _)
    (alpha'_beta'_gamma'_ne_zero α β σ α' β' γ' hirr htriv habc).1

include α β σ hirr htriv habc in
lemma c₁γ_ne_zero : c₁ α' β' γ' • γ' ≠ 0 :=
  smul_ne_zero (c₁_ne_zero _ _ _)
    (alpha'_beta'_gamma'_ne_zero α β σ α' β' γ' hirr htriv habc).2.2

include α β σ hirr htriv habc in
lemma house_bound_c₁α :
    house (c₁ α' β' γ' • α') ^ (a q t * l q u) ≤
      house (c₁ α' β' γ' • α') ^ (m K * q) := by
  refine Bound.pow_le_pow_right_of_le_one_or_one_le (Or.inl ⟨one_le_house_of_isIntegral
    (isIntegral_c₁α α' β' γ') (c₁α_ne_zero α β σ α' β' γ' hirr htriv habc), ?_⟩)
  simpa [mul_comm] using mul_le_mul (finProdFinEquiv.symm t).1.isLt
    (finProdFinEquiv.symm u).1.isLt zero_le zero_le

omit [NumberField K] in
private lemma isIntegral_c₁_smul_addNSMul (a b : ℕ) :
    IsIntegral ℤ (c₁ α' β' γ' • ((a : K) + b • β')) := by
  simpa [smul_add, zsmul_eq_mul, nsmul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
    ((IsIntegral.Cast (c₁ α' β' γ')).mul (IsIntegral.Nat a)).add
      ((IsIntegral.Nat b).mul (isIntegral_c₁β α' β' γ'))

omit [NumberField K] in
/-- The scaled sum `c₁ • (q + q • β')` is an algebraic integer over `ℤ`. -/
lemma isIntegral_c₁_smul_q_β' : IsIntegral ℤ (c₁ α' β' γ' • ((q : K) + q • β')) :=
  isIntegral_c₁_smul_addNSMul _ _ _ q q

omit [NumberField K] in
/-- The scaled sum `c₁ • (a + b • β')` is an algebraic integer over `ℤ`. -/
lemma isIntegral_c₁_smul_a_b_β' :
    IsIntegral ℤ (c₁ α' β' γ' • ((a q t : K) + b q t • β')) :=
  isIntegral_c₁_smul_addNSMul _ _ _ _ _

include hirr σ habc in
lemma β'_ne_zero : ((a q t : K) + b q t • β') ≠ 0 := fun H ↦
  hirr (-(a q t : ℤ)) (b q t) <| by
    have hEq : (a q t : ℂ) + b q t * β = 0 := by
      simpa [nsmul_eq_mul, map_add, map_mul, ← habc.2.1] using congrArg σ H
    push_cast
    exact eq_div_iff_mul_eq (by unfold b; norm_cast) |>.mpr (by grind)

include hq0 hirr habc in
lemma b_sum_ne_zero : (↑q : K) + q • β' ≠ 0 := fun H ↦ hirr (-1) 1 <| by
  have hEq : (q : ℂ) + q * β = 0 := by
    simpa [nsmul_eq_mul, ← habc.2.1] using congrArg σ H
  exact mul_left_cancel₀ (a := (q : ℂ)) (mod_cast hq0.ne') (by linear_combination hEq)

include α β σ hq0 hirr habc in
lemma bound_c₁β : 1 ≤ house (c₁ α' β' γ' • ((q : K) + q • β')) :=
  one_le_house_of_isIntegral (isIntegral_c₁_smul_q_β' _ _ _ _)
    (smul_ne_zero (c₁_ne_zero _ _ _) (b_sum_ne_zero α β σ α' β' γ' hirr habc q hq0))

include α β σ hirr htriv habc in
lemma one_le_house_c₁γ : 1 ≤ house (c₁ α' β' γ' • γ') :=
  one_le_house_of_isIntegral (isIntegral_c₁γ α' β' γ')
    (c₁γ_ne_zero α β σ α' β' γ' hirr htriv habc)

/-- A large integer constant independent of `n` and `q`, used as a foundational base
to bound the houses (maximum absolute values of conjugates) of the algebraic coefficients. -/
def c₂ : ℤ := (|c₁ α' β' γ'| ^ (((1 + 2 * (m K) *
  (2 * (m K)))) + (1 + 2 * (m K) * (2 * (m K)))))

lemma one_le_c₂ : 1 ≤ c₂ α' β' γ' := one_le_pow₀ (one_le_abs_c₁ α' β' γ')

open Real

/-- A real-valued bounding constant encompassing `c₂` and the houses of `α'`, `β'`, and `γ'`.
Used to establish a strict upper bound on the entries of the linear system matrix `A`. -/
def c₃ : ℝ := c₂ α' β' γ' * (1 + house β') * sqrt (2 * m K) *
  (max 1 ((house α' ^ (2 * m K ^ 2)) * house γ' ^ (2 * m K ^ 2)))

lemma one_le_c₃ : 1 ≤ c₃ α' β' γ' :=
  one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
  (one_le_mul_of_one_le_of_one_le (mod_cast one_le_c₂ α' β' γ') <|
  le_add_of_nonneg_right <| house_nonneg _) <|
  one_le_sqrt.mpr <| mod_cast (by have := one_le_m K; linarith)) <| le_max_left 1 _

/-! Moreover, the absolute value of the conjugates of the various coefficients is at most
  `c₂^n (q + q * |β|) ^ (n - 1) * |α| ^ (m q) * |γ| ^ (m q) ≤ c₃^n * n^((n - 1) / 2)`.
-/
include u in
omit t h2mq in
lemma k_le_n_sub_one : k q u ≤ n K q - 1 :=
  Nat.le_sub_one_of_lt (finProdFinEquiv.symm u).2.isLt

include u in
omit t in
lemma fin_mul_l_le_mq (i : Fin q) : (i.val + 1) * l q u ≤ m K * q :=
  (Nat.mul_le_mul i.isLt (finProdFinEquiv.symm u).1.isLt).trans_eq (mul_comm _ _)

include u t in
lemma al_le_mq : a q t * l q u ≤ m K * q := by
  unfold a
  exact fin_mul_l_le_mq q u ((finProdFinEquiv.symm t).1)

include u t in
lemma bl_le_mq : b q t * l q u ≤ m K * q := by
  unfold b
  exact fin_mul_l_le_mq q u ((finProdFinEquiv.symm t).2)

include h2mq in
lemma mq_le_m_two_mnq : m K * q ≤ m K * (2 * (m K * n K q)) := by
  simpa [mul_assoc] using Nat.mul_le_mul_left (m K)
    ((Nat.le_pow Nat.zero_lt_two).trans (Nat.mul_div_cancel' h2mq).symm.le)

include α' β' γ' in
lemma house_c₁_smul_le (x : K) :
    house (c₁ α' β' γ' • x) ≤ ↑|c₁ α' β' γ'| * house x := by
  rw [zsmul_eq_mul]; exact (house_mul_le _ _).trans_eq (by simp)

include α' β' γ' in
lemma house_cCoeffs_smul_eq_factorized :
    house (cCoeffs α' β' γ' q • systemCoeffs α' β' γ' q u t) =
    house ((c₁ α' β' γ' ^ ((n K q - 1) - k q u) *
        c₁ α' β' γ' ^ (m K * q - a q t * l q u) *
        (c₁ α' β' γ' : K) ^ (m K * q - b q t * l q u)) • (((c₁ α' β' γ' : K) ^ k q u) *
        ((a q t : K) + (b q t) * β') ^ k q u * ((c₁ α' β' γ' : K) ^ (a q t * l q u)) *
        α' ^ (a q t * l q u) * ((c₁ α' β' γ' : K) ^ (b q t * l q u)) *
        γ' ^ (b q t * l q u))) := by
  have hk := k_le_n_sub_one q u
  have hal := al_le_mq q u t
  have hbl := bl_le_mq q u t
  rw [cCoeffs, show c₁ α' β' γ' ^ (n K q - 1) * c₁ α' β' γ' ^ (m K * q) *
        c₁ α' β' γ' ^ (m K * q) =
        (c₁ α' β' γ' ^ (n K q - 1 - k q u) *
          c₁ α' β' γ' ^ (m K * q - a q t * l q u) *
          c₁ α' β' γ' ^ (m K * q - b q t * l q u)) *
        (c₁ α' β' γ' ^ k q u * c₁ α' β' γ' ^ (a q t * l q u) *
          c₁ α' β' γ' ^ (b q t * l q u)) by
      rw [← pow_sub_mul_pow _ hk]; nth_rw 1 [← pow_sub_mul_pow _ hal]
      rw [← pow_sub_mul_pow _ hbl]; ring, mul_smul]
  congr 1; ring

include α β K σ α' β' γ' hirr htriv habc hq0 h2mq u t q in
lemma house_factorized_le_prod :
    house ((c₁ α' β' γ' ^ ((n K q - 1) - k q u) *
        c₁ α' β' γ' ^ (m K * q - a q t * l q u) *
        (c₁ α' β' γ' : K) ^ (m K * q - b q t * l q u)) • (((c₁ α' β' γ' : K) ^ k q u) *
        ((a q t : K) + (b q t) * β') ^ k q u * ((c₁ α' β' γ' : K) ^ (a q t * l q u)) *
        α' ^ (a q t * l q u) * ((c₁ α' β' γ' : K) ^ (b q t * l q u)) *
        γ' ^ (b q t * l q u))) ≤
    house (((c₁ α' β' γ' : K) ^ (n K q - 1 - k q u) * (c₁ α' β' γ' : K) ^
        (m K * q - a q t * l q u) *
        (c₁ α' β' γ' : K) ^ (m K * q - b q t * l q u))) *
        house (c₁ α' β' γ' ^ (k q u) • (↑(a q t) + (b q t) • β') ^ (k q u)) *
        house (c₁ α' β' γ' ^ (a q t * l q u) • α' ^ (a q t * l q u)) *
        house (c₁ α' β' γ' ^ (b q t * l q u) • γ' ^ (b q t * l q u)) := by
  simp only [nsmul_eq_mul, zsmul_eq_mul, Int.cast_pow, mul_assoc]
  refine (house_mul_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (house_nonneg _))
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc]
  refine (house_mul_le _ _).trans ?_
  rw [← mul_assoc]
  exact mul_le_mul (by grind [mul_assoc, house_mul_le]) le_rfl (house_nonneg _)
    (mul_nonneg (house_nonneg _) (house_nonneg _))

include α β K σ α' β' γ' hirr htriv habc hq0 h2mq u t q in
lemma house_prod_le_smul_pow :
    house (((c₁ α' β' γ' : K) ^ (n K q - 1 - k q u) * (c₁ α' β' γ' : K) ^
        (m K * q - a q t * l q u) *
        (c₁ α' β' γ' : K) ^ (m K * q - b q t * l q u))) *
        house (c₁ α' β' γ' ^ (k q u) • (↑(a q t) + (b q t) • β') ^ (k q u)) *
        house (c₁ α' β' γ' ^ (a q t * l q u) • α' ^ (a q t * l q u)) *
        house (c₁ α' β' γ' ^ (b q t * l q u) • γ' ^ (b q t * l q u)) ≤
    house (((c₁ α' β' γ' : K) ^ (n K q - 1 - k q u) * (c₁ α' β' γ' : K) ^
        (m K * q - a q t * l q u) *
        (c₁ α' β' γ' : K) ^ (m K * q - b q t * l q u))) *
        house (c₁ α' β' γ' • (↑(a q t) + (b q t) • β')) ^ (k q u) *
        house (c₁ α' β' γ' • α') ^ (a q t * l q u) *
        house (c₁ α' β' γ' • γ') ^ (b q t * l q u) := by
  simp only [nsmul_eq_mul, zsmul_eq_mul, Int.cast_pow, ← mul_pow]
  gcongr <;> exact house_pow_le _ _

include α β K σ α' β' γ' hirr htriv habc hq0 h2mq u t q in
lemma house_smul_pow_le_abs :
    house (((c₁ α' β' γ' : K) ^ (n K q - 1 - k q u) * (c₁ α' β' γ' : K) ^
        (m K * q - a q t * l q u) *
        (c₁ α' β' γ' : K) ^ (m K * q - b q t * l q u))) *
        house (c₁ α' β' γ' • (↑(a q t) + (b q t) • β')) ^ (k q u) *
        house (c₁ α' β' γ' • α') ^ (a q t * l q u) *
        house (c₁ α' β' γ' • γ') ^ (b q t * l q u) ≤
    |(((c₁ α' β' γ') ^ (n K q - 1 - k q u) *
        (c₁ α' β' γ') ^ (m K * q - a q t * l q u) *
        (c₁ α' β' γ') ^ (m K * q - b q t * l q u)))| * (|c₁ α' β' γ'| *
        (|(q : ℤ)| * (1 + house (β')))) ^ (n K q - 1) * (|c₁ α' β' γ'| * house (α')) ^
        (mTwoMnq K q) * (|c₁ α' β' γ'| * house (γ')) ^
        (mTwoMnq K q) := by
  have hk := k_le_n_sub_one q u
  have hal := al_le_mq q u t
  have hbl := bl_le_mq q u t
  have h_mq := mq_le_m_two_mnq q h2mq
  have hbd : ∀ x : K, house (c₁ α' β' γ' • x) ≤ ↑|c₁ α' β' γ'| * house x :=
    fun _ ↦ by rw [zsmul_eq_mul]; exact (house_mul_le _ _).trans_eq (by simp)
  gcongr
  · rw [← house_intCast (K := K)]; simp
  · refine (pow_le_pow_right₀
        (one_le_house_of_isIntegral (isIntegral_c₁_smul_a_b_β' _ _ _ q t)
          (smul_ne_zero (c₁_ne_zero α' β' γ')
            (β'_ne_zero α β σ α' β' γ' hirr habc q t))) hk).trans
      (pow_le_pow_left₀ (house_nonneg _) ((hbd _).trans
        (mul_le_mul_of_nonneg_left ?_ (by positivity))) _)
    rw [show (↑(a q t) + b q t • β' : K) =
          ((a q t : ℤ) : K) + ((b q t : ℤ) : K) * β' by push_cast [nsmul_eq_mul]; rfl,
        mul_one_add (((|(q : ℤ)| : ℤ) : ℝ)) (house β')]
    refine (house_add_le _ _).trans (add_le_add ?_ ((house_mul_le _ _).trans ?_)) <;>
      simp only [house_intCast]
    · simpa using (finProdFinEquiv.symm t).1.isLt
    · gcongr; simpa using (finProdFinEquiv.symm t).2.isLt
  · exact (pow_le_pow_left₀ (house_nonneg _) (hbd _) _).trans (pow_le_pow_right₀
      ((one_le_house_of_isIntegral (isIntegral_c₁α α' β' γ')
        (c₁α_ne_zero α β σ α' β' γ' hirr htriv habc)).trans (hbd _)) (hal.trans h_mq))
  · exact (pow_le_pow_left₀ (house_nonneg _) (hbd _) _).trans (pow_le_pow_right₀
      ((one_le_house_c₁γ α β σ α' β' γ' hirr htriv habc).trans (hbd _)) (hbl.trans h_mq))

include α β K σ α' β' γ' hq0 h2mq u t q in
lemma abs_bound_le_c₂ :
    |(((c₁ α' β' γ') ^ (n K q - 1 - k q u) *
        (c₁ α' β' γ') ^ (m K * q - a q t * l q u) *
        (c₁ α' β' γ') ^ (m K * q - b q t * l q u)))| * (|c₁ α' β' γ'| *
        (|(q : ℤ)| * (1 + house (β')))) ^ (n K q - 1) * (|c₁ α' β' γ'| * house (α')) ^
        (mTwoMnq K q) * (|c₁ α' β' γ'| * house (γ')) ^
        (mTwoMnq K q) ≤
    ↑(c₂ α' β' γ') ^ (n K q) *
      (↑|↑q| ^ ((n K q ) - 1) * (1 + house β') ^ (n K q - 1) *
      house α' ^ (mTwoMnq K q) *
      house γ' ^ (mTwoMnq K q)) := by
  have hk := k_le_n_sub_one q u
  have hal := al_le_mq q u t
  have hbl := bl_le_mq q u t
  have h_mq := mq_le_m_two_mnq q h2mq
  calc
    _ = |(c₁ α' β' γ')| ^ (n K q - 1 - k q u) *
          |(c₁ α' β' γ')| ^ (m K * q - a q t * l q u) *
          |(c₁ α' β' γ')| ^ (m K * q - b q t * l q u) *
          ↑|c₁ α' β' γ'| ^ ((n K q - 1) +  (2 * m K *
          (2 * (m K * n K q)))) *
          (↑|↑q| ^ ((n K q) - 1) * (1 + house β') ^ (n K q - 1) *
          house α' ^ (mTwoMnq K q) *
          house γ' ^ (mTwoMnq K q)) := by
      simp only [abs_pow, mul_pow, Int.cast_abs, Int.cast_pow, Nat.abs_cast, ← pow_add, two_mul,
        mTwoMnq]
      push_cast; ring
    _ ≤ ↑(c₂ α' β' γ') ^ (n K q) *
          (↑|↑q| ^ ((n K q ) - 1) * (1 + house β') ^ (n K q - 1) *
          house α' ^ (mTwoMnq K q) *
          house γ' ^ (mTwoMnq K q)) := by
      gcongr
      simp only [← pow_add, Int.cast_abs, c₂, Int.cast_pow, ← pow_mul]
      refine pow_le_pow_right₀ (mod_cast one_le_abs_c₁ α' β' γ') ?_
      simp only [add_mul, one_mul, mul_assoc,
        (Nat.two_mul (m K * (2 * (m K * n K q)))), add_assoc]
      gcongr <;> omega

include α β K σ α' β' γ' hq0 h2mq q in
lemma c₂_bound_le_c₃ :
    ↑(c₂ α' β' γ') ^ (n K q) *
      (↑|↑q| ^ ((n K q ) - 1) * (1 + house β') ^ (n K q - 1) *
      house α' ^ (mTwoMnq K q) *
      house γ' ^ (mTwoMnq K q)) ≤
    c₃ α' β' γ' ^ (n K q : ℝ) *
      (n K q : ℝ) ^ (((n K q : ℝ) - 1) / 2) := by
  calc
    _ ≤ ↑(c₂ α' β' γ') ^ (n K q) *
          (√(2 * m K) ^ (n K q - 1) *
          √((n K q : ℝ)) ^ ((n K q : ℝ) - 1) *
          ((1 + house β') ^ (n K q - 1) *
          (house α' ^ (mTwoMnq K q) *
           house γ' ^ (mTwoMnq K q)))) := by
      refine mul_le_mul_of_nonneg_left ?_ (by unfold c₂; positivity)
      conv_lhs => rw [mul_assoc, mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      rw [← Nat.cast_one (R := ℝ), ← Nat.cast_sub (n_one_le q hq0 h2mq),
        rpow_natCast, ← mul_pow, ← sqrt_mul (by positivity)]
      gcongr; push_cast [abs_of_nonneg (show (0 : ℝ) ≤ q by positivity)]
      exact (le_sqrt (by positivity) (by positivity)).2
        (mod_cast (Nat.mul_div_cancel' h2mq).symm.le)
    _ ≤ ↑(c₂ α' β' γ') ^ (n K q) *
          (√(2 * m K) ^ (n K q) *
          √((n K q : ℝ)) ^ ((n K q : ℝ) - 1) *
          ((1 + house β') ^ (n K q) *
          (max 1 (house α' ^ (2 * m K ^ 2) *
            house γ' ^ (2 * m K ^ 2))) ^ (n K q))) := by
      gcongr <;> first
          | omega
          | (unfold c₂; positivity)
          | exact one_le_sqrt.mpr (by exact_mod_cast (by grind [one_le_m K]))
          | (rw [show mTwoMnq K q = 2 * m K ^ 2 * n K q by simp [mTwoMnq]; ring,
                pow_mul (house α'), pow_mul (house γ'), ← mul_pow]
             exact pow_le_pow_left₀ (by positivity) (le_max_right _ _) _)
          | simp
    _ = c₃ α' β' γ' ^ (n K q : ℝ) *
          (n K q : ℝ) ^ (((n K q : ℝ) - 1) / 2) := by
      rw [show (n K q : ℝ) ^ (((n K q : ℝ) - 1) / 2) =
            sqrt (n K q) ^ ((n K q : ℝ) - 1) by
          rw [sqrt_eq_rpow, ← rpow_mul (Nat.cast_nonneg _), mul_comm, mul_div, mul_one]]
      simp_rw [c₃, rpow_natCast, mul_pow]; ring

include α β K σ α' β' γ' hirr htriv habc hq0 h2mq u t q in
lemma house_matrixA_le :
    house ((algebraMap (𝓞 K) K) ((A α' β' γ' q) u t)) ≤
      (c₃ α' β' γ' ^ (n K q : ℝ) * (n K q : ℝ) ^ (((n K q : ℝ) - 1) / 2)) := by
  simp only [A, systemCoeffs, RingOfIntegers.restrict, RingOfIntegers.map_mk]
  rw [house_cCoeffs_smul_eq_factorized]
  exact (@house_factorized_le_prod K _ α β σ α' β' γ' hirr htriv habc _ q hq0 u t h2mq).trans
    ((@house_prod_le_smul_pow K _ α β σ α' β' γ' hirr htriv habc _ q hq0 u t h2mq).trans
      ((@house_smul_pow_le_abs K _ α β σ α' β' γ' hirr htriv habc _ q hq0 u t h2mq).trans
        ((@abs_bound_le_c₂ K _ α β σ α' β' γ' _ q hq0 u t h2mq).trans
          (@c₂_bound_le_c₃ K _ α β σ α' β' γ' _ q hq0 h2mq))))

open NumberField

include α β σ α' β' γ' hirr htriv habc q hq0 h2mq in
/-- The matrix `A` is nonzero, ensuring Siegel's lemma yields a nontrivial solution. -/
lemma A_ne_zero : A α' β' γ' q ≠ 0 := by
  intro H
  let u : Fin _ := ⟨0, Nat.mul_pos (one_le_m K) (n_one_le q hq0 h2mq)⟩
  let t : Fin _ := ⟨0, mul_pos hq0 hq0⟩
  have H_eval : (A α' β' γ' q u t).val = 0 := by rw [H]; rfl
  simp only [A, RingOfIntegers.restrict, zsmul_eq_mul, Int.cast_mul, Int.cast_pow] at H_eval
  obtain ⟨hα, _, hγ⟩ := alpha'_beta'_gamma'_ne_zero α β σ α' β' γ' hirr htriv habc
  have := β'_ne_zero α β σ α' β' γ' hirr habc q t
  revert H_eval; simp [c₁_ne_zero, hα, hγ]; grind

variable [DecidableEq (K →+* ℂ)]

include α β σ α' β' γ' hirr htriv habc in
/-- A non-trivial integer vector (in `𝓞 K`) residing in the kernel of the matrix `A`.
Its existence is guaranteed by Siegel's lemma (`exists_ne_zero_int_vec_house_le`). -/
abbrev η : Fin (q * q) → 𝓞 K :=
  (house.exists_ne_zero_int_vec_house_le K (A α' β' γ' q)
    (A_ne_zero α β σ α' β' γ' hirr htriv habc q hq0 h2mq)
    (Nat.mul_pos (one_le_m K) (n_one_le q hq0 h2mq))
    ((mul_assoc 2 _ _).symm ▸ lt_mul_of_one_lt_left
      (Nat.mul_pos (one_le_m K) (n_one_le q hq0 h2mq)) Nat.one_lt_two
      |>.trans_eq ((Nat.mul_div_cancel' h2mq).trans (pow_two q))) (Fintype.card_fin _)
    (fun u t ↦ house_matrixA_le α β σ α' β' γ' hirr htriv habc q hq0 u t h2mq)
    (Fintype.card_fin _)).choose

/-- A real-valued bounding constant used to bound the norm (house) of the
solution vector `η`. -/
def c₄ : ℝ := (max 1 ((house.c₁ K) * house.c₁ K * 2 * (m K))) * (c₃ α' β' γ' : ℝ)

include hq0 h2mq in
open house in
lemma η_spec (t : Fin (q * q)) :
    house (algebraMap (𝓞 K) K
        (η (K := K) α β σ α' β' γ' hirr htriv habc q hq0 h2mq t)) ≤
      house.c₁ K * (house.c₁ K * ↑(q * q) *
        (c₃ α' β' γ' ^ (n K q : ℝ) *
          (n K q : ℝ) ^ (((n K q : ℝ) - 1) / 2))) ^
        ((m K * n K q : ℝ) / (↑(q * q : ℝ) - ↑(m K * n K q))) := by
  dsimp [η]
  exact_mod_cast (Exists.choose_spec (house.exists_ne_zero_int_vec_house_le K (A α' β' γ' q)
    (A_ne_zero α β σ α' β' γ' hirr htriv habc q hq0 h2mq)
    (Nat.mul_pos (one_le_m K) (n_one_le q hq0 h2mq))
    ((mul_assoc 2 _ _).symm ▸ lt_mul_of_one_lt_left
      (Nat.mul_pos (one_le_m K) (n_one_le q hq0 h2mq)) Nat.one_lt_two
      |>.trans_eq ((Nat.mul_div_cancel' h2mq).trans (pow_two q))) (Fintype.card_fin _)
    (fun u t ↦ house_matrixA_le α β σ α' β' γ' hirr htriv habc q hq0 u t h2mq)
    (Fintype.card_fin _))).2.2 t

/-!
`‖ηₖ‖ ≤ c₄ⁿ * n^((n - 1) / 2)`, for `1 ≤ k ≤ t`.
-/
lemma house_eta_le_c₄_pow :
    house (algebraMap (𝓞 K) K
        (η (K := K) α β σ α' β' γ' hirr htriv habc q hq0 h2mq t)) ≤
      c₄ α' β' γ' ^ (n K q : ℝ) * (n K q : ℝ) ^ (((n K q : ℝ) + 1) / 2) := by
  have hn : (1 : ℝ) ≤ (n K q : ℝ) := mod_cast n_one_le q hq0 h2mq
  have hqR : (q : ℝ) * q = 2 * (m K * n K q : ℝ) := by
    exact_mod_cast (pow_two q).symm.trans ((Nat.mul_div_cancel' h2mq).symm.trans (mul_assoc ..))
  have hN : (n K q : ℝ) * (n K q : ℝ) ^ (((n K q : ℝ) - 1) / 2) =
      (n K q : ℝ) ^ (((n K q : ℝ) + 1) / 2) := by
    nth_rw 1 [← Real.rpow_one (n K q : ℝ)]
    rw [← Real.rpow_add (zero_lt_one.trans_le hn)]; congr 1; ring
  calc _ ≤ house.c₁ K * (house.c₁ K * ↑(q * q) *
            (c₃ α' β' γ' ^ (n K q : ℝ) *
            (n K q : ℝ) ^ (((n K q : ℝ) - 1) / 2))) ^
            ((m K * n K q : ℝ) /
              (↑(q * q : ℝ) - ↑(m K * n K q))) := ?_
      _ = house.c₁ K * (house.c₁ K * 2 * m K *
            c₃ α' β' γ' ^ (n K q : ℝ) * ((n K q : ℝ) *
            (n K q : ℝ) ^ (((n K q : ℝ) - 1) / 2))) := ?_
      _ ≤ c₄ α' β' γ' ^ (n K q : ℝ) *
            (n K q : ℝ) ^ (((n K q : ℝ) + 1) / 2) := ?_
  · exact η_spec α β σ α' β' γ' hirr htriv habc q hq0 h2mq t
  · rw [show ((↑(q * q : ℝ) : ℝ) - ↑(m K * n K q)) =
       (m K * n K q : ℝ) by push_cast; linarith [hqR],
       div_self (mod_cast (Nat.mul_pos (one_le_m K) (n_one_le q hq0 h2mq)).ne'), rpow_one]
    push_cast; linear_combination
      (house.c₁ K ^ 2 * c₃ α' β' γ' ^ (n K q : ℝ) *
            (n K q : ℝ) ^ (((n K q : ℝ) - 1) / 2)) * hqR
  · simp only [← mul_assoc, hN]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [c₄, mul_rpow (by positivity) (zero_le_one.trans (one_le_c₃ _ _ _))]
    refine mul_le_mul_of_nonneg_right ?_ (rpow_nonneg (zero_le_one.trans (one_le_c₃ _ _ _)) _)
    exact (le_max_right _ _).trans <| by
      simpa [Real.rpow_one] using rpow_le_rpow_of_exponent_le (le_max_left _ _) hn

end GelfondSchneider
