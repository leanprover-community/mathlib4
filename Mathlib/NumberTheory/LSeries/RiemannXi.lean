/-
Copyright (c) 2026 Edward Falk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edward Falk
-/
module

public import Mathlib.NumberTheory.LSeries.ZetaZeros
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# The Riemann ξ function

This file defines Riemann's ξ function and proves its basic properties using mathlib's
`completedRiemannZeta` infrastructure.

## Definition

The Riemann ξ function is defined as:
  ξ(s) = ½ · s · (s − 1) · Λ(s)
where Λ(s) = π^(−s/2) · Γ(s/2) · ζ(s) is the completed Riemann zeta function
(`completedRiemannZeta` in mathlib).

Since Λ has simple poles at s = 0 and s = 1, and s(s−1) has simple zeros there,
ξ extends to an entire function. We use mathlib's `completedRiemannZeta₀` (the entire
regularization of Λ) to give a globally defined formula:

  ξ(s) = ½ · s · (s − 1) · Λ₀(s) + ½

where the identity ½ · s · (s − 1) · (−1/s − 1/(1−s)) = −½ justifies the constant.

## Main definitions

* `riemannXi` — the Riemann ξ function, defined as an entire function.

## Main results

* `riemannXi_one_sub` — functional equation: ξ(1 − s) = ξ(s).
* `riemannXi_zero`, `riemannXi_one` — ξ(0) = ξ(1) = ½.
* `riemannXi_eq_half_mul_completedZeta` — for s ≠ 0, 1:
    ξ(s) = ½ · s · (s − 1) · Λ(s).
* `differentiable_riemannXi` — ξ is entire (differentiable on all of ℂ).
* `riemannXi_eq_zero_iff` — ξ(s) = 0 ↔ s is a nontrivial zero of ζ (no hypotheses on s).
* `iteratedDeriv_riemannXi_one_sub` — ξ^(n)(1 − s) = (−1)ⁿ · ξ^(n)(s).

## References

* Riemann, B. "Ueber die Anzahl der Primzahlen unter einer gegebenen Grösse."
  Monatsberichte der Berliner Akademie, 1859.
* Edwards, H.M. "Riemann's Zeta Function." Academic Press, 1974.
-/

@[expose] public section

open Complex

noncomputable section

/-! ### Definition -/

/-- The Riemann ξ (xi) function, defined via the regularized completed zeta function.

Mathematically, for s ∉ {0, 1}: ξ(s) = ½ · s · (s − 1) · π^(−s/2) · Γ(s/2) · ζ(s).

Using mathlib's `completedRiemannZeta₀` (the entire regularization), this extends to
the globally defined formula ξ(s) = ½ · s · (s − 1) · Λ₀(s) + ½, which is entire. -/
def riemannXi (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta₀ s + (1 / 2 : ℂ)

/-! ### Functional equation -/

/-- The functional equation for the Riemann ξ function: ξ(1 − s) = ξ(s).

This follows immediately from the functional equation for `completedRiemannZeta₀`
and the algebraic identity (1−s)((1−s)−1) = s(s−1). -/
theorem riemannXi_one_sub (s : ℂ) : riemannXi (1 - s) = riemannXi s := by
  unfold riemannXi
  rw [completedRiemannZeta₀_one_sub]
  ring

/-! ### Special values -/

/-- ξ(0) = ½. -/
theorem riemannXi_zero : riemannXi 0 = (1 / 2 : ℂ) := by
  simp [riemannXi]

/-- ξ(1) = ½. -/
theorem riemannXi_one : riemannXi 1 = (1 / 2 : ℂ) := by
  simp [riemannXi]

/-! ### Connection to the completed zeta function -/

/-- For s ≠ 0 and s ≠ 1, ξ(s) equals ½ · s · (s − 1) · Λ(s), where Λ is the
    completed Riemann zeta function. -/
theorem riemannXi_eq_half_mul_completedZeta {s : ℂ} (hs : s ≠ 0) (hs' : s ≠ 1) :
    riemannXi s = (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta s := by
  unfold riemannXi
  rw [completedRiemannZeta_eq]
  have h0 : (s : ℂ) ≠ 0 := hs
  have h1 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs')
  field_simp
  ring

/-! ### Differentiability -/

/-- The Riemann ξ function is entire (differentiable on all of ℂ).

This follows because `completedRiemannZeta₀` is entire and multiplication by
polynomials preserves differentiability. -/
theorem differentiable_riemannXi : Differentiable ℂ riemannXi := by
  unfold riemannXi
  apply Differentiable.add
  · exact ((((differentiable_const _).mul differentiable_id).mul
      (differentiable_id.sub (differentiable_const _))).mul
      differentiable_completedZeta₀)
  · exact differentiable_const _

/-- `riemannXi` is differentiable at every point. -/
theorem differentiableAt_riemannXi (s : ℂ) : DifferentiableAt ℂ riemannXi s :=
  differentiable_riemannXi s

/-! ### Zeros of ξ -/

/-- The non-trivial zeros of ζ are zeros of ξ. -/
theorem riemannXi_eq_zero_of_nontrivialZero {s : ℂ}
    (hmem : s ∈ riemannZetaNontrivialZeros) : riemannXi s = 0 := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hmem
    simp [riemannZetaNontrivialZeros, riemannZetaZeros, riemannZetaTrivialZeros] at hmem
    simp [riemannZeta_zero] at hmem
  have hs1 : s ≠ 1 := by
    intro h
    exact hmem.2 (Set.mem_union_right _ (Set.mem_singleton_iff.mpr h))
  rw [riemannXi_eq_half_mul_completedZeta hs0 hs1]
  -- ζ(s) = 0 since s is a zero
  have hzeta : riemannZeta s = 0 := (mem_riemannZetaZeros.mp hmem.1)
  -- Γ_ℝ(s) ≠ 0: by Gammaℝ_eq_zero_iff, Γ_ℝ vanishes iff s = -2n for some n : ℕ.
  -- But s ≠ 0 (= -2·0), and s is not a trivial zero (≠ -2(n+1) for any n).
  have hGamma : s.Gammaℝ ≠ 0 := by
    intro habs
    rw [Complex.Gammaℝ_eq_zero_iff] at habs
    obtain ⟨n, hn⟩ := habs
    by_cases hn0 : n = 0
    · exact hs0 (by simp [hn, hn0])
    · have : s ∈ riemannZetaTrivialZeros := by
        obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn0
        exact ⟨m, by simp [hn, hm]⟩
      exact hmem.2 (Set.mem_union_left _ this)
  -- From ζ(s) = Λ(s) / Γ_ℝ(s) and ζ(s) = 0, deduce Λ(s) = 0.
  have hLambda : completedRiemannZeta s = 0 := by
    have := riemannZeta_def_of_ne_zero hs0
    rw [hzeta] at this
    exact (div_eq_zero_iff.mp this.symm).resolve_right hGamma
  simp [hLambda]

/-- If ξ(s) = 0 and s ≠ 0 and s ≠ 1, then s is a zero of ζ.
    Proof: ξ(s) = ½s(s−1)Λ(s) and ½s(s−1) ≠ 0, so Λ(s) = 0, hence ζ(s) = Λ(s)/Γ_ℝ(s) = 0. -/
theorem riemannZeta_eq_zero_of_riemannXi_eq_zero {s : ℂ}
    (hxi : riemannXi s = 0) (hs : s ≠ 0) (hs' : s ≠ 1) :
    riemannZeta s = 0 := by
  have hxi' := riemannXi_eq_half_mul_completedZeta hs hs'
  rw [hxi] at hxi'
  have hprod : (1 / 2 : ℂ) * s * (s - 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hs) (sub_ne_zero.mpr hs')
  have hcz : completedRiemannZeta s = 0 := by
    by_contra h
    exact absurd hxi'.symm (mul_ne_zero hprod h)
  rw [riemannZeta_def_of_ne_zero hs, hcz, zero_div]

/-! ### Properties of nontrivial zeros -/

/-- Nontrivial zeros of ζ have real part strictly less than 1.
    Follows from the classical prime number theorem consequence: ζ(s) ≠ 0 for Re(s) ≥ 1. -/
theorem re_lt_one_of_nontrivialZero {s : ℂ}
    (hmem : s ∈ riemannZetaNontrivialZeros) : s.re < 1 := by
  by_contra h
  push Not at h
  have hzeta : riemannZeta s = 0 := mem_riemannZetaZeros.mp hmem.1
  exact absurd hzeta (riemannZeta_ne_zero_of_one_le_re h)

/-- Nontrivial zeros of ζ have real part strictly greater than 0.
    Follows from the functional equation: if Re(s) ≤ 0 and ζ(s) = 0, then s is a trivial
    zero or s = 0. Since nontrivial zeros exclude both, Re(s) > 0. -/
theorem re_pos_of_nontrivialZero {s : ℂ}
    (hmem : s ∈ riemannZetaNontrivialZeros) : 0 < s.re := by
  -- ξ(s) = 0 for nontrivial zeros
  have hxi := riemannXi_eq_zero_of_nontrivialZero hmem
  -- By the functional equation, ξ(1-s) = 0 as well
  have hxi' : riemannXi (1 - s) = 0 := by rw [riemannXi_one_sub]; exact hxi
  -- If Re(s) ≤ 0, then Re(1-s) ≥ 1. Since ξ(1-s) = 0, deduce ζ(1-s) = 0 ...
  by_contra h
  push Not at h
  -- Re(1-s) = 1 - Re(s) ≥ 1
  have hre : 1 ≤ (1 - s).re := by simp [Complex.sub_re]; linarith
  -- ... which contradicts ζ ≠ 0 for Re ≥ 1.
  -- But we need 1-s ≠ 0 and 1-s ≠ 1 to apply riemannZeta_eq_zero_of_riemannXi_eq_zero.
  have hne0 : (1 : ℂ) - s ≠ 0 := by
    intro heq
    have : s = 1 := by linear_combination -heq
    exact hmem.2 (Set.mem_union_right _ (Set.mem_singleton_iff.mpr this))
  have hne1 : (1 : ℂ) - s ≠ 1 := by
    intro heq
    have hs0 : s = 0 := by linear_combination -heq
    have : riemannZeta s = 0 := mem_riemannZetaZeros.mp hmem.1
    rw [hs0, riemannZeta_zero] at this
    norm_num at this
  have hzeta_conj : riemannZeta (1 - s) = 0 :=
    riemannZeta_eq_zero_of_riemannXi_eq_zero hxi' hne0 hne1
  exact absurd hzeta_conj (riemannZeta_ne_zero_of_one_le_re hre)

/-- Nontrivial zeros lie in the open critical strip: 0 < Re(s) < 1. -/
theorem re_mem_Ioo_of_nontrivialZero {s : ℂ}
    (hmem : s ∈ riemannZetaNontrivialZeros) : s.re ∈ Set.Ioo 0 1 :=
  ⟨re_pos_of_nontrivialZero hmem, re_lt_one_of_nontrivialZero hmem⟩

/-- The zeros of ξ are symmetric under s ↦ 1 − s. -/
theorem riemannXi_eq_zero_one_sub {s : ℂ} (h : riemannXi s = 0) :
    riemannXi (1 - s) = 0 := by
  rw [riemannXi_one_sub]; exact h

/-! ### Non-vanishing at trivial zeros -/

/-- The completed Riemann zeta function Λ(s) is nonzero when Re(s) ≥ 1 and s ≠ 1.

    Proof: from ζ(s) = Λ(s)/Γ_ℝ(s) (for s ≠ 0), ζ(s) ≠ 0 (for Re ≥ 1), and
    Γ_ℝ(s) ≠ 0 (since Re(s) ≥ 1 means s ≠ −2n for any n), we get Λ(s) ≠ 0. -/
theorem completedRiemannZeta_ne_zero_of_one_le_re {s : ℂ}
    (hre : 1 ≤ s.re) (hs1 : s ≠ 1) : completedRiemannZeta s ≠ 0 := by
  -- s ≠ 0 since Re(s) ≥ 1 > 0
  have hs0 : s ≠ 0 := by
    intro h; subst h; norm_num at hre
  -- ζ(s) ≠ 0 for Re(s) ≥ 1
  have hzeta : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hre
  -- Γ_ℝ(s) ≠ 0: by Gammaℝ_eq_zero_iff, Γ_ℝ vanishes iff s = -2n for some n,
  -- but Re(s) ≥ 1 rules this out.
  have hGamma : s.Gammaℝ ≠ 0 := by
    intro habs
    rw [Complex.Gammaℝ_eq_zero_iff] at habs
    obtain ⟨n, hn⟩ := habs
    have : s.re = -(2 * ↑n) := by
      rw [hn]; simp
    linarith
  -- From ζ(s) = Λ(s)/Γ_ℝ(s) and ζ(s) ≠ 0, deduce Λ(s) ≠ 0.
  intro habs
  have := riemannZeta_def_of_ne_zero hs0
  rw [habs, zero_div] at this
  exact hzeta this

/-- ξ does not vanish at trivial zeros of ζ.

    At a trivial zero s = −2(n+1), we use the functional equation ξ(s) = ξ(1−s) to
    reduce to ξ(2n+3). Since Re(2n+3) ≥ 3 > 1, ζ and Γ_ℝ are both nonzero there,
    so Λ(2n+3) ≠ 0, hence ξ(2n+3) = ½·(2n+3)·(2n+2)·Λ(2n+3) ≠ 0. -/
theorem riemannXi_ne_zero_of_trivialZero {s : ℂ}
    (hmem : s ∈ riemannZetaTrivialZeros) : riemannXi s ≠ 0 := by
  obtain ⟨n, hn⟩ := hmem
  -- Use the functional equation: ξ(s) = ξ(1 − s)
  rw [hn, show riemannXi (-2 * (↑n + 1)) = riemannXi (2 * ↑n + 3) from by
    conv_lhs => rw [← riemannXi_one_sub (-2 * (↑n + 1))]
    congr 1; ring]
  -- Now show ξ(2n+3) ≠ 0
  set t : ℂ := 2 * ↑n + 3 with ht_def
  have ht_re : t.re = 2 * ↑n + 3 := by simp [ht_def]
  have ht_ne0 : t ≠ 0 := by
    intro h; have := congr_arg Complex.re h
    simp [ht_def] at this; linarith [Nat.cast_nonneg (α := ℝ) n]
  have ht_ne1 : t ≠ 1 := by
    intro h; have := congr_arg Complex.re h
    simp [ht_def] at this; linarith [Nat.cast_nonneg (α := ℝ) n]
  rw [riemannXi_eq_half_mul_completedZeta ht_ne0 ht_ne1]
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) ht_ne0) (sub_ne_zero.mpr ht_ne1))
    (completedRiemannZeta_ne_zero_of_one_le_re
      (by rw [ht_re]; linarith [Nat.cast_nonneg (α := ℝ) n]) ht_ne1)

/-- **Biconditional zero characterization**: for s ≠ 0 and s ≠ 1,
    ξ(s) = 0 if and only if s is a non-trivial zero of ζ. -/
theorem riemannXi_eq_zero_iff_nontrivialZero {s : ℂ} (hs : s ≠ 0) (hs' : s ≠ 1) :
    riemannXi s = 0 ↔ s ∈ riemannZetaNontrivialZeros := by
  constructor
  · intro hxi
    constructor
    · -- s is a zero of ζ
      exact riemannZeta_eq_zero_of_riemannXi_eq_zero hxi hs hs'
    · -- s is neither trivial nor 1
      intro hmem
      rcases hmem with htriv | hone
      · exact absurd hxi (riemannXi_ne_zero_of_trivialZero htriv)
      · exact hs' (Set.mem_singleton_iff.mp hone)
  · exact riemannXi_eq_zero_of_nontrivialZero

/-! ### Derivative of ξ at s = 1 -/

/-- General derivative formula: ξ'(s) = ½(2s−1)Λ₀(s) + ½s(s−1)Λ₀'(s).

This is the full product rule applied to ξ(s) = ½s(s−1)Λ₀(s) + ½. The specialization
at s = 1 (where the second term vanishes) is `hasDerivAt_riemannXi_one`. -/
theorem hasDerivAt_riemannXi (s : ℂ) :
    HasDerivAt riemannXi
      ((1 / 2 : ℂ) * (2 * s - 1) * completedRiemannZeta₀ s +
       (1 / 2 : ℂ) * s * (s - 1) * deriv completedRiemannZeta₀ s) s := by
  unfold riemannXi
  have h_id : HasDerivAt (fun t : ℂ => t) 1 s := hasDerivAt_id' s
  have h_sub : HasDerivAt (fun t : ℂ => t - 1) 1 s := (hasDerivAt_id' s).sub_const 1
  have h_poly : HasDerivAt (fun t : ℂ => t * (t - 1)) (2 * s - 1) s := by
    have h := h_id.fun_mul h_sub
    rw [show (1 : ℂ) * (s - 1) + s * 1 = 2 * s - 1 from by ring] at h
    exact h
  have h_cpoly : HasDerivAt (fun t : ℂ => (1 / 2 : ℂ) * t * (t - 1))
      ((1 / 2 : ℂ) * (2 * s - 1)) s := by
    have h := h_poly.const_mul (1 / 2 : ℂ)
    simpa only [mul_assoc] using h
  have h_cz : HasDerivAt completedRiemannZeta₀ (deriv completedRiemannZeta₀ s) s :=
    (differentiable_completedZeta₀ s).hasDerivAt
  have h_prod : HasDerivAt
      (fun t => (1 / 2 : ℂ) * t * (t - 1) * completedRiemannZeta₀ t)
      ((1 / 2 : ℂ) * (2 * s - 1) * completedRiemannZeta₀ s +
       (1 / 2 : ℂ) * s * (s - 1) * deriv completedRiemannZeta₀ s) s :=
    h_cpoly.fun_mul h_cz
  exact h_prod.add_const (1 / 2 : ℂ)

/-- The derivative of ξ at s = 1 equals Λ₀(1)/2.

Specialization of `hasDerivAt_riemannXi`: at s = 1, the s(s−1) term vanishes,
leaving ξ'(1) = ½ · 1 · Λ₀(1) = Λ₀(1)/2. -/
theorem hasDerivAt_riemannXi_one :
    HasDerivAt riemannXi (completedRiemannZeta₀ 1 / 2) 1 := by
  have := hasDerivAt_riemannXi 1
  convert this using 1
  simp; ring

/-- The derivative of ξ at s = 1 (deriv version). -/
theorem deriv_riemannXi_one : deriv riemannXi 1 = completedRiemannZeta₀ 1 / 2 :=
  hasDerivAt_riemannXi_one.deriv

/-- Derivative antisymmetry: ξ'(1 − s) = −ξ'(s).
    Follows by differentiating the functional equation ξ(1 − s) = ξ(s) via the chain rule. -/
theorem deriv_riemannXi_one_sub (s : ℂ) :
    deriv riemannXi (1 - s) = -deriv riemannXi s := by
  have hfun : (fun t => riemannXi (1 - t)) = riemannXi := funext riemannXi_one_sub
  have hsub : HasDerivAt (fun t => (1 : ℂ) - t) (-1) s := (hasDerivAt_id' s).const_sub 1
  have hd : HasDerivAt (fun t => riemannXi (1 - t))
      (deriv riemannXi (1 - s) * (-1)) s :=
    (differentiable_riemannXi (1 - s)).hasDerivAt.comp s hsub
  have hd' : HasDerivAt riemannXi (deriv riemannXi (1 - s) * (-1)) s := by
    rwa [hfun] at hd
  have heq := hd'.deriv
  rw [heq, mul_neg_one, neg_neg]

/-- ξ'(1/2) = 0: the derivative of ξ vanishes at the center of the critical strip.
    Corollary of `deriv_riemannXi_one_sub` at s = 1/2. -/
theorem deriv_riemannXi_half : deriv riemannXi (1 / 2 : ℂ) = 0 := by
  have h := deriv_riemannXi_one_sub (1 / 2 : ℂ)
  simp only [show (1 : ℂ) - 1 / 2 = 1 / 2 from by ring] at h
  linear_combination (1 / 2 : ℂ) * h

/-- **Unconditional biconditional**: ξ(s) = 0 if and only if s is a non-trivial zero of ζ.
    No hypotheses needed — the cases s = 0 and s = 1 are vacuous since ξ(0) = ξ(1) = ½ ≠ 0
    and neither point is a non-trivial zero. -/
theorem riemannXi_eq_zero_iff {s : ℂ} :
    riemannXi s = 0 ↔ s ∈ riemannZetaNontrivialZeros := by
  by_cases hs : s = 0
  · subst hs
    simp only [riemannXi_zero]
    constructor
    · intro h; norm_num at h
    · intro h
      exfalso
      have := h.1
      rw [mem_riemannZetaZeros, riemannZeta_zero] at this
      norm_num at this
  · by_cases hs' : s = 1
    · subst hs'
      simp only [riemannXi_one]
      constructor
      · intro h; norm_num at h
      · intro h; exact absurd (Set.mem_union_right _ (Set.mem_singleton_iff.mpr rfl)) h.2
    · exact riemannXi_eq_zero_iff_nontrivialZero hs hs'

/-! ### Non-vanishing in the half-plane Re(s) ≥ 1 -/

/-- ξ does not vanish when Re(s) ≥ 1: the zeros of ξ (= nontrivial zeros of ζ) lie
    strictly inside the open critical strip 0 < Re(s) < 1.

    This packages `riemannXi_eq_zero_iff` and `re_lt_one_of_nontrivialZero`. -/
theorem riemannXi_ne_zero_of_one_le_re {s : ℂ} (hre : 1 ≤ s.re) : riemannXi s ≠ 0 := by
  intro habs
  rw [riemannXi_eq_zero_iff] at habs
  exact absurd (re_lt_one_of_nontrivialZero habs) (not_lt.mpr hre)

/-- ξ does not vanish when Re(s) ≤ 0: by the functional equation ξ(s) = ξ(1−s),
    non-vanishing for Re ≥ 1 implies non-vanishing for Re ≤ 0. -/
theorem riemannXi_ne_zero_of_re_le_zero {s : ℂ} (hre : s.re ≤ 0) : riemannXi s ≠ 0 := by
  intro habs
  rw [riemannXi_eq_zero_iff] at habs
  exact absurd (re_pos_of_nontrivialZero habs) (not_lt.mpr hre)

/-! ### Symmetry of nontrivial zeros -/

/-- If ρ is a nontrivial zero of ζ, then so is 1 − ρ.
    This follows immediately from the functional equation ξ(1 − s) = ξ(s)
    and the characterization ξ(s) = 0 ↔ s ∈ nontrivialZeros. -/
theorem nontrivialZero_one_sub {s : ℂ} (hs : s ∈ riemannZetaNontrivialZeros) :
    1 - s ∈ riemannZetaNontrivialZeros := by
  rw [← riemannXi_eq_zero_iff]
  rw [riemannXi_one_sub]
  rwa [riemannXi_eq_zero_iff]

/-- The map s ↦ 1 − s is an involution on the set of nontrivial zeros. -/
theorem nontrivialZero_one_sub_iff {s : ℂ} :
    1 - s ∈ riemannZetaNontrivialZeros ↔ s ∈ riemannZetaNontrivialZeros := by
  constructor
  · intro h
    have := nontrivialZero_one_sub h
    simp only [sub_sub_cancel] at this
    exact this
  · exact nontrivialZero_one_sub

/-- A nontrivial zero is never equal to 0: since Re(ρ) > 0 and Re(0) = 0. -/
theorem nontrivialZero_ne_zero {s : ℂ} (hs : s ∈ riemannZetaNontrivialZeros) : s ≠ 0 := by
  intro h; subst h
  exact absurd (re_pos_of_nontrivialZero hs) (by simp)

/-- A nontrivial zero is never equal to 1: since Re(ρ) < 1 and Re(1) = 1. -/
theorem nontrivialZero_ne_one {s : ℂ} (hs : s ∈ riemannZetaNontrivialZeros) : s ≠ 1 := by
  intro h; subst h
  exact absurd (re_lt_one_of_nontrivialZero hs) (by simp)

/-! ### Smoothness and analyticity -/

/-- The Riemann ξ function is C^∞ (smooth of all orders). -/
theorem contDiff_riemannXi {n : WithTop ℕ∞} : ContDiff ℂ n riemannXi :=
  differentiable_riemannXi.contDiff

/-- The Riemann ξ function is analytic at every point. -/
theorem analyticAt_riemannXi (s : ℂ) : AnalyticAt ℂ riemannXi s :=
  differentiable_riemannXi.analyticAt s

/-- The regularized completed zeta Λ₀ is C^∞. -/
theorem contDiff_completedRiemannZeta₀ {n : WithTop ℕ∞} :
    ContDiff ℂ n completedRiemannZeta₀ :=
  differentiable_completedZeta₀.contDiff

/-- The regularized completed zeta Λ₀ is analytic at every point. -/
theorem analyticAt_completedRiemannZeta₀ (s : ℂ) : AnalyticAt ℂ completedRiemannZeta₀ s :=
  differentiable_completedZeta₀.analyticAt s

/-! ### Iterated derivative symmetry -/

/-- The n-th iterated derivative of Λ₀ satisfies the same reflection formula as Λ₀:
    Λ₀^(n)(1 − s) = (−1)ⁿ · Λ₀^(n)(s).

Follows from the functional equation `completedRiemannZeta₀_one_sub` by induction. -/
theorem iteratedDeriv_completedRiemannZeta₀_one_sub (n : ℕ) (s : ℂ) :
    iteratedDeriv n completedRiemannZeta₀ (1 - s) =
      (-1 : ℂ) ^ n * iteratedDeriv n completedRiemannZeta₀ s := by
  induction n generalizing s with
  | zero => simp [iteratedDeriv_zero, completedRiemannZeta₀_one_sub]
  | succ n ih =>
    simp only [iteratedDeriv_succ]
    have h_diff : Differentiable ℂ (iteratedDeriv n completedRiemannZeta₀) :=
      differentiable_completedZeta₀.contDiff.differentiable_iteratedDeriv' n
    have h_sub : HasDerivAt (fun t : ℂ => 1 - t) (-1) s := (hasDerivAt_id' s).const_sub 1
    have h_lhs : HasDerivAt (fun t => iteratedDeriv n completedRiemannZeta₀ (1 - t))
        (deriv (iteratedDeriv n completedRiemannZeta₀) (1 - s) * (-1)) s :=
      (h_diff (1 - s)).hasDerivAt.comp s h_sub
    have hfun : (fun t => iteratedDeriv n completedRiemannZeta₀ (1 - t)) =
        fun t => (-1 : ℂ) ^ n * iteratedDeriv n completedRiemannZeta₀ t := funext ih
    rw [hfun] at h_lhs
    have h_rhs : HasDerivAt (fun t => (-1 : ℂ) ^ n * iteratedDeriv n completedRiemannZeta₀ t)
        ((-1 : ℂ) ^ n * deriv (iteratedDeriv n completedRiemannZeta₀) s) s :=
      (h_diff s).hasDerivAt.const_mul _
    have heq := h_lhs.unique h_rhs
    linear_combination (-1 : ℂ) * heq

/-- Odd-order derivatives of Λ₀ vanish at 1/2. -/
theorem iteratedDeriv_completedRiemannZeta₀_half_of_odd (k : ℕ) :
    iteratedDeriv (2 * k + 1) completedRiemannZeta₀ (1 / 2 : ℂ) = 0 := by
  have h := iteratedDeriv_completedRiemannZeta₀_one_sub (2 * k + 1) (1 / 2 : ℂ)
  simp only [show (1 : ℂ) - 1 / 2 = 1 / 2 from by ring] at h
  have : (-1 : ℂ) ^ (2 * k + 1) = -1 := by
    rw [pow_add, pow_mul, neg_one_sq, one_pow, one_mul, pow_one]
  rw [this] at h
  linear_combination (1 / 2 : ℂ) * h

/-- The n-th iterated derivative of ξ satisfies a reflection formula:
    ξ^(n)(1 − s) = (−1)ⁿ · ξ^(n)(s).

This generalizes the functional equation (n = 0) and the derivative antisymmetry
`deriv_riemannXi_one_sub` (n = 1). The proof is by induction: assuming the identity
for the n-th derivative, we differentiate both sides (using the chain rule for s ↦ 1−s)
to obtain the (n+1)-th derivative identity. -/
theorem iteratedDeriv_riemannXi_one_sub (n : ℕ) (s : ℂ) :
    iteratedDeriv n riemannXi (1 - s) = (-1 : ℂ) ^ n * iteratedDeriv n riemannXi s := by
  induction n generalizing s with
  | zero => simp [iteratedDeriv_zero, riemannXi_one_sub]
  | succ n ih =>
    simp only [iteratedDeriv_succ]
    have h_diff : Differentiable ℂ (iteratedDeriv n riemannXi) :=
      differentiable_riemannXi.contDiff.differentiable_iteratedDeriv' n
    have h_sub : HasDerivAt (fun t : ℂ => 1 - t) (-1) s := (hasDerivAt_id' s).const_sub 1
    have h_lhs : HasDerivAt (fun t => iteratedDeriv n riemannXi (1 - t))
        (deriv (iteratedDeriv n riemannXi) (1 - s) * (-1)) s :=
      (h_diff (1 - s)).hasDerivAt.comp s h_sub
    have hfun : (fun t => iteratedDeriv n riemannXi (1 - t)) =
        fun t => (-1 : ℂ) ^ n * iteratedDeriv n riemannXi t := funext ih
    rw [hfun] at h_lhs
    have h_rhs : HasDerivAt (fun t => (-1 : ℂ) ^ n * iteratedDeriv n riemannXi t)
        ((-1 : ℂ) ^ n * deriv (iteratedDeriv n riemannXi) s) s :=
      (h_diff s).hasDerivAt.const_mul _
    have heq := h_lhs.unique h_rhs
    linear_combination (-1 : ℂ) * heq

/-- Odd-order derivatives of ξ vanish at the center of the critical strip s = 1/2.

This generalizes `deriv_riemannXi_half` (the k = 0 case). The Taylor expansion of ξ
at s = 1/2 therefore contains only even powers of (s − 1/2). -/
theorem iteratedDeriv_riemannXi_half_of_odd (k : ℕ) :
    iteratedDeriv (2 * k + 1) riemannXi (1 / 2 : ℂ) = 0 := by
  have h := iteratedDeriv_riemannXi_one_sub (2 * k + 1) (1 / 2 : ℂ)
  simp only [show (1 : ℂ) - 1 / 2 = 1 / 2 from by ring] at h
  have : (-1 : ℂ) ^ (2 * k + 1) = -1 := by
    rw [pow_add, pow_mul, neg_one_sq, one_pow, one_mul, pow_one]
  rw [this] at h
  linear_combination (1 / 2 : ℂ) * h

/-! ### Specializations of the Λ₀ reflection formula -/

/-- Derivative antisymmetry for Λ₀: Λ₀'(1 − s) = −Λ₀'(s).
    Specialization of `iteratedDeriv_completedRiemannZeta₀_one_sub` at n = 1. -/
theorem deriv_completedRiemannZeta₀_one_sub (s : ℂ) :
    deriv completedRiemannZeta₀ (1 - s) = -deriv completedRiemannZeta₀ s := by
  have h := iteratedDeriv_completedRiemannZeta₀_one_sub 1 s
  simp only [iteratedDeriv_one, pow_one] at h
  linear_combination h

/-- Λ₀'(1/2) = 0: the derivative of Λ₀ vanishes at the center of the critical strip.
    Parallels `deriv_riemannXi_half`. -/
theorem deriv_completedRiemannZeta₀_half : deriv completedRiemannZeta₀ (1 / 2 : ℂ) = 0 := by
  have h := iteratedDeriv_completedRiemannZeta₀_one_sub 1 (1 / 2 : ℂ)
  simp only [iteratedDeriv_one, pow_one,
    show (1 : ℂ) - 1 / 2 = 1 / 2 from by ring] at h
  linear_combination (1 / 2 : ℂ) * h

/-- Λ₀'(0) = −Λ₀'(1). Specialization of `deriv_completedRiemannZeta₀_one_sub` at s = 1. -/
theorem deriv_completedRiemannZeta₀_zero :
    deriv completedRiemannZeta₀ 0 = -deriv completedRiemannZeta₀ 1 := by
  have h := iteratedDeriv_completedRiemannZeta₀_one_sub 1 1
  simp only [iteratedDeriv_one, pow_one,
    show (1 : ℂ) - 1 = 0 from by ring] at h
  linear_combination h

/-! ### Derivatives at s = 0 -/

/-- The derivative of ξ at s = 0 equals −Λ₀(1)/2.
    Corollary of `deriv_riemannXi_one_sub` at s = 1: ξ'(0) = ξ'(1−1) = −ξ'(1) = −Λ₀(1)/2. -/
theorem deriv_riemannXi_zero : deriv riemannXi 0 = -completedRiemannZeta₀ 1 / 2 := by
  have h := deriv_riemannXi_one_sub 1
  rw [show (1 : ℂ) - 1 = 0 from by ring] at h
  rw [h, deriv_riemannXi_one]
  ring

/-- Iterated derivatives of Λ₀ at s = 0 are related to those at s = 1 by the
    reflection formula: Λ₀^(n)(0) = (−1)ⁿ · Λ₀^(n)(1).

    Follows from `iteratedDeriv_completedRiemannZeta₀_one_sub` at s = 1. -/
theorem iteratedDeriv_completedRiemannZeta₀_zero (n : ℕ) :
    iteratedDeriv n completedRiemannZeta₀ 0 =
      (-1 : ℂ) ^ n * iteratedDeriv n completedRiemannZeta₀ 1 := by
  have h := iteratedDeriv_completedRiemannZeta₀_one_sub n 1
  rw [show (1 : ℂ) - 1 = 0 from by ring] at h
  exact h

/-- Iterated derivatives of ξ at s = 0 are related to those at s = 1 by the
    reflection formula: ξ^(n)(0) = (−1)ⁿ · ξ^(n)(1).

    Corollary of `iteratedDeriv_riemannXi_one_sub` at s = 1. -/
theorem iteratedDeriv_riemannXi_zero (n : ℕ) :
    iteratedDeriv n riemannXi 0 = (-1 : ℂ) ^ n * iteratedDeriv n riemannXi 1 := by
  have h := iteratedDeriv_riemannXi_one_sub n 1
  rw [show (1 : ℂ) - 1 = 0 from by ring] at h
  exact h

end

end
