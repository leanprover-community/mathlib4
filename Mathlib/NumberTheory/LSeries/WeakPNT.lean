/-
Copyright (c) 2026 The PrimeNumberTheoremAnd contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jose Francisco Antonio Balderas, Vincent Beffara, Alex Kontorovich, Terence Tao,
  Ruben Van de Velde, Arend Mellendijk, Alastair Irving
-/
module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.LSeries.PrimesInAP
public import Mathlib.NumberTheory.LSeries.WienerIkehara

/-!
# The weak prime number theorem

We deduce the prime number theorem, and its version for primes in arithmetic progressions, from
the Wiener–Ikehara Tauberian theorem `WienerIkehara.tendsto_sum_div`.

Here `ψ x = ∑ n ≤ x, Λ n` and `θ x = ∑ p ≤ x, log p` (the sum running over primes) are the
Chebyshev functions `Chebyshev.psi` and `Chebyshev.theta`.

## Main results

* `ArithmeticFunction.vonMangoldt.tendsto_sum_modEq_div_atTop`: the von Mangoldt form of the
  prime number theorem in arithmetic progressions: for `a` coprime to `q`,
  `∑ n ≤ x, n ≡ a [MOD q], Λ n = x / φ q + o(x)`.
* `Chebyshev.isEquivalent_psi_id`: the `ψ`-form of the prime number theorem, `ψ x ~ x`
  (equivalently `Chebyshev.tendsto_psi_div_atTop`, `ψ x / x → 1`); this is the `q = 1` case of
  the previous result.
* `Chebyshev.isEquivalent_theta_id`: the `θ`-form, `θ x ~ x`.
* `Nat.isEquivalent_primeCounting`: **the prime number theorem** `π x ~ x / log x`, deduced
  from the `θ`-form by Abel summation (`Chebyshev.isLittleO_primeCounting_mul_log_sub_theta`).
* `Nat.isEquivalent_card_prime_modEq`: **the prime number theorem in arithmetic progressions**:
  for `a` coprime to `q`, the number of primes `p ≤ x` with `p ≡ a [MOD q]` is asymptotic to
  `x / (φ q * log x)`.
* `Nat.eventually_exists_prime_mem_Ioc`: for every `ε > 0` and every sufficiently large `x`, there
  is a prime in `(x, (1 + ε) * x]`; `Nat.eventually_exists_prime_mem_Ioc_sub` gives one in
  `((1 - ε) * x, x]`.
* `Nat.isEquivalent_nth_prime_succ`: consecutive primes are asymptotically equal, `pₙ₊₁ ~ pₙ`.
* `Nat.isEquivalent_log_primorial_id`: `log (primorial n) ~ n`.
* `Nat.isEquivalent_log_lcmUpto_id`: `log (Nat.lcmUpto n) ~ n`.

## Future directions

* Versions of `Nat.eventually_exists_prime_mem_Ioc` and `Nat.eventually_exists_prime_mem_Ioc_sub`
for arithmetic progressions
* Showing that the nth prime is asymptotic to `n * log n`

Note though that all the results here could eventually be superseded by other approaches to the
prime number theorem with stronger error terms.

-/

public section

open Nat hiding log
open ArithmeticFunction.vonMangoldt Filter LSeries Chebyshev Real Finset ZMod Asymptotics
open scoped Topology

/-- **The prime number theorem in arithmetic progressions**, von Mangoldt form, stated for a unit
`a` of `ZMod q`: the average of `residueClass a` over `[0, x]` tends to `(φ q)⁻¹`. -/
theorem ArithmeticFunction.vonMangoldt.tendsto_sum_residueClass_div_atTop {q : ℕ} [NeZero q]
    {a : ZMod q} (ha : IsUnit a) :
    Tendsto (fun x : ℝ ↦ (∑ n ∈ Icc 0 ⌊x⌋₊, residueClass a n) / x) atTop (𝓝 (φ q)⁻¹) :=
  WienerIkehara.tendsto_sum_div (C := log 4 + 4) (G := LFunctionResidueClassAux a)
    (fun N ↦ (sum_le_sum fun i _ ↦ residueClass_le a i).trans (sum_range_vonMangoldt_le N))
    (continuousOn_LFunctionResidueClassAux a)
    (fun s hs ↦ by rw [eqOn_LFunctionResidueClassAux ha hs]; push_cast; ring)
    (residueClass_nonneg a)

/-- **The prime number theorem in arithmetic progressions**, von Mangoldt form.  For `a` coprime
to `q`, the von Mangoldt function summed over `n ≤ x` with `n ≡ a [MOD q]` grows like
`x / φ q`. -/
theorem ArithmeticFunction.vonMangoldt.tendsto_sum_modEq_div_atTop {q a : ℕ} [NeZero q]
    (ha : a.Coprime q) :
    Tendsto (fun x : ℝ ↦ (∑ n ∈ Icc 0 ⌊x⌋₊ with n ≡ a [MOD q], Λ n) / x) atTop (𝓝 (φ q)⁻¹) := by
  apply (tendsto_sum_residueClass_div_atTop ((isUnit_iff_coprime a q).mpr ha)).congr
  simp [residueClass, Set.indicator_apply, sum_filter, natCast_eq_natCast_iff]

namespace Chebyshev

/-- **The prime number theorem, `ψ` form**: `ψ x / x → 1` as `x → ∞`, where
`ψ x = ∑ n ≤ x, Λ n` is the Chebyshev function `Chebyshev.psi`. -/
theorem tendsto_psi_div_atTop : Tendsto (fun x ↦ ψ x / x) atTop (𝓝 1) := by
  simpa [Nat.modEq_one, totient_one, psi_eq_sum_Icc] using
    tendsto_sum_modEq_div_atTop (q := 1) (a := 0) (by simp)

/-- **The prime number theorem, `ψ` form**: `ψ x ∼ x`, where `ψ x = ∑ n ≤ x, Λ n` is the
Chebyshev function `Chebyshev.psi`. -/
theorem isEquivalent_psi_id : ψ ~[atTop] id := by
  rw [isEquivalent_iff_tendsto_one (by exact eventually_ne_atTop 0)]
  exact tendsto_psi_div_atTop.congr (by simp)

/-- **The prime number theorem, `θ` form**: `θ x / x → 1` as `x → ∞`, where
`θ x = ∑ p ≤ x, log p` (over primes `p`) is the Chebyshev function `Chebyshev.theta`. -/
theorem tendsto_theta_div_atTop : Tendsto (fun x ↦ θ x / x) atTop (𝓝 1) := by
  simpa using (tendsto_psi_div_atTop.sub isLittleO_psi_sub_theta_id.tendsto_div_nhds_zero).congr
    fun x ↦ by grind [Pi.sub_apply]

/-- **The prime number theorem, `θ` form**: `θ x ~ x`, where `θ x = ∑ p ≤ x, log p` (over
primes `p`) is the Chebyshev function `Chebyshev.theta`. -/
theorem isEquivalent_theta_id : θ ~[atTop] id := by
  rw [isEquivalent_iff_tendsto_one (by exact eventually_ne_atTop 0)]
  exact tendsto_theta_div_atTop.congr (by simp)

/-- **The prime number theorem in arithmetic progressions**, `θ` form.  For `a` coprime to `q`,
`∑ p ≤ x, p ≡ a [MOD q], log p` (over primes `p`) is asymptotic to `x / φ q`. -/
theorem tendsto_sum_log_prime_modEq_div_atTop {q a : ℕ} [NeZero q] (ha : a.Coprime q) :
    Tendsto (fun x : ℝ ↦ (∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime ∧ p ≡ a [MOD q], log p) / x) atTop
      (𝓝 (φ q)⁻¹) := by
  have hψ : Tendsto (fun x : ℝ ↦ (∑ n ∈ Ioc 0 ⌊x⌋₊ with n ≡ a [MOD q], Λ n) / x) atTop
      (𝓝 (φ q)⁻¹) :=
    (tendsto_sum_modEq_div_atTop ha).congr fun x ↦ by
      rw [sum_filter, sum_filter, ← add_sum_Ioc_eq_sum_Icc] <;> simp
  simpa using (hψ.sub (isLittleO_sum_vonMangoldt_with_sum_prime_log_with
    (· ≡ a [MOD q])).tendsto_div_nhds_zero).congr <| by grind

/-- If the Chebyshev function `θ` is strictly larger at `b` than at `a`, then there is a prime in
the half-open interval `(a, b]`. -/
theorem exists_prime_of_theta_lt {a b} (hab : θ a < θ b) :
    ∃ p : ℕ, p.Prime ∧ ↑p ∈ Set.Ioc a b := by
  have : ⌊a⌋₊ ≤ ⌊b⌋₊ := by
    rw [theta_eq_theta_coe_floor a, theta_eq_theta_coe_floor b] at hab
    contrapose! hab
    exact theta_mono (mod_cast hab.le)
  have : θ b = ∑ p ∈ primesLE ⌊b⌋₊ \ primesLE ⌊a⌋₊, log (p : ℝ) + θ a := by
    simp_rw [theta_eq_sum_primesLE, sum_sdiff (primesLE_mono this)]
  obtain ⟨p, hp⟩ : ∃ p, p ∈ ⌊b⌋₊.primesLE \ ⌊a⌋₊.primesLE :=
    nonempty_of_sum_ne_zero <| by simpa [this] using hab.ne'
  simp_rw [Finset.mem_sdiff, mem_primesLE] at hp
  obtain ⟨⟨hpb, hpp⟩, _⟩ := hp
  refine ⟨p, hpp, ?_, ?_⟩
  · grw [lt_floor_add_one a]
    norm_cast
    grind
  · grind [le_floor_iff, one_le_floor_iff]

end Chebyshev

namespace Nat

/-- **The prime number theorem**: the prime counting function satisfies `π x ~ x / Real.log x`. -/
theorem isEquivalent_primeCounting :
    (fun x : ℝ ↦ (primeCounting ⌊x⌋₊ : ℝ)) ~[atTop] fun x ↦ x / Real.log x := by
  have h := tendsto_theta_div_atTop.add
    isLittleO_primeCounting_mul_log_sub_theta.tendsto_div_nhds_zero
  rw [add_zero] at h
  rw [isEquivalent_iff_tendsto_one (by
    filter_upwards [eventually_gt_atTop 1]; grind [Real.log_pos])]
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 1]
  grind [Pi.div_apply, Real.log_pos]

/-- **The prime number theorem in arithmetic progressions**: for `a` coprime to `q`, the number
`π(x; q, a)` of primes `p ≤ x` with `p ≡ a [MOD q]` satisfies
`π(x; q, a) * log x / x → 1 / φ(q)`. -/
theorem tendsto_card_prime_modEq_mul_log_div_atTop {q a : ℕ} [NeZero q] (ha : a.Coprime q) :
    Tendsto (fun x : ℝ ↦ #{p ∈ Ioc 0 ⌊x⌋₊ | p.Prime ∧ p ≡ a [MOD q]} * Real.log x / x) atTop
      (𝓝 (φ q)⁻¹) := by
  simpa using ((tendsto_sum_log_prime_modEq_div_atTop ha).add
    (isLittleO_card_prime_with_mul_log_sum_prime_log_with
      (· ≡ a [MOD q])).tendsto_div_nhds_zero).congr fun x ↦ by grind

/-- **The prime number theorem in arithmetic progressions**: for `a` coprime to `q`, the number
`π(x; q, a)` of primes `p ≤ x` with `p ≡ a [MOD q]` satisfies `π(x; q, a) ~ x / (φ(q) log x)`. -/
theorem isEquivalent_card_prime_modEq {q a : ℕ} [NeZero q] (ha : a.Coprime q) :
    (fun x : ℝ ↦ (#{p ∈ Ioc 0 ⌊x⌋₊ | p.Prime ∧ p ≡ a [MOD q]} : ℝ)) ~[atTop]
      fun x ↦ x / (φ q * Real.log x) := by
  have hφ : (φ q : ℝ) ≠ 0 := mod_cast (totient_pos.mpr (NeZero.pos q)).ne'
  rw [isEquivalent_iff_tendsto_one (by
    filter_upwards [eventually_gt_atTop 1] with x hx
    exact div_ne_zero (by linarith) (mul_ne_zero hφ (Real.log_pos hx).ne'))]
  convert ((tendsto_card_prime_modEq_mul_log_div_atTop ha).const_mul (φ q : ℝ)).congr' ?_
  · field_simp
  · filter_upwards [eventually_gt_atTop 1]
    grind [Pi.div_apply, Real.log_pos]

/-- **Small prime gaps.**  Let `ε > 0`.  Then for every sufficiently large `x`, there exists a
prime in the interval `(x, (1 + ε) * x]`. -/
theorem eventually_exists_prime_mem_Ioc {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∃ p : ℕ, p.Prime ∧ ↑p ∈ Set.Ioc x ((1 + ε) * x) := by
  have : Tendsto (fun x ↦ θ ((1 + ε) * x) / ((1 + ε) * x)) atTop (𝓝 1) :=
    tendsto_theta_div_atTop.comp (tendsto_id.const_mul_atTop (by linarith))
  have : Tendsto (fun x ↦ θ ((1 + ε) * x) / x) atTop (𝓝 (1 + ε)) := by
    convert (this.mul_const (1 + ε)).congr' ?_
    · simp
    · filter_upwards [eventually_gt_atTop 0] with x hx; field_simp [hx.ne']
  have : Tendsto (fun x ↦ (θ ((1 + ε) * x) - θ x) / x) atTop (𝓝 ε) := by
    grind [this.sub tendsto_theta_div_atTop]
  filter_upwards [this.eventually_const_lt hε, eventually_gt_atTop 0] with x _ hx
  exact exists_prime_of_theta_lt (by grind [lt_div_iff₀ hx])

/-- **Small prime gaps**, dual form.  Let `ε > 0`.  Then for every sufficiently large `x`, there
exists a prime in the interval `((1 - ε) * x, x]`. -/
theorem eventually_exists_prime_mem_Ioc_sub {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∃ p : ℕ, p.Prime ∧ ↑p ∈ Set.Ioc ((1 - ε) * x) x := by
  wlog hε1 : ε < 1
  · filter_upwards [this (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num), eventually_ge_atTop 0]
      with x ⟨p, hp, h1, h2⟩ hx
    exact ⟨p, hp, by nlinarith, h2⟩
  filter_upwards [(tendsto_id.const_mul_atTop (by linarith : 0 < 1 - ε)).eventually
    (eventually_exists_prime_mem_Ioc hε), eventually_ge_atTop 0] with x ⟨p, hp, h1, h2⟩ hx
  exact ⟨p, hp, h1, h2.trans (by rw [id_eq]; nlinarith [mul_nonneg (sq_nonneg ε) hx])⟩

/-- **Consecutive primes are asymptotically equal**: the `(n + 1)`-th prime is asymptotic to the
`n`-th prime. -/
theorem isEquivalent_nth_prime_succ :
    (fun n ↦ ↑(nth Nat.Prime (n + 1))) ~[atTop] fun n ↦ (nth Nat.Prime n : ℝ) := by
  have hpos (n) : (0 : ℝ) < nth Nat.Prime n := mod_cast by linarith [add_two_le_nth_prime n]
  rw [isEquivalent_iff_tendsto_one (Eventually.of_forall fun n ↦ (hpos n).ne')]
  refine tendsto_order.2 ⟨fun c hc ↦ Eventually.of_forall fun n ↦ ?_, fun c hc ↦ ?_⟩
  · grw [Pi.div_apply, hc]
    field_simp [hpos n]
    simp [nth_monotone infinite_setOfPred_prime n.le_succ]
  · obtain ⟨ε, hε, hεc⟩ : ∃ ε, 0 < ε ∧ 1 + ε < c := ⟨(c - 1) / 2, by linarith, by linarith⟩
    filter_upwards [(tendsto_natCast_atTop_atTop.comp (nth_strictMono
      infinite_setOfPred_prime).tendsto_atTop).eventually (eventually_exists_prime_mem_Ioc hε)]
      with n ⟨q, hq, hq1, hq2⟩
    specialize hpos n
    simp only [Function.comp_apply, Pi.div_apply] at hq1 hq2 ⊢
    have : nth Prime (n + 1) ≤ q :=
      (nth_add_one_le_iff infinite_setOfPred_prime hq).mpr (mod_cast hq1)
    grw [this, hq2, ← hεc]
    simp [field]

/-- **Least common multiple asymptotics**: `Real.log (lcmUpto n) / n → 1`. -/
theorem tendsto_log_lcmUpto_div_atTop : Tendsto (fun n ↦ Real.log (lcmUpto n) / n) atTop (𝓝 1) :=
  (tendsto_psi_div_atTop.comp tendsto_natCast_atTop_atTop).congr (by simp [psi_eq_log_lcmUpto])

/-- **Least common multiple asymptotics**: `Real.log (lcmUpto n) ~ n`. -/
theorem isEquivalent_log_lcmUpto_id : (fun n ↦ Real.log (lcmUpto n)) ~[atTop] (↑·) := by
  rw [isEquivalent_iff_tendsto_one
    (by filter_upwards [eventually_gt_atTop 0] with _ _ using by positivity)]
  exact tendsto_log_lcmUpto_div_atTop.congr (by simp)

/-- **Primorial asymptotics**: `Real.log (primorial n) / n → 1`. -/
theorem tendsto_log_primorial_div_atTop :
    Tendsto (fun n ↦ Real.log (primorial n) / n) atTop (𝓝 1) :=
  (tendsto_theta_div_atTop.comp tendsto_natCast_atTop_atTop).congr
  (by simp [theta_eq_log_primorial])

/-- **Primorial asymptotics**: `Real.log (primorial n) ~ n`. -/
theorem isEquivalent_log_primorial_id : (fun n ↦ Real.log (primorial n)) ~[atTop] (↑·) := by
  rw [isEquivalent_iff_tendsto_one
    (by filter_upwards [eventually_gt_atTop 0] with _ _ using by positivity)]
  exact tendsto_log_primorial_div_atTop.congr (by simp)

end Nat
