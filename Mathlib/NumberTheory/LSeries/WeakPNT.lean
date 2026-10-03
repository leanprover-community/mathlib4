/-
Copyright (c) 2026 The PrimeNumberTheoremAnd contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jose Francisco Antonio Balderas, Vincent Beffara, Alex Kontorovich, Terence Tao,
  Ruben Van de Velde, Arend Mellendijk, Alastair Irving
-/
module

public import Mathlib.NumberTheory.LSeries.WienerIkehara
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# The weak prime number theorem

We deduce the weak prime number theorem, and its version in arithmetic progressions, from the
Wiener–Ikehara Tauberian theorem `WienerIkehara.tendsto_sum_div`.

## Main results

* `ArithmeticFunction.vonMangoldt.tendsto_residueClass_sum_div_atTop`: the weak prime number
  theorem in arithmetic progressions: for `a` coprime to `q`,
  `∑ n ≤ x, n ≡ a [MOD q], Λ n = x / q.totient + o(x)`.
* `ArithmeticFunction.vonMangoldt.tendsto_sum_div_atTop`: the weak prime number theorem
  `∑ n ≤ x, Λ n = x + o(x)`, the `q = 1` case.
* `Chebyshev.isEquivalent_psi_id`: the `ψ`-form of the prime number theorem, `ψ x ~ x`
  (equivalently `Chebyshev.tendsto_psi_div_atTop`, `ψ x / x → 1`).
* `Chebyshev.isEquivalent_theta_id`: the `θ`-form, `θ x ~ x`.
* `Chebyshev.isEquivalent_primeCounting`: **the prime number theorem** `π x ~ x / log x`, deduced
  from the `θ`-form by Abel summation.
* `Chebyshev.eventually_exists_prime_mem_Ioc`: for every `ε > 0`, every sufficiently large `x` has
  a prime in `(x, (1 + ε) * x]`.
* `Chebyshev.isEquivalent_nth_prime_succ`: consecutive primes are asymptotically equal, `pₙ₊₁ ~ pₙ`.
* `Chebyshev.isEquivalent_log_primorial_id`: `log (primorial n) ~ n`.
* `Chebyshev.isEquivalent_log_lcmUpto_id`: `log (Nat.lcmUpto n) ~ n`.
* `Mertens.tendsto_M_div_atTop` / `Mertens.isLittleO_M_id`: the **Möbius form of the prime number
  theorem** `∑ n ≤ x, μ n = o(x)`, obtained by applying Wiener–Ikehara to the nonnegative function
  `n ↦ 1 + μ n` (with `L`-series `ζ s + 1/ζ s`).
-/

public section

open Nat hiding log
open Complex hiding log
open ArithmeticFunction.vonMangoldt Filter LSeries Chebyshev Real Finset ZMod Asymptotics
open scoped Topology

/-- The Wiener–Ikehara theorem applied to the von Mangoldt function restricted to the residue
class `a` mod `q`: the average of `residueClass a` over `[0, x]` tends to `(q.totient)⁻¹`. -/
private theorem tendsto_residueClass_sum_div {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) :
    Tendsto (fun x : ℝ ↦ (∑ n ∈ Icc 0 ⌊x⌋₊, residueClass a n) / x) atTop (𝓝 q.totient⁻¹) :=
  @WienerIkehara.tendsto_sum_div
    { f := residueClass a
      C := log 4 + 4
      bound N := calc
        _ ≤ ∑ i ∈ range N, Λ i := by
          simp_rw [abs_of_nonneg (residueClass_nonneg _ _)]
          grw [residueClass_le]
        _ ≤ (log 4 + 4) * N := by
          rcases eq_or_ne N 0 with rfl | h
          · simp
          grw [range_eq_Icc_zero_sub_one _ h, (by simp : N - 1 = ⌊(N : ℝ) - 1⌋₊),
            ← psi_eq_sum_Icc, psi_le_const_mul_self <| sub_nonneg_of_le <|
            one_le_cast_iff_ne_zero.mpr h, (by linarith : (N : ℝ) - 1 ≤ N)]
      A := q.totient⁻¹
      hA := by positivity
      G := LFunctionResidueClassAux a
      hG := continuousOn_LFunctionResidueClassAux a
      hG' s hs := by rw [eqOn_LFunctionResidueClassAux ha hs]; push_cast; ring
      hf σ hσ := LSeriesSummable_of_abscissaOfAbsConv_lt_re <|
        (abscissaOfAbsConv_residueClass_le_one a).trans_lt <| mod_cast hσ
      hpos := residueClass_nonneg a }

/-- **The weak prime number theorem in arithmetic progressions.**  For `a` coprime to `q`, the
von Mangoldt function summed over `n ≤ x` with `n ≡ a mod q` grows like `x / q.totient`. -/
theorem ArithmeticFunction.vonMangoldt.tendsto_residueClass_sum_div_atTop {q a} [NeZero q]
    (ha : a.Coprime q) (ha' : a < q) : Tendsto (fun x : ℝ ↦ (∑ n ∈ Icc 0 ⌊x⌋₊,
      if n % q = a then Λ n else 0) / x) atTop (𝓝 q.totient⁻¹) := by
  apply (tendsto_residueClass_sum_div ((isUnit_iff_coprime a q).mpr ha)).congr
  simp [residueClass, Set.indicator_apply, natCast_eq_natCast_iff', mod_eq_of_lt ha']
namespace Chebyshev

/-- **The prime number theorem, `ψ` form**: `ψ x / x → 1` as `x → ∞`. -/
theorem tendsto_psi_div_atTop : Tendsto (fun x ↦ ψ x / x) atTop (𝓝 1) := by
  simpa [mod_one, totient_one, psi_eq_sum_Icc] using
    tendsto_residueClass_sum_div_atTop (by simp) one_pos

/-- **The prime number theorem, `ψ` form**: `ψ x ∼ x`. -/
theorem isEquivalent_psi_id : ψ ~[atTop] id := by
  rw [isEquivalent_iff_tendsto_one (by exact eventually_ne_atTop 0)]
  exact tendsto_psi_div_atTop.congr (by simp)

/-- **The prime number theorem, `θ` form**: `θ x / x → 1` as `x → ∞`. -/
theorem tendsto_theta_div_atTop : Tendsto (fun x ↦ θ x / x) atTop (𝓝 1) := by
  suffices Tendsto (fun x ↦ (ψ x - θ x) / x) atTop (𝓝 0) by
    convert (tendsto_psi_div_atTop.sub this).congr' ?_
    · simp
    · filter_upwards [eventually_gt_atTop 0]; grind
  obtain ⟨C, hC⟩ := psi_sub_theta_le_mul_sqrt
  have : Tendsto (fun x ↦ C * √x / x) atTop (𝓝 0) := by
    apply ((tendsto_const_nhds (x := C)).div_atTop tendsto_sqrt_atTop).congr'
    filter_upwards [eventually_gt_atTop 0]; grind
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds this
  · filter_upwards [eventually_gt_atTop 0] with x _; positivity [theta_le_psi x]
  · filter_upwards [eventually_gt_atTop 0] with x _; grw [hC x]

/-- **The prime number theorem, `θ` form**: `θ x ~ x`. -/
theorem isEquivalent_theta_id : θ ~[atTop] id := by
  rw [isEquivalent_iff_tendsto_one (by exact eventually_ne_atTop 0)]
  exact tendsto_theta_div_atTop.congr (by simp)

/-- **The prime number theorem**: the prime counting function satisfies `π x ~ x / log x`. -/
theorem isEquivalent_primeCounting : (↑⌊·⌋₊.primeCounting) ~[atTop] fun x ↦ x / log x := by
  rw [(by grind : (↑⌊·⌋₊.primeCounting) = fun x ↦ θ x / log x + (⌊x⌋₊.primeCounting - θ x / log x))]
  apply IsEquivalent.add_isLittleO
  · rw [isEquivalent_iff_tendsto_one (by
      filter_upwards [eventually_gt_atTop 1] with x hx; grind [log_pos hx])]
    apply tendsto_theta_div_atTop.congr'
    filter_upwards [eventually_gt_atTop 1] with x hx
    simp [div_div_div_cancel_right₀ (log_pos hx).ne']
  · refine integral_theta_div_log_sq_isLittleO.congr' ?_ (Eventually.of_forall fun _ ↦ rfl)
    filter_upwards [eventually_ge_atTop 2]
    grind [primeCounting_eq_theta_div_log_add_integral]

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
  simp [this] at hab
  obtain ⟨p, hp⟩ := nonempty_of_sum_ne_zero hab.ne'
  simp_rw [Finset.mem_sdiff, mem_primesLE] at hp
  obtain ⟨⟨hpb, hpp⟩, _⟩ := hp
  refine ⟨p, hpp, ?_, ?_⟩
  · grw [lt_floor_add_one a]
    exact_mod_cast (by grind)
  · rwa [← le_floor_iff]
    grw [← hpp.one_le] at hpb
    grind [one_le_floor_iff]

/-- **Small prime gaps.**  For every `ε > 0`, every sufficiently large `x` admits a prime in the
interval `(x, (1 + ε) * x]`. -/
theorem eventually_exists_prime_mem_Ioc {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in atTop, ∃ p : ℕ, p.Prime ∧ ↑p ∈ Set.Ioc x ((1 + ε) * x) := by
  have : Tendsto (fun x ↦ θ ((1 + ε) * x) / ((1 + ε) * x)) atTop (𝓝 1) :=
    tendsto_theta_div_atTop.comp (tendsto_id.const_mul_atTop (by linarith))
  have : Tendsto (fun x ↦ θ ((1 + ε) * x) / x) atTop (𝓝 (1 + ε)) := by
    convert (this.mul_const (1 + ε)).congr' ?_
    · simp
    · filter_upwards [eventually_gt_atTop 0] with x hx; field_simp [hx.ne']
  have : Tendsto (fun x ↦ (θ ((1 + ε) * x) - θ x) / x) atTop (𝓝 ε) := by
    have := this.sub tendsto_theta_div_atTop
    rw [add_sub_cancel_left] at this
    exact this.congr' (by filter_upwards; grind)
  filter_upwards [(tendsto_order.1 this).1 0 hε, eventually_gt_atTop 0] with x _ hx
  exact exists_prime_of_theta_lt (by grind [lt_div_iff₀ hx])

/-- **Consecutive primes are asymptotically equal**: the `(n + 1)`-th prime is asymptotic to the
`n`-th prime.. -/
theorem isEquivalent_nth_prime_succ :
    (fun n ↦ ↑(nth Nat.Prime (n + 1))) ~[atTop] fun n ↦ (nth Nat.Prime n : ℝ) := by
  have hpos (n) : (0 : ℝ) < nth Nat.Prime n := mod_cast by linarith [add_two_le_nth_prime n]
  rw [isEquivalent_iff_tendsto_one (Eventually.of_forall fun n ↦ (hpos n).ne')]
  refine tendsto_order.2 ⟨fun c hc ↦ Eventually.of_forall fun n ↦ ?_, fun c hc ↦ ?_⟩
  · dsimp
    grw [hc]
    field_simp [hpos n]
    simp [nth_monotone infinite_setOfPred_prime n.le_succ]
  · obtain ⟨ε, hε, hεc⟩ : ∃ ε, 0 < ε ∧ 1 + ε < c := ⟨(c - 1) / 2, by linarith, by linarith⟩
    filter_upwards [(tendsto_natCast_atTop_atTop.comp (nth_strictMono
      infinite_setOfPred_prime).tendsto_atTop).eventually (eventually_exists_prime_mem_Ioc hε)]
      with n ⟨q, hq, hq1, hq2⟩
    specialize hpos n
    dsimp at *
    grw [(nth_add_one_le_iff infinite_setOfPred_prime hq).mpr (mod_cast hq1), hq2, ← hεc]
    simp [field]

/-- **Primorial asymptotics**: `log (primorial n) / n → 1`. -/
theorem tendsto_log_primorial_div_atTop : Tendsto (fun n ↦ log (primorial n) / n) atTop (𝓝 1) :=
  (tendsto_theta_div_atTop.comp tendsto_natCast_atTop_atTop).congr
  (by simp [theta_eq_log_primorial])

/-- **Primorial asymptotics**: `log (primorial n) ~ n`. -/
theorem isEquivalent_log_primorial_id : (fun n ↦ log (primorial n)) ~[atTop] (↑·) := by
  rw [isEquivalent_iff_tendsto_one
    (by filter_upwards [eventually_gt_atTop 0] with _ _ using by positivity)]
  exact tendsto_log_primorial_div_atTop.congr (by simp)

/-- **Least common multiple asymptotics**: `log (lcmUpto n) / n → 1`. -/
theorem tendsto_log_lcmUpto_div_atTop : Tendsto (fun n ↦ log (lcmUpto n) / n) atTop (𝓝 1) :=
  (tendsto_psi_div_atTop.comp tendsto_natCast_atTop_atTop).congr (by simp [psi_eq_log_lcmUpto])

/-- **Least common multiple asymptotics**: `log (lcmUpto n) ~ n`. -/
theorem isEquivalent_log_lcmUpto_id : (fun n ↦ log (lcmUpto n)) ~[atTop] (↑·) := by
  rw [isEquivalent_iff_tendsto_one
    (by filter_upwards [eventually_gt_atTop 0] with _ _ using by positivity)]
  exact tendsto_log_lcmUpto_div_atTop.congr (by simp)

end Chebyshev

namespace Mertens

open scoped ArithmeticFunction.Moebius

/-- The **Mertens function** `M x = ∑ n ≤ x, μ n`, the partial sums of the Möbius function.
Following `Chebyshev.psi`/`Chebyshev.theta`, the sum is taken over `Ioc 0 ⌊x⌋₊`; see `M_eq_sum_Icc`
for the equal sum over `Icc 0 ⌊x⌋₊`. -/
noncomputable def M (x : ℝ) : ℤ := ∑ n ∈ Ioc 0 ⌊x⌋₊, μ n

theorem M_eq_sum_Icc (x : ℝ) : M x = ∑ n ∈ Icc 0 ⌊x⌋₊, μ n := by
  rw [M, ← add_sum_Ioc_eq_sum_Icc] <;> simp

/-- The trivial bound `|M x| ≤ x`. -/
theorem abs_M_le {x : ℝ} (hx : 0 ≤ x) : |M x| ≤ x := by
  unfold M
  grw [abs_sum_le_sum_abs, ArithmeticFunction.abs_moebius_le_one]
  simp [floor_le hx]

/-- The **Möbius form of the prime number theorem**: `M x / x → 0`. -/
theorem tendsto_M_div_atTop : Tendsto (fun x ↦ (M x : ℝ) / x) atTop (𝓝 0) := by
  have (s : ℂ) (hs : 1 ≤ s.re) : riemannZeta₁ s ≠ 0 := by
    rcases eq_or_ne s 1 with rfl | hs1
    · simp
    · grind [riemannZeta_eq_inv_sub_mul hs1, riemannZeta_ne_zero_of_one_le_re]
  have e : (fun n ↦ ofReal (1 + μ n)) = 1 + fun n ↦ (μ n : ℂ) := by push_cast; funext; simp
  have hWI : Tendsto (fun x : ℝ ↦ (∑ n ∈ Icc 0 ⌊x⌋₊, ((1 : ℝ) + μ n)) / x) atTop (𝓝 1) :=
    @WienerIkehara.tendsto_sum_div
      { f n := 1 + μ n
        C := 2
        bound _ := mod_cast by
          grw [abs_add_le, ArithmeticFunction.abs_moebius_le_one]; simp; grind
        A := 1
        hA := zero_le_one
        G s := riemannZeta₀ s + (s - 1) * (riemannZeta₁ s)⁻¹
        hG := .add differentiable_riemannZeta₀.continuous.continuousOn <|
          .mul (by fun_prop) (differentiable_riemannZeta₁.continuous.continuousOn.inv₀ this)
        hG' s hs := by
          have : s ≠ 1 := by rintro rfl; simp at hs
          have : LSeries (fun n ↦ (μ n : ℂ)) s = (riemannZeta s)⁻¹ := by
            grind [LSeries_one_eq_riemannZeta hs, LSeries_one_mul_Lseries_moebius]
          have : LSeries (fun n ↦ ofReal (1 + μ n)) s = riemannZeta s + (riemannZeta s)⁻¹ := by
            rw [e, LSeries_add, LSeries_one_eq_riemannZeta hs, this]
            exacts [LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (by simp) hs,
              ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs]
          change riemannZeta₀ s + (s - 1) * (riemannZeta₁ s)⁻¹
            = LSeries (fun n ↦ ofReal (1 + μ n)) s - 1 / (s - 1)
          grind [inv_riemannZeta_eq_sub_mul_of_ne_one, riemannZeta_eq_inv_sub_add]
        hf σ hσ := by
          have : 1 < (σ : ℂ).re := by simpa using hσ
          change LSeriesSummable (fun n ↦ ofReal (1 + μ n)) (σ : ℂ)
          rw [e]
          exact (LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ ↦ by simp) this).add
            (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr this)
        hpos n := by dsimp; grw [← (abs_le.mp ArithmeticFunction.abs_moebius_le_one).1]; simp }
  have : Tendsto (fun x : ℝ ↦ (⌊x⌋₊ + 1) / x) atTop (𝓝 1) := by
    convert ((tendsto_nat_floor_div_atTop (R := ℝ)).add tendsto_inv_atTop_zero).congr' ?_
    · simp
    · filter_upwards [eventually_gt_atTop 0]; grind
  convert (hWI.sub this).congr' ?_
  · simp
  · filter_upwards [eventually_gt_atTop 0]; simp [← sub_div, sum_add_distrib, M_eq_sum_Icc]

/-- The **Möbius form of the prime number theorem**, asymptotic form: `M x = o(x)`. -/
theorem isLittleO_M_id : (fun x ↦ (M x : ℝ)) =o[atTop] id :=
  (isLittleO_iff_tendsto' (by filter_upwards [eventually_gt_atTop 0]; grind)).mpr
  (tendsto_M_div_atTop.congr (by simp))

end Mertens
