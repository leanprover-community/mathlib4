
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Complex.Divisor
import Mathlib.Analysis.Complex.CartanInverseFactorBound
/-!
## Cartan bookkeeping (intrinsic): Bound on finite sums of the majorant

This file isolates the expensive  bookkeeping step used in the Cartan/minimum-modulus argument:
we bound finite partial sums `∑_{p∈s} b p` of the majorant exponent `b` by
`Cprod * (1+r)^τ`, where `Cprod` depends only on `τ`, `m`, and the τ-sum `Sτ`.

The point is exclusively performance
-/

noncomputable section

/-!
## Cartan/minimum-modulus helpers (stubbed API)
This repository previously imported `PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.CartanBound`.
In this workspace we provide the small API surface that downstream files currently use:
`LogSingularity.φ`, `LogSingularity.Cφ`, and the basic facts `φ_nonneg`, `Cφ_pos`.
The heavy Cartan/minimum-modulus lemmas live elsewhere; this file is intentionally minimal.
-/

noncomputable section

/-!
## Cartan bookkeeping (intrinsic): Bound on finite sums of the majorant

This file isolates the expensive  bookkeeping step used in the Cartan/minimum-modulus argument:
we bound finite partial sums `∑_{p∈s} b p` of the majorant exponent `b` by
`Cprod * (1+r)^τ`, where `Cprod` depends only on `τ`, `m`, and the τ-sum `Sτ`.

The point is exclusively performance
-/

noncomputable section

namespace Complex.Hadamard

open scoped BigOperators
open Filter Finset Real Topology

private lemma cartan_majorant_nonneg
    {f : ℂ → ℂ} {m : ℕ} {τ r : ℝ} (hr : 0 ≤ r)
    (small : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) :
    letI : DecidableEq (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := Classical.decEq _
    let ap : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ := fun p => ‖divisorZeroIndex₀_val p‖
    let b : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
      fun p =>
        if p ∈ small then
          LogSingularity.φ (r / ap p) + (m : ℝ) * (1 + (r / ap p) ^ τ)
        else
          (2 : ℝ) * (r / ap p) ^ τ
    ∀ p, 0 ≤ b p := by
  classical
  dsimp
  intro p
  let ap : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ := fun q => ‖divisorZeroIndex₀_val q‖
  have hap : ap p = ‖divisorZeroIndex₀_val p‖ := rfl
  by_cases hp : p ∈ small
  · have hφ : 0 ≤ LogSingularity.φ (r / ap p) := LogSingularity.φ_nonneg (t := r / ap p)
    have hm0 : 0 ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
    have h1 : 0 ≤ (1 + (r / ap p) ^ τ) := by positivity
    have : 0 ≤ LogSingularity.φ (r / ap p) + (m : ℝ) * (1 + (r / ap p) ^ τ) := by
      nlinarith [hφ, hm0, h1]
    simpa [hap, hp, ap] using this
  · have hbase : 0 ≤ r / ap p := div_nonneg hr (by positivity)
    have hpow : 0 ≤ (r / ap p) ^ τ := Real.rpow_nonneg hbase τ
    have : 0 ≤ (2 : ℝ) * (r / ap p) ^ τ := mul_nonneg (by norm_num) hpow
    simpa [hap, hp, ap] using this

private lemma cartan_majorant_summable
    {f : ℂ → ℂ} {m : ℕ} {τ r : ℝ} (hr : 0 ≤ r)
    (small : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)))
    (hsumτ :
      Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
        ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ)) :
    letI : DecidableEq (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := Classical.decEq _
    let ap : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ := fun p => ‖divisorZeroIndex₀_val p‖
    let b : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
      fun p =>
        if p ∈ small then
          LogSingularity.φ (r / ap p) + (m : ℝ) * (1 + (r / ap p) ^ τ)
        else
          (2 : ℝ) * (r / ap p) ^ τ
    Summable b := by
  classical
  dsimp
  let ap : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ := fun q => ‖divisorZeroIndex₀_val q‖
  let b : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
    fun p =>
      if p ∈ small then
        LogSingularity.φ (r / ap p) + (m : ℝ) * (1 + (r / ap p) ^ τ)
      else
        (2 : ℝ) * (r / ap p) ^ τ
  have hb : Summable b := by
    let b₁ : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
      fun p =>
        if p ∈ small then
          LogSingularity.φ (r / ap p) + (m : ℝ) * (1 + (r / ap p) ^ τ)
        else 0
    let b₂ : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
      fun p => if p ∈ small then 0 else (2 : ℝ) * (r / ap p) ^ τ
    have hb_decomp : b = fun p => b₁ p + b₂ p := by
      funext p
      by_cases hp : p ∈ small <;> simp [b, b₁, b₂, hp]
    have hb₁ : Summable b₁ := by
      refine summable_of_finite_support ?_
      refine (Finset.finite_toSet small).subset ?_
      intro p hp
      by_contra hps
      have hps' : p ∉ small := by simpa using hps
      have : b₁ p = 0 := by simp [b₁, hps']
      exact hp (by simp [this])
    have hb₂ : Summable b₂ := by
      have hconst :
          Summable (fun p =>
            (2 : ℝ) * (r ^ τ) * (‖divisorZeroIndex₀_val p‖⁻¹ ^ τ)) :=
        hsumτ.mul_left ((2 : ℝ) * (r ^ τ))
      refine Summable.of_nonneg_of_le
        (fun p => by
          by_cases hp : p ∈ small
          · simp [b₂, hp]
          · have : 0 ≤ (2 : ℝ) * (r / ap p) ^ τ := by positivity
            simpa [b₂, hp] using this)
        (fun p => ?_) hconst
      by_cases hp : p ∈ small
      · have : 0 ≤ (2 : ℝ) * (r ^ τ) * (‖divisorZeroIndex₀_val p‖⁻¹ ^ τ) := by positivity
        simpa [b₂, hp] using this
      · have hrpow : (r / ap p) ^ τ = (r ^ τ) * (‖divisorZeroIndex₀_val p‖⁻¹ ^ τ) := by
          have ha0 : 0 ≤ (‖divisorZeroIndex₀_val p‖⁻¹ : ℝ) := by positivity
          simpa [ap, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
            (Real.mul_rpow (x := r) (y := (‖divisorZeroIndex₀_val p‖⁻¹ : ℝ)) (z := τ) hr ha0)
        simp [b₂, hp, hrpow, mul_assoc, mul_left_comm, mul_comm]
    simpa [hb_decomp] using hb₁.add hb₂
  refine hb.congr ?_
  intro p
  by_cases hp : p ∈ small <;> simp [b, ap, hp]

private lemma cartan_card_small_le
    {f : ℂ → ℂ} {τ R : ℝ} (hRpos : 0 < R) (hτ_nonneg : 0 ≤ τ)
    (small : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)))
    (hsmall : ∀ p ∈ small, ‖divisorZeroIndex₀_val p‖ ≤ 4 * R)
    (hsumτ :
      Summable
        (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
          ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ)) :
    (small.card : ℝ)
      ≤ (4 * R) ^ τ
          * ((∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
                ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ) + 1) := by
  classical
  set Sτ : ℝ :=
    ∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ
  have hsum_le : (∑ p ∈ small, ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ) ≤ Sτ := by
    have hnn :
        ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
          0 ≤ ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ := by
      intro p
      exact Real.rpow_nonneg (inv_nonneg.2 (norm_nonneg _)) _
    simpa [Sτ] using
      (Summable.sum_le_tsum (s := small)
        (f := fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
          ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ)
        (fun p _ => hnn p) hsumτ)
  have hgeom_sum :
      (small.card : ℝ) ≤ ∑ p ∈ small, (4 * R) ^ τ * ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ := by
    have hcard_eq : (small.card : ℝ) = ∑ p ∈ small, (1 : ℝ) := by simp
    rw [hcard_eq]
    refine Finset.sum_le_sum (fun p hp => ?_)
    have hp_le : ‖divisorZeroIndex₀_val p‖ ≤ 4 * R := hsmall p hp
    have hap : 0 < ‖divisorZeroIndex₀_val p‖ :=
      norm_pos_iff.2 (divisorZeroIndex₀_val_ne_zero p)
    have hbase : (1 : ℝ) ≤ (4 * R) / ‖divisorZeroIndex₀_val p‖ := by
      exact (le_div_iff₀ hap).2 (by simpa [mul_one] using hp_le)
    have : (1 : ℝ) ≤ ((4 * R) / ‖divisorZeroIndex₀_val p‖) ^ τ :=
      Real.one_le_rpow hbase hτ_nonneg
    have hdiv :
        ((4 * R) / ‖divisorZeroIndex₀_val p‖) ^ τ =
          (4 * R) ^ τ * (‖divisorZeroIndex₀_val p‖)⁻¹ ^ τ := by
      have h4 : 0 ≤ (4 * R : ℝ) := by nlinarith [le_of_lt hRpos]
      have ha : 0 ≤ (‖divisorZeroIndex₀_val p‖ : ℝ)⁻¹ := by positivity
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        (Real.mul_rpow (x := (4 * R : ℝ))
          (y := (‖divisorZeroIndex₀_val p‖ : ℝ)⁻¹) (z := τ) h4 ha)
    have : (1 : ℝ) ≤ (4 * R) ^ τ * ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ := by
      simpa [hdiv] using this
    exact this
  have hgeom :
      (small.card : ℝ) ≤ (4 * R) ^ τ * (∑ p ∈ small, ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ) := by
    simpa [Finset.mul_sum] using hgeom_sum
  have hsmall_le : (small.card : ℝ) ≤ (4 * R) ^ τ * Sτ := by
    exact hgeom.trans (mul_le_mul_of_nonneg_left hsum_le (by positivity))
  have hS_le : (4 * R) ^ τ * Sτ ≤ (4 * R) ^ τ * (Sτ + 1) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    linarith
  have : (small.card : ℝ) ≤ (4 * R) ^ τ * (Sτ + 1) := hsmall_le.trans hS_le
  simpa [Sτ, add_comm, add_left_comm, add_assoc, mul_assoc] using this

private lemma cartan_rpow_mul_le
    {τ R r : ℝ} (hRpos : 0 < R) (hrpos : 0 < r) (hR_le_r : R ≤ r) (hτ_nonneg : 0 ≤ τ) :
    (4 * R) ^ τ ≤ (4 : ℝ) ^ τ * (1 + r) ^ τ := by
  have hR_le_1r : R ≤ 1 + r := by linarith [hR_le_r, le_of_lt hrpos]
  have hbase0 : 0 ≤ (4 * R : ℝ) := by nlinarith [le_of_lt hRpos]
  have : (4 * R) ^ τ ≤ (4 * (1 + r)) ^ τ := by
    refine Real.rpow_le_rpow hbase0 ?_ hτ_nonneg
    nlinarith [hR_le_1r]
  have hmul : (4 * (1 + r)) ^ τ = (4 : ℝ) ^ τ * (1 + r) ^ τ := by
    have h4 : 0 ≤ (4 : ℝ) := by norm_num
    have h1 : 0 ≤ (1 + r : ℝ) := by positivity
    simpa [mul_assoc] using
      (Real.mul_rpow (x := (4 : ℝ)) (y := (1 + r : ℝ)) (z := τ) h4 h1)
  simpa [hmul] using this

open Classical in
theorem cartan_sum_majorant_le
    {f : ℂ → ℂ} {m : ℕ} {τ R r : ℝ}
    (hRpos : 0 < R)
    (hrpos : 0 < r)
    (hR_le_r : R ≤ r)
    (hτ_nonneg : 0 ≤ τ)
    (smallSet : Set (divisorZeroIndex₀ f (Set.univ : Set ℂ)))
    (hsmall_fin : smallSet.Finite)
    (hsmallSet :
      smallSet = {p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | ‖divisorZeroIndex₀_val p‖ ≤ 4 * R})
    (hsumτ :
      Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) => ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ))
    (hr_phi :
      let small : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := hsmall_fin.toFinset
      let a : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ := fun p => ‖divisorZeroIndex₀_val p‖
      (∑ p ∈ small, LogSingularity.φ (r / a p)) ≤ LogSingularity.Cφ * (small.card : ℝ)) :
    let small : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := hsmall_fin.toFinset
    letI : DecidableEq (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := Classical.decEq _
    let ap : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ := fun p => ‖divisorZeroIndex₀_val p‖
    let b : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
      fun p =>
        if p ∈ small then
          LogSingularity.φ (r / ap p) + (m : ℝ) * (1 + (r / ap p) ^ τ)
        else
          (2 : ℝ) * (r / ap p) ^ τ
    let Sτ : ℝ := ∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ
    let Cprod : ℝ := ((LogSingularity.Cφ + (2 : ℝ) * m) * (4 : ℝ) ^ τ + 3) * (Sτ + 1)
    ∀ s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)),
      (∑ p ∈ s, b p) ≤ Cprod * (1 + r) ^ τ := by
  classical
  intro small ap b Sτ Cprod s
  have hr : 0 ≤ r := le_of_lt hrpos
  have hSτ_nonneg : 0 ≤ Sτ :=
    tsum_nonneg (fun _ => Real.rpow_nonneg (inv_nonneg.2 (norm_nonneg _)) _)
  have hsmall_mem : ∀ p, p ∈ small ↔ p ∈ smallSet := by
    intro p
    simp [small, hsmall_fin.mem_toFinset]
  have hphi_sum :
      (∑ p ∈ small, LogSingularity.φ (r / ap p)) ≤ LogSingularity.Cφ * (small.card : ℝ) := by
    simpa [small, ap] using hr_phi
  have hb_nonneg : ∀ p, 0 ≤ b p := by
    simpa [ap, b] using (cartan_majorant_nonneg (f := f) (m := m) (τ := τ) (r := r) hr small)
  have hb_summable : Summable b := by
    simpa [ap, b] using
      (cartan_majorant_summable (f := f) (m := m) (τ := τ) (r := r) hr small hsumτ)
  have hsmall_norm : ∀ p ∈ small, ‖divisorZeroIndex₀_val p‖ ≤ 4 * R := by
    intro p hp
    have : p ∈ smallSet := (hsmall_mem p).1 hp
    simpa [hsmallSet] using this
  have hcard_le : (small.card : ℝ) ≤ (4 * R) ^ τ * (Sτ + 1) := by
    simpa [Sτ, mul_assoc, add_assoc, add_left_comm, add_comm] using
      (cartan_card_small_le (f := f) (τ := τ) (R := R) hRpos hτ_nonneg small hsmall_norm hsumτ)
  have hpowR : (4 * R) ^ τ ≤ (4 : ℝ) ^ τ * (1 + r) ^ τ :=
    cartan_rpow_mul_le (τ := τ) (R := R) (r := r) hRpos hrpos hR_le_r hτ_nonneg
  have hcard_le' : (small.card : ℝ) ≤ (4 : ℝ) ^ τ * (1 + r) ^ τ * (Sτ + 1) := by
    have : (4 * R) ^ τ * (Sτ + 1) ≤ (4 : ℝ) ^ τ * (1 + r) ^ τ * (Sτ + 1) := by
      exact mul_le_mul_of_nonneg_right hpowR (by linarith [hSτ_nonneg])
    exact le_trans hcard_le this
  have hb_tsum_le :
      (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), b p) ≤ Cprod * (1 + r) ^ τ := by
    let bφ : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
      fun p => if p ∈ small then LogSingularity.φ (r / ap p) else 0
    let b0 : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
      fun p => if p ∈ small then (m : ℝ) else 0
    let bmτ : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
      fun p => if p ∈ small then (m : ℝ) * (r / ap p) ^ τ else 0
    let bt : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
      fun p => (2 : ℝ) * (r / ap p) ^ τ
    have hb_pointwise : ∀ p, b p ≤ bφ p + b0 p + bmτ p + bt p := by
      intro p
      by_cases hp : p ∈ small
      · have hbase : 0 ≤ r / ap p := div_nonneg hr (by positivity)
        have hx : 0 ≤ (r / ap p) ^ τ := Real.rpow_nonneg hbase τ
        have hpos : 0 ≤ (2 : ℝ) * (r / ap p) ^ τ := mul_nonneg (by norm_num) hx
        simp [b, bφ, b0, bmτ, bt, hp]
        nlinarith
      · simp [b, bφ, b0, bmτ, bt, hp]
    have hmaj_summ : Summable (fun p => bφ p + b0 p + bmτ p + bt p) := by
      have hbφ_summ : Summable bφ := by
        refine summable_of_finite_support ?_
        refine (Finset.finite_toSet small).subset ?_
        intro p hp
        by_contra hps
        have hps' : p ∉ small := by simpa using hps
        have : bφ p = 0 := by simp [bφ, hps']
        exact hp (by simp [this])
      have hb0_summ : Summable b0 := by
        refine summable_of_finite_support ?_
        refine (Finset.finite_toSet small).subset ?_
        intro p hp
        by_contra hps
        have hps' : p ∉ small := by simpa using hps
        have : b0 p = 0 := by simp [b0, hps']
        exact hp (by simp [this])
      have hbmτ_summ : Summable bmτ := by
        refine summable_of_finite_support ?_
        refine (Finset.finite_toSet small).subset ?_
        intro p hp
        by_contra hps
        have hps' : p ∉ small := by simpa using hps
        have : bmτ p = 0 := by simp [bmτ, hps']
        exact hp (by simp [this])
      have hbt_summ : Summable bt := by
        have hconst : Summable (fun p =>
            (2 : ℝ) * (r ^ τ) * (‖divisorZeroIndex₀_val p‖⁻¹ ^ τ)) :=
          hsumτ.mul_left ((2 : ℝ) * (r ^ τ))
        refine hconst.congr ?_
        intro p
        have hr0 : 0 ≤ r := hr
        have ha0 : 0 ≤ (‖divisorZeroIndex₀_val p‖⁻¹ : ℝ) := by positivity
        simp [bt, ap, div_eq_mul_inv, Real.mul_rpow hr0 ha0, mul_assoc, mul_left_comm, mul_comm]
      have h' : Summable (fun p => bφ p + b0 p + (bmτ p + bt p)) :=
        (hbφ_summ.add hb0_summ).add (hbmτ_summ.add hbt_summ)
      simpa [add_assoc] using h'
    have htsum_le :
        (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), b p)
          ≤ ∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), (bφ p + b0 p + bmτ p + bt p) :=
      (hasSum_le hb_pointwise hb_summable.hasSum hmaj_summ.hasSum)
    have htsum_bφ :
        (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), bφ p)
          = ∑ p ∈ small, LogSingularity.φ (r / ap p) := by
      classical
      simpa [bφ] using
        (tsum_eq_sum (s := small) (f := fun p => bφ p) (by intro p hp; simp [bφ, hp]))
    have htsum_b0 :
        (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), b0 p)
          = (m : ℝ) * (small.card : ℝ) := by
      classical
      have : (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), b0 p) = ∑ p ∈ small, (m : ℝ) := by
        simpa [b0] using
          (tsum_eq_sum (s := small) (f := fun p => b0 p) (by intro p hp; simp [b0, hp]))
      simp [this, Finset.sum_const, nsmul_eq_mul, mul_comm]
    have htsum_bmτ :
        (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), bmτ p)
          = (m : ℝ) * ∑ p ∈ small, (r / ap p) ^ τ := by
      classical
      have :
          (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), bmτ p)
            = ∑ p ∈ small, (m : ℝ) * (r / ap p) ^ τ := by
        simpa [bmτ] using
          (tsum_eq_sum (s := small) (f := fun p => bmτ p) (by intro p hp; simp [bmτ, hp]))
      simp [this, Finset.mul_sum]
    have htsum_bt :
        (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), bt p)
          ≤ (2 : ℝ) * (Sτ + 1) * (1 + r) ^ τ := by
      have hbt_eq :
          (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), bt p) = (2 : ℝ) * (r ^ τ) * Sτ := by
        have hpow :
            ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
              (r / ap p) ^ τ = (r ^ τ) * (‖divisorZeroIndex₀_val p‖⁻¹ : ℝ) ^ τ := by
          intro p
          have ha0 : 0 ≤ (‖divisorZeroIndex₀_val p‖⁻¹ : ℝ) := by positivity
          simpa [ap, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
            (Real.mul_rpow (x := r) (y := (‖divisorZeroIndex₀_val p‖⁻¹ : ℝ)) (z := τ) hr ha0)
        calc
          (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), bt p)
              = (2 : ℝ) * ∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), (r / ap p) ^ τ := by
                simpa [bt, mul_assoc] using
                  (tsum_mul_left (a := (2 : ℝ))
                    (f := fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) => (r / ap p) ^ τ))
          _ = (2 : ℝ) * ∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
                (r ^ τ) * (‖divisorZeroIndex₀_val p‖⁻¹ : ℝ) ^ τ := by
                refine congrArg (fun t => (2 : ℝ) * t) ?_
                refine tsum_congr ?_
                intro p
                simp [hpow p]
          _ = (2 : ℝ) * ((r ^ τ) * ∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
                (‖divisorZeroIndex₀_val p‖⁻¹ : ℝ) ^ τ) := by
                simp [tsum_mul_left]
          _ = (2 : ℝ) * (r ^ τ) * Sτ := by
                simp [Sτ, mul_assoc]
      have h1r : r ^ τ ≤ (1 + r) ^ τ :=
        Real.rpow_le_rpow (by positivity) (by linarith) hτ_nonneg
      have hS : Sτ ≤ Sτ + 1 := by linarith
      have hle : (r ^ τ) * Sτ ≤ (1 + r) ^ τ * (Sτ + 1) :=
        mul_le_mul h1r hS (by linarith) (by positivity)
      have : (2 : ℝ) * (r ^ τ) * Sτ ≤ (2 : ℝ) * (Sτ + 1) * (1 + r) ^ τ := by
        nlinarith [hle]
      exact (le_trans (le_of_eq hbt_eq) this)
    have hsum_small_rpow_le :
        (∑ p ∈ small, (r / ap p) ^ τ) ≤ (Sτ + 1) * (1 + r) ^ τ := by
      have hsum_inv : (∑ p ∈ small, (‖divisorZeroIndex₀_val p‖⁻¹ : ℝ) ^ τ) ≤ Sτ := by
        have hnn :
            ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ), 0 ≤ (‖divisorZeroIndex₀_val p‖⁻¹ : ℝ) ^ τ := by
          intro p; positivity
        simpa [Sτ] using
          (Summable.sum_le_tsum (s := small)
            (f := fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) => (‖divisorZeroIndex₀_val p‖⁻¹ : ℝ) ^ τ)
            (fun p _ => hnn p) hsumτ)
      have hrpow : ∀ p, (r / ap p) ^ τ = (r ^ τ) * (‖divisorZeroIndex₀_val p‖⁻¹ : ℝ) ^ τ := by
        intro p
        have ha0 : 0 ≤ (‖divisorZeroIndex₀_val p‖⁻¹ : ℝ) := by positivity
        simpa [ap, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
          (Real.mul_rpow (x := r) (y := (‖divisorZeroIndex₀_val p‖⁻¹ : ℝ)) (z := τ) hr ha0)
      have : ∑ p ∈ small, (r / ap p) ^ τ = (r ^ τ) * ∑ p ∈ small, (‖divisorZeroIndex₀_val p‖⁻¹ : ℝ) ^ τ := by
        classical
        simp [hrpow, Finset.mul_sum]
      have h1r : r ^ τ ≤ (1 + r) ^ τ :=
        Real.rpow_le_rpow (by positivity) (by linarith) hτ_nonneg
      have hS : (∑ p ∈ small, (‖divisorZeroIndex₀_val p‖⁻¹ : ℝ) ^ τ) ≤ Sτ + 1 := by
        linarith [hsum_inv]
      have hle : (r ^ τ) * (∑ p ∈ small, (‖divisorZeroIndex₀_val p‖⁻¹ : ℝ) ^ τ) ≤
          (1 + r) ^ τ * (Sτ + 1) :=
        mul_le_mul h1r hS (by positivity) (by positivity)
      simpa [this, mul_assoc, mul_left_comm, mul_comm] using hle
    have hm0 : 0 ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
    have hCφ : 0 ≤ LogSingularity.Cφ := le_of_lt LogSingularity.Cφ_pos
    have hS : 0 ≤ Sτ + 1 := by linarith [hSτ_nonneg]
    have htsum_majorant :
        (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), (bφ p + b0 p + bmτ p + bt p))
          ≤ (((LogSingularity.Cφ + (2 : ℝ) * m) * (4 : ℝ) ^ τ + 2) * (Sτ + 1)) * (1 + r) ^ τ := by
      have hφ_le :
          (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), bφ p) ≤ LogSingularity.Cφ * (small.card : ℝ) := by
        simpa [htsum_bφ] using hphi_sum
      have hb0_le :
          (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), b0 p) ≤ (m : ℝ) * (small.card : ℝ) := by
        simp [htsum_b0]
      have hbmτ_le :
          (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), bmτ p) ≤
            (m : ℝ) * (4 : ℝ) ^ τ * (Sτ + 1) * (1 + r) ^ τ := by
        have h0 :
            (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), bmτ p)
              ≤ (m : ℝ) * ((Sτ + 1) * (1 + r) ^ τ) := by
          have hmul := mul_le_mul_of_nonneg_left hsum_small_rpow_le hm0
          -- `hmul : m * (∑_{p∈small} ...) ≤ m * ((Sτ+1) * (1+r)^τ)`
          simpa [htsum_bmτ, mul_assoc, mul_left_comm, mul_comm] using hmul
        have h1 : (1 : ℝ) ≤ (4 : ℝ) ^ τ :=
          Real.one_le_rpow (by norm_num) hτ_nonneg
        have hscale :
            (m : ℝ) * ((Sτ + 1) * (1 + r) ^ τ) ≤ (m : ℝ) * (4 : ℝ) ^ τ * (Sτ + 1) * (1 + r) ^ τ := by
          have hnonneg : 0 ≤ (m : ℝ) * ((Sτ + 1) * (1 + r) ^ τ) := by
            have : 0 ≤ (Sτ + 1) * (1 + r) ^ τ := by positivity
            exact mul_nonneg hm0 this
          simpa [mul_assoc, mul_left_comm, mul_comm] using (mul_le_mul_of_nonneg_right h1 hnonneg)
        exact h0.trans hscale
      have hbt_le :
          (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), bt p) ≤ (2 : ℝ) * (Sτ + 1) * (1 + r) ^ τ := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using htsum_bt
      have hsplit :
          (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), (bφ p + b0 p + bmτ p + bt p))
            = (∑' p, bφ p) + (∑' p, b0 p) + (∑' p, bmτ p) + (∑' p, bt p) := by
        classical
        have hbφ_summ : Summable bφ := by
          refine summable_of_finite_support ?_
          refine (Finset.finite_toSet small).subset ?_
          intro p hp
          by_contra hps
          have hps' : p ∉ small := by simpa using hps
          have : bφ p = 0 := by simp [bφ, hps']
          exact hp (by simp [this])
        have hb0_summ : Summable b0 := by
          refine summable_of_finite_support ?_
          refine (Finset.finite_toSet small).subset ?_
          intro p hp
          by_contra hps
          have hps' : p ∉ small := by simpa using hps
          have : b0 p = 0 := by simp [b0, hps']
          exact hp (by simp [this])
        have hbmτ_summ : Summable bmτ := by
          refine summable_of_finite_support ?_
          refine (Finset.finite_toSet small).subset ?_
          intro p hp
          by_contra hps
          have hps' : p ∉ small := by simpa using hps
          have : bmτ p = 0 := by simp [bmτ, hps']
          exact hp (by simp [this])
        have hbt_summ : Summable bt := by
          have hconst :
              Summable
                (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
                  (2 : ℝ) * (r ^ τ) * ((‖divisorZeroIndex₀_val p‖⁻¹ : ℝ) ^ τ)) :=
            hsumτ.mul_left ((2 : ℝ) * (r ^ τ))
          refine hconst.congr ?_
          intro p
          have ha0 : 0 ≤ (‖divisorZeroIndex₀_val p‖⁻¹ : ℝ) := by positivity
          have hrpow :
              (r / ap p) ^ τ = (r ^ τ) * ((‖divisorZeroIndex₀_val p‖⁻¹ : ℝ) ^ τ) := by
            simpa [ap, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
              (Real.mul_rpow (x := r) (y := (‖divisorZeroIndex₀_val p‖⁻¹ : ℝ)) (z := τ) hr ha0)
          simp [bt, hrpow, mul_assoc, mul_left_comm, mul_comm]
        have hφ0 :
            (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), (bφ p + b0 p))
              = (∑' p, bφ p) + (∑' p, b0 p) :=
          (Summable.tsum_add hbφ_summ hb0_summ)
        have hmτt :
            (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), (bmτ p + bt p))
              = (∑' p, bmτ p) + (∑' p, bt p) :=
          (Summable.tsum_add hbmτ_summ hbt_summ)
        calc
          (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), (bφ p + b0 p + bmτ p + bt p))
              = ∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), ((bφ p + b0 p) + (bmτ p + bt p)) := by
                  simp [add_left_comm, add_comm]
          _ = (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), (bφ p + b0 p))
                + (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), (bmτ p + bt p)) :=
              Summable.tsum_add (hbφ_summ.add hb0_summ) (hbmτ_summ.add hbt_summ)
          _ = ((∑' p, bφ p) + (∑' p, b0 p)) + ((∑' p, bmτ p) + (∑' p, bt p)) := by
              simp [hφ0, hmτt]
          _ = (∑' p, bφ p) + (∑' p, b0 p) + (∑' p, bmτ p) + (∑' p, bt p) := by
              ring
      have hcard_le'' :
          (small.card : ℝ) ≤ (4 : ℝ) ^ τ * (Sτ + 1) * (1 + r) ^ τ := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hcard_le'
      have hφ_le' :
          (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), bφ p) ≤
            LogSingularity.Cφ * (4 : ℝ) ^ τ * (Sτ + 1) * (1 + r) ^ τ := by
        have : LogSingularity.Cφ * (small.card : ℝ) ≤
            LogSingularity.Cφ * ((4 : ℝ) ^ τ * (Sτ + 1) * (1 + r) ^ τ) :=
          mul_le_mul_of_nonneg_left hcard_le'' hCφ
        exact hφ_le.trans (by simpa [mul_assoc, mul_left_comm, mul_comm] using this)
      have hb0_le' :
          (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), b0 p) ≤
            (m : ℝ) * (4 : ℝ) ^ τ * (Sτ + 1) * (1 + r) ^ τ := by
        have : (m : ℝ) * (small.card : ℝ) ≤ (m : ℝ) * ((4 : ℝ) ^ τ * (Sτ + 1) * (1 + r) ^ τ) :=
          mul_le_mul_of_nonneg_left hcard_le'' hm0
        exact hb0_le.trans (by simpa [mul_assoc, mul_left_comm, mul_comm] using this)
      have htsum_majorant' :
          (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), (bφ p + b0 p + bmτ p + bt p))
            ≤ (LogSingularity.Cφ + (2 : ℝ) * m) * (4 : ℝ) ^ τ * (Sτ + 1) * (1 + r) ^ τ
              + (2 : ℝ) * (Sτ + 1) * (1 + r) ^ τ := by
        rw [hsplit]
        set Y : ℝ := Sτ + 1 with hY
        have hφ_leY :
            (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), bφ p)
              ≤ LogSingularity.Cφ * (4 : ℝ) ^ τ * Y * (1 + r) ^ τ := by
          simpa [hY, mul_assoc] using hφ_le'
        have hb0_leY :
            (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), b0 p)
              ≤ (m : ℝ) * (4 : ℝ) ^ τ * Y * (1 + r) ^ τ := by
          simpa [hY, mul_assoc] using hb0_le'
        have hbmτ_leY :
            (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), bmτ p)
              ≤ (m : ℝ) * (4 : ℝ) ^ τ * Y * (1 + r) ^ τ := by
          simpa [hY, mul_assoc] using hbmτ_le
        have h12 :
            (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), bφ p)
              + (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), b0 p)
              ≤ LogSingularity.Cφ * (4 : ℝ) ^ τ * Y * (1 + r) ^ τ
                + (m : ℝ) * (4 : ℝ) ^ τ * Y * (1 + r) ^ τ :=
          add_le_add hφ_leY hb0_leY
        have h123 :
            ((∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), bφ p)
                + (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), b0 p))
              + (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), bmτ p)
              ≤ (LogSingularity.Cφ * (4 : ℝ) ^ τ * Y * (1 + r) ^ τ
                    + (m : ℝ) * (4 : ℝ) ^ τ * Y * (1 + r) ^ τ)
                  + (m : ℝ) * (4 : ℝ) ^ τ * Y * (1 + r) ^ τ :=
          add_le_add h12 hbmτ_leY
        have h123' :
            ((∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), bφ p)
                + (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), b0 p))
              + (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), bmτ p)
              ≤ (LogSingularity.Cφ + (2 : ℝ) * m) * (4 : ℝ) ^ τ * Y * (1 + r) ^ τ := by
          have :
              (LogSingularity.Cφ * (4 : ℝ) ^ τ * Y * (1 + r) ^ τ
                    + (m : ℝ) * (4 : ℝ) ^ τ * Y * (1 + r) ^ τ)
                  + (m : ℝ) * (4 : ℝ) ^ τ * Y * (1 + r) ^ τ
                = (LogSingularity.Cφ + (2 : ℝ) * m) * (4 : ℝ) ^ τ * Y * (1 + r) ^ τ := by
            ring
          simpa [this] using h123
        have h4 :
            (((∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), bφ p)
                  + (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), b0 p))
                + (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), bmτ p))
              + (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), bt p)
              ≤ (LogSingularity.Cφ + (2 : ℝ) * m) * (4 : ℝ) ^ τ * Y * (1 + r) ^ τ
                + (2 : ℝ) * Y * (1 + r) ^ τ := by
          have hbt_leY :
              (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), bt p) ≤ (2 : ℝ) * Y *
                (1 + r) ^ τ := by
            simpa [hY, mul_assoc] using hbt_le
          exact add_le_add h123' hbt_leY
        have h4' := h4
        rw [hY] at h4'
        exact h4'
      have hring :
          (LogSingularity.Cφ + (2 : ℝ) * m) * (4 : ℝ) ^ τ * (Sτ + 1) * (1 + r) ^ τ
              + (2 : ℝ) * (Sτ + 1) * (1 + r) ^ τ
            = (((LogSingularity.Cφ + (2 : ℝ) * m) * (4 : ℝ) ^ τ + 2) * (Sτ + 1)) * (1 + r) ^ τ := by
        ring
      rw [← hring]
      exact htsum_majorant'
    have hCprod' :
        (((LogSingularity.Cφ + (2 : ℝ) * m) * (4 : ℝ) ^ τ + 2) * (Sτ + 1)) * (1 + r) ^ τ
          ≤ Cprod * (1 + r) ^ τ := by
      have hnr' : 0 ≤ (1 + r) ^ τ := by positivity
      have : ((LogSingularity.Cφ + (2 : ℝ) * m) * (4 : ℝ) ^ τ + 2) * (Sτ + 1)
            ≤ ((LogSingularity.Cφ + (2 : ℝ) * m) * (4 : ℝ) ^ τ + 3) * (Sτ + 1) := by
        nlinarith [hS]
      have := mul_le_mul_of_nonneg_right this hnr'
      simpa [Cprod, mul_assoc, mul_left_comm, mul_comm] using this
    exact (le_trans (le_trans htsum_le htsum_majorant) hCprod')
  have hsum_fin_le :
      (∑ p ∈ s, b p) ≤ (∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), b p) := by
    simpa using
      (Summable.sum_le_tsum (s := s) (f := b) (fun p _ => hb_nonneg p) hb_summable)
  exact hsum_fin_le.trans hb_tsum_le

end Complex.Hadamard
