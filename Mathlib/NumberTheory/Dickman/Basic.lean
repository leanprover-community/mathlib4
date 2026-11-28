/-
Copyright (c) 2026 Krishnan Adaikkappan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krishnan Adaikkappan
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The Dickman function: definition and basic properties

The Dickman function `ρ : ℝ → ℝ` is the continuous solution of the delay-differential equation
`u ρ'(u) = -ρ(u - 1)` for `u > 1`, with `ρ = 1` on `[0, 1]`. Dickman introduced it in 1930
(K. Dickman, *Ark. Mat. Astr. Fys.* 22A, no. 10, pp. 1–14, 1930) as the limiting density of
`y`-smooth integers. It is studied in detail by de Bruijn (N. G. de Bruijn, *Indag. Math.* 13,
1951, pp. 50–60) and in Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*,
3rd edition, Chapter III.5.

The definition is stepwise. `dickmanPiece k` agrees with `ρ` on `[0, k]` for `k ≥ 1`, and
`dickmanRho u` uses the piece at `⌊u⌋₊ + 1`. On each unit interval `[n, n + 1]` with `n ≥ 1`,
`ρ` satisfies the integral equation `ρ u = ρ n - ∫ₙᵘ ρ (t - 1) / t dt`.

## Main definitions

* `Real.dickmanRho`: the Dickman function.

## Main results

* `Real.dickmanRho_of_le_one`: `ρ u = 1` for `u ≤ 1`.
* `Real.dickmanRho_of_mem_Ioc_one_two`: `ρ u = 1 - log u` for `1 < u ≤ 2`.
* `Real.dickmanRho_integral_eq`: the integral equation on `[n, n + 1]`.
* `Real.dickmanRho_continuous`: `ρ` is continuous.
* `Real.hasDerivAt_dickmanRho`: the derivative of `ρ` off the integers.
* `Real.mul_dickmanRho_eq_integral`: `u ρ u = ∫_{u-1}^{u} ρ` for `u ≥ 1`.
* `Real.dickmanRho_pos`: `ρ` is positive.
* `Real.dickmanRho_antitoneOn_Ici_one`: `ρ` is antitone on `[1, ∞)`.
* `Real.dickmanRho_le_one`: `ρ u ≤ 1`.

The decay bound and the integral `∫₀^∞ ρ = exp γ` are left to a follow-up file.
-/

public section

open Set intervalIntegral MeasureTheory Filter Topology

namespace Real


/-- The pieces of the Dickman function: `dickmanPiece k` agrees with `dickmanRho` on `[0, k]`
for `k ≥ 1`. -/
noncomputable def dickmanPiece : ℕ → ℝ → ℝ
  | 0 => fun _ => 1
  | 1 => fun _ => 1
  | k + 2 => fun u =>
    if u ≤ ((k + 1 : ℕ) : ℝ) then dickmanPiece (k + 1) u
    else dickmanPiece (k + 1) ((k + 1 : ℕ) : ℝ) -
      ∫ t in ((k + 1 : ℕ) : ℝ)..u, dickmanPiece (k + 1) (t - 1) / t

/-- The Dickman function `ρ`. -/
noncomputable def dickmanRho (u : ℝ) : ℝ := dickmanPiece (⌊u⌋₊ + 1) u

private lemma dickmanPiece_of_le_one (m : ℕ) {u : ℝ} (hu : u ≤ 1) : dickmanPiece m u = 1 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m, ih with
    | 0, _ => simp [dickmanPiece]
    | 1, _ => simp [dickmanPiece]
    | k + 2, ih =>
      simp only [dickmanPiece]
      have hc : u ≤ ((k + 1 : ℕ) : ℝ) := by
        push_cast; have := (k.cast_nonneg : (0 : ℝ) ≤ k); linarith
      simp only [hc, ↓reduceIte]
      exact ih (k + 1) (by omega)

private lemma dickmanPiece_succ_of_le {k : ℕ} (hk : 1 ≤ k) {u : ℝ} (hu : u ≤ k) :
    dickmanPiece (k + 1) u = dickmanPiece k u := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [show j + 1 + 1 = j + 2 from rfl]
  simp only [dickmanPiece]
  have hc : u ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast hu
  simp only [hc, ↓reduceIte]

private lemma dickmanPiece_eq_of_le {k m : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) {u : ℝ} (hu : u ≤ k) :
    dickmanPiece m u = dickmanPiece k u := by
  induction m, hkm using Nat.le_induction with
  | base => rfl
  | succ m hkm ih =>
    rw [dickmanPiece_succ_of_le (by omega) (hu.trans (by exact_mod_cast hkm)), ih]

private lemma dickmanRho_eq_dickmanPiece {m : ℕ} (hm : 1 ≤ m) {u : ℝ} (hu : u ≤ m) :
    dickmanRho u = dickmanPiece m u := by
  unfold dickmanRho
  rcases le_or_gt (⌊u⌋₊ + 1) m with h | h
  · have hu' : u ≤ ((⌊u⌋₊ + 1 : ℕ) : ℝ) := by
      push_cast; exact (Nat.lt_floor_add_one u).le
    exact (dickmanPiece_eq_of_le (by omega) h hu').symm
  · have hu0 : (0 : ℝ) ≤ u := by
      by_contra hneg
      rw [not_le] at hneg
      have : ⌊u⌋₊ = 0 := Nat.floor_of_nonpos hneg.le
      omega
    have hfl : ⌊u⌋₊ = m := by
      apply le_antisymm
      · exact_mod_cast ((Nat.floor_le hu0).trans hu)
      · omega
    rw [hfl]
    exact dickmanPiece_succ_of_le hm hu

/-- The Dickman function is `1` on `[0, 1]`. -/
theorem dickmanRho_of_le_one {u : ℝ} (hu : u ≤ 1) : dickmanRho u = 1 := by
  unfold dickmanRho
  exact dickmanPiece_of_le_one _ hu

/-- The Dickman function is `1 - log u` on `(1, 2]`. -/
theorem dickmanRho_of_mem_Ioc_one_two {u : ℝ} (h1 : 1 < u) (h2 : u ≤ 2) :
    dickmanRho u = 1 - Real.log u := by
  rw [dickmanRho_eq_dickmanPiece (m := 2) (by norm_num) (by norm_num; exact h2)]
  have hP1 : ∀ x : ℝ, dickmanPiece 1 x = 1 := fun x => by simp [dickmanPiece]
  have hnot : ¬ u ≤ ((0 + 1 : ℕ) : ℝ) := not_le.mpr (by norm_num; exact h1)
  change (if u ≤ ((0 + 1 : ℕ) : ℝ) then dickmanPiece (0 + 1) u else
      dickmanPiece (0 + 1) ((0 + 1 : ℕ) : ℝ) -
        ∫ t in ((0 + 1 : ℕ) : ℝ)..u, dickmanPiece (0 + 1) (t - 1) / t) = 1 - Real.log u
  simp only [hnot, ↓reduceIte, hP1]
  rw [show ((0 + 1 : ℕ) : ℝ) = 1 by norm_num, integral_one_div_of_pos one_pos (by linarith),
    div_one]

/-- The integral equation `ρ u = ρ n - ∫ₙᵘ ρ (t - 1) / t dt` on `[n, n + 1]` for `n ≥ 1`. -/
theorem dickmanRho_integral_eq {n : ℕ} (hn : 1 ≤ n) {u : ℝ} (hu1 : (n : ℝ) ≤ u)
    (hu2 : u ≤ (n : ℝ) + 1) :
    dickmanRho u = dickmanRho n - ∫ t in (n : ℝ)..u, dickmanRho (t - 1) / t := by
  rcases eq_or_lt_of_le hu1 with h | h
  · rw [← h]; simp
  · have hu : u ≤ ((n + 1 : ℕ) : ℝ) := by push_cast; exact hu2
    rw [dickmanRho_eq_dickmanPiece (by omega) hu,
      dickmanRho_eq_dickmanPiece hn (le_refl (n : ℝ))]
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    rw [show j + 1 + 1 = j + 2 from rfl]
    simp only [dickmanPiece]
    simp only [not_le.mpr h, ↓reduceIte]
    congr 1
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le h.le] at ht
    rw [dickmanRho_eq_dickmanPiece (m := j + 1) (by omega)
      (by push_cast at hu2 ⊢; linarith [ht.2])]

private lemma dickmanPiece_succ_succ (k : ℕ) (u : ℝ) :
    dickmanPiece (k + 1 + 1) u = if u ≤ ((k + 1 : ℕ) : ℝ) then dickmanPiece (k + 1) u else
      dickmanPiece (k + 1) ((k + 1 : ℕ) : ℝ) -
        ∫ t in ((k + 1 : ℕ) : ℝ)..u, dickmanPiece (k + 1) (t - 1) / t := by
  rw [dickmanPiece]

private lemma continuousOn_dickmanPiece (k : ℕ) :
    ContinuousOn (dickmanPiece (k + 1)) (Iic ((k + 1 : ℕ) : ℝ)) := by
  induction k with
  | zero =>
    have h1 : dickmanPiece 1 = fun _ => 1 := by
      funext x; simp [dickmanPiece]
    rw [h1]
    exact continuousOn_const
  | succ k ih =>
    have hab : ((k + 1 : ℕ) : ℝ) ≤ ((k + 1 + 1 : ℕ) : ℝ) := by
      push_cast; linarith
    have hA : ContinuousOn (dickmanPiece (k + 1 + 1)) (Iic ((k + 1 : ℕ) : ℝ)) := by
      refine ih.congr ?_
      intro u hu
      have hle : u ≤ ((k + 1 : ℕ) : ℝ) := hu
      simp only [dickmanPiece_succ_succ, hle, ↓reduceIte]
    have hF : ContinuousOn (fun t : ℝ => dickmanPiece (k + 1) (t - 1) / t)
        (uIcc ((k + 1 : ℕ) : ℝ) ((k + 1 + 1 : ℕ) : ℝ)) := by
      rw [uIcc_of_le hab]
      apply ContinuousOn.div
      · apply ih.comp (continuousOn_id.sub continuousOn_const)
        intro t ht
        have h2 : t ≤ ((k + 1 + 1 : ℕ) : ℝ) := ht.2
        have h3 : ((k + 1 + 1 : ℕ) : ℝ) = ((k + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
        change t - 1 ≤ ((k + 1 : ℕ) : ℝ)
        linarith
      · exact continuousOn_id
      · intro t ht
        have h1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
        have h4 : (1 : ℝ) ≤ t := by linarith [ht.1]
        exact (by linarith : (0 : ℝ) < t).ne'
    have hB : ContinuousOn (dickmanPiece (k + 1 + 1))
        (uIcc ((k + 1 : ℕ) : ℝ) ((k + 1 + 1 : ℕ) : ℝ)) := by
      have hint : MeasureTheory.IntegrableOn (fun t : ℝ => dickmanPiece (k + 1) (t - 1) / t)
          (uIcc ((k + 1 : ℕ) : ℝ) ((k + 1 + 1 : ℕ) : ℝ)) :=
        hF.integrableOn_compact isCompact_uIcc
      have hG : ContinuousOn (fun u : ℝ => dickmanPiece (k + 1) ((k + 1 : ℕ) : ℝ) -
          ∫ t in ((k + 1 : ℕ) : ℝ)..u, dickmanPiece (k + 1) (t - 1) / t)
          (uIcc ((k + 1 : ℕ) : ℝ) ((k + 1 + 1 : ℕ) : ℝ)) :=
        continuousOn_const.sub (intervalIntegral.continuousOn_primitive_interval hint)
      refine hG.congr ?_
      intro u hu
      rw [uIcc_of_le hab] at hu
      rcases eq_or_lt_of_le hu.1 with h | h
      · rw [← h]
        simp only [dickmanPiece_succ_succ, le_rfl, ↓reduceIte, intervalIntegral.integral_same,
          sub_zero]
      · have hnle : ¬ u ≤ ((k + 1 : ℕ) : ℝ) := not_le.mpr h
        simp only [dickmanPiece_succ_succ, hnle, ↓reduceIte]
    have hcov : Set.Iic ((k + 1 + 1 : ℕ) : ℝ) = Set.Iic ((k + 1 : ℕ) : ℝ) ∪
        uIcc ((k + 1 : ℕ) : ℝ) ((k + 1 + 1 : ℕ) : ℝ) := by
      rw [uIcc_of_le hab, Set.Iic_union_Icc_eq_Iic hab]
    rw [hcov]
    exact ContinuousOn.union_of_isClosed hA hB isClosed_Iic
      (by rw [uIcc_of_le hab]; exact isClosed_Icc)

/-- The Dickman function is continuous on `ℝ`. -/
theorem dickmanRho_continuous : Continuous dickmanRho := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  obtain ⟨n, hn⟩ := exists_nat_gt x
  have hpiece : ContinuousOn dickmanRho (Iic ((n + 1 : ℕ) : ℝ)) := by
    refine (continuousOn_dickmanPiece n).congr ?_
    intro u hu
    exact dickmanRho_eq_dickmanPiece (m := n + 1) (by omega) hu
  refine hpiece.continuousAt (Iic_mem_nhds ?_)
  push_cast
  linarith

/-- The kernel `ρ(t - 1) / t` is continuous on `[1, ∞)`. -/
private lemma continuousOn_kernel : ContinuousOn (fun t : ℝ => dickmanRho (t - 1) / t) (Ici 1) := by
  apply ContinuousOn.div
    (dickmanRho_continuous.comp (continuous_id.sub continuous_const)).continuousOn
    continuousOn_id
  intro t ht
  exact (by linarith [(show (1 : ℝ) ≤ t from ht)] : (0 : ℝ) < t).ne'

private lemma intervalIntegrable_kernel {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    IntervalIntegrable (fun t : ℝ => dickmanRho (t - 1) / t) MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  have hsub : uIcc a b ⊆ Ici 1 := by
    intro x hx
    rcases Set.mem_uIcc.mp hx with h | h
    · exact le_trans ha h.1
    · exact le_trans hb h.1
  exact continuousOn_kernel.mono hsub

/-- The integral equation from `1`: `ρ u = 1 - ∫₁ᵘ ρ(t - 1) / t dt` for `u ∈ [1, n]`. -/
private lemma dickmanRho_eq_one_sub_integral_aux (n : ℕ) (hn : 1 ≤ n) :
    ∀ u ∈ Icc (1 : ℝ) n, dickmanRho u = 1 - ∫ t in (1 : ℝ)..u, dickmanRho (t - 1) / t := by
  induction n, hn using Nat.le_induction with
  | base =>
    intro u hu
    have hu1 : u = 1 := le_antisymm (by simpa using hu.2) hu.1
    rw [hu1, intervalIntegral.integral_same, sub_zero, dickmanRho_of_le_one le_rfl]
  | succ n hn ih =>
    intro u hu
    rcases le_or_gt u n with hun | hun
    · exact ih u ⟨hu.1, hun⟩
    · have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hu2 : u ≤ (n : ℝ) + 1 := by push_cast at hu; exact hu.2
      have hu1 : (1 : ℝ) ≤ u := hu.1
      have h1 := intervalIntegrable_kernel (le_refl (1 : ℝ)) hnR
      have h2 := intervalIntegrable_kernel hnR hu1
      rw [dickmanRho_integral_eq hn hun.le hu2, ih n ⟨hnR, le_rfl⟩,
        ← intervalIntegral.integral_add_adjacent_intervals h1 h2]
      ring

/-- The integral equation `ρ u = 1 - ∫₁ᵘ ρ(t - 1) / t dt` holds for all `u ≥ 1`. -/
theorem dickmanRho_eq_one_sub_integral {u : ℝ} (hu : 1 ≤ u) :
    dickmanRho u = 1 - ∫ t in (1 : ℝ)..u, dickmanRho (t - 1) / t := by
  obtain ⟨n, hn⟩ := exists_nat_gt u
  exact dickmanRho_eq_one_sub_integral_aux (n + 1) (by omega) u
    ⟨hu, by push_cast; linarith⟩

/-- The Dickman function has derivative `-ρ(u - 1) / u` at every `u > 1`. -/
theorem hasDerivAt_dickmanRho {u : ℝ} (hu : 1 < u) :
    HasDerivAt dickmanRho (-(dickmanRho (u - 1) / u)) u := by
  have hK : ContinuousOn (fun t : ℝ => dickmanRho (t - 1) / t) (Ioi 1) :=
    continuousOn_kernel.mono Ioi_subset_Ici_self
  have hint : HasDerivAt (fun x : ℝ => ∫ t in (1 : ℝ)..x, dickmanRho (t - 1) / t)
      (dickmanRho (u - 1) / u) u := by
    apply intervalIntegral.integral_hasDerivAt_right
    · exact (intervalIntegrable_kernel (le_refl (1 : ℝ)) hu.le)
    · exact hK.stronglyMeasurableAtFilter isOpen_Ioi u hu
    · exact hK.continuousAt (Ioi_mem_nhds hu)
  have hloc : dickmanRho =ᶠ[nhds u] fun x => 1 - ∫ t in (1 : ℝ)..x, dickmanRho (t - 1) / t := by
    filter_upwards [Ioi_mem_nhds hu] with x hx
    exact dickmanRho_eq_one_sub_integral (le_of_lt hx)
  exact (hint.const_sub 1).congr_of_eventuallyEq hloc |>.congr_deriv (by ring)

/-- `∫₀¹ ρ = 1`, since `ρ = 1` on `[0, 1]`. -/
private lemma integral_dickmanRho_zero_one : ∫ t in (0 : ℝ)..1, dickmanRho t = 1 := by
  rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ))]
  · simp
  · intro x hx
    rw [Set.uIcc_of_le zero_le_one] at hx
    exact dickmanRho_of_le_one hx.2

/-- The primitive `x ↦ ∫₀ˣ ρ` is differentiable with derivative `ρ`. -/
private lemma hasDerivAt_primitive_dickmanRho (x : ℝ) :
    HasDerivAt (fun y : ℝ => ∫ t in (0 : ℝ)..y, dickmanRho t) (dickmanRho x) x :=
  (dickmanRho_continuous.integral_hasStrictDerivAt 0 x).hasDerivAt

/-- The identity `u ρ(u) = ∫_{u-1}^{u} ρ` for `u ≥ 1`. -/
theorem mul_dickmanRho_eq_integral {u : ℝ} (hu : 1 ≤ u) :
    u * dickmanRho u = ∫ t in (u - 1)..u, dickmanRho t := by
  set H : ℝ → ℝ := fun x => x * dickmanRho x -
    ((∫ t in (0 : ℝ)..x, dickmanRho t) - ∫ t in (0 : ℝ)..(x - 1), dickmanRho t) with hHdef
  have hHcont : Continuous H := by
    have hG : Continuous fun x : ℝ => ∫ t in (0 : ℝ)..x, dickmanRho t :=
      continuous_primitive (fun a b => dickmanRho_continuous.intervalIntegrable a b) 0
    have hG' : Continuous fun x : ℝ => ∫ t in (0 : ℝ)..(x - 1), dickmanRho t :=
      hG.comp (continuous_id.sub continuous_const)
    exact (continuous_id.mul dickmanRho_continuous).sub (hG.sub hG')
  have hderiv : ∀ x ∈ Ioi (1 : ℝ), HasDerivAt H 0 x := by
    intro x hx
    have hx1 : (1 : ℝ) < x := hx
    have hx0 : x ≠ 0 := by linarith
    have hA : HasDerivAt (fun y : ℝ => y * dickmanRho y)
        (1 * dickmanRho x + x * (-(dickmanRho (x - 1) / x))) x :=
      (hasDerivAt_id x).mul (hasDerivAt_dickmanRho hx1)
    have hB := hasDerivAt_primitive_dickmanRho x
    have hC : HasDerivAt (fun y : ℝ => ∫ t in (0 : ℝ)..(y - 1), dickmanRho t)
        (dickmanRho (x - 1)) x := by
      have := (hasDerivAt_primitive_dickmanRho (x - 1)).comp_sub_const x 1
      simpa using this
    have := hA.sub (hB.sub hC)
    convert this using 1
    field_simp
    ring
  have hconst : ∀ c ∈ Ioo (1 : ℝ) u, H c = H u := by
    intro c hc
    have hsub : Icc c u ⊆ Ioi 1 := fun y hy => lt_of_lt_of_le hc.1 hy.1
    have key := constant_of_has_deriv_right_zero (f := H) (a := c) (b := u)
      hHcont.continuousOn
      (fun y hy => (hderiv y (hsub (Ico_subset_Icc_self hy))).hasDerivWithinAt)
    exact (key u ⟨le_of_lt hc.2, le_rfl⟩).symm
  have hu' : H u = 0 := by
    rcases eq_or_lt_of_le hu with h1 | h1
    · have hH1 : H 1 = 0 := by
        simp only [hHdef, dickmanRho_of_le_one (le_refl (1 : ℝ)), sub_self, one_mul,
          intervalIntegral.integral_same, sub_zero, integral_dickmanRho_zero_one]
      rw [← h1] at *
      exact hH1
    · have hclosed : IsClosed {c : ℝ | H c = H u} := isClosed_eq hHcont continuous_const
      have hsubset : Ioo (1 : ℝ) u ⊆ {c : ℝ | H c = H u} := fun c hc => hconst c hc
      have h1mem : (1 : ℝ) ∈ {c : ℝ | H c = H u} := by
        have hcl := closure_minimal hsubset hclosed
        rw [closure_Ioo (ne_of_lt h1)] at hcl
        exact hcl ⟨le_rfl, hu⟩
      have hH1 : H 1 = 0 := by
        simp only [hHdef, dickmanRho_of_le_one (le_refl (1 : ℝ)), sub_self, one_mul,
          intervalIntegral.integral_same, sub_zero, integral_dickmanRho_zero_one]
      have hm : H 1 = H u := h1mem
      linarith
  have hsplit : ∫ t in (u - 1)..u, dickmanRho t =
      (∫ t in (0 : ℝ)..u, dickmanRho t) - ∫ t in (0 : ℝ)..(u - 1), dickmanRho t :=
    (intervalIntegral.integral_interval_sub_left
      (dickmanRho_continuous.intervalIntegrable _ _)
      (dickmanRho_continuous.intervalIntegrable _ _)).symm
  have := hu'
  simp only [hHdef] at this
  rw [hsplit]
  linarith

/-- The Dickman function is positive everywhere. -/
theorem dickmanRho_pos (u : ℝ) : 0 < dickmanRho u := by
  by_cases hu1 : u ≤ 1
  · rw [dickmanRho_of_le_one hu1]; exact one_pos
  by_contra hneg
  have hu : 1 < u := not_le.mp hu1
  have hZc : IsClosed (Ici (1 : ℝ) ∩ {x | dickmanRho x ≤ 0}) :=
    isClosed_Ici.inter (isClosed_le dickmanRho_continuous continuous_const)
  have hZne : (Ici (1 : ℝ) ∩ {x | dickmanRho x ≤ 0}).Nonempty :=
    ⟨u, le_of_lt hu, not_lt.mp hneg⟩
  have hBdd : BddBelow (Ici (1 : ℝ) ∩ {x | dickmanRho x ≤ 0}) :=
    ⟨1, fun x hx => hx.1⟩
  set a := sInf (Ici (1 : ℝ) ∩ {x | dickmanRho x ≤ 0}) with ha_def
  have hamem : a ∈ Ici (1 : ℝ) ∩ {x | dickmanRho x ≤ 0} := hZc.csInf_mem hZne hBdd
  have ha1 : (1 : ℝ) ≤ a := hamem.1
  have ha0 : dickmanRho a ≤ 0 := hamem.2
  have hpos : ∀ x ∈ Ioo (a - 1) a, 0 < dickmanRho x := by
    intro x hx
    by_cases hx1 : x ≤ 1
    · rw [dickmanRho_of_le_one hx1]; exact one_pos
    · have h1x : (1 : ℝ) ≤ x := le_of_lt (not_le.mp hx1)
      have hnot : x ∉ Ici (1 : ℝ) ∩ {x | dickmanRho x ≤ 0} :=
        notMem_of_lt_csInf hx.2 hBdd
      exact not_le.mp (fun h => hnot ⟨h1x, h⟩)
  have hint : 0 < ∫ t in (a - 1)..a, dickmanRho t :=
    intervalIntegral.intervalIntegral_pos_of_pos_on
      (dickmanRho_continuous.intervalIntegrable _ _) hpos (by linarith)
  have hid := mul_dickmanRho_eq_integral ha1
  have hneg' : a * dickmanRho a ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) ha0
  linarith

/-- The Dickman function is antitone on `[1, ∞)`. -/
theorem dickmanRho_antitoneOn_Ici_one : AntitoneOn dickmanRho (Ici (1 : ℝ)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 1) dickmanRho_continuous.continuousOn
  · intro x hx
    have hx1 : (1 : ℝ) < x := by
      rw [interior_Ici] at hx; exact hx
    exact (hasDerivAt_dickmanRho hx1).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hx1 : (1 : ℝ) < x := hx
    rw [(hasDerivAt_dickmanRho hx1).deriv]
    have hpos := dickmanRho_pos (x - 1)
    have hx0 : (0 : ℝ) ≤ x := by linarith
    have : 0 ≤ dickmanRho (x - 1) / x := div_nonneg hpos.le hx0
    linarith

/-- The Dickman function is at most `1`. -/
theorem dickmanRho_le_one (u : ℝ) : dickmanRho u ≤ 1 := by
  by_cases hu : u ≤ 1
  · rw [dickmanRho_of_le_one hu]
  · have h := dickmanRho_antitoneOn_Ici_one (a := 1) (b := u) (le_refl 1)
      (show (1 : ℝ) ≤ u by linarith [not_le.mp hu]) (le_of_lt (not_le.mp hu))
    rw [dickmanRho_of_le_one (le_refl (1 : ℝ))] at h
    exact h

end Real

end
