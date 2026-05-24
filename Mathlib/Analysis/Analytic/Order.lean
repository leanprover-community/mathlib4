/-
Copyright (c) 2022 Vincent Beffara. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Beffara, Stefan Kebekus
-/
module

public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Vanishing Order of Analytic Functions

This file defines the order of vanishing of an analytic function `f` at a point `z₀`, as an element
of `ℕ∞`.

## TODO

Uniformize API between analytic and meromorphic functions
-/

@[expose] public section

open Filter Set
open scoped Topology

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormMetric E] [AddCommGroup E] [IsNormedAddGroup E] [NormedSpace 𝕜 E]

/-!
## Vanishing Order at a Point: Definition and Characterization
-/

section NormedSpace
variable {f g : 𝕜 → E} {n : ℕ} {z₀ : 𝕜}

open scoped Classical in
/-- The order of vanishing of `f` at `z₀`, as an element of `ℕ∞`.

The order is defined to be `∞` if `f` is identically 0 on a neighbourhood of `z₀`, and otherwise the
unique `n` such that `f` can locally be written as `f z = (z - z₀) ^ n • g z`, where `g` is analytic
and does not vanish at `z₀`. See `AnalyticAt.analyticOrderAt_eq_top` and
`AnalyticAt.analyticOrderAt_eq_natCast` for these equivalences.

If `f` isn't analytic at `z₀`, then `analyticOrderAt f z₀` returns a junk value of `0`. -/
noncomputable def analyticOrderAt (f : 𝕜 → E) (z₀ : 𝕜) : ℕ∞ :=
  if hf : AnalyticAt 𝕜 f z₀ then
    if h : ∀ᶠ z in 𝓝 z₀, f z = 0 then ⊤
    else ↑(hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr h).choose
  else 0

/-- The order of vanishing of `f` at `z₀`, as an element of `ℕ`.

The order is defined to be `0` if `f` is identically zero on a neighbourhood of `z₀`,
and is otherwise the unique `n` such that `f` can locally be written as `f z = (z - z₀) ^ n • g z`,
where `g` is analytic and does not vanish at `z₀`. See `AnalyticAt.analyticOrderAt_eq_top` and
`AnalyticAt.analyticOrderAt_eq_natCast` for these equivalences.

If `f` isn't analytic at `z₀`, then `analyticOrderNatAt f z₀` returns a junk value of `0`. -/
noncomputable def analyticOrderNatAt (f : 𝕜 → E) (z₀ : 𝕜) : ℕ := (analyticOrderAt f z₀).toNat

@[simp]
lemma analyticOrderAt_of_not_analyticAt (hf : ¬ AnalyticAt 𝕜 f z₀) : analyticOrderAt f z₀ = 0 :=
  dif_neg hf

@[simp]
lemma analyticOrderNatAt_of_not_analyticAt (hf : ¬ AnalyticAt 𝕜 f z₀) :
    analyticOrderNatAt f z₀ = 0 := by simp [analyticOrderNatAt, hf]

@[simp] lemma Nat.cast_analyticOrderNatAt (hf : analyticOrderAt f z₀ ≠ ⊤) :
    analyticOrderNatAt f z₀ = analyticOrderAt f z₀ := ENat.coe_toNat hf

/-- The order of a function `f` at a `z₀` is infinity iff `f` vanishes locally around `z₀`. -/
lemma analyticOrderAt_eq_top : analyticOrderAt f z₀ = ⊤ ↔ ∀ᶠ z in 𝓝 z₀, f z = 0 where
  mp hf := by unfold analyticOrderAt at hf; split_ifs at hf with h <;> simp [*] at *
  mpr hf := by unfold analyticOrderAt; simp [hf, analyticAt_congr hf, analyticAt_const]

lemma eventuallyConst_iff_analyticOrderAt_sub_eq_top :
    EventuallyConst f (𝓝 z₀) ↔ analyticOrderAt (f · - f z₀) z₀ = ⊤ := by
  simpa [eventuallyConst_iff_exists_eventuallyEq, analyticOrderAt_eq_top, sub_eq_zero]
    using ⟨fun ⟨c, hc⟩ ↦ (show f z₀ = c from hc.self_of_nhds) ▸ hc, fun h ↦ ⟨_, h⟩⟩

/-- The order of an analytic function `f` at `z₀` equals a natural number `n` iff `f` can locally
be written as `f z = (z - z₀) ^ n • g z`, where `g` is analytic and does not vanish at `z₀`. -/
lemma AnalyticAt.analyticOrderAt_eq_natCast (hf : AnalyticAt 𝕜 f z₀) :
    analyticOrderAt f z₀ = n ↔
      ∃ (g : 𝕜 → E), AnalyticAt 𝕜 g z₀ ∧ g z₀ ≠ 0 ∧ ∀ᶠ z in 𝓝 z₀, f z = (z - z₀) ^ n • g z := by
  unfold analyticOrderAt
  -- bug with split_ifs and Jovan's bundled classes
  split_ifs with h' h
  · simp only [ENat.top_ne_coe, false_iff]
    contrapose h
    rw [← hf.exists_eventuallyEq_pow_smul_nonzero_iff]
    exact ⟨n, h⟩
  · rw [← hf.exists_eventuallyEq_pow_smul_nonzero_iff] at h
    refine ⟨fun hn ↦ (WithTop.coe_inj.mp hn : h.choose = n) ▸ h.choose_spec, fun h' ↦ ?_⟩
    rw [AnalyticAt.unique_eventuallyEq_pow_smul_nonzero h.choose_spec h']
  · exact absurd hf h'
  · exact absurd hf h'

/-- The order of an analytic function `f` at `z₀` equals a natural number `n` iff `f` can locally
be written as `f z = (z - z₀) ^ n • g z`, where `g` is analytic and does not vanish at `z₀`. -/
lemma AnalyticAt.analyticOrderNatAt_eq_iff (hf : AnalyticAt 𝕜 f z₀) (hf' : analyticOrderAt f z₀ ≠ ⊤)
    {n : ℕ} :
    analyticOrderNatAt f z₀ = n ↔
      ∃ (g : 𝕜 → E), AnalyticAt 𝕜 g z₀ ∧ g z₀ ≠ 0 ∧ ∀ᶠ z in 𝓝 z₀, f z = (z - z₀) ^ n • g z := by
  simp [← Nat.cast_inj (R := ℕ∞), Nat.cast_analyticOrderNatAt hf', hf.analyticOrderAt_eq_natCast]

/-- The order of an analytic function `f` at `z₀` is finite iff `f` can locally be written as `f z =
  (z - z₀) ^ analyticOrderNatAt f z₀ • g z`, where `g` is analytic and does not vanish at `z₀`.

See `MeromorphicNFAt.order_eq_zero_iff` for an analogous statement about meromorphic functions in
normal form.
-/
lemma AnalyticAt.analyticOrderAt_ne_top (hf : AnalyticAt 𝕜 f z₀) :
    analyticOrderAt f z₀ ≠ ⊤ ↔
      ∃ (g : 𝕜 → E), AnalyticAt 𝕜 g z₀ ∧ g z₀ ≠ 0 ∧
        f =ᶠ[𝓝 z₀] fun z ↦ (z - z₀) ^ analyticOrderNatAt f z₀ • g z := by
  simp only [← ENat.coe_toNat_eq_self, Eq.comm, EventuallyEq, ← hf.analyticOrderAt_eq_natCast,
    analyticOrderNatAt]

lemma analyticOrderAt_eq_zero : analyticOrderAt f z₀ = 0 ↔ ¬ AnalyticAt 𝕜 f z₀ ∨ f z₀ ≠ 0 := by
  by_cases hf : AnalyticAt 𝕜 f z₀
  · rw [← ENat.coe_zero, hf.analyticOrderAt_eq_natCast]
    constructor
    · intro ⟨g, _, _, hg⟩
      simpa [hf, hg.self_of_nhds]
    · exact fun hz ↦ ⟨f, hf, hz.resolve_left <| not_not_intro hf, by simp⟩
  · simp [hf]

lemma analyticOrderAt_ne_zero : analyticOrderAt f z₀ ≠ 0 ↔ AnalyticAt 𝕜 f z₀ ∧ f z₀ = 0 := by
  simp [analyticOrderAt_eq_zero]

/-- The order of an analytic function `f` at `z₀` is zero iff `f` does not vanish at `z₀`. -/
protected lemma AnalyticAt.analyticOrderAt_eq_zero (hf : AnalyticAt 𝕜 f z₀) :
    analyticOrderAt f z₀ = 0 ↔ f z₀ ≠ 0 := by simp [hf, analyticOrderAt_eq_zero]

/-- The order of an analytic function `f` at `z₀` is zero iff `f` does not vanish at `z₀`. -/
protected lemma AnalyticAt.analyticOrderAt_ne_zero (hf : AnalyticAt 𝕜 f z₀) :
    analyticOrderAt f z₀ ≠ 0 ↔ f z₀ = 0 := hf.analyticOrderAt_eq_zero.not_left

/-- A function vanishes at a point if its analytic order is nonzero in `ℕ∞`. -/
lemma apply_eq_zero_of_analyticOrderAt_ne_zero (hf : analyticOrderAt f z₀ ≠ 0) :
    f z₀ = 0 := by
  by_cases hf' : AnalyticAt 𝕜 f z₀ <;> simp_all [analyticOrderAt_eq_zero]

/-- A function vanishes at a point if its analytic order is nonzero when converted to ℕ. -/
lemma apply_eq_zero_of_analyticOrderNatAt_ne_zero (hf : analyticOrderNatAt f z₀ ≠ 0) :
    f z₀ = 0 := by
  by_cases hf' : AnalyticAt 𝕜 f z₀ <;> simp_all [analyticOrderNatAt, analyticOrderAt_eq_zero]

/-- Characterization of which natural numbers are `≤ hf.order`. Useful for avoiding case splits,
since it applies whether or not the order is `∞`. -/
lemma natCast_le_analyticOrderAt (hf : AnalyticAt 𝕜 f z₀) {n : ℕ} :
    n ≤ analyticOrderAt f z₀ ↔
      ∃ g, AnalyticAt 𝕜 g z₀ ∧ ∀ᶠ z in 𝓝 z₀, f z = (z - z₀) ^ n • g z := by
  unfold analyticOrderAt
  -- bug with split_ifs and Jovan's bundled classes
  split_ifs with h' h
  · simpa using ⟨0, analyticAt_const .., by simpa⟩
  · let m := (hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr h).choose
    obtain ⟨g, hg, hg_ne, hm⟩ := (hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr h).choose_spec
    rw [ENat.coe_le_coe]
    refine ⟨fun hmn ↦ ⟨fun z ↦ (z - z₀) ^ (m - n) • g z, by fun_prop, ?_⟩, fun ⟨h, hh, hfh⟩ ↦ ?_⟩
    · filter_upwards [hm] with z hz using by rwa [← mul_smul, ← pow_add, Nat.add_sub_of_le hmn]
    · contrapose! hg_ne
      have : ContinuousAt (fun z ↦ (z - z₀) ^ (n - m) • h z) z₀ := by fun_prop
      rw [tendsto_nhds_unique_of_eventuallyEq (l := 𝓝[≠] z₀)
        hg.continuousAt.continuousWithinAt this.continuousWithinAt ?_]
      · simp [m, Nat.sub_ne_zero_of_lt hg_ne]
      · filter_upwards [self_mem_nhdsWithin, hm.filter_mono nhdsWithin_le_nhds,
          hfh.filter_mono nhdsWithin_le_nhds] with z hz hf' hf''
        rw [← inv_smul_eq_iff₀ (pow_ne_zero _ <| sub_ne_zero_of_ne hz), hf'', smul_comm,
          ← mul_smul] at hf'
        rw [pow_sub₀ _ (sub_ne_zero_of_ne hz) (by lia), ← hf']
  · exact absurd hf h'
  · exact absurd hf h'

/-- If two functions agree in a neighborhood of `z₀`, then their orders at `z₀` agree. -/
lemma analyticOrderAt_congr (hfg : f =ᶠ[𝓝 z₀] g) :
    analyticOrderAt f z₀ = analyticOrderAt g z₀ := by
  by_cases hf : AnalyticAt 𝕜 f z₀
  · refine ENat.eq_of_forall_natCast_le_iff fun n ↦ ?_
    simp only [natCast_le_analyticOrderAt, hf, hf.congr hfg]
    congr! 3
    exact hfg.congr_left
  · rw [analyticOrderAt_of_not_analyticAt hf,
      analyticOrderAt_of_not_analyticAt fun hg ↦ hf <| hg.congr hfg.symm]

@[simp] lemma analyticOrderAt_id : analyticOrderAt (𝕜 := 𝕜) id 0 = 1 :=
  analyticAt_id.analyticOrderAt_eq_natCast.mpr ⟨fun _ ↦ 1, by fun_prop, by simp, by simp⟩

@[simp] lemma analyticOrderAt_neg : analyticOrderAt (-f) z₀ = analyticOrderAt f z₀ := by
  by_cases hf : AnalyticAt 𝕜 f z₀
  · refine ENat.eq_of_forall_natCast_le_iff fun n ↦ ?_
    simp only [natCast_le_analyticOrderAt, hf, hf.neg]
    exact (Equiv.neg _).exists_congr <| by simp [neg_eq_iff_eq_neg]
  · rw [analyticOrderAt_of_not_analyticAt hf,
      analyticOrderAt_of_not_analyticAt <| analyticAt_neg.not.2 hf]

/-- The order of a sum is at least the minimum of the orders of the summands. -/
theorem le_analyticOrderAt_add :
    min (analyticOrderAt f z₀) (analyticOrderAt g z₀) ≤ analyticOrderAt (f + g) z₀ := by
  by_cases hf : AnalyticAt 𝕜 f z₀
  · by_cases hg : AnalyticAt 𝕜 g z₀
    · refine ENat.forall_natCast_le_iff_le.mp fun n ↦ ?_
      simp only [le_min_iff, natCast_le_analyticOrderAt, hf, hg, hf.add hg]
      refine fun ⟨⟨F, hF, hF'⟩, ⟨G, hG, hG'⟩⟩ ↦ ⟨F + G, hF.add hG, ?_⟩
      filter_upwards [hF', hG'] with z using by simp +contextual
    · simp [*]
  · simp [*]

lemma le_analyticOrderAt_sub :
    min (analyticOrderAt f z₀) (analyticOrderAt g z₀) ≤ analyticOrderAt (f - g) z₀ := by
  simpa [sub_eq_add_neg] using le_analyticOrderAt_add (f := f) (g := -g)

lemma analyticOrderAt_add_eq_left_of_lt (hfg : analyticOrderAt f z₀ < analyticOrderAt g z₀) :
    analyticOrderAt (f + g) z₀ = analyticOrderAt f z₀ :=
  le_antisymm (by simpa [hfg.not_ge] using le_analyticOrderAt_sub (f := f + g) (g := g) (z₀ := z₀))
    (by simpa [hfg.le] using le_analyticOrderAt_add (f := f) (g := g) (z₀ := z₀))

lemma analyticOrderAt_add_eq_right_of_lt (hgf : analyticOrderAt g z₀ < analyticOrderAt f z₀) :
    analyticOrderAt (f + g) z₀ = analyticOrderAt g z₀ := by
  rw [add_comm, analyticOrderAt_add_eq_left_of_lt hgf]

/-- If two functions have unequal orders, then the order of their sum is exactly the minimum
of the orders of the summands. -/
lemma analyticOrderAt_add_of_ne (hfg : analyticOrderAt f z₀ ≠ analyticOrderAt g z₀) :
    analyticOrderAt (f + g) z₀ = min (analyticOrderAt f z₀) (analyticOrderAt g z₀) := by
  obtain hfg | hgf := hfg.lt_or_gt
  · simpa [hfg.le] using analyticOrderAt_add_eq_left_of_lt hfg
  · simpa [hgf.le] using analyticOrderAt_add_eq_right_of_lt hgf

lemma analyticOrderAt_smul_eq_top_of_left {f : 𝕜 → 𝕜} (hf : analyticOrderAt f z₀ = ⊤) :
     analyticOrderAt (f • g) z₀ = ⊤ := by
  rw [analyticOrderAt_eq_top, eventually_nhds_iff] at *
  obtain ⟨t, h₁t, h₂t, h₃t⟩ := hf
  exact ⟨t, fun y hy ↦ by simp [h₁t y hy], h₂t, h₃t⟩

lemma analyticOrderAt_smul_eq_top_of_right {f : 𝕜 → 𝕜} (hg : analyticOrderAt g z₀ = ⊤) :
    analyticOrderAt (f • g) z₀ = ⊤ := by
  rw [analyticOrderAt_eq_top, eventually_nhds_iff] at *
  obtain ⟨t, h₁t, h₂t, h₃t⟩ := hg
  exact ⟨t, fun y hy ↦ by simp [h₁t y hy], h₂t, h₃t⟩

/-- The order is additive when scalar multiplying analytic functions. -/
lemma analyticOrderAt_smul {f : 𝕜 → 𝕜} (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀) :
    analyticOrderAt (f • g) z₀ = analyticOrderAt f z₀ + analyticOrderAt g z₀ := by
  -- Trivial cases: one of the functions vanishes around z₀
  by_cases hf' : analyticOrderAt f z₀ = ⊤
  · simp [analyticOrderAt_smul_eq_top_of_left, *]
  by_cases hg' : analyticOrderAt g z₀ = ⊤
  · simp [analyticOrderAt_smul_eq_top_of_right, *]
  -- Non-trivial case: both functions do not vanish around z₀
  obtain ⟨f', h₁f', h₂f', h₃f'⟩ := hf.analyticOrderAt_ne_top.1 hf'
  obtain ⟨g', h₁g', h₂g', h₃g'⟩ := hg.analyticOrderAt_ne_top.1 hg'
  rw [← Nat.cast_analyticOrderNatAt hf', ← Nat.cast_analyticOrderNatAt hg', ← ENat.coe_add,
      (hf.smul hg).analyticOrderAt_eq_natCast]
  refine ⟨f' • g', h₁f'.smul h₁g', ?_, ?_⟩
  · simp
    tauto
  · obtain ⟨t, h₁t, h₂t, h₃t⟩ := eventually_nhds_iff.1 h₃f'
    obtain ⟨s, h₁s, h₂s, h₃s⟩ := eventually_nhds_iff.1 h₃g'
    exact eventually_nhds_iff.2
      ⟨t ∩ s, fun y hy ↦ (by simp [h₁t y hy.1, h₁s y hy.2]; module), h₂t.inter h₂s, h₃t, h₃s⟩

theorem AnalyticAt.analyticOrderAt_deriv_add_one {x : 𝕜} (hf : AnalyticAt 𝕜 f x)
    [CompleteSpace E] [CharZero 𝕜] :
    analyticOrderAt (deriv f) x + 1 = analyticOrderAt (f · - f x) x := by
  generalize h : analyticOrderAt (f · - f x) x = r
  cases r with
  | top =>
    suffices analyticOrderAt (deriv f) x = ⊤ by simp_all
    simp only [analyticOrderAt_eq_top, sub_eq_zero] at h ⊢
    obtain ⟨U, hUf, hUo, hUx⟩ := eventually_nhds_iff.mp h
    filter_upwards [hUo.mem_nhds hUx] with y hy
    simp [(eventuallyEq_of_mem (hUo.mem_nhds hy) hUf).deriv_eq]
  | coe r =>
    have hrne : r ≠ 0 := by
      intro hr
      rw [hr, ENat.coe_zero, AnalyticAt.analyticOrderAt_eq_zero (by fun_prop)] at h
      grind
    obtain ⟨s, rfl⟩ := Nat.exists_add_one_eq.mpr (Nat.pos_of_ne_zero hrne)
    rw [Nat.cast_succ]
    congr 1
    rw [analyticOrderAt_eq_natCast (by fun_prop)] at h
    obtain ⟨F, hFa, hFne, hfF⟩ := h
    simp only [sub_eq_iff_eq_add] at hfF
    obtain ⟨U, hUf, hUo, hUx⟩ := eventually_nhds_iff.mp (hfF.and hFa.eventually_analyticAt)
    have : ∀ y ∈ U, deriv f y =
        (y - x) ^ (s + 1) • deriv F y + (s + 1) • (y - x) ^ s • F y := by
      intro y hy
      rw [EventuallyEq.deriv_eq (eventually_of_mem (hUo.mem_nhds hy) (fun u hu ↦ (hUf u hu).1)),
        deriv_add_const, deriv_fun_smul (by fun_prop) (hUf y hy).2.differentiableAt]
      simp [mul_smul, add_smul, Nat.cast_smul_eq_nsmul]
    rw [analyticOrderAt_congr (eventually_of_mem (hUo.mem_nhds hUx) this)]
    have : analyticOrderAt (fun y ↦ (s + 1) • (y - x) ^ s • F y) x = s := by
      rw [analyticOrderAt_eq_natCast]
      · refine ⟨fun z ↦ (↑(s + 1) : 𝕜) • F z, hFa.fun_const_smul, ?_, .of_forall fun y ↦ ?_⟩
        · simpa using ⟨by norm_cast, hFne⟩
        · simpa only [Nat.cast_smul_eq_nsmul] using smul_comm ..
      · simp_rw [← Nat.cast_smul_eq_nsmul 𝕜]
        fun_prop
    rwa [← Pi.add_def, analyticOrderAt_add_eq_right_of_lt]
    rw [this, ← Order.succ_le_iff_of_not_isMax (not_isMax_iff.mpr ⟨⊤, ENat.coe_lt_top s⟩),
      ENat.succ_def, ← Nat.cast_add_one, natCast_le_analyticOrderAt (by fun_prop)]
    exact ⟨deriv F, hFa.deriv, by simp⟩

theorem AnalyticAt.analyticOrderAt_sub_eq_one_of_deriv_ne_zero {x : 𝕜} (hf : AnalyticAt 𝕜 f x)
    (hf' : deriv f x ≠ 0) : analyticOrderAt (f · - f x) x = 1 := by
  generalize h : analyticOrderAt (f · - f x) x = r
  cases r with
  | top =>
    simp_rw [analyticOrderAt_eq_top, sub_eq_zero] at h
    refine (hf' ?_).elim
    rw [EventuallyEq.deriv_eq h, deriv_const]
  | coe r =>
    norm_cast
    obtain ⟨F, hFa, hFne, hfF⟩ := (analyticOrderAt_eq_natCast (by fun_prop)).mp h
    apply eq_of_ge_of_le
    · by_contra! hr
      have := hfF.self_of_nhds
      simp_all
    · contrapose! hf'
      simp_rw [sub_eq_iff_eq_add] at hfF
      rw [EventuallyEq.deriv_eq hfF, deriv_add_const, deriv_fun_smul (by fun_prop) (by fun_prop),
        deriv_fun_pow (by fun_prop), sub_self, zero_pow (by lia), zero_pow (by lia),
        mul_zero, zero_mul, zero_smul, zero_smul, add_zero]

/-- At a zero with nonvanishing derivative, the analytic order is 1.
This is a variant of `analyticOrderAt_sub_eq_one_of_deriv_ne_zero` with `f z₀ = 0`
replacing the subtraction. -/
theorem AnalyticAt.analyticOrderAt_eq_one_of_zero_deriv_ne_zero {x : 𝕜}
    (hf : AnalyticAt 𝕜 f x) (hfx : f x = 0) (hf' : deriv f x ≠ 0) :
    analyticOrderAt f x = 1 := by
  simpa [hfx] using hf.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hf'

lemma natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero [CharZero 𝕜] [CompleteSpace E]
    (hf : AnalyticAt 𝕜 f z₀) :
    n ≤ analyticOrderAt f z₀ ↔ ∀ i < n, iteratedDeriv i f z₀ = 0 := by
  induction n generalizing f with
  | zero => simp
  | succ n IH =>
    by_cases hfz : f z₀ = 0; swap
    · simpa [analyticOrderAt_eq_zero.mpr (.inr hfz)] using ⟨0, by simp, by simpa⟩
    have : analyticOrderAt (deriv f) z₀ + 1 = analyticOrderAt f z₀ := by
      simpa [hfz] using hf.analyticOrderAt_deriv_add_one
    simp [← this, IH hf.deriv, iteratedDeriv_succ',
      -Order.lt_add_one_iff, Nat.forall_lt_succ_left, hfz]

lemma analyticOrderAt_deriv_of_pos {𝕜 : Type*} {E : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜]
    [NormMetric E] [AddCommGroup E] [IsNormedAddGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] {f : 𝕜 → E} {z₀ : 𝕜}
    (hf : AnalyticAt 𝕜 f z₀) {n : ℕ} (horder : analyticOrderAt f z₀ = n + 1) :
    analyticOrderAt (deriv f) z₀ = n := by
  have ⟨g, hg, hg₀, hfg⟩ := (AnalyticAt.analyticOrderAt_eq_natCast hf).1 horder
  have hz₀ : f z₀ = 0 := by
    simpa [sub_self, zero_pow, zero_smul] using Filter.Eventually.self_of_nhds hfg
  simpa [hz₀, sub_zero, horder] using hf.analyticOrderAt_deriv_add_one

lemma analyticOrderAt_iterated_deriv {𝕜 : Type*} {E : Type*} [NontriviallyNormedField 𝕜]
    [NormMetric E] [AddCommGroup E] [IsNormedAddGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] {f : 𝕜 → E} {z₀ : 𝕜}
    (hf : AnalyticAt 𝕜 f z₀) {k n : ℕ} [CharZero 𝕜] :
    n = analyticOrderAt f z₀ → n ≠ 0 → k ≤ n → analyticOrderAt (deriv^[k] f) z₀ = (n - k : ℕ) := by
  induction k generalizing n with
  | zero => exact fun Hn Hpos Hk ↦ Hn.symm
  | succ n' hk =>
    intro Hn Hpos Hk
    rw [Function.iterate_succ']
    have horder : analyticOrderAt (deriv^[n'] f) z₀ = (n - n'.succ) + 1 := by
      refine (hk Hn Hpos (by lia)).trans ?_
      have : (n - n'.succ) + 1 = n - n' := by grind
      rw [← this]
      simp
    simpa using (analyticOrderAt_deriv_of_pos (hf := AnalyticAt.iterated_deriv hf n')
      (n := n - n'.succ) horder)

attribute [local simp] Nat.factorial_ne_zero in
/-- A version of **Taylor's theorem** for analytic functions in one variable, with the error
term of the form `z ^ n` times a function analytic at 0.

(See `AnalyticAt.exists_eq_sum_add_pow_mul` for a version asserting global equality rather than
just on a neighbourhood of 0.) -/
lemma AnalyticAt.exists_eventuallyEq_sum_add_pow_mul [CharZero 𝕜] [CompleteSpace E]
    {f : 𝕜 → E} (hf : AnalyticAt 𝕜 f 0) (n : ℕ) :
    ∃ F : 𝕜 → E, AnalyticAt 𝕜 F 0 ∧ ∀ᶠ z in 𝓝 0,
      f z = (∑ i ∈ .range n, (z ^ i / i.factorial) • iteratedDeriv i f 0) + z ^ n • F z := by
  simp only [← sub_eq_iff_eq_add']
  have : AnalyticAt 𝕜
      (fun z : 𝕜 ↦ ∑ i ∈ .range n, (z ^ i / i.factorial) • iteratedDeriv i f 0) 0 := by
    refine Finset.analyticAt_fun_sum _ fun i hi ↦ ?_
    fun_prop
  convert (natCast_le_analyticOrderAt (hf.fun_sub this)).mp ?_
  · simp
  · rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hf.fun_sub this)]
    intro i hi
    rw [iteratedDeriv_fun_sub (AnalyticAt.contDiffAt <| by fun_prop) this.contDiffAt]
    simp (disch := fun_prop) only [iteratedDeriv_fun_sum, iteratedDeriv_smul_const,
      iteratedDeriv_div_const, iteratedDeriv_fun_pow_zero]
    simp [ite_div, Finset.sum_ite_eq_of_mem _ _ _ (Finset.mem_range.mpr hi)]

attribute [local simp] Nat.factorial_ne_zero in
/-- A version of **Taylor's theorem** for analytic functions in one variable, with the error
term of the form `z ^ n` times a function analytic at 0.

(See `AnalyticAt.exists_eventuallyEq_sum_add_pow_mul` for a version asserting equality on a
neighbourhood of `0` rather than globally.) -/
lemma AnalyticAt.exists_eq_sum_add_pow_mul [CharZero 𝕜] [CompleteSpace E]
    {f : 𝕜 → E} (hf : AnalyticAt 𝕜 f 0) (n : ℕ) :
    ∃ F : 𝕜 → E, AnalyticAt 𝕜 F 0 ∧ ∀ z,
      f z = (∑ i ∈ .range n, (z ^ i / i.factorial) • iteratedDeriv i f 0) + z ^ n • F z := by
  classical
  obtain ⟨F, hFa, hF⟩ := hf.exists_eventuallyEq_sum_add_pow_mul n
  obtain ⟨U, hU0, hU'⟩ := by rwa [eventually_iff_exists_mem] at hF
  refine ⟨fun z ↦ if z ∈ U then F z else (z ^ n)⁻¹ • (f z
      - (∑ i ∈ .range n, (z ^ i / i.factorial) • iteratedDeriv i f 0)), ?_, fun z ↦ ?_⟩
  · exact hFa.congr (by filter_upwards [hU0] using by simp +contextual)
  · by_cases hz : z ∈ U
    · simpa [hz] using hU' z hz
    · simp only [if_neg hz]
      rw [smul_inv_smul₀]
      · module
      · contrapose hz
        exact (pow_eq_zero_iff'.mp hz).1 ▸ mem_of_mem_nhds hU0

end NormedSpace

/-!
## Vanishing Order at a Point: Elementary Computations
-/

/-- Simplifier lemma for the order of a centered monomial -/
@[simp]
lemma analyticOrderAt_centeredMonomial {z₀ : 𝕜} {n : ℕ} :
    analyticOrderAt ((· - z₀) ^ n) z₀ = n := by
  rw [AnalyticAt.analyticOrderAt_eq_natCast (by fun_prop)]
  exact ⟨1, by simp [Pi.one_def, analyticAt_const]⟩

section NontriviallyNormedField
variable {f g : 𝕜 → 𝕜} {z₀ : 𝕜}

lemma analyticOrderAt_mul_eq_top_of_left (hf : analyticOrderAt f z₀ = ⊤) :
    analyticOrderAt (f * g) z₀ = ⊤ := analyticOrderAt_smul_eq_top_of_left hf

lemma analyticOrderAt_mul_eq_top_of_right (hg : analyticOrderAt g z₀ = ⊤) :
    analyticOrderAt (f * g) z₀ = ⊤ := analyticOrderAt_smul_eq_top_of_right hg

/-- The order is additive when multiplying analytic functions. -/
theorem analyticOrderAt_mul (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀) :
    analyticOrderAt (f * g) z₀ = analyticOrderAt f z₀ + analyticOrderAt g z₀ :=
  analyticOrderAt_smul hf hg

/-- The order is additive when multiplying analytic functions. -/
theorem analyticOrderNatAt_mul (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀)
    (hf' : analyticOrderAt f z₀ ≠ ⊤) (hg' : analyticOrderAt g z₀ ≠ ⊤) :
    analyticOrderNatAt (f * g) z₀ = analyticOrderNatAt f z₀ + analyticOrderNatAt g z₀ := by
  simp [analyticOrderNatAt, analyticOrderAt_mul, ENat.toNat_add, *]

/-- The order multiplies by `n` when taking an analytic function to its `n`th power. -/
theorem analyticOrderAt_pow (hf : AnalyticAt 𝕜 f z₀) :
    ∀ n, analyticOrderAt (f ^ n) z₀ = n • analyticOrderAt f z₀
  | 0 => by simp [analyticOrderAt_eq_zero]
  | n + 1 => by simp [add_mul, pow_add, analyticOrderAt_mul (hf.pow n), analyticOrderAt_pow, hf]

/-- The order multiplies by `n` when taking an analytic function to its `n`th power. -/
theorem analyticOrderNatAt_pow (hf : AnalyticAt 𝕜 f z₀) (n : ℕ) :
    analyticOrderNatAt (f ^ n) z₀ = n • analyticOrderNatAt f z₀ := by
  simp [analyticOrderNatAt, analyticOrderAt_pow, hf]

end NontriviallyNormedField

section comp

/-!
## Vanishing Order at a Point: Composition
-/
variable {f : 𝕜 → E} {g : 𝕜 → 𝕜} {z₀ : 𝕜}

/-- Analytic order of a composition of analytic functions. -/
lemma AnalyticAt.analyticOrderAt_comp (hf : AnalyticAt 𝕜 f (g z₀)) (hg : AnalyticAt 𝕜 g z₀) :
    analyticOrderAt (f ∘ g) z₀ = analyticOrderAt f (g z₀) * analyticOrderAt (g · - g z₀) z₀ := by
  by_cases hg_nc : EventuallyConst g (𝓝 z₀)
  · -- If `g` is eventually constant, both sides are either `⊤` or `0`.
    have := hg_nc.comp f
    rw [eventuallyConst_iff_analyticOrderAt_sub_eq_top] at hg_nc this
    rw [hg_nc]
    by_cases hf' : f (g z₀) = 0
    · simpa [hf', show analyticOrderAt f (g z₀) ≠ 0 by grind [analyticOrderAt_ne_zero]]
    · rw [show analyticOrderAt f (g z₀) = 0 from ?_, zero_mul] <;>
      grind [hf.comp hg, AnalyticAt.analyticOrderAt_eq_zero]
  by_cases hf' : analyticOrderAt f (g z₀) = ⊤
  · -- If `f` is eventually constant but `g` is not, we have `⊤ = ⊤ * (non-zero thing)`
    rw [hf', analyticOrderAt_eq_top.mpr
      (EventuallyEq.comp_tendsto (analyticOrderAt_eq_top.mp hf') hg.continuousAt), ENat.top_mul]
    rw [AnalyticAt.analyticOrderAt_ne_zero (by fun_prop), sub_eq_zero]
  · -- The interesting case: both orders are finite. First unpack the data:
    rw [eventuallyConst_iff_analyticOrderAt_sub_eq_top] at hg_nc
    obtain ⟨r, hr⟩ := ENat.ne_top_iff_exists.mp hf'
    obtain ⟨s, hs⟩ := ENat.ne_top_iff_exists.mp hg_nc
    rw [← hr, ← hs, ← ENat.coe_mul, (hf.comp hg).analyticOrderAt_eq_natCast]
    rw [Eq.comm, hf.analyticOrderAt_eq_natCast] at hr
    rcases hr with ⟨F, hFa, hFne, hfF⟩
    rw [Eq.comm, AnalyticAt.analyticOrderAt_eq_natCast (by fun_prop)] at hs
    rcases hs with ⟨G, hGa, hGne, hgG⟩
    -- Now write `f ∘ g` locally as the product of `(z - z₀) ^ (r * s)` and the
    -- non-vanishing analytic function `fun z ↦ (G z) ^ r • F (g z)`.
    refine ⟨fun z ↦ (G z) ^ r • F (g z), by fun_prop, by aesop, ?_⟩
    filter_upwards [EventuallyEq.comp_tendsto hfF hg.continuousAt, hgG] with z hfz hgz
    simp only [hfz, Function.comp_def, hgz, smul_eq_mul, mul_pow, mul_smul, mul_comm r s, pow_mul]

/-- If `g` is analytic at `x`, and `g' x ≠ 0`, then the analytic order of
`f ∘ g` at `x` is the analytic order of `f` at `g x` (even if `f` is not analytic). -/
lemma analyticOrderAt_comp_of_deriv_ne_zero (hg : AnalyticAt 𝕜 g z₀) (hg' : deriv g z₀ ≠ 0)
    [CompleteSpace 𝕜] [CharZero 𝕜] :
    analyticOrderAt (f ∘ g) z₀ = analyticOrderAt f (g z₀) := by
  by_cases hf : AnalyticAt 𝕜 f (g z₀)
  · simp [hf.analyticOrderAt_comp hg, hg.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hg']
  · rw [analyticOrderAt_of_not_analyticAt hf, analyticOrderAt_of_not_analyticAt]
    rwa [analyticAt_comp_iff_of_deriv_ne_zero hg hg']

end comp

/-!
## Level Sets of the Order Function
-/

namespace AnalyticOnNhd

variable {U : Set 𝕜} {f : 𝕜 → E}

/-- The set where an analytic function has infinite order is clopen in its domain of analyticity. -/
theorem isClopen_setOf_analyticOrderAt_eq_top (hf : AnalyticOnNhd 𝕜 f U) :
    IsClopen {u : U | analyticOrderAt f u = ⊤} := by
  constructor
  · rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro z hz
    rcases (hf z.1 z.2).eventually_eq_zero_or_eventually_ne_zero with h | h
    · -- Case: f is locally zero in a punctured neighborhood of z
      rw [← analyticOrderAt_eq_top] at h
      tauto
    · -- Case: f is locally nonzero in a punctured neighborhood of z
      obtain ⟨t', h₁t', h₂t', h₃t'⟩ := eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 h)
      use Subtype.val ⁻¹' t'
      constructor
      · intro w hw
        push _ ∈ _
        by_cases h₁w : w = z
        · rwa [h₁w]
        · rw [(hf _ w.2).analyticOrderAt_eq_zero.2 ((h₁t' w hw) (Subtype.coe_ne_coe.mpr h₁w))]
          exact ENat.zero_ne_top
      · exact ⟨isOpen_induced h₂t', h₃t'⟩
  · apply isOpen_iff_forall_mem_open.mpr
    intro z hz
    conv =>
      arg 1; intro; left; right; arg 1; intro
      rw [analyticOrderAt_eq_top, eventually_nhds_iff]
    simp only [mem_setOf_eq] at hz
    rw [analyticOrderAt_eq_top, eventually_nhds_iff] at hz
    obtain ⟨t', h₁t', h₂t', h₃t'⟩ := hz
    use Subtype.val ⁻¹' t'
    simp only [isOpen_induced h₂t', mem_preimage, h₃t', and_self, and_true]
    grind

/-- On a connected set, there exists a point where a meromorphic function `f` has finite order iff
`f` has finite order at every point. -/
theorem exists_analyticOrderAt_ne_top_iff_forall (hf : AnalyticOnNhd 𝕜 f U) (hU : IsConnected U) :
    (∃ u : U, analyticOrderAt f u ≠ ⊤) ↔ (∀ u : U, analyticOrderAt f u ≠ ⊤) := by
  have : ConnectedSpace U := Subtype.connectedSpace hU
  obtain ⟨v⟩ : Nonempty U := inferInstance
  suffices (∀ (u : U), analyticOrderAt f u ≠ ⊤) ∨ ∀ (u : U), analyticOrderAt f u = ⊤ by tauto
  simpa [Set.eq_empty_iff_forall_notMem, Set.eq_univ_iff_forall] using
      isClopen_iff.1 hf.isClopen_setOf_analyticOrderAt_eq_top

/-- On a preconnected set, a meromorphic function has finite order at one point if it has finite
order at another point. -/
theorem analyticOrderAt_ne_top_of_isPreconnected {x y : 𝕜} (hf : AnalyticOnNhd 𝕜 f U)
    (hU : IsPreconnected U) (h₁x : x ∈ U) (hy : y ∈ U) (h₂x : analyticOrderAt f x ≠ ⊤) :
    analyticOrderAt f y ≠ ⊤ :=
  (hf.exists_analyticOrderAt_ne_top_iff_forall ⟨nonempty_of_mem h₁x, hU⟩).1 (by use ⟨x, h₁x⟩)
    ⟨y, hy⟩

/-- The set where an analytic function has zero or infinite order is discrete within its domain of
analyticity. -/
theorem codiscrete_setOf_analyticOrderAt_eq_zero_or_top (hf : AnalyticOnNhd 𝕜 f U) :
    {u : U | analyticOrderAt f u = 0 ∨ analyticOrderAt f u = ⊤} ∈ Filter.codiscrete U := by
  simp_rw [mem_codiscrete_subtype_iff_mem_codiscreteWithin, mem_codiscreteWithin,
    disjoint_principal_right]
  intro x hx
  rcases (hf x hx).eventually_eq_zero_or_eventually_ne_zero with h₁f | h₁f
  · filter_upwards [eventually_nhdsWithin_of_eventually_nhds h₁f.eventually_nhds] with a ha
    simp [analyticOrderAt_eq_top, ha]
  · filter_upwards [h₁f] with a ha
    simp +contextual [(hf a _).analyticOrderAt_eq_zero, ha]

/--
The set where an analytic function has zero or infinite order is discrete within its domain of
analyticity.
-/
theorem codiscreteWithin_setOf_analyticOrderAt_eq_zero_or_top (hf : AnalyticOnNhd 𝕜 f U) :
    {u : 𝕜 | analyticOrderAt f u = 0 ∨ analyticOrderAt f u = ⊤} ∈ codiscreteWithin U := by
  simp_rw [mem_codiscreteWithin, disjoint_principal_right]
  intro x hx
  rcases (hf x hx).eventually_eq_zero_or_eventually_ne_zero with h₁f | h₁f
  · filter_upwards [eventually_nhdsWithin_of_eventually_nhds h₁f.eventually_nhds] with a ha
    simp [analyticOrderAt_eq_top, ha]
  · filter_upwards [h₁f] with a ha
    simp +contextual [(hf a _).analyticOrderAt_eq_zero, ha]

/--
If an analytic function `f` is not constantly zero on a connected set `U`, then its set of zeros is
codiscrete within `U`.

See `AnalyticOnNhd.preimage_mem_codiscreteWithin` for a more general statement in preimages of
codiscrete sets.
-/
theorem preimage_zero_mem_codiscreteWithin {x : 𝕜} (h₁f : AnalyticOnNhd 𝕜 f U) (h₂f : f x ≠ 0)
    (hx : x ∈ U) (hU : IsConnected U) :
    f ⁻¹' {0}ᶜ ∈ codiscreteWithin U := by
  filter_upwards [h₁f.codiscreteWithin_setOf_analyticOrderAt_eq_zero_or_top,
    self_mem_codiscreteWithin U] with a ha h₂a
  rw [← (h₁f x hx).analyticOrderAt_eq_zero] at h₂f
  have {u : U} : analyticOrderAt f u ≠ ⊤ := by
    apply (h₁f.exists_analyticOrderAt_ne_top_iff_forall hU).1
    use ⟨x, hx⟩
    simp_all
  simp_all [(h₁f a h₂a).analyticOrderAt_eq_zero]

/--
If an analytic function `f` is not constantly zero on `𝕜`, then its set of zeros is codiscrete.

See `AnalyticOnNhd.preimage_mem_codiscreteWithin` for a more general statement in preimages of
codiscrete sets.
-/
theorem preimage_zero_mem_codiscrete [ConnectedSpace 𝕜] {x : 𝕜} (hf : AnalyticOnNhd 𝕜 f Set.univ)
    (hx : f x ≠ 0) :
    f ⁻¹' {0}ᶜ ∈ codiscrete 𝕜 :=
  hf.preimage_zero_mem_codiscreteWithin hx trivial isConnected_univ

lemma analyticOrderAt_eq_top_iff_eq_zero [PreconnectedSpace 𝕜] {f : 𝕜 → E} (z : 𝕜)
    (hf : ∀ z₀, AnalyticAt 𝕜 f z₀) : analyticOrderAt f z = ⊤ ↔ f = 0 := by
  refine analyticOrderAt_eq_top.trans ⟨fun h ↦ eqOn_univ .. |>.mp ?_, by simp +contextual⟩
  apply eqOn_zero_of_preconnected_of_frequently_eq_zero (fun z _ ↦ hf z) isPreconnected_univ trivial
  exact hf z |>.frequently_eq_iff_eventually_eq analyticAt_const |>.mpr h

lemma _root_.IsOpen.forall_analyticOrderAt_eq_top_iff_eqOn_zero {s : Set 𝕜} (hs : IsOpen s)
    (f : 𝕜 → E) : (∀ z ∈ s, analyticOrderAt f z = ⊤) ↔ EqOn f 0 s := by
  refine ⟨(EventuallyEq.eq_of_nhds <| analyticOrderAt_eq_top.mp <| · · ·), fun hzero z hz ↦ ?_⟩
  apply analyticOrderAt_eq_top.mpr
  filter_upwards [hs.mem_nhds hz]
  exact fun _ ↦ hzero.eq_of_mem

end AnalyticOnNhd
