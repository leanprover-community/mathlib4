/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler, Stefan Kebekus
-/
module

public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Algebra.Order.WithTop.Untop0

/-!
# Orders of Meromorphic Functions

This file defines the order of a meromorphic function `f` at a point `z₀`, as an element of
`ℤ ∪ {∞}`.

We characterize the order being `< 0`, or `= 0`, or `> 0`, as the convergence of the function
to infinity, resp. a nonzero constant, resp. zero.

## TODO

Uniformize API between analytic and meromorphic functions
-/

@[expose] public section

open Filter Set WithTop.LinearOrderedAddCommGroup
open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f f₁ f₂ : 𝕜 → E} {x : 𝕜}

/-!
## Order at a Point: Definition and Characterization
-/

open scoped Classical in
/-- The order of a meromorphic function `f` at `z₀`, as an element of `ℤ ∪ {∞}`.

The order is defined to be `∞` if `f` is identically 0 on a neighbourhood of `z₀`, and otherwise the
unique `n` such that `f` can locally be written as `f z = (z - z₀) ^ n • g z`, where `g` is analytic
and does not vanish at `z₀`. See `MeromorphicAt.meromorphicOrderAt_eq_top_iff` and
`MeromorphicAt.meromorphicOrderAt_eq_int_iff` for these equivalences.

If the function is not meromorphic at `x`, we use the junk value `0`. -/
noncomputable def meromorphicOrderAt (f : 𝕜 → E) (x : 𝕜) : WithTop ℤ :=
  if hf : MeromorphicAt f x then
    ((analyticOrderAt (fun z ↦ (z - x) ^ hf.choose • f z) x).map (↑· : ℕ → ℤ)) - hf.choose
  else 0

@[simp]
lemma meromorphicOrderAt_of_not_meromorphicAt (hf : ¬ MeromorphicAt f x) :
    meromorphicOrderAt f x = 0 :=
  dif_neg hf

lemma meromorphicAt_of_meromorphicOrderAt_ne_zero (hf : meromorphicOrderAt f x ≠ 0) :
    MeromorphicAt f x := by
  contrapose hf
  simp [hf]

/-- The order of a meromorphic function `f` at a `z₀` is infinity iff `f` vanishes locally around
`z₀`. -/
lemma meromorphicOrderAt_eq_top_iff :
    meromorphicOrderAt f x = ⊤ ↔ ∀ᶠ z in 𝓝[≠] x, f z = 0 := by
  by_cases hf : MeromorphicAt f x; swap
  · simp only [hf, not_false_eq_true, meromorphicOrderAt_of_not_meromorphicAt, WithTop.zero_ne_top,
      false_iff]
    contrapose hf
    exact (MeromorphicAt.const 0 x).congr (EventuallyEq.symm hf)
  simp only [meromorphicOrderAt, hf, ↓reduceDIte, sub_eq_top_iff, ENat.map_eq_top_iff,
    WithTop.natCast_ne_top, or_false]
  by_cases h : analyticOrderAt (fun z ↦ (z - x) ^ hf.choose • f z) x = ⊤
  · simp only [h, eventually_nhdsWithin_iff, mem_compl_iff, mem_singleton_iff, true_iff]
    rw [analyticOrderAt_eq_top] at h
    filter_upwards [h] with z hf hz
    rwa [smul_eq_zero_iff_right <| pow_ne_zero _ (sub_ne_zero.mpr hz)] at hf
  · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp h
    simp only [← hm, ENat.coe_ne_top, false_iff]
    contrapose h
    rw [analyticOrderAt_eq_top]
    rw [← hf.choose_spec.frequently_eq_iff_eventually_eq analyticAt_const]
    apply Eventually.frequently
    filter_upwards [h] with z hfz
    rw [hfz, smul_zero]

lemma eventuallyConst_nhdsNE_iff_meromorphicOrderAt_sub_eq_top :
    EventuallyConst f (𝓝[≠] x) ↔ ∃ c, meromorphicOrderAt (f · - c) x = ⊤ := by
  simp only [eventuallyConst_iff_exists_eventuallyEq, meromorphicOrderAt_eq_top_iff,
    sub_eq_zero, EventuallyEq]

/-- The order of a meromorphic function `f` at `z₀` equals an integer `n` iff `f` can locally be
written as `f z = (z - z₀) ^ n • g z`, where `g` is analytic and does not vanish at `z₀`. -/
lemma meromorphicOrderAt_eq_int_iff {n : ℤ} (hf : MeromorphicAt f x) : meromorphicOrderAt f x = n ↔
    ∃ g : 𝕜 → E, AnalyticAt 𝕜 g x ∧ g x ≠ 0 ∧ ∀ᶠ z in 𝓝[≠] x, f z = (z - x) ^ n • g z := by
  simp only [meromorphicOrderAt, hf, ↓reduceDIte]
  by_cases h : analyticOrderAt (fun z ↦ (z - x) ^ hf.choose • f z) x = ⊤
  · rw [h, ENat.map_top, ← WithTop.coe_natCast, top_sub,
      eq_false_intro WithTop.top_ne_coe, false_iff]
    rw [analyticOrderAt_eq_top] at h
    refine fun ⟨g, hg_an, hg_ne, hg_eq⟩ ↦ hg_ne ?_
    apply EventuallyEq.eq_of_nhds
    rw [EventuallyEq, ← AnalyticAt.frequently_eq_iff_eventually_eq hg_an analyticAt_const]
    apply Eventually.frequently
    rw [eventually_nhdsWithin_iff] at hg_eq ⊢
    filter_upwards [h, hg_eq] with z hfz hfz_eq hz
    rwa [hfz_eq hz, ← mul_smul, smul_eq_zero_iff_right] at hfz
    exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hz)) (zpow_ne_zero _ (sub_ne_zero.mpr hz))
  · obtain ⟨m, h⟩ := ENat.ne_top_iff_exists.mp h
    rw [← h, ENat.map_coe, ← WithTop.coe_natCast, ← coe_sub, WithTop.coe_inj]
    obtain ⟨g, hg_an, hg_ne, hg_eq⟩ := hf.choose_spec.analyticOrderAt_eq_natCast.mp h.symm
    replace hg_eq : ∀ᶠ (z : 𝕜) in 𝓝[≠] x, f z = (z - x) ^ (↑m - ↑hf.choose : ℤ) • g z := by
      rw [eventually_nhdsWithin_iff]
      filter_upwards [hg_eq] with z hg_eq hz
      rwa [← smul_right_inj <| zpow_ne_zero _ (sub_ne_zero.mpr hz), ← mul_smul,
        ← zpow_add₀ (sub_ne_zero.mpr hz), ← add_sub_assoc, add_sub_cancel_left, zpow_natCast,
        zpow_natCast]
    exact ⟨fun h ↦ ⟨g, hg_an, hg_ne, h ▸ hg_eq⟩,
      AnalyticAt.unique_eventuallyEq_zpow_smul_nonzero ⟨g, hg_an, hg_ne, hg_eq⟩⟩

/--
The order of a meromorphic function `f` at `z₀` is finite iff `f` can locally be
written as `f z = (z - z₀) ^ order • g z`, where `g` is analytic and does not
vanish at `z₀`.
-/
theorem meromorphicOrderAt_ne_top_iff {f : 𝕜 → E} {z₀ : 𝕜} (hf : MeromorphicAt f z₀) :
    meromorphicOrderAt f z₀ ≠ ⊤ ↔ ∃ (g : 𝕜 → E), AnalyticAt 𝕜 g z₀ ∧ g z₀ ≠ 0 ∧
      f =ᶠ[𝓝[≠] z₀] fun z ↦ (z - z₀) ^ ((meromorphicOrderAt f z₀).untop₀) • g z :=
  ⟨fun h ↦ (meromorphicOrderAt_eq_int_iff hf).1 (WithTop.coe_untop₀_of_ne_top h).symm,
    fun h ↦ Option.ne_none_iff_exists'.2
      ⟨(meromorphicOrderAt f z₀).untopD 0, (meromorphicOrderAt_eq_int_iff hf).2 h⟩⟩

/--
The order of a meromorphic function `f` at `z₀` is finite iff `f` does not have
any zeros in a sufficiently small neighborhood of `z₀`.
-/
theorem meromorphicOrderAt_ne_top_iff_eventually_ne_zero {f : 𝕜 → E} (hf : MeromorphicAt f x) :
    meromorphicOrderAt f x ≠ ⊤ ↔ ∀ᶠ x in 𝓝[≠] x, f x ≠ 0 := by
  constructor
  · intro h
    obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOrderAt_ne_top_iff hf).1 h
    filter_upwards [h₃g, self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
      ((h₁g.continuousAt.ne_iff_eventually_ne continuousAt_const).mp h₂g)]
    simp_all [zpow_ne_zero, sub_ne_zero]
  · simp_all [meromorphicOrderAt_eq_top_iff, Eventually.frequently]

/-- If the order of a meromorphic function is negative, then this function converges to infinity
at this point. See also the iff version `tendsto_cobounded_iff_meromorphicOrderAt_neg`. -/
lemma tendsto_cobounded_of_meromorphicOrderAt_neg (ho : meromorphicOrderAt f x < 0) :
    Tendsto f (𝓝[≠] x) (Bornology.cobounded E) := by
  have hf : MeromorphicAt f x := meromorphicAt_of_meromorphicOrderAt_ne_zero ho.ne
  simp only [← tendsto_norm_atTop_iff_cobounded]
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp ho.ne_top
  have m_neg : m < 0 := by simpa [← hm] using ho
  rcases (meromorphicOrderAt_eq_int_iff hf).1 hm.symm with ⟨g, g_an, gx, hg⟩
  have A : Tendsto (fun z ↦ ‖(z - x) ^ m • g z‖) (𝓝[≠] x) atTop := by
    simp only [norm_smul]
    apply Filter.Tendsto.atTop_mul_pos (C := ‖g x‖) (by simp [gx]) _
      g_an.continuousAt.continuousWithinAt.tendsto.norm
    have : Tendsto (fun z ↦ z - x) (𝓝[≠] x) (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : ContinuousWithinAt (fun z ↦ z - x) {x}ᶜ x := by fun_prop
        simpa using this.tendsto
      · filter_upwards [self_mem_nhdsWithin] with y hy
        simpa [sub_eq_zero] using hy
    exact (tendsto_norm_cobounded_atTop.comp (tendsto_zpow_nhdsNE_zero_cobounded m_neg)).comp this
  apply A.congr'
  filter_upwards [hg] with z hz using by simp [hz]

/-- If the order of a meromorphic function is zero, then this function converges to a nonzero
limit at this point. See also the iff version `tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero`. -/
lemma tendsto_ne_zero_of_meromorphicOrderAt_eq_zero
    (hf : MeromorphicAt f x) (ho : meromorphicOrderAt f x = 0) :
    ∃ c ≠ 0, Tendsto f (𝓝[≠] x) (𝓝 c) := by
  rcases (meromorphicOrderAt_eq_int_iff hf).1 ho with ⟨g, g_an, gx, hg⟩
  refine ⟨g x, gx, ?_⟩
  apply g_an.continuousAt.continuousWithinAt.tendsto.congr'
  filter_upwards [hg] with y hy using by simp [hy]

/-- If the order of a meromorphic function is positive, then this function converges to zero
at this point. See also the iff version `tendsto_zero_iff_meromorphicOrderAt_pos`. -/
lemma tendsto_zero_of_meromorphicOrderAt_pos (ho : 0 < meromorphicOrderAt f x) :
    Tendsto f (𝓝[≠] x) (𝓝 0) := by
  have hf : MeromorphicAt f x := meromorphicAt_of_meromorphicOrderAt_ne_zero ho.ne'
  cases h'o : meromorphicOrderAt f x with
  | top =>
    apply tendsto_const_nhds.congr'
    filter_upwards [meromorphicOrderAt_eq_top_iff.1 h'o] with y hy using hy.symm
  | coe n =>
    rcases (meromorphicOrderAt_eq_int_iff hf).1 h'o with ⟨g, g_an, gx, hg⟩
    lift n to ℕ using by simpa [h'o] using ho.le
    have : (0 : E) = (x - x) ^ n • g x := by
      have : 0 < n := by simpa [h'o] using ho
      simp [zero_pow_eq_zero.2 this.ne']
    rw [this]
    have : ContinuousAt (fun z ↦ (z - x) ^ n • g z) x := by fun_prop
    apply this.continuousWithinAt.tendsto.congr'
    filter_upwards [hg] with y hy using by simp [hy]

/-- If the order of a meromorphic function is nonnegative, then this function converges
at this point. See also the iff version `tendsto_nhds_iff_meromorphicOrderAt_nonneg`. -/
lemma tendsto_nhds_of_meromorphicOrderAt_nonneg
    (hf : MeromorphicAt f x) (ho : 0 ≤ meromorphicOrderAt f x) :
    ∃ c, Tendsto f (𝓝[≠] x) (𝓝 c) := by
  rcases ho.eq_or_lt with ho | ho
  · rcases tendsto_ne_zero_of_meromorphicOrderAt_eq_zero hf ho.symm with ⟨c, -, hc⟩
    exact ⟨c, hc⟩
  · exact ⟨0, tendsto_zero_of_meromorphicOrderAt_pos ho⟩

/-- A meromorphic function converges to infinity iff its order is negative. -/
lemma tendsto_cobounded_iff_meromorphicOrderAt_neg (hf : MeromorphicAt f x) :
    Tendsto f (𝓝[≠] x) (Bornology.cobounded E) ↔ meromorphicOrderAt f x < 0 := by
  rcases lt_or_ge (meromorphicOrderAt f x) 0 with ho | ho
  · simp [ho, tendsto_cobounded_of_meromorphicOrderAt_neg]
  · simp only [lt_iff_not_ge, ho, not_true_eq_false, iff_false, ← tendsto_norm_atTop_iff_cobounded]
    obtain ⟨c, hc⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hf ho
    exact not_tendsto_atTop_of_tendsto_nhds hc.norm

/-- A meromorphic function converges to a limit iff its order is nonnegative. -/
lemma tendsto_nhds_iff_meromorphicOrderAt_nonneg (hf : MeromorphicAt f x) :
    (∃ c, Tendsto f (𝓝[≠] x) (𝓝 c)) ↔ 0 ≤ meromorphicOrderAt f x := by
  rcases lt_or_ge (meromorphicOrderAt f x) 0 with ho | ho
  · simp only [← not_lt, ho, not_true_eq_false, iff_false, not_exists]
    intro c hc
    apply not_tendsto_atTop_of_tendsto_nhds hc.norm
    rw [tendsto_norm_atTop_iff_cobounded]
    exact tendsto_cobounded_of_meromorphicOrderAt_neg ho
  · simp [ho, tendsto_nhds_of_meromorphicOrderAt_nonneg hf ho]

/-- A meromorphic function converges to a nonzero limit iff its order is zero. -/
lemma tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero (hf : MeromorphicAt f x) :
    (∃ c ≠ 0, Tendsto f (𝓝[≠] x) (𝓝 c)) ↔ meromorphicOrderAt f x = 0 := by
  rcases eq_or_ne (meromorphicOrderAt f x) 0 with ho | ho
  · simp [ho, tendsto_ne_zero_of_meromorphicOrderAt_eq_zero hf ho]
  simp only [ne_eq, ho, iff_false, not_exists, not_and]
  intro c c_ne hc
  rcases ho.lt_or_gt with ho | ho
  · apply not_tendsto_atTop_of_tendsto_nhds hc.norm
    rw [tendsto_norm_atTop_iff_cobounded]
    exact tendsto_cobounded_of_meromorphicOrderAt_neg ho
  · apply c_ne
    exact tendsto_nhds_unique hc (tendsto_zero_of_meromorphicOrderAt_pos ho)

/-- A meromorphic function converges to zero iff its order is positive. -/
lemma tendsto_zero_iff_meromorphicOrderAt_pos (hf : MeromorphicAt f x) :
    (Tendsto f (𝓝[≠] x) (𝓝 0)) ↔ 0 < meromorphicOrderAt f x := by
  rcases lt_or_ge 0 (meromorphicOrderAt f x) with ho | ho
  · simp [ho, tendsto_zero_of_meromorphicOrderAt_pos ho]
  simp only [← not_le, ho, not_true_eq_false, iff_false]
  intro hc
  rcases ho.eq_or_lt with ho | ho
  · obtain ⟨c, c_ne, h'c⟩ := tendsto_ne_zero_of_meromorphicOrderAt_eq_zero hf ho
    apply c_ne
    exact tendsto_nhds_unique h'c hc
  · apply not_tendsto_atTop_of_tendsto_nhds hc.norm
    rw [tendsto_norm_atTop_iff_cobounded]
    exact tendsto_cobounded_of_meromorphicOrderAt_neg ho

/-- Meromorphic functions that agree in a punctured neighborhood of `z₀` have the same order at
`z₀`. -/
theorem meromorphicOrderAt_congr (hf₁₂ : f₁ =ᶠ[𝓝[≠] x] f₂) :
    meromorphicOrderAt f₁ x = meromorphicOrderAt f₂ x := by
  by_cases hf₁ : MeromorphicAt f₁ x; swap
  · have : ¬ MeromorphicAt f₂ x := by
      contrapose hf₁
      exact hf₁.congr hf₁₂.symm
    simp [hf₁, this]
  by_cases h₁f₁ : meromorphicOrderAt f₁ x = ⊤
  · rw [h₁f₁, eq_comm]
    rw [meromorphicOrderAt_eq_top_iff] at h₁f₁ ⊢
    exact EventuallyEq.rw h₁f₁ (fun x => Eq (f₂ x)) hf₁₂.symm
  · obtain ⟨n, hn : meromorphicOrderAt f₁ x = n⟩ := Option.ne_none_iff_exists'.mp h₁f₁
    obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOrderAt_eq_int_iff hf₁).1 hn
    rw [hn, eq_comm, meromorphicOrderAt_eq_int_iff (hf₁.congr hf₁₂)]
    use g, h₁g, h₂g
    exact EventuallyEq.rw h₃g (fun x => Eq (f₂ x)) hf₁₂.symm

/-- Compatibility of notions of `order` for analytic and meromorphic functions. -/
lemma AnalyticAt.meromorphicOrderAt_eq (hf : AnalyticAt 𝕜 f x) :
    meromorphicOrderAt f x = (analyticOrderAt f x).map (↑) := by
  cases hn : analyticOrderAt f x
  · rw [ENat.map_top, meromorphicOrderAt_eq_top_iff]
    exact (analyticOrderAt_eq_top.mp hn).filter_mono nhdsWithin_le_nhds
  · simp_rw [ENat.map_coe, meromorphicOrderAt_eq_int_iff hf.meromorphicAt, zpow_natCast]
    rcases hf.analyticOrderAt_eq_natCast.mp hn with ⟨g, h1, h2, h3⟩
    exact ⟨g, h1, h2, h3.filter_mono nhdsWithin_le_nhds⟩

/--
When seen as meromorphic functions, analytic functions have nonnegative order.
-/
theorem AnalyticAt.meromorphicOrderAt_nonneg (hf : AnalyticAt 𝕜 f x) :
    0 ≤ meromorphicOrderAt f x := by
  simp [hf.meromorphicOrderAt_eq]

/-- If a function is both meromorphic and continuous at a point, then it is analytic there. -/
protected theorem MeromorphicAt.analyticAt {f : 𝕜 → E} {x : 𝕜}
    (h : MeromorphicAt f x) (h' : ContinuousAt f x) :
    AnalyticAt 𝕜 f x := by
  cases ho : meromorphicOrderAt f x with
  | top =>
    /- If the order is infinite, then `f` vanishes on a pointed neighborhood of `x`. By continuity,
    it also vanishes at `x`.-/
    have : AnalyticAt 𝕜 (fun _ ↦ (0 : E)) x := analyticAt_const
    apply this.congr
    rw [← ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE continuousAt_const h']
    filter_upwards [meromorphicOrderAt_eq_top_iff.1 ho] with y hy using by simp [hy]
  | coe n =>
    /- If the order is finite, then the order has to be nonnegative, as otherwise the norm of `f`
    would tend to infinity at `x`. Then the local expression of `f` coming from its meromorphicity
    shows that it coincides with an analytic function close to `x`, except maybe at `x`. By
    continuity of `f`, the two functions also coincide at `x`. -/
    rcases (meromorphicOrderAt_eq_int_iff h).1 ho with ⟨g, g_an, gx, hg⟩
    have : 0 ≤ meromorphicOrderAt f x := by
      apply (tendsto_nhds_iff_meromorphicOrderAt_nonneg h).1
      exact ⟨f x, h'.continuousWithinAt.tendsto⟩
    lift n to ℕ using by simpa [ho] using this
    have A : ∀ᶠ (z : 𝕜) in 𝓝 x, (z - x) ^ n • g z = f z := by
      apply (ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE (by fun_prop) h').1
      filter_upwards [hg] with z hz using by simpa using hz.symm
    exact AnalyticAt.congr (by fun_prop) A

lemma AnalyticAt.of_meromorphicOrderAt_pos {f : 𝕜 → E} {x : 𝕜}
    (h : 0 < meromorphicOrderAt f x) (hf : f x = 0) :
    AnalyticAt 𝕜 f x := by
  refine (meromorphicAt_of_meromorphicOrderAt_ne_zero h.ne').analyticAt ?_
  rw [continuousAt_iff_punctured_nhds, hf]
  exact tendsto_zero_of_meromorphicOrderAt_pos h

/--
The order of a constant function is `⊤` if the constant is zero and `0` otherwise.
-/
theorem meromorphicOrderAt_const (z₀ : 𝕜) (e : E) [Decidable (e = 0)] :
    meromorphicOrderAt (fun _ ↦ e) z₀ = if e = 0 then ⊤ else (0 : WithTop ℤ) := by
  split_ifs with he
  · simp [he, meromorphicOrderAt_eq_top_iff]
  · exact (meromorphicOrderAt_eq_int_iff (.const e z₀)).2 ⟨fun _ ↦ e, by fun_prop, by simpa⟩

@[simp]
lemma meromorphicOrderAt_id : meromorphicOrderAt (𝕜 := 𝕜) id 0 = 1 := by
  simp [analyticAt_id.meromorphicOrderAt_eq]

/--
The order of a constant function is `⊤` if the constant is zero and `0` otherwise.
-/
theorem meromorphicOrderAt_const_intCast (z₀ : 𝕜) (n : ℤ) [Decidable ((n : 𝕜) = 0)] :
    meromorphicOrderAt (n : 𝕜 → 𝕜) z₀ = if (n : 𝕜) = 0 then ⊤ else (0 : WithTop ℤ) :=
  meromorphicOrderAt_const z₀ (n : 𝕜)

/--
The order of a constant function is `⊤` if the constant is zero and `0` otherwise.
-/
theorem meromorphicOrderAt_const_natCast (z₀ : 𝕜) (n : ℕ) [Decidable ((n : 𝕜) = 0)] :
    meromorphicOrderAt (n : 𝕜 → 𝕜) z₀ = if (n : 𝕜) = 0 then ⊤ else (0 : WithTop ℤ) :=
  meromorphicOrderAt_const z₀ (n : 𝕜)

/--
The order of a constant function is `⊤` if the constant is zero and `0` otherwise.
-/
@[simp] theorem meromorphicOrderAt_const_ofNat (z₀ : 𝕜) (n : ℕ) [Decidable ((n : 𝕜) = 0)] :
    meromorphicOrderAt (ofNat(n) : 𝕜 → 𝕜) z₀ = if (n : 𝕜) = 0 then ⊤ else (0 : WithTop ℤ) := by
  convert meromorphicOrderAt_const z₀ (n : 𝕜)
  simp [Semiring.toGrindSemiring_ofNat 𝕜 n]

/-- The order of `(· - x) ^ n` at `x` is `n`. -/
@[simp, to_fun] theorem meromorphicOrderAt_zpow_id_sub_const {n : ℤ} :
    meromorphicOrderAt ((· - x) ^ n) x = n := by
  rw [meromorphicOrderAt_eq_int_iff (by fun_prop)]
  exact ⟨fun z ↦ 1, by fun_prop, one_ne_zero, by aesop⟩

/-- The order of `(· - x) ^ n` at `x` is `n`. -/
@[simp, to_fun] theorem meromorphicOrderAt_pow_id_sub_const {n : ℕ} :
    meromorphicOrderAt ((· - x) ^ n) x = n := by
  convert meromorphicOrderAt_zpow_id_sub_const
  simp only [zpow_natCast]

/-- The order of `· - x` at `x` is `1`. -/
@[simp] theorem meromorphicOrderAt_id_sub_const :
    meromorphicOrderAt (· - x) x = 1 := by
  rw [← WithTop.coe_one, ← meromorphicOrderAt_zpow_id_sub_const (𝕜 := 𝕜), zpow_one]

/-!
## Order at a Point: Behaviour under Ring Operations

We establish additivity of the order under multiplication and taking powers.
-/

/-- The order is additive when multiplying scalar-valued and vector-valued meromorphic functions. -/
@[to_fun] theorem meromorphicOrderAt_smul {f : 𝕜 → 𝕜} {g : 𝕜 → E}
    (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    meromorphicOrderAt (f • g) x = meromorphicOrderAt f x + meromorphicOrderAt g x := by
  -- Trivial cases: one of the functions vanishes around z₀
  cases h₂f : meromorphicOrderAt f x with
  | top =>
    simp only [top_add, meromorphicOrderAt_eq_top_iff] at h₂f ⊢
    filter_upwards [h₂f] with z hz using by simp [hz]
  | coe m =>
    cases h₂g : meromorphicOrderAt g x with
    | top =>
      simp only [add_top, meromorphicOrderAt_eq_top_iff] at h₂g ⊢
      filter_upwards [h₂g] with z hz using by simp [hz]
    | coe n => -- Non-trivial case: both functions do not vanish around z₀
      rw [← WithTop.coe_add, meromorphicOrderAt_eq_int_iff (hf.smul hg)]
      obtain ⟨F, h₁F, h₂F, h₃F⟩ := (meromorphicOrderAt_eq_int_iff hf).1 h₂f
      obtain ⟨G, h₁G, h₂G, h₃G⟩ := (meromorphicOrderAt_eq_int_iff hg).1 h₂g
      use F • G, h₁F.smul h₁G, by simp [h₂F, h₂G]
      filter_upwards [self_mem_nhdsWithin, h₃F, h₃G] with a ha hfa hga
      simp [hfa, hga, smul_comm (F a), zpow_add₀ (sub_ne_zero.mpr ha), mul_smul]

/-- The order is additive when multiplying meromorphic functions. -/
@[to_fun] theorem meromorphicOrderAt_mul {f g : 𝕜 → 𝕜} (hf : MeromorphicAt f x)
    (hg : MeromorphicAt g x) :
    meromorphicOrderAt (f * g) x = meromorphicOrderAt f x + meromorphicOrderAt g x :=
  meromorphicOrderAt_smul hf hg

/--
The order is additive in products of meromorphic functions.
-/
theorem meromorphicOrderAt_prod {x : 𝕜} {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜}
    (hf : ∀ i ∈ s, MeromorphicAt (f i) x) :
    meromorphicOrderAt (∏ i ∈ s, f i) x = ∑ i ∈ s, meromorphicOrderAt (f i) x := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty, ← WithTop.coe_zero, meromorphicOrderAt_eq_int_iff]
    · exact ⟨1, analyticAt_const, by simp⟩
    · apply MeromorphicAt.const
  | insert a s ha hs =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, meromorphicOrderAt_mul
      (hf a (Finset.mem_insert_self a s))
      (MeromorphicAt.prod (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)))]
    congr
    rw [hs (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))]

/--
The order is additive in products of meromorphic functions.
-/
theorem meromorphicOrderAt_fun_prod {x : 𝕜} {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜}
    (hf : ∀ i ∈ s, MeromorphicAt (f i) x) :
    meromorphicOrderAt (fun a ↦ ∏ i ∈ s, f i a) x = ∑ i ∈ s, meromorphicOrderAt (f i) x := by
  convert meromorphicOrderAt_prod hf
  exact (Finset.prod_apply _ s f).symm

/--
A finprod of functions that do not vanish locally does not vanish locally.
-/
lemma meromorphicOrderAt_finprod_ne_top {x : 𝕜} {ι : Type*} {F : ι → 𝕜 → 𝕜}
    (h₁ : ∀ c, MeromorphicAt (F c) x) (h₂ : ∀ c, meromorphicOrderAt (F c) x ≠ ⊤) :
    meromorphicOrderAt (∏ᶠ c, F c) x ≠ ⊤ := by
  classical
  by_cases hF : F.HasFiniteMulSupport
  · simpa [finprod_eq_prod F hF, meromorphicOrderAt_prod (fun x _ ↦ h₁ x)] using fun x _ ↦ h₂ x
  simp [finprod_of_not_hasFiniteMulSupport hF]

/-- The order multiplies by `n` when taking a meromorphic function to its `n`th power. -/
@[to_fun] theorem meromorphicOrderAt_pow {f : 𝕜 → 𝕜} {x : 𝕜} (hf : MeromorphicAt f x) {n : ℕ} :
    meromorphicOrderAt (f ^ n) x = n * meromorphicOrderAt f x := by
  induction n
  case zero =>
    simp only [pow_zero, CharP.cast_eq_zero, zero_mul]
    rw [← WithTop.coe_zero, meromorphicOrderAt_eq_int_iff]
    · exact ⟨1, analyticAt_const, by simp⟩
    · apply MeromorphicAt.const
  case succ n hn =>
    simp only [pow_add, pow_one, meromorphicOrderAt_mul (hf.pow n) hf, hn, Nat.cast_add,
      Nat.cast_one]
    cases meromorphicOrderAt f x
    · aesop
    · norm_cast
      simp only [Nat.cast_add, Nat.cast_one]
      ring

/-- The order multiplies by `n` when taking a meromorphic function to its `n`th power. -/
@[to_fun] theorem meromorphicOrderAt_zpow {f : 𝕜 → 𝕜} {x : 𝕜} (hf : MeromorphicAt f x) {n : ℤ} :
    meromorphicOrderAt (f ^ n) x = n * meromorphicOrderAt f x := by
  -- Trivial case: n = 0
  by_cases hn : n = 0
  · simp only [hn, zpow_zero, WithTop.coe_zero, zero_mul]
    rw [← WithTop.coe_zero, meromorphicOrderAt_eq_int_iff]
    · exact ⟨1, analyticAt_const, by simp⟩
    · apply MeromorphicAt.const
  -- Trivial case: f locally zero
  by_cases h : meromorphicOrderAt f x = ⊤
  · simp only [h, ne_eq, WithTop.coe_eq_zero, hn, not_false_eq_true, WithTop.mul_top]
    rw [meromorphicOrderAt_eq_top_iff] at *
    filter_upwards [h]
    intro y hy
    simp [hy, zero_zpow n hn]
  -- General case
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOrderAt_ne_top_iff hf).1 h
  rw [← WithTop.coe_untop₀_of_ne_top h, ← WithTop.coe_mul,
    meromorphicOrderAt_eq_int_iff (hf.zpow n)]
  use g ^ n, h₁g.zpow h₂g
  constructor
  · simp_all [zpow_eq_zero_iff hn]
  · filter_upwards [h₃g]
    intro y hy
    rw [Pi.pow_apply, hy, smul_eq_mul, mul_zpow]
    congr 1
    rw [mul_comm, zpow_mul]

/-- The order of the inverse is the negative of the order. -/
@[to_fun] theorem meromorphicOrderAt_inv {f : 𝕜 → 𝕜} :
    meromorphicOrderAt (f⁻¹) x = -meromorphicOrderAt f x := by
  by_cases hf : MeromorphicAt f x; swap
  · have : ¬ MeromorphicAt (f⁻¹) x := by
      contrapose hf
      simpa using hf.inv
    simp [hf, this]
  by_cases h₂f : meromorphicOrderAt f x = ⊤
  · rw [h₂f, ← LinearOrderedAddCommGroupWithTop.neg_top, neg_neg]
    rw [meromorphicOrderAt_eq_top_iff] at *
    filter_upwards [h₂f]
    simp
  lift meromorphicOrderAt f x to ℤ using h₂f with a ha
  apply (meromorphicOrderAt_eq_int_iff hf.inv).2
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOrderAt_eq_int_iff hf).1 ha.symm
  use g⁻¹, h₁g.inv h₂g, inv_eq_zero.not.2 h₂g
  rw [eventually_nhdsWithin_iff] at *
  filter_upwards [h₃g]
  intro _ h₁a h₂a
  simp only [Pi.inv_apply, h₁a h₂a, smul_eq_mul, mul_inv_rev, zpow_neg]
  ring

/--
The order of a quotient is the difference of the orders.
-/
@[to_fun] theorem meromorphicOrderAt_div {f g : 𝕜 → 𝕜} (hf : MeromorphicAt f x)
    (hg : MeromorphicAt g x) :
    meromorphicOrderAt (f / g) x = meromorphicOrderAt f x - meromorphicOrderAt g x := by
  rw [div_eq_mul_inv, meromorphicOrderAt_mul hf hg.inv, meromorphicOrderAt_inv, sub_eq_add_neg]

/--
Adding a locally vanishing function does not change the order.
-/
@[simp]
theorem meromorphicOrderAt_add_of_top_left
    {f₁ f₂ : 𝕜 → E} {x : 𝕜} (hf₁ : meromorphicOrderAt f₁ x = ⊤) :
    meromorphicOrderAt (f₁ + f₂) x = meromorphicOrderAt f₂ x := by
  rw [meromorphicOrderAt_congr]
  filter_upwards [meromorphicOrderAt_eq_top_iff.1 hf₁] with z hz
  simp_all

/--
Adding a locally vanishing function does not change the order.
-/
@[simp]
theorem meromorphicOrderAt_add_of_top_right
    {f₁ f₂ : 𝕜 → E} {x : 𝕜} (hf₂ : meromorphicOrderAt f₂ x = ⊤) :
    meromorphicOrderAt (f₁ + f₂) x = meromorphicOrderAt f₁ x := by
  rw [add_comm, meromorphicOrderAt_add_of_top_left hf₂]

/--
The order of a sum is at least the minimum of the orders of the summands.
-/
theorem meromorphicOrderAt_add (hf₁ : MeromorphicAt f₁ x) (hf₂ : MeromorphicAt f₂ x) :
    min (meromorphicOrderAt f₁ x) (meromorphicOrderAt f₂ x) ≤ meromorphicOrderAt (f₁ + f₂) x := by
  -- Handle the trivial cases where one of the orders equals ⊤
  by_cases h₂f₁ : meromorphicOrderAt f₁ x = ⊤
  · rw [h₂f₁, min_top_left, meromorphicOrderAt_congr]
    filter_upwards [meromorphicOrderAt_eq_top_iff.1 h₂f₁]
    simp
  by_cases h₂f₂ : meromorphicOrderAt f₂ x = ⊤
  · simp only [h₂f₂, le_top, inf_of_le_left]
    rw [meromorphicOrderAt_congr]
    filter_upwards [meromorphicOrderAt_eq_top_iff.1 h₂f₂]
    simp
  -- General case
  lift meromorphicOrderAt f₁ x to ℤ using h₂f₁ with n₁ hn₁
  lift meromorphicOrderAt f₂ x to ℤ using h₂f₂ with n₂ hn₂
  obtain ⟨g₁, h₁g₁, h₂g₁, h₃g₁⟩ := (meromorphicOrderAt_eq_int_iff hf₁).1 hn₁.symm
  obtain ⟨g₂, h₁g₂, h₂g₂, h₃g₂⟩ := (meromorphicOrderAt_eq_int_iff hf₂).1 hn₂.symm
  let n := min n₁ n₂
  let g := (fun z ↦ (z - x) ^ (n₁ - n)) • g₁ + (fun z ↦ (z - x) ^ (n₂ - n)) • g₂
  have h₁g : AnalyticAt 𝕜 g x := by
    apply AnalyticAt.add
    · apply (AnalyticAt.zpow_nonneg (by fun_prop) (sub_nonneg.2 (min_le_left n₁ n₂))).smul h₁g₁
    apply (AnalyticAt.zpow_nonneg (by fun_prop) (sub_nonneg.2 (min_le_right n₁ n₂))).smul h₁g₂
  have : f₁ + f₂ =ᶠ[𝓝[≠] x] ((· - x) ^ n) • g := by
    filter_upwards [h₃g₁, h₃g₂, self_mem_nhdsWithin]
    simp_all [g, ← smul_assoc, ← zpow_add', sub_ne_zero]
  have t₀ : MeromorphicAt ((· - x) ^ n) x := by fun_prop
  have t₁ : meromorphicOrderAt ((· - x) ^ n) x = n :=
    (meromorphicOrderAt_eq_int_iff t₀).2 ⟨1, analyticAt_const, by simp⟩
  rw [meromorphicOrderAt_congr this, meromorphicOrderAt_smul t₀ h₁g.meromorphicAt, t₁]
  exact le_add_of_nonneg_right h₁g.meromorphicOrderAt_nonneg

/--
Helper lemma for `meromorphicOrderAt_add_of_ne`.
-/
lemma meromorphicOrderAt_add_eq_left_of_lt (hf₂ : MeromorphicAt f₂ x)
    (h : meromorphicOrderAt f₁ x < meromorphicOrderAt f₂ x) :
    meromorphicOrderAt (f₁ + f₂) x = meromorphicOrderAt f₁ x := by
  by_cases hf₁ : MeromorphicAt f₁ x; swap
  · have : ¬ (MeromorphicAt (f₁ + f₂) x) := by
      contrapose hf₁
      simpa using hf₁.sub hf₂
    simp [this, hf₁]
  -- Trivial case: f₂ vanishes identically around z₀
  by_cases h₁f₂ : meromorphicOrderAt f₂ x = ⊤
  · rw [meromorphicOrderAt_congr]
    filter_upwards [meromorphicOrderAt_eq_top_iff.1 h₁f₂]
    simp
  -- General case
  lift meromorphicOrderAt f₂ x to ℤ using h₁f₂ with n₂ hn₂
  lift meromorphicOrderAt f₁ x to ℤ using h.ne_top with n₁ hn₁
  obtain ⟨g₁, h₁g₁, h₂g₁, h₃g₁⟩ := (meromorphicOrderAt_eq_int_iff hf₁).1 hn₁.symm
  obtain ⟨g₂, h₁g₂, h₂g₂, h₃g₂⟩ := (meromorphicOrderAt_eq_int_iff hf₂).1 hn₂.symm
  rw [meromorphicOrderAt_eq_int_iff (hf₁.add hf₂)]
  refine ⟨g₁ + (· - x) ^ (n₂ - n₁) • g₂, ?_, ?_, ?_⟩
  · apply h₁g₁.add (AnalyticAt.smul _ h₁g₂)
    apply AnalyticAt.zpow_nonneg (by fun_prop)
      (sub_nonneg.2 (le_of_lt (WithTop.coe_lt_coe.1 h)))
  · simpa [zero_zpow _ <| sub_ne_zero.mpr (WithTop.coe_lt_coe.1 h).ne']
  · filter_upwards [h₃g₁, h₃g₂, self_mem_nhdsWithin]
    simp_all [smul_add, ← smul_assoc, ← zpow_add', sub_ne_zero]

/--
Helper lemma for `meromorphicOrderAt_add_of_ne`.
-/
lemma meromorphicOrderAt_add_eq_right_of_lt (hf₁ : MeromorphicAt f₁ x)
    (h : meromorphicOrderAt f₂ x < meromorphicOrderAt f₁ x) :
    meromorphicOrderAt (f₁ + f₂) x = meromorphicOrderAt f₂ x := by
  rw [add_comm]
  exact meromorphicOrderAt_add_eq_left_of_lt hf₁ h

/--
If two meromorphic functions have unequal orders, then the order of their sum is
exactly the minimum of the orders of the summands.
-/
theorem meromorphicOrderAt_add_of_ne
    (hf₁ : MeromorphicAt f₁ x) (hf₂ : MeromorphicAt f₂ x)
    (h : meromorphicOrderAt f₁ x ≠ meromorphicOrderAt f₂ x) :
    meromorphicOrderAt (f₁ + f₂) x = min (meromorphicOrderAt f₁ x) (meromorphicOrderAt f₂ x) := by
  rcases lt_or_lt_iff_ne.mpr h with h | h
  · simpa [h.le] using meromorphicOrderAt_add_eq_left_of_lt hf₂ h
  · simpa [h.le] using meromorphicOrderAt_add_eq_right_of_lt hf₁ h

/-!
## Level Sets of the Order Function
-/

namespace MeromorphicOn

variable {U : Set 𝕜}

/-- The set where a meromorphic function has infinite order is clopen in its domain of meromorphy.
-/
theorem isClopen_setOf_meromorphicOrderAt_eq_top (hf : MeromorphicOn f U) :
    IsClopen { u : U | meromorphicOrderAt f u = ⊤ } := by
  constructor
  · rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro z hz
    rcases (hf z.1 z.2).eventually_eq_zero_or_eventually_ne_zero with h | h
    · -- Case: f is locally zero in a punctured neighborhood of z
      rw [← meromorphicOrderAt_eq_top_iff] at h
      tauto
    · -- Case: f is locally nonzero in a punctured neighborhood of z
      obtain ⟨t', h₁t', h₂t', h₃t'⟩ := eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 h)
      use Subtype.val ⁻¹' t'
      constructor
      · intro w hw
        push _ ∈ _
        by_cases h₁w : w = z
        · rwa [h₁w]
        · rw [meromorphicOrderAt_eq_top_iff, not_eventually]
          apply Filter.Eventually.frequently
          rw [eventually_nhdsWithin_iff, eventually_nhds_iff]
          use t' \ {z.1}, fun y h₁y h₂y ↦ h₁t' y h₁y.1 h₁y.2, h₂t'.sdiff isClosed_singleton, hw,
            mem_singleton_iff.not.2 (Subtype.coe_ne_coe.mpr h₁w)
      · exact ⟨isOpen_induced h₂t', h₃t'⟩
  · apply isOpen_iff_forall_mem_open.mpr
    intro z hz
    conv =>
      arg 1; intro; left; right; arg 1; intro
      rw [meromorphicOrderAt_eq_top_iff, eventually_nhdsWithin_iff, eventually_nhds_iff]
    simp only [mem_setOf_eq] at hz
    rw [meromorphicOrderAt_eq_top_iff, eventually_nhdsWithin_iff, eventually_nhds_iff] at hz
    obtain ⟨t', h₁t', h₂t', h₃t'⟩ := hz
    use Subtype.val ⁻¹' t'
    simp only [mem_compl_iff, mem_singleton_iff, isOpen_induced h₂t', mem_preimage,
      h₃t', and_self, and_true]
    intro w hw
    simp only [mem_setOf_eq]
    -- Trivial case: w = z
    by_cases h₁w : w = z
    · rw [h₁w]
      tauto
    -- Nontrivial case: w ≠ z
    use t' \ {z.1}, fun y h₁y _ ↦ h₁t' y (mem_of_mem_diff h₁y) (mem_of_mem_inter_right h₁y)
    constructor
    · exact h₂t'.sdiff isClosed_singleton
    · apply (mem_diff w).1
      exact ⟨hw, mem_singleton_iff.not.1 (Subtype.coe_ne_coe.2 h₁w)⟩

/--
On a connected set, there exists a point where a meromorphic function `f` has finite order iff `f`
has finite order at every point.

See `Meromorphic.exists_meromorphicOrderAt_ne_top_iff_forall` in file
`Mathlib/Analysis/Meromorphic/RCLike` for a related result assuming that `f` is meromorphic on all
of `𝕜`.
-/
theorem exists_meromorphicOrderAt_ne_top_iff_forall (hf : MeromorphicOn f U) (hU : IsConnected U) :
    (∃ u : U, meromorphicOrderAt f u ≠ ⊤) ↔ (∀ u : U, meromorphicOrderAt f u ≠ ⊤) := by
  constructor
  · intro h₂f
    have := isPreconnected_iff_preconnectedSpace.1 hU.isPreconnected
    rcases isClopen_iff.1 hf.isClopen_setOf_meromorphicOrderAt_eq_top with h | h
    · intro u
      have : u ∉ (∅ : Set U) := by exact fun a => a
      rw [← h] at this
      tauto
    · obtain ⟨u, hU⟩ := h₂f
      have : u ∈ univ := by trivial
      rw [← h] at this
      tauto
  · intro h₂f
    obtain ⟨v, hv⟩ := hU.nonempty
    use ⟨v, hv⟩, h₂f ⟨v, hv⟩

/--
Variant of `MeromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall`, with membership in lieu of
subtypes.
-/
theorem exists_meromorphicOrderAt_ne_top_iff_forall_mem (hf : MeromorphicOn f U)
    (hU : IsConnected U) :
    (∃ u ∈ U, meromorphicOrderAt f u ≠ ⊤) ↔ (∀ u ∈ U, meromorphicOrderAt f u ≠ ⊤) := by
  convert exists_meromorphicOrderAt_ne_top_iff_forall hf hU
  <;> simp

/-- On a preconnected set, a meromorphic function has finite order at one point if it has finite
order at another point. -/
theorem meromorphicOrderAt_ne_top_of_isPreconnected (hf : MeromorphicOn f U) {y : 𝕜}
    (hU : IsPreconnected U) (h₁x : x ∈ U) (hy : y ∈ U) (h₂x : meromorphicOrderAt f x ≠ ⊤) :
    meromorphicOrderAt f y ≠ ⊤ :=
  (hf.exists_meromorphicOrderAt_ne_top_iff_forall ⟨nonempty_of_mem h₁x, hU⟩).1
    (by use ⟨x, h₁x⟩) ⟨y, hy⟩

/-- If a function is meromorphic on a set `U`, then for each point in `U`, it is analytic at nearby
points in `U`. When the target space is complete, this can be strengthened to analyticity at all
nearby points, see `MeromorphicAt.eventually_analyticAt`. -/
theorem eventually_analyticAt (h : MeromorphicOn f U) (hx : x ∈ U) :
    ∀ᶠ y in 𝓝[U \ {x}] x, AnalyticAt 𝕜 f y := by
  /- At neighboring points in `U`, the function `f` is both meromorphic (by meromorphicity on `U`)
  and continuous (thanks to the formula for a meromorphic function around the point `x`), so it is
  analytic. -/
  have : ∀ᶠ y in 𝓝[U \ {x}] x, ContinuousAt f y := by
    have : U \ {x} ⊆ {x}ᶜ := by simp
    exact nhdsWithin_mono _ this (h x hx).eventually_continuousAt
  filter_upwards [this, self_mem_nhdsWithin] with y hy h'y
  exact (h y h'y.1).analyticAt hy

theorem eventually_analyticAt_or_mem_compl (h : MeromorphicOn f U) (hx : x ∈ U) :
    ∀ᶠ y in 𝓝[≠] x, AnalyticAt 𝕜 f y ∨ y ∈ Uᶜ := by
  have : {x}ᶜ = (U \ {x}) ∪ Uᶜ := by aesop (add simp Classical.em)
  rw [this, nhdsWithin_union]
  simp only [mem_compl_iff, eventually_sup]
  refine ⟨?_, ?_⟩
  · filter_upwards [h.eventually_analyticAt hx] with y hy using Or.inl hy
  · filter_upwards [self_mem_nhdsWithin] with y hy using Or.inr hy

/-- Meromorphic functions on `U` are analytic on `U`, outside of a discrete subset. -/
theorem analyticAt_mem_codiscreteWithin (hf : MeromorphicOn f U) :
    { x | AnalyticAt 𝕜 f x } ∈ Filter.codiscreteWithin U := by
  rw [mem_codiscreteWithin]
  intro x hx
  rw [Filter.disjoint_principal_right, ← Filter.eventually_mem_set]
  filter_upwards [hf.eventually_analyticAt_or_mem_compl hx] with y hy
  simp
  tauto

/-- The set where a meromorphic function has zero or infinite
order is codiscrete within its domain of meromorphicity. -/
theorem codiscrete_setOf_meromorphicOrderAt_eq_zero_or_top (hf : MeromorphicOn f U) :
    {u : U | meromorphicOrderAt f u = 0 ∨ meromorphicOrderAt f u = ⊤} ∈ Filter.codiscrete U := by
  rw [mem_codiscrete_subtype_iff_mem_codiscreteWithin, mem_codiscreteWithin]
  intro x hx
  rw [Filter.disjoint_principal_right]
  rcases (hf x hx).eventually_eq_zero_or_eventually_ne_zero with h₁f | h₁f
  · filter_upwards [eventually_eventually_nhdsWithin.2 h₁f] with a h₁a
    suffices ∀ᶠ (z : 𝕜) in 𝓝[≠] a, f z = 0 by
      simp +contextual [meromorphicOrderAt_eq_top_iff, this]
    obtain rfl | hax := eq_or_ne a x
    · exact h₁a
    rw [eventually_nhdsWithin_iff, eventually_nhds_iff] at h₁a ⊢
    obtain ⟨t, h₁t, h₂t, h₃t⟩ := h₁a
    use t \ {x}, fun y h₁y _ ↦ h₁t y h₁y.1 h₁y.2
    exact ⟨h₂t.sdiff isClosed_singleton, Set.mem_diff_of_mem h₃t hax⟩
  · filter_upwards [hf.eventually_analyticAt_or_mem_compl hx, h₁f] with a h₁a h'₁a
    simp only [mem_compl_iff, mem_diff, mem_image, mem_setOf_eq, Subtype.exists, exists_and_right,
      exists_eq_right, not_exists, not_or, not_and, not_forall, Decidable.not_not]
    rcases h₁a with h' | h'
    · simp +contextual [h'.meromorphicOrderAt_eq, h'.analyticOrderAt_eq_zero.2, h'₁a]
    · exact fun ha ↦ (h' ha).elim

end MeromorphicOn

section comp
/-!
## Order at a Point: Behaviour under Composition
-/
variable {x : 𝕜} {f : 𝕜 → E} {g : 𝕜 → 𝕜}

/-- If `g` is analytic at `x`, `f` is meromorphic at `g x`, and `g` is not locally constant near
`x`, the order of `f ∘ g` is the product of the orders of `f` and `g · - g x`. -/
lemma MeromorphicAt.meromorphicOrderAt_comp (hf : MeromorphicAt f (g x)) (hg : AnalyticAt 𝕜 g x)
    (hg_nc : ¬EventuallyConst g (𝓝 x)) :
    meromorphicOrderAt (f ∘ g) x =
      (meromorphicOrderAt f (g x)) * (analyticOrderAt (g · - g x) x).map Nat.cast := by
  -- First deal with the silly case that `f` is identically zero around `g x`.
  rcases eq_or_ne (meromorphicOrderAt f (g x)) ⊤ with hf' | hf'
  · rw [hf', WithTop.top_mul]
    · rw [meromorphicOrderAt_eq_top_iff] at hf' ⊢
      rw [Function.comp_def, ← eventually_map (P := (f · = 0))]
      exact EventuallyEq.filter_mono hf' (hg.map_nhdsNE hg_nc)
    · simp [(show AnalyticAt 𝕜 (g · - g x) x by fun_prop).analyticOrderAt_eq_zero]
  -- Now the interesting case. First unpack the data
  have hr := (WithTop.coe_untop₀_of_ne_top hf').symm
  rw [meromorphicOrderAt_ne_top_iff hf] at hf'
  set r := (meromorphicOrderAt f (g x)).untop₀
  rw [hr]
  -- Now write `f = (· - g x) ^ r • F` for `F` analytic and nonzero at `g x`
  obtain ⟨F, hFan, hFne, hFev⟩ := hf'
  have aux1 : f ∘ g =ᶠ[𝓝[≠] x] (g · - g x) ^ r • (F ∘ g) := hFev.comp_tendsto (hg.map_nhdsNE hg_nc)
  have aux2 : meromorphicOrderAt (F ∘ g) x = 0 := by
    rw [AnalyticAt.meromorphicOrderAt_eq (by fun_prop),
      analyticOrderAt_eq_zero.mpr (by exact .inr hFne), ENat.map_zero, CharP.cast_eq_zero,
      WithTop.coe_zero]
  rw [meromorphicOrderAt_congr aux1, meromorphicOrderAt_smul ?_ (AnalyticAt.meromorphicAt ?_),
    aux2, add_zero, meromorphicOrderAt_zpow, AnalyticAt.meromorphicOrderAt_eq] <;>
  fun_prop

/-- If `g` is analytic at `x`, and `g' x ≠ 0`, then the meromorphic order of
`f ∘ g` at `x` is the meromorphic order of `f` at `g x` (even if `f` is not meromorphic). -/
lemma meromorphicOrderAt_comp_of_deriv_ne_zero (hg : AnalyticAt 𝕜 g x) (hg' : deriv g x ≠ 0)
    [CompleteSpace 𝕜] [CharZero 𝕜] :
    meromorphicOrderAt (f ∘ g) x = meromorphicOrderAt f (g x) := by
  by_cases hf : MeromorphicAt f (g x)
  · have hgo : analyticOrderAt _ x = 1 := hg.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hg'
    rw [hf.meromorphicOrderAt_comp hg, hgo] <;>
    simp [eventuallyConst_iff_analyticOrderAt_sub_eq_top, hgo]
  · rw [meromorphicOrderAt_of_not_meromorphicAt hf, meromorphicOrderAt_of_not_meromorphicAt]
    rwa [meromorphicAt_comp_iff_of_deriv_ne_zero hg hg']

end comp

section smul

variable {g : 𝕜 → 𝕜}

lemma meromorphicOrderAt_smul_of_ne_zero (hg : AnalyticAt 𝕜 g x) (hg' : g x ≠ 0) :
    meromorphicOrderAt (g • f) x = meromorphicOrderAt f x := by
  by_cases hf : MeromorphicAt f x
  · simp [meromorphicOrderAt_smul hg.meromorphicAt hf, hg.meromorphicOrderAt_eq,
      hg.analyticOrderAt_eq_zero.mpr hg']
  · rw [meromorphicOrderAt_of_not_meromorphicAt hf, meromorphicOrderAt_of_not_meromorphicAt]
    rwa [meromorphicAt_smul_iff_of_ne_zero hg hg']

lemma meromorphicOrderAt_mul_of_ne_zero {f : 𝕜 → 𝕜} (hg : AnalyticAt 𝕜 g x) (hg' : g x ≠ 0) :
    meromorphicOrderAt (g * f) x = meromorphicOrderAt f x :=
  meromorphicOrderAt_smul_of_ne_zero hg hg'

end smul
