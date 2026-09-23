/-
Copyright (c) 2022 Vincent Beffara. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Beffara, Stefan Kebekus
-/
module

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Order.Filter.EventuallyConst
public import Mathlib.Topology.Perfect

/-!
# Principle of isolated zeros

This file proves the fact that the zeros of a non-constant analytic function of one variable are
isolated. It also introduces a little bit of API in the `HasFPowerSeriesAt` namespace that is useful
in this setup.

## Main results

* `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero` is the main statement that if a function is
  analytic at `z₀`, then either it is identically zero in a neighborhood of `z₀`, or it does not
  vanish in a punctured neighborhood of `z₀`.
* `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq` is the identity theorem for analytic
  functions: if a function `f` is analytic on a connected set `U` and is zero on a set with an
  accumulation point in `U` then `f` is identically `0` on `U`.

## Applications

* Vanishing of products of analytic functions, `eq_zero_or_eq_zero_of_smul_eq_zero`: If `f, g` are
  analytic on a neighbourhood of the preconnected open set `U`, and `f • g = 0` on `U`, then either
  `f = 0` on `U` or `g = 0` on `U`.
* Preimages of codiscrete sets, `AnalyticOnNhd.preimage_mem_codiscreteWithin`: if `f` is analytic
  on a neighbourhood of `U` and not locally constant, then the preimage of any subset codiscrete
  within `f '' U` is codiscrete within `U`.
-/

public section

open Filter Function Module Nat FormalMultilinearSeries EMetric Set

open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {s : E} {p q : FormalMultilinearSeries 𝕜 𝕜 E} {f g : 𝕜 → E} {n : ℕ} {z z₀ : 𝕜}

namespace HasSum

variable {a : ℕ → E}

theorem hasSum_at_zero (a : ℕ → E) : HasSum (fun n => (0 : 𝕜) ^ n • a n) (a 0) := by
  convert hasSum_single (α := E) 0 fun b h ↦ _ <;> simp [*]

theorem exists_hasSum_smul_of_apply_eq_zero (hs : HasSum (fun m => z ^ m • a m) s)
    (ha : ∀ k < n, a k = 0) : ∃ t : E, z ^ n • t = s ∧ HasSum (fun m => z ^ m • a (m + n)) t := by
  obtain rfl | hn := n.eq_zero_or_pos
  · simpa
  by_cases h : z = 0
  · have : s = 0 := hs.unique (by simpa [ha 0 hn, h] using hasSum_at_zero a)
    exact ⟨a n, by simp [h, hn.ne', this], by simpa [h] using hasSum_at_zero fun m => a (m + n)⟩
  · refine ⟨(z ^ n)⁻¹ • s, by match_scalars; field, ?_⟩
    have h1 : ∑ i ∈ Finset.range n, z ^ i • a i = 0 :=
      Finset.sum_eq_zero fun k hk => by simp [ha k (Finset.mem_range.mp hk)]
    have h2 : HasSum (fun m => z ^ (m + n) • a (m + n)) s := by
      simpa [h1] using (hasSum_nat_add_iff' n).mpr hs
    convert h2.const_smul (z⁻¹ ^ n) using 2 with x
    · match_scalars
      simp [field, pow_add]
    · simp only [inv_pow]

end HasSum

namespace HasFPowerSeriesAt

theorem has_fpower_series_dslope_fslope (hp : HasFPowerSeriesAt f p z₀) :
    HasFPowerSeriesAt (dslope f z₀) p.fslope z₀ := by
  have hpd : deriv f z₀ = p.coeff 1 := hp.deriv
  have hp0 : p.coeff 0 = f z₀ := hp.coeff_zero 1
  simp only [hasFPowerSeriesAt_iff, coeff_fslope] at hp ⊢
  refine hp.mono fun x hx => ?_
  by_cases h : x = 0
  · convert hasSum_single (α := E) 0 _ <;> intros <;> simp [*]
  · have hxx : ∀ n : ℕ, x⁻¹ * x ^ (n + 1) = x ^ n := fun n => by simp [field, _root_.pow_succ]
    suffices HasSum (fun n => x⁻¹ • x ^ (n + 1) • p.coeff (n + 1)) (x⁻¹ • (f (z₀ + x) - f z₀)) by
      simpa [dslope, slope, h, smul_smul, hxx] using this
    simpa [hp0] using ((hasSum_nat_add_iff' 1).mpr hx).const_smul x⁻¹

theorem has_fpower_series_iterate_dslope_fslope (n : ℕ) (hp : HasFPowerSeriesAt f p z₀) :
    HasFPowerSeriesAt ((swap dslope z₀)^[n] f) (fslope^[n] p) z₀ := by
  induction n generalizing f p with
  | zero => exact hp
  | succ n ih => simpa using ih (has_fpower_series_dslope_fslope hp)

theorem iterate_dslope_fslope_ne_zero (hp : HasFPowerSeriesAt f p z₀) (h : p ≠ 0) :
    (swap dslope z₀)^[p.order] f z₀ ≠ 0 := by
  rw [← coeff_zero (has_fpower_series_iterate_dslope_fslope p.order hp) 1]
  simpa [coeff_eq_zero] using apply_order_ne_zero h

theorem eq_pow_order_mul_iterate_dslope (hp : HasFPowerSeriesAt f p z₀) :
    ∀ᶠ z in 𝓝 z₀, f z = (z - z₀) ^ p.order • (swap dslope z₀)^[p.order] f z := by
  have hq := hasFPowerSeriesAt_iff'.mp (has_fpower_series_iterate_dslope_fslope p.order hp)
  filter_upwards [hq, hasFPowerSeriesAt_iff'.mp hp] with x hx1 hx2
  have : ∀ k < p.order, p.coeff k = 0 := fun k hk => by
    simpa [coeff_eq_zero] using apply_eq_zero_of_lt_order hk
  obtain ⟨s, hs1, hs2⟩ := HasSum.exists_hasSum_smul_of_apply_eq_zero hx2 this
  convert hs1.symm
  simp only [coeff_iterate_fslope] at hx1
  exact hx1.unique hs2

theorem locally_ne_zero (hp : HasFPowerSeriesAt f p z₀) (h : p ≠ 0) : ∀ᶠ z in 𝓝[≠] z₀, f z ≠ 0 := by
  rw [eventually_nhdsWithin_iff]
  have h2 := (has_fpower_series_iterate_dslope_fslope p.order hp).continuousAt
  have h3 := h2.eventually_ne (iterate_dslope_fslope_ne_zero hp h)
  filter_upwards [eq_pow_order_mul_iterate_dslope hp, h3] with z e1 e2 e3
  simpa [e1, e2, e3] using pow_ne_zero p.order (sub_ne_zero.mpr e3)

theorem locally_zero_iff (hp : HasFPowerSeriesAt f p z₀) : (∀ᶠ z in 𝓝 z₀, f z = 0) ↔ p = 0 :=
  ⟨fun hf => hp.eq_zero_of_eventually hf, fun h => eventually_eq_zero (𝕜 := 𝕜) (by rwa [h] at hp)⟩

end HasFPowerSeriesAt

namespace AnalyticAt

/-- The *principle of isolated zeros* for an analytic function, local version: if a function is
analytic at `z₀`, then either it is identically zero in a neighborhood of `z₀`, or it does not
vanish in a punctured neighborhood of `z₀`. -/
theorem eventually_eq_zero_or_eventually_ne_zero (hf : AnalyticAt 𝕜 f z₀) :
    (∀ᶠ z in 𝓝 z₀, f z = 0) ∨ ∀ᶠ z in 𝓝[≠] z₀, f z ≠ 0 := by
  rcases hf with ⟨p, hp⟩
  by_cases h : p = 0
  · exact Or.inl (HasFPowerSeriesAt.eventually_eq_zero (by rwa [h] at hp))
  · exact Or.inr (hp.locally_ne_zero h)

theorem eventually_eq_or_eventually_ne (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀) :
    (∀ᶠ z in 𝓝 z₀, f z = g z) ∨ ∀ᶠ z in 𝓝[≠] z₀, f z ≠ g z := by
  simpa [sub_eq_zero] using (hf.sub hg).eventually_eq_zero_or_eventually_ne_zero

theorem frequently_zero_iff_eventually_zero {f : 𝕜 → E} {w : 𝕜} (hf : AnalyticAt 𝕜 f w) :
    (∃ᶠ z in 𝓝[≠] w, f z = 0) ↔ ∀ᶠ z in 𝓝 w, f z = 0 :=
  ⟨hf.eventually_eq_zero_or_eventually_ne_zero.resolve_right, fun h =>
    (h.filter_mono nhdsWithin_le_nhds).frequently⟩

theorem frequently_eq_iff_eventually_eq (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀) :
    (∃ᶠ z in 𝓝[≠] z₀, f z = g z) ↔ ∀ᶠ z in 𝓝 z₀, f z = g z := by
  simpa [sub_eq_zero] using frequently_zero_iff_eventually_zero (hf.sub hg)

/-- For a function `f` on `𝕜`, and `z₀ ∈ 𝕜`, there exists at most one `n` such that on a punctured
neighbourhood of `z₀` we have `f z = (z - z₀) ^ n • g z`, with `g` analytic and nonvanishing at
`z₀`. We formulate this with `n : ℤ`, and deduce the case `n : ℕ` later, for applications to
meromorphic functions. -/
lemma unique_eventuallyEq_zpow_smul_nonzero {m n : ℤ}
    (hm : ∃ g, AnalyticAt 𝕜 g z₀ ∧ g z₀ ≠ 0 ∧ ∀ᶠ z in 𝓝[≠] z₀, f z = (z - z₀) ^ m • g z)
    (hn : ∃ g, AnalyticAt 𝕜 g z₀ ∧ g z₀ ≠ 0 ∧ ∀ᶠ z in 𝓝[≠] z₀, f z = (z - z₀) ^ n • g z) :
    m = n := by
  wlog! h_le : n ≤ m generalizing m n
  · exact ((this hn hm) h_le.le).symm
  let ⟨g, hg_an, _, hg_eq⟩ := hm
  let ⟨j, hj_an, hj_ne, hj_eq⟩ := hn
  contrapose! hj_ne
  have : ∃ᶠ z in 𝓝[≠] z₀, j z = (z - z₀) ^ (m - n) • g z := by
    apply Filter.Eventually.frequently
    rw [eventually_nhdsWithin_iff] at hg_eq hj_eq ⊢
    filter_upwards [hg_eq, hj_eq] with z hfz hfz' hz
    rw [← add_sub_cancel_left n m, add_sub_assoc, zpow_add₀ <| sub_ne_zero.mpr hz, mul_smul,
      hfz' hz, smul_right_inj <| zpow_ne_zero _ <| sub_ne_zero.mpr hz] at hfz
    exact hfz hz
  rw [frequently_eq_iff_eventually_eq hj_an] at this
  · rw [EventuallyEq.eq_of_nhds this, sub_self, zero_zpow _ (sub_ne_zero.mpr hj_ne), zero_smul]
  conv => enter [2, z, 1]; rw [← Int.toNat_sub_of_le h_le, zpow_natCast]
  exact ((analyticAt_id.sub analyticAt_const).pow _).smul hg_an

/-- For a function `f` on `𝕜`, and `z₀ ∈ 𝕜`, there exists at most one `n` such that on a
neighbourhood of `z₀` we have `f z = (z - z₀) ^ n • g z`, with `g` analytic and nonvanishing at
`z₀`. -/
lemma unique_eventuallyEq_pow_smul_nonzero {m n : ℕ}
    (hm : ∃ g, AnalyticAt 𝕜 g z₀ ∧ g z₀ ≠ 0 ∧ ∀ᶠ z in 𝓝 z₀, f z = (z - z₀) ^ m • g z)
    (hn : ∃ g, AnalyticAt 𝕜 g z₀ ∧ g z₀ ≠ 0 ∧ ∀ᶠ z in 𝓝 z₀, f z = (z - z₀) ^ n • g z) :
    m = n := by
  simp_rw [← zpow_natCast] at hm hn
  exact Int.ofNat_inj.mp <| unique_eventuallyEq_zpow_smul_nonzero
    (let ⟨g, h₁, h₂, h₃⟩ := hm; ⟨g, h₁, h₂, h₃.filter_mono nhdsWithin_le_nhds⟩)
    (let ⟨g, h₁, h₂, h₃⟩ := hn; ⟨g, h₁, h₂, h₃.filter_mono nhdsWithin_le_nhds⟩)

/-- If `f` is analytic at `z₀`, then exactly one of the following two possibilities occurs: either
`f` vanishes identically near `z₀`, or locally around `z₀` it has the form `z ↦ (z - z₀) ^ n • g z`
for some `n` and some `g` which is analytic and non-vanishing at `z₀`. -/
theorem exists_eventuallyEq_pow_smul_nonzero_iff (hf : AnalyticAt 𝕜 f z₀) :
    (∃ (n : ℕ), ∃ (g : 𝕜 → E), AnalyticAt 𝕜 g z₀ ∧ g z₀ ≠ 0 ∧
    ∀ᶠ z in 𝓝 z₀, f z = (z - z₀) ^ n • g z) ↔ (¬∀ᶠ z in 𝓝 z₀, f z = 0) := by
  constructor
  · rintro ⟨n, g, hg_an, hg_ne, hg_eq⟩
    contrapose hg_ne
    apply EventuallyEq.eq_of_nhds
    rw [EventuallyEq, ← AnalyticAt.frequently_eq_iff_eventually_eq hg_an analyticAt_const]
    refine (eventually_nhdsWithin_iff.mpr ?_).frequently
    filter_upwards [hg_eq, hg_ne] with z hf_eq hf0 hz
    rwa [hf0, eq_comm, smul_eq_zero_iff_right] at hf_eq
    exact pow_ne_zero _ (sub_ne_zero.mpr hz)
  · intro hf_ne
    rcases hf with ⟨p, hp⟩
    exact ⟨p.order, _, ⟨_, hp.has_fpower_series_iterate_dslope_fslope p.order⟩,
      hp.iterate_dslope_fslope_ne_zero (hf_ne.imp hp.locally_zero_iff.mpr),
      hp.eq_pow_order_mul_iterate_dslope⟩

end AnalyticAt

namespace AnalyticOnNhd

variable {U : Set 𝕜}

/-- The *principle of isolated zeros* for an analytic function, global version: if a function is
analytic on a connected set `U` and vanishes in arbitrary neighborhoods of a point `z₀ ∈ U`, then
it is identically zero in `U`.
For higher-dimensional versions requiring that the function vanishes in a neighborhood of `z₀`,
see `AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero`. -/
theorem eqOn_zero_of_preconnected_of_frequently_eq_zero (hf : AnalyticOnNhd 𝕜 f U)
    (hU : IsPreconnected U) (h₀ : z₀ ∈ U) (hfw : ∃ᶠ z in 𝓝[≠] z₀, f z = 0) : EqOn f 0 U :=
  hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU h₀
    ((hf z₀ h₀).frequently_zero_iff_eventually_zero.1 hfw)

theorem eqOn_zero_or_eventually_ne_zero_of_preconnected (hf : AnalyticOnNhd 𝕜 f U)
    (hU : IsPreconnected U) : EqOn f 0 U ∨ ∀ᶠ x in codiscreteWithin U, f x ≠ 0 := by
  simp only [or_iff_not_imp_right, ne_eq, eventually_iff, mem_codiscreteWithin,
    disjoint_principal_right, not_forall]
  rintro ⟨x, hx, hx2⟩
  refine hf.eqOn_zero_of_preconnected_of_frequently_eq_zero hU hx fun nh ↦ hx2 ?_
  filter_upwards [nh] with a ha
  simp_all

theorem eqOn_zero_of_preconnected_of_mem_closure (hf : AnalyticOnNhd 𝕜 f U) (hU : IsPreconnected U)
    (h₀ : z₀ ∈ U) (hfz₀ : z₀ ∈ closure ({z | f z = 0} \ {z₀})) : EqOn f 0 U :=
  hf.eqOn_zero_of_preconnected_of_frequently_eq_zero hU h₀
    (mem_closure_ne_iff_frequently_within.mp hfz₀)

/-- The *identity principle* for analytic functions, global version: if two functions are
analytic on a connected set `U` and coincide at points which accumulate to a point `z₀ ∈ U`, then
they coincide globally in `U`.
For higher-dimensional versions requiring that the functions coincide in a neighborhood of `z₀`,
see `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`. -/
theorem eqOn_of_preconnected_of_frequently_eq (hf : AnalyticOnNhd 𝕜 f U) (hg : AnalyticOnNhd 𝕜 g U)
    (hU : IsPreconnected U) (h₀ : z₀ ∈ U) (hfg : ∃ᶠ z in 𝓝[≠] z₀, f z = g z) : EqOn f g U := by
  have hfg' : ∃ᶠ z in 𝓝[≠] z₀, (f - g) z = 0 :=
    hfg.mono fun z h => by rw [Pi.sub_apply, h, sub_self]
  simpa [sub_eq_zero] using fun z hz =>
    (hf.sub hg).eqOn_zero_of_preconnected_of_frequently_eq_zero hU h₀ hfg' hz

theorem eqOn_or_eventually_ne_of_preconnected (hf : AnalyticOnNhd 𝕜 f U) (hg : AnalyticOnNhd 𝕜 g U)
    (hU : IsPreconnected U) : EqOn f g U ∨ ∀ᶠ x in codiscreteWithin U, f x ≠ g x :=
  (eqOn_zero_or_eventually_ne_zero_of_preconnected (hf.sub hg) hU).imp
    (fun h _ hx ↦ eq_of_sub_eq_zero (h hx))
    (by simp only [Pi.sub_apply, ne_eq, sub_eq_zero, imp_self])

theorem eqOn_of_preconnected_of_mem_closure (hf : AnalyticOnNhd 𝕜 f U) (hg : AnalyticOnNhd 𝕜 g U)
    (hU : IsPreconnected U) (h₀ : z₀ ∈ U) (hfg : z₀ ∈ closure ({z | f z = g z} \ {z₀})) :
    EqOn f g U :=
  hf.eqOn_of_preconnected_of_frequently_eq hg hU h₀ (mem_closure_ne_iff_frequently_within.mp hfg)

/-- The *identity principle* for analytic functions, global version: if two functions on a normed
field `𝕜` are analytic everywhere and coincide at points which accumulate to a point `z₀`, then
they coincide globally.
For higher-dimensional versions requiring that the functions coincide in a neighborhood of `z₀`,
see `AnalyticOnNhd.eq_of_eventuallyEq`. -/
theorem eq_of_frequently_eq [ConnectedSpace 𝕜] (hf : AnalyticOnNhd 𝕜 f univ)
    (hg : AnalyticOnNhd 𝕜 g univ) (hfg : ∃ᶠ z in 𝓝[≠] z₀, f z = g z) : f = g :=
  funext fun x =>
    eqOn_of_preconnected_of_frequently_eq hf hg isPreconnected_univ (mem_univ z₀) hfg (mem_univ x)

section Mul
/-!
### Vanishing of products of analytic functions
-/

variable {A : Type*} [NormedRing A] [IsDomain A] [NormedAlgebra 𝕜 A]
  {B : Type*} [NormedAddCommGroup B] [NormedSpace 𝕜 B] [Module A B]

/-- If `f, g` are analytic on a neighbourhood of the preconnected open set `U`, and `f • g = 0`
on `U`, then either `f = 0` on `U` or `g = 0` on `U`. -/
lemma eq_zero_or_eq_zero_of_smul_eq_zero [IsTorsionFree A B]
    {f : 𝕜 → A} {g : 𝕜 → B} (hf : AnalyticOnNhd 𝕜 f U) (hg : AnalyticOnNhd 𝕜 g U)
    (hfg : ∀ z ∈ U, f z • g z = 0) (hU : IsPreconnected U) :
    (∀ z ∈ U, f z = 0) ∨ (∀ z ∈ U, g z = 0) := by
  -- We want to apply `IsPreconnected.preperfect_of_nontrivial` which requires `U` to have at least
  -- two elements. So we need to dispose of the cases `#U = 0` and `#U = 1` first.
  by_cases hU' : U = ∅
  · simp [hU']
  obtain ⟨z, hz⟩ : ∃ z, z ∈ U := nonempty_iff_ne_empty.mpr hU'
  by_cases hU'' : U = {z}
  · simpa [hU''] using hfg z hz
  apply (nontrivial_iff_ne_singleton hz).mpr at hU''
  -- Now connectedness implies that `z` is an accumulation point of `U`, so at least one of
  -- `f` and `g` must vanish frequently in a neighbourhood of `z`.
  have : ∃ᶠ w in 𝓝[≠] z, w ∈ U :=
    frequently_mem_iff_neBot.mpr <| hU.preperfect_of_nontrivial hU'' z hz
  have : ∃ᶠ w in 𝓝[≠] z, f w = 0 ∨ g w = 0 :=
    this.mp <| by filter_upwards with w hw using smul_eq_zero.mp (hfg w hw)
  cases frequently_or_distrib.mp this with
  | inl h => exact Or.inl <| hf.eqOn_zero_of_preconnected_of_frequently_eq_zero hU hz h
  | inr h => exact Or.inr <| hg.eqOn_zero_of_preconnected_of_frequently_eq_zero hU hz h

/-- If `f, g` are analytic on a neighbourhood of the preconnected open set `U`, and `f * g = 0`
on `U`, then either `f = 0` on `U` or `g = 0` on `U`. -/
lemma eq_zero_or_eq_zero_of_mul_eq_zero {f g : 𝕜 → A} (hf : AnalyticOnNhd 𝕜 f U)
    (hg : AnalyticOnNhd 𝕜 g U) (hfg : ∀ z ∈ U, f z * g z = 0) (hU : IsPreconnected U) :
    (∀ z ∈ U, f z = 0) ∨ (∀ z ∈ U, g z = 0) :=
  eq_zero_or_eq_zero_of_smul_eq_zero hf hg hfg hU

end Mul
end AnalyticOnNhd

/-!
### Preimages of codiscrete sets
-/

section PreimgCodiscrete

/-- Preimages of codiscrete sets, local version: if `f` is analytic at `x` and not locally constant,
then the preimage of any punctured neighbourhood of `f x` is a punctured neighbourhood of `x`. -/
theorem AnalyticAt.preimage_of_nhdsNE {x : 𝕜} {f : 𝕜 → E} {s : Set E} (hfx : AnalyticAt 𝕜 f x)
    (h₂f : ¬EventuallyConst f (𝓝 x)) (hs : s ∈ 𝓝[≠] f x) :
    f ⁻¹' s ∈ 𝓝[≠] x := by
  have : ∀ᶠ (z : 𝕜) in 𝓝 x, f z ∈ insert (f x) s := by
    filter_upwards [hfx.continuousAt.preimage_mem_nhds (insert_mem_nhds_iff.2 hs)]
    tauto
  contrapose h₂f with h
  rw [eventuallyConst_iff_exists_eventuallyEq]
  use f x
  rw [EventuallyEq, ← hfx.frequently_eq_iff_eventually_eq analyticAt_const]
  apply ((frequently_imp_distrib_right.2 h).and_eventually
    (eventually_nhdsWithin_of_eventually_nhds this)).mono
  intro z ⟨h₁z, h₂z⟩
  rw [Set.mem_insert_iff] at h₂z
  tauto

/-- Preimages of codiscrete sets, local filter version: if `f` is analytic at `x` and not locally
constant, then the push-forward of the punctured neighbourhood filter `𝓝[≠] x` is less than or
equal to the punctured neighbourhood filter `𝓝[≠] f x`. -/
theorem AnalyticAt.map_nhdsNE {x : 𝕜} {f : 𝕜 → E} (hfx : AnalyticAt 𝕜 f x)
    (h₂f : ¬EventuallyConst f (𝓝 x)) :
    (𝓝[≠] x).map f ≤ (𝓝[≠] f x) := fun _ hs ↦ mem_map.1 (preimage_of_nhdsNE hfx h₂f hs)

/--
Preimages of codiscrete sets: if `f` is analytic on a neighbourhood of `U` and not locally constant,
then the preimage of any subset codiscrete within `f '' U` is codiscrete within `U`.

See `AnalyticOnNhd.preimage_zero_mem_codiscreteWithin` for the special case that `s` is the
complement of zero. Applications might want to use the theorem `Filter.codiscreteWithin.mono`.
-/
theorem AnalyticOnNhd.preimage_mem_codiscreteWithin {U : Set 𝕜} {s : Set E} {f : 𝕜 → E}
    (hfU : AnalyticOnNhd 𝕜 f U) (h₂f : ∀ x ∈ U, ¬EventuallyConst f (𝓝 x))
    (hs : s ∈ codiscreteWithin (f '' U)) :
    f ⁻¹' s ∈ codiscreteWithin U := by
  simp_rw [mem_codiscreteWithin, disjoint_principal_right, Set.compl_diff] at *
  intro x hx
  apply mem_of_superset ((hfU x hx).preimage_of_nhdsNE (h₂f x hx) (hs (f x) (by tauto)))
  rw [preimage_union, preimage_compl]
  apply union_subset_union_right (f ⁻¹' s)
  intro x hx
  push _ ∈ _ at hx ⊢
  push Not at hx
  tauto

/-- Preimages of codiscrete sets, filter version: if `f` is analytic on a neighbourhood of `U` and
not locally constant, then the push-forward of the filter of sets codiscrete within `U` is less
than or equal to the filter of sets codiscrete within `f '' U`.

Applications might want to use the theorem `Filter.codiscreteWithin.mono`.
-/
theorem AnalyticOnNhd.map_codiscreteWithin {U : Set 𝕜} {f : 𝕜 → E}
    (hfU : AnalyticOnNhd 𝕜 f U) (h₂f : ∀ x ∈ U, ¬EventuallyConst f (𝓝 x)) :
    map f (codiscreteWithin U) ≤ (codiscreteWithin (f '' U)) :=
  fun _ hs ↦ mem_map.1 (preimage_mem_codiscreteWithin hfU h₂f hs)

end PreimgCodiscrete
