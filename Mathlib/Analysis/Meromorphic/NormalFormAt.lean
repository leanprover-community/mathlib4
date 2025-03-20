/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Meromorphic.Order

/-!
# Normal form of meromorphic functions and continuous extension

If a function `f` is meromorphic on `U` and if `g` differs from `f` only along a
set that is codiscrete within `U`, then `g` is likewise meromorphic. The set of
meromorphic functions is therefore huge, and `=ᶠ[codiscreteWithin U]` defines an
equivalence relation.

This file implements continuous extension to provide an API that allows picking
the 'unique best' representative of any given equivalence class, where 'best'
means that the representative can locally near any point `x` be written 'in
normal form', as `f =ᶠ[𝓝 x] fun z ↦ (z - x) ^ n • g` where `g` is analytic and
does not vanish at `x`.

## TODO

Establish the analogous notion `MeromorphicNFOn`.
-/

open Topology

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f : 𝕜 → E} {g : 𝕜 → 𝕜}
  {x : 𝕜}

/-!
# Normal form of meromorphic functions at a given point

## Definition and characterizations
-/

variable (f x) in
/-- A function is 'meromorphic in normal form' at `x` if it vanishes around `x`
or if it can locally be written as `fun z ↦ (z - x) ^ n • g` where `g` is
analytic and does not vanish at `x`. -/
def MeromorphicNFAt :=
  f =ᶠ[𝓝 x] 0 ∨
    ∃ (n : ℤ) (g : 𝕜 → E), AnalyticAt 𝕜 g x ∧ g x ≠ 0 ∧ f =ᶠ[𝓝 x] (· - x) ^ n • g

/-- A meromorphic function has normal form at `x` iff it is either analytic
there, or if it has a pole at `x` and takes the default value `0`. -/
theorem meromorphicNFAt_iff_analyticAt_or :
    MeromorphicNFAt f x ↔ AnalyticAt 𝕜 f x ∨ ∃ hf : MeromorphicAt f x, hf.order < 0 ∧ f x = 0 := by
  constructor
  · rintro (h | ⟨n, g, h₁g, h₂g, h₃g⟩)
    · simp [(analyticAt_congr h).2 analyticAt_const]
    · have hf : MeromorphicAt f x := by
        apply MeromorphicAt.congr _ (h₃g.filter_mono nhdsWithin_le_nhds).symm
        fun_prop
      have : hf.order = n := by
        rw [hf.order_eq_int_iff]
        use g, h₁g, h₂g
        exact eventually_nhdsWithin_of_eventually_nhds h₃g
      by_cases hn : 0 ≤ n
      · left
        rw [analyticAt_congr h₃g]
        apply (AnalyticAt.zpow_nonneg (by fun_prop) hn).smul h₁g
      · right
        use hf
        simp [this, WithTop.coe_lt_zero.2 (not_le.1 hn), h₃g.eq_of_nhds,
          zero_zpow n (ne_of_not_le hn).symm]
  · rintro (h | ⟨h₁, h₂, h₃⟩)
    · by_cases h₂f : h.order = ⊤
      · rw [AnalyticAt.order_eq_top_iff] at h₂f
        tauto
      · right
        use h.order.toNat
        have : h.order ≠ ⊤ := h₂f
        rw [← ENat.coe_toNat_eq_self, eq_comm, AnalyticAt.order_eq_nat_iff] at this
        obtain ⟨g, h₁g, h₂g, h₃g⟩ := this
        use g, h₁g, h₂g
        simpa
    · right
      lift h₁.order to ℤ using LT.lt.ne_top h₂ with n hn
      obtain ⟨g, h₁g, h₂g, h₃g⟩ := (h₁.order_eq_int_iff n).1 hn.symm
      use n, g, h₁g, h₂g
      filter_upwards [eventually_nhdsWithin_iff.1 h₃g]
      intro z hz
      by_cases h₁z : z = x
      · simp only [h₁z, h₂, Pi.smul_apply', Pi.pow_apply, sub_self]
        rw [h₃]
        apply (smul_eq_zero_of_left (zero_zpow n _) (g x)).symm
        by_contra hCon
        simp [hCon] at h₂
      · exact hz h₁z

/-!
## Relation to other properties of functions
-/

/-- If a function is meromorphic in normal form at `x`, then it is meromorphic at `x`. -/
theorem MeromorphicNFAt.meromorphicAt (hf : MeromorphicNFAt f x) :
    MeromorphicAt f x := by
  rw [meromorphicNFAt_iff_analyticAt_or] at hf
  rcases hf with h | h
  · exact h.meromorphicAt
  · obtain ⟨hf, _⟩ := h
    exact hf

/-- If a function is meromorphic in normal form at `x`, then it has non-negative order iff it is
analytic. -/
theorem MeromorphicNFAt.order_nonneg_iff_analyticAt (hf : MeromorphicNFAt f x) :
    0 ≤ hf.meromorphicAt.order ↔ AnalyticAt 𝕜 f x := by
  constructor <;> intro h₂f
  · rw [meromorphicNFAt_iff_analyticAt_or] at hf
    rcases hf with h | ⟨_, h₃f, _⟩
    · exact h
    · by_contra h'
      exact lt_irrefl 0 (lt_of_le_of_lt h₂f h₃f)
  · rw [h₂f.meromorphicAt_order]
    simp

/-- Analytic functions are meromorphic in normal form. -/
theorem AnalyticAt.meromorphicNFAt (hf : AnalyticAt 𝕜 f x) :
    MeromorphicNFAt f x := by
  simp [meromorphicNFAt_iff_analyticAt_or, hf]

/-- Meromorphic functions have normal form outside of a discrete subset in the domain of
meromorphicity. -/
theorem MeromorphicOn.meromorphicNFAt_mem_codiscreteWithin [CompleteSpace E] {U : Set 𝕜}
    (hf : MeromorphicOn f U) :
    { x | MeromorphicNFAt f x } ∈ Filter.codiscreteWithin U := by
  filter_upwards [hf.analyticAt_mem_codiscreteWithin] with _ ha
  exact ha.meromorphicNFAt

/-!
## Vanishing and order
-/

/-- If `f` is meromorphic in normal form at `x`, then `f` has order zero iff it does not vanish at
`x`.

See `AnalyticAt.order_eq_zero_iff` for an analogous statement about analytic functions. -/
theorem MeromorphicNFAt.order_eq_zero_iff (hf : MeromorphicNFAt f x) :
    hf.meromorphicAt.order = 0 ↔ f x ≠ 0 := by
  constructor
  · intro h₁f
    have h₂f := hf.order_nonneg_iff_analyticAt.1 (le_of_eq h₁f.symm)
    apply h₂f.order_eq_zero_iff.1
    apply (ENat.map_natCast_eq_zero (α := ℤ)).1
    rwa [h₂f.meromorphicAt_order] at h₁f
  · intro h
    rcases id hf with h₁ | ⟨n, g, h₁g, h₂g, h₃g⟩
    · have := h₁.eq_of_nhds
      tauto
    · have : n = 0 := by
        by_contra hContra
        have := h₃g.eq_of_nhds
        simp only [Pi.smul_apply', Pi.pow_apply, sub_self, zero_zpow n hContra, zero_smul] at this
        tauto
      simp only [this, zpow_zero, smul_eq_mul, one_mul] at h₃g
      apply (hf.meromorphicAt.order_eq_int_iff 0).2
      use g, h₁g, h₂g
      simp only [zpow_zero, smul_eq_mul, one_mul]
      exact h₃g.filter_mono nhdsWithin_le_nhds

/-!
## Local nature of the definition and local identity theorem
-/

/-- **Local identity theorem**: two meromorphic functions in normal form agree in a
neighborhood iff they agree in a pointed neighborhood.

See `ContinuousAt.eventuallyEq_nhdNE_iff_eventuallyEq_nhd` for the analogous
statement for continuous functions.
-/
theorem MeromorphicNFAt.eventuallyEq_nhdNE_iff_eventuallyEq_nhd {g : 𝕜 → E}
    (hf : MeromorphicNFAt f x) (hg : MeromorphicNFAt g x) :
    f =ᶠ[𝓝[≠] x] g ↔ f =ᶠ[𝓝 x] g := by
  constructor
  · intro h
    have t₀ := hf.meromorphicAt.order_congr h
    by_cases cs : hf.meromorphicAt.order = 0
    · rw [cs] at t₀
      have Z := (hf.order_nonneg_iff_analyticAt.1 (le_of_eq cs.symm)).continuousAt
      have W := (hg.order_nonneg_iff_analyticAt.1 (le_of_eq t₀)).continuousAt
      exact (Z.eventuallyEq_nhd_iff_eventuallyEq_nhdNE W).1 h
    · apply eventuallyEq_nhds_of_eventuallyEq_nhdsNE h
      let h₁f := cs
      rw [hf.order_eq_zero_iff] at h₁f
      let h₁g := cs
      rw [t₀, hg.order_eq_zero_iff] at h₁g
      simp only [not_not] at *
      rw [h₁f, h₁g]
  · exact (Filter.EventuallyEq.filter_mono · nhdsWithin_le_nhds)

/-- Meromorphicity in normal form is a local property. -/
theorem meromorphicNFAt_congr {g : 𝕜 → E} (hfg : f =ᶠ[𝓝 x] g) :
    MeromorphicNFAt f x ↔ MeromorphicNFAt g x := by
  constructor
  · rintro (h | ⟨n, h, h₁h, h₂h, h₃h⟩)
    · exact .inl (hfg.symm.trans h)
    · exact .inr ⟨n, h, h₁h, h₂h, hfg.symm.trans h₃h⟩
  · rintro (h | ⟨n, h, h₁h, h₂h, h₃h⟩)
    · exact .inl (hfg.trans h)
    · exact .inr ⟨n, h, h₁h, h₂h, hfg.trans h₃h⟩

/-!
## Criteria to guarantee normal form
-/

/-- Helper lemma for `meromorphicNFAt_iff_meromorphicNFAt_of_smul_analytic`: if
`f` is meromorphic in normal form at `x` and `g` is analytic without zero at
`x`, then `g • f` is meromorphic in normal form at `x`. -/
lemma MeromorphicNFAt.smul_analytic (hf : MeromorphicNFAt f x)
    (h₁g : AnalyticAt 𝕜 g x) (h₂g : g x ≠ 0) :
    MeromorphicNFAt (g • f) x := by
  rcases hf with h₁f | ⟨n, g_f, h₁g_f, h₂g_f, h₃g_f⟩
  · left
    filter_upwards [h₁f]
    simp_all
  · right
    use n, g • g_f, h₁g.smul h₁g_f
    constructor
    · simp [smul_ne_zero h₂g h₂g_f]
    · filter_upwards [h₃g_f]
      intro y hy
      simp only [Pi.smul_apply', hy, Pi.pow_apply]
      rw [smul_comm]

/-- If `f` is any function and `g` is analytic without zero at `z₀`, then `f` is meromorphic in
normal form at `z₀` iff `g • f` is meromorphic in normal form at `z₀`. -/
theorem meromorphicNFAt_smul_iff_right_of_analyticAt (h₁g : AnalyticAt 𝕜 g x)
    (h₂g : g x ≠ 0) :
    MeromorphicNFAt (g • f) x ↔ MeromorphicNFAt f x := by
  constructor
  · intro hprod
    have : f =ᶠ[𝓝 x] g⁻¹ • g • f := by
      filter_upwards [h₁g.continuousAt.preimage_mem_nhds (compl_singleton_mem_nhds_iff.mpr h₂g)]
      intro y hy
      rw [Set.preimage_compl, Set.mem_compl_iff, Set.mem_preimage,
        Set.mem_singleton_iff] at hy
      simp [hy]
    rw [meromorphicNFAt_congr this]
    exact hprod.smul_analytic (h₁g.inv h₂g) (inv_ne_zero h₂g)
  · exact fun hf ↦ hf.smul_analytic h₁g h₂g

/-- If `f` is any function and `g` is analytic without zero at `z₀`, then `f` is meromorphic in
normal form at `z₀` iff `g * f` is meromorphic in normal form at `z₀`. -/
theorem meromorphicNFAt_mul_iff_right {f : 𝕜 → 𝕜} (h₁g : AnalyticAt 𝕜 g x)
    (h₂g : g x ≠ 0) :
    MeromorphicNFAt (g * f) x ↔ MeromorphicNFAt f x := by
  rw [← smul_eq_mul]
  exact meromorphicNFAt_smul_iff_right_of_analyticAt h₁g h₂g

/-- If `f` is any function and `g` is analytic without zero at `z₀`, then `f` is meromorphic in
normal form at `z₀` iff `f * g` is meromorphic in normal form at `z₀`. -/
theorem meromorphicNFAt_mul_iff_left {f : 𝕜 → 𝕜} (h₁g : AnalyticAt 𝕜 g x)
    (h₂g : g x ≠ 0) :
    MeromorphicNFAt (f * g) x ↔ MeromorphicNFAt f x := by
  rw [mul_comm, ← smul_eq_mul]
  exact meromorphicNFAt_smul_iff_right_of_analyticAt h₁g h₂g

/-!
## Continuous extension and conversion to normal form
-/

variable (f x) in
/-- If `f` is meromorphic at `x`, convert `f` to normal form at `x` by changing its value at `x`.
Otherwise, returns the 0 function. -/
noncomputable def toMeromorphicNFAt :
    𝕜 → E := by
  by_cases hf : MeromorphicAt f x
  · classical -- do not complain about decidability issues in Function.update
    apply Function.update f x
    by_cases h₁f : hf.order = (0 : ℤ)
    · rw [hf.order_eq_int_iff] at h₁f
      exact (Classical.choose h₁f) x
    · exact 0
  · exact 0

/-- Conversion to normal form at `x` changes the value only at x. -/
lemma MeromorphicAt.eqOn_compl_singleton_toMermomorphicNFAt (hf : MeromorphicAt f x) :
    Set.EqOn f (toMeromorphicNFAt f x) {x}ᶜ :=
  fun _ _ ↦ by simp_all [toMeromorphicNFAt]

/-- If `f` is not meromorphic, conversion to normal form at `x` maps the function to `0`. -/
@[simp] lemma toMeromorphicNFAt_of_not_meromorphicAt (hf : ¬MeromorphicAt f x) :
    toMeromorphicNFAt f x = 0 := by
  simp [toMeromorphicNFAt, hf]

/-- Conversion to normal form at `x` changes the value only at x. -/
lemma MeromorphicAt.eq_nhdNE_toMeromorphicNFAt (hf : MeromorphicAt f x) :
    f =ᶠ[𝓝[≠] x] toMeromorphicNFAt f x :=
  eventually_nhdsWithin_of_forall (fun _ hz ↦ hf.eqOn_compl_singleton_toMermomorphicNFAt hz)

/-- After conversion to normal form at `x`, the function has normal form. -/
theorem meromorphicNFAt_toMeromorphicNFAt :
    MeromorphicNFAt (toMeromorphicNFAt f x) x := by
  by_cases hf : MeromorphicAt f x
  · by_cases h₂f : hf.order = ⊤
    · have : toMeromorphicNFAt f x =ᶠ[𝓝 x] 0 := by
        apply eventuallyEq_nhds_of_eventuallyEq_nhdsNE
        · exact hf.eq_nhdNE_toMeromorphicNFAt.symm.trans (hf.order_eq_top_iff.1 h₂f)
        · simp [h₂f, toMeromorphicNFAt, hf]
      apply AnalyticAt.meromorphicNFAt
      rw [analyticAt_congr this]
      exact analyticAt_const
    · lift hf.order to ℤ using h₂f with n hn
      obtain ⟨g, h₁g, h₂g, h₃g⟩ := (hf.order_eq_int_iff n).1 hn.symm
      right
      use n, g, h₁g, h₂g
      apply eventuallyEq_nhds_of_eventuallyEq_nhdsNE (hf.eq_nhdNE_toMeromorphicNFAt.symm.trans h₃g)
      simp only [toMeromorphicNFAt, hf, ↓reduceDIte, ← hn, WithTop.coe_zero,
        WithTop.coe_eq_zero, ne_eq, Function.update_self, sub_self]
      split_ifs with h₃f
      · obtain ⟨h₁G, _, h₃G⟩ := Classical.choose_spec ((hf.order_eq_int_iff 0).1 (h₃f ▸ hn.symm))
        apply Filter.EventuallyEq.eq_of_nhds
        apply (h₁G.continuousAt.eventuallyEq_nhd_iff_eventuallyEq_nhdNE (by fun_prop)).1
        filter_upwards [h₃g, h₃G]
        simp_all
      · simp [h₃f, zero_zpow]
  · simp only [toMeromorphicNFAt, hf, ↓reduceDIte]
    exact analyticAt_const.meromorphicNFAt

/-- If `f` has normal form at `x`, then `f` equals `f.toNF`. -/
@[simp] theorem toMeromorphicNFAt_eq_self :
    MeromorphicNFAt f x ↔ f = toMeromorphicNFAt f x where
  mp hf := by
    funext z
    by_cases hz : z = x
    · rw [hz]
      simp only [toMeromorphicNFAt, hf.meromorphicAt, WithTop.coe_zero, ne_eq, Function.update_self]
      have h₀f := hf
      rcases hf with h₁f | h₁f
      · simpa [(h₀f.meromorphicAt.order_eq_top_iff).2 (h₁f.filter_mono nhdsWithin_le_nhds)]
          using h₁f.eq_of_nhds
      · obtain ⟨n, g, h₁g, h₂g, h₃g⟩ := h₁f
        rw [Filter.EventuallyEq.eq_of_nhds h₃g]
        have : h₀f.meromorphicAt.order = n := by
          rw [MeromorphicAt.order_eq_int_iff (MeromorphicNFAt.meromorphicAt h₀f) n]
          use g, h₁g, h₂g
          exact eventually_nhdsWithin_of_eventually_nhds h₃g
        by_cases h₃f : h₀f.meromorphicAt.order = 0
        · simp only [Pi.smul_apply', Pi.pow_apply, sub_self, h₃f, ↓reduceDIte]
          have hn : n = (0 : ℤ) := by
            rw [h₃f] at this
            exact WithTop.coe_eq_zero.mp this.symm
          simp_rw [hn]
          simp only [zpow_zero, one_smul]
          have : g =ᶠ[𝓝 x] (Classical.choose ((h₀f.meromorphicAt.order_eq_int_iff 0).1 h₃f)) := by
            obtain ⟨h₀, h₁, h₂⟩ := Classical.choose_spec
              ((h₀f.meromorphicAt.order_eq_int_iff 0).1 h₃f)
            rw [← h₁g.continuousAt.eventuallyEq_nhd_iff_eventuallyEq_nhdNE h₀.continuousAt]
            rw [hn] at h₃g
            simp only [zpow_zero, one_smul, ne_eq] at h₃g h₂
            exact (h₃g.filter_mono nhdsWithin_le_nhds).symm.trans h₂
          simp only [Function.update_self]
          exact Filter.EventuallyEq.eq_of_nhds this
        · simp only [Pi.smul_apply', Pi.pow_apply, sub_self, h₃f, ↓reduceDIte, smul_eq_zero,
            Function.update_self, smul_eq_zero]
          left
          apply zero_zpow n
          by_contra hn
          rw [hn] at this
          tauto
    · exact hf.meromorphicAt.eqOn_compl_singleton_toMermomorphicNFAt hz
  mpr hf := by
    rw [hf]
    exact meromorphicNFAt_toMeromorphicNFAt
