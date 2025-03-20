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

Establish further properties of meromorphic functions in normal form, such
as a local identity theorem. Establish the analogous notion `MeromorphicNFOn`.
-/

open Topology

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f : 𝕜 → E}
  {x : 𝕜}

/-!
# Normal form of meromorphic functions at a given point

## Definition and characterizations
-/

/-- A function is 'meromorphic in normal form' at `x` if it vanishes around `x`
or if it can locally be written as `fun z ↦ (z - x) ^ n • g` where `g` is
analytic and does not vanish at `x`. -/
def MeromorphicNFAt (f : 𝕜 → E) (x : 𝕜) :=
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

/-- Two analytic functions agree on a punctured neighborhood iff they agree on a neighborhood. -/
private lemma AnalyticAt.eventuallyEq_nhdNE_iff_eventuallyEq_nhd {g : 𝕜 → E} {z₀ : 𝕜}
    (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀) (hfg : f =ᶠ[𝓝[≠] z₀] g) :
    f =ᶠ[𝓝 z₀] g := by
  rcases ((hf.sub hg).eventually_eq_zero_or_eventually_ne_zero) with h | h
  · exact Filter.eventuallyEq_iff_sub.2 h
  · simpa using (Filter.eventually_and.2 ⟨Filter.eventuallyEq_iff_sub.mp hfg, h⟩).exists

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
        apply h₁G.eventuallyEq_nhdNE_iff_eventuallyEq_nhd (by fun_prop)
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
            apply h₁g.eventuallyEq_nhdNE_iff_eventuallyEq_nhd h₀
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
