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

TODO: Establish further properties of meromorphic functions in normal form, such
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
theorem MeromorphicAt.meromorphicNFAt_iff :
    MeromorphicNFAt f x ↔ AnalyticAt 𝕜 f x ∨ ∃ hf : MeromorphicAt f x, hf.order < 0 ∧ f x = 0 := by
  constructor
  · intro h₁f
    have hf : MeromorphicAt f x := by
      rcases h₁f with h | h
      · have : f =ᶠ[𝓝[≠] x] 0 := Filter.EventuallyEq.filter_mono h nhdsWithin_le_nhds
        exact analyticAt_const.meromorphicAt.congr this.symm
      · obtain ⟨n, g, h₁g, _, h₃g⟩ := h
        apply MeromorphicAt.congr _ (Filter.EventuallyEq.filter_mono h₃g nhdsWithin_le_nhds).symm
        fun_prop
    rcases h₁f with h | h
    · simp [(analyticAt_congr h).2 analyticAt_const]
    · obtain ⟨n, g, h₁g, h₂g, h₃g⟩ := h
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
  · intro h₁f
    rcases h₁f with h | ⟨h₁, h₂, h₃⟩
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
  unfold MeromorphicNFAt
  constructor
  · intro h
    rcases h with h | h
    · left
      exact hfg.symm.trans h
    · obtain ⟨n, h, h₁h, h₂h, h₃h⟩ := h
      right
      use n, h, h₁h, h₂h, hfg.symm.trans h₃h
  · intro h
    rcases h with h | h
    · left
      exact hfg.trans h
    · obtain ⟨n, h, h₁h, h₂h, h₃h⟩ := h
      right
      use n, h, h₁h, h₂h, hfg.trans h₃h

/-!
## Relation to other properties of functions
-/

/-- If a function is meromorphic in normal form at `x`, then it is meromorphic at `x`. -/
theorem MeromorphicNFAt.meromorphicAt (hf : MeromorphicNFAt f x) :
    MeromorphicAt f x := by
  rw [MeromorphicAt.meromorphicNFAt_iff] at hf
  rcases hf with h | h
  · exact h.meromorphicAt
  · obtain ⟨hf, _⟩ := h
    exact hf

/-- If a function is meromorphic in normal form at `x` and has non-negative
order, then it is analytic. -/
theorem MeromorphicNFAt.analyticAt (h₁f : MeromorphicNFAt f x)
    (h₂f : 0 ≤ h₁f.meromorphicAt.order) :
    AnalyticAt 𝕜 f x := by
  rw [MeromorphicAt.meromorphicNFAt_iff] at h₁f
  rcases h₁f with h | h
  · exact h
  · by_contra h'
    obtain ⟨h₃f, h₄f, h₅f⟩ := h
    exact lt_irrefl 0 (lt_of_le_of_lt h₂f h₄f)

/-- Analytic functions are meromorphic in normal form. -/
theorem AnalyticAt.MeromorphicNFAt (hf : AnalyticAt 𝕜 f x) :
    MeromorphicNFAt f x := by
  simp [MeromorphicAt.meromorphicNFAt_iff, hf]

/-!
## Continuous extension and conversion to normal form
-/

/-- Convert a meromorphic function to normal form at `x` by changing its value at `x`. -/
noncomputable def MeromorphicAt.toNF (hf : MeromorphicAt f x) :
    𝕜 → E := by
  classical -- do not complain about decidability issues in Function.update
  apply Function.update f x
  by_cases h₁f : hf.order = (0 : ℤ)
  · rw [hf.order_eq_int_iff] at h₁f
    exact (Classical.choose h₁f) x
  · exact 0

/-- Conversion to normal form at `x` by changes the value only at x. -/
lemma MeromorphicAt.toNF_id_on_complement (hf : MeromorphicAt f x) :
    Set.EqOn f hf.toNF {x}ᶜ :=
  fun _ _ ↦ by simp_all [MeromorphicAt.toNF]

/-- Conversion to normal form at `x` changes the value only at x. -/
lemma MeromorphicAt.toNF_id_on_nhdNE (hf : MeromorphicAt f x) :
    f =ᶠ[𝓝[≠] x] hf.toNF :=
  eventually_nhdsWithin_of_forall (fun _ hz ↦ hf.toNF_id_on_complement hz)

/-- After conversion to normal form at `x`, the function has normal form. -/
theorem MeromorphicAt.MeromorphicNFAt_of_toNF (hf : MeromorphicAt f x) :
    MeromorphicNFAt hf.toNF x := by
  by_cases h₂f : hf.order = ⊤
  · have : hf.toNF =ᶠ[𝓝 x] 0 := by
      apply eventuallyEq_nhds_of_eventuallyEq_nhdsNE
      · exact hf.toNF_id_on_nhdNE.symm.trans (hf.order_eq_top_iff.1 h₂f)
      · simp [h₂f, MeromorphicAt.toNF]
    apply AnalyticAt.MeromorphicNFAt
    rw [analyticAt_congr this]
    exact analyticAt_const
  · lift hf.order to ℤ using h₂f with n hn
    obtain ⟨g, h₁g, h₂g, h₃g⟩ := (hf.order_eq_int_iff n).1 hn.symm
    right
    use n, g, h₁g, h₂g
    apply eventuallyEq_nhds_of_eventuallyEq_nhdsNE
    · exact hf.toNF_id_on_nhdNE.symm.trans h₃g
    · unfold MeromorphicAt.toNF
      simp only [WithTop.coe_zero, ne_eq, Function.update_self, Pi.smul_apply', Pi.pow_apply,
        sub_self]
      by_cases h₃f : hf.order = (0 : ℤ)
      · simp only [h₃f, WithTop.coe_zero, ↓reduceDIte, WithTop.untopD_zero, zpow_zero, one_smul]
        obtain ⟨h₁G, h₂G, h₃G⟩  := Classical.choose_spec ((hf.order_eq_int_iff 0).1 h₃f)
        simp only [zpow_zero, ne_eq, one_smul] at h₃G
        apply Filter.EventuallyEq.eq_of_nhds
        apply (AnalyticAt.eventuallyEq_nhdNE_iff_eventuallyEq_nhd h₁G (by fun_prop)).1
        filter_upwards [h₃g, h₃G]
        simp_all
      · simp_rw [← hn, WithTop.coe_zero, WithTop.coe_eq_zero] at *
        simp [h₃f, zero_zpow n h₃f]

/-- If `f` has normal form at `x`, then `f` equals `f.toNF`. -/
theorem MeromorphicNFAt.toNF_eq_id (hf : MeromorphicNFAt f x) :
    f = hf.meromorphicAt.toNF := by
  funext z
  by_cases hz : z = x
  · rw [hz]
    unfold MeromorphicAt.toNF
    simp only [WithTop.coe_zero, ne_eq, Function.update_self]
    have h₀f := hf
    rcases hf with h₁f | h₁f
    · simp only [(h₀f.meromorphicAt.order_eq_top_iff).2 (h₁f.filter_mono nhdsWithin_le_nhds),
        LinearOrderedAddCommGroupWithTop.top_ne_zero, ↓reduceDIte]
      exact Filter.EventuallyEq.eq_of_nhds h₁f
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
          apply (h₁g.eventuallyEq_nhdNE_iff_eventuallyEq_nhd h₀).1
          rw [hn] at h₃g
          simp only [zpow_zero, one_smul, ne_eq] at h₃g h₂
          exact (h₃g.filter_mono nhdsWithin_le_nhds).symm.trans h₂
        exact Filter.EventuallyEq.eq_of_nhds this
      · simp only [Pi.smul_apply', Pi.pow_apply, sub_self, h₃f, ↓reduceDIte, smul_eq_zero]
        left
        apply zero_zpow n
        by_contra hn
        rw [hn] at this
        tauto
  · exact (MeromorphicNFAt.meromorphicAt hf).toNF_id_on_complement hz
