/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Meromorphic.Divisor

/-!
# Normal form of meromorphic functions and continuous extension

If a function `f` is meromorphic on `U` and if `g` differs from `f` only along a set that is
codiscrete within `U`, then `g` is likewise meromorphic. The set of meromorphic functions is
therefore huge, and `=ᶠ[codiscreteWithin U]` defines an equivalence relation.

This file implements continuous extension to provide an API that allows picking the 'unique best'
representative of any given equivalence class, where 'best' means that the representative can
locally near any point `x` be written 'in normal form', as `f =ᶠ[𝓝 x] fun z ↦ (z - x) ^ n • g`
where `g` is analytic and does not vanish at `x`.

The relevant notions are `MeromorphicNFAt` and `MeromorphicNFOn`; these guarantee normal
form at a single point and along a set, respectively.
-/

@[expose] public section

open Topology WithTop

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f : 𝕜 → E} {g : 𝕜 → 𝕜}
  {x : 𝕜}
  {U : Set 𝕜}

/-!
## Normal form of meromorphic functions at a given point

### Definition and characterizations
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
    MeromorphicNFAt f x ↔
      AnalyticAt 𝕜 f x ∨ (MeromorphicAt f x ∧ meromorphicOrderAt f x < 0 ∧ f x = 0) := by
  constructor
  · rintro (h | ⟨n, g, h₁g, h₂g, h₃g⟩)
    · simp [(analyticAt_congr h).2 analyticAt_const]
    · have hf : MeromorphicAt f x := by
        apply MeromorphicAt.congr _ (h₃g.filter_mono nhdsWithin_le_nhds).symm
        fun_prop
      have : meromorphicOrderAt f x = n := by
        rw [meromorphicOrderAt_eq_int_iff hf]
        use g, h₁g, h₂g
        exact eventually_nhdsWithin_of_eventually_nhds h₃g
      by_cases! hn : 0 ≤ n
      · left
        rw [analyticAt_congr h₃g]
        apply (AnalyticAt.zpow_nonneg (by fun_prop) hn).smul h₁g
      · right
        use hf
        simp [this, WithTop.coe_lt_zero.2 hn, h₃g.eq_of_nhds,
          zero_zpow n hn.ne]
  · rintro (h | ⟨h₁, h₂, h₃⟩)
    · by_cases h₂f : analyticOrderAt f x = ⊤
      · rw [analyticOrderAt_eq_top] at h₂f
        tauto
      · right
        use analyticOrderNatAt f x
        have : analyticOrderAt f x ≠ ⊤ := h₂f
        rw [← ENat.coe_toNat_eq_self, eq_comm, h.analyticOrderAt_eq_natCast] at this
        obtain ⟨g, h₁g, h₂g, h₃g⟩ := this
        use g, h₁g, h₂g
        simpa
    · right
      lift meromorphicOrderAt f x to ℤ using LT.lt.ne_top h₂ with n hn
      obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOrderAt_eq_int_iff h₁).1 hn.symm
      use n, g, h₁g, h₂g
      filter_upwards [eventually_nhdsWithin_iff.1 h₃g]
      intro z hz
      by_cases h₁z : z = x
      · simp only [h₁z, Pi.smul_apply', Pi.pow_apply, sub_self]
        rw [h₃]
        apply (smul_eq_zero_of_left (zero_zpow n _) (g x)).symm
        by_contra hCon
        simp [hCon] at h₂
      · exact hz h₁z

/-!
### Relation to other properties of functions
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
theorem MeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt (hf : MeromorphicNFAt f x) :
    0 ≤ meromorphicOrderAt f x ↔ AnalyticAt 𝕜 f x := by
  constructor <;> intro h₂f
  · rw [meromorphicNFAt_iff_analyticAt_or] at hf
    rcases hf with h | ⟨_, h₃f, _⟩
    · exact h
    · by_contra h'
      exact lt_irrefl 0 (lt_of_le_of_lt h₂f h₃f)
  · rw [h₂f.meromorphicOrderAt_eq]
    simp

/-- Analytic functions are meromorphic in normal form. -/
theorem AnalyticAt.meromorphicNFAt (hf : AnalyticAt 𝕜 f x) :
    MeromorphicNFAt f x := by
  simp [meromorphicNFAt_iff_analyticAt_or, hf]

/-- Meromorphic functions have normal form outside of a discrete subset in the domain of
meromorphicity. -/
theorem MeromorphicOn.meromorphicNFAt_mem_codiscreteWithin {U : Set 𝕜}
    (hf : MeromorphicOn f U) :
    { x | MeromorphicNFAt f x } ∈ Filter.codiscreteWithin U := by
  filter_upwards [hf.analyticAt_mem_codiscreteWithin] with _ ha
  exact ha.meromorphicNFAt

/-!
### Vanishing and order
-/

/-- If `f` is meromorphic in normal form at `x`, then `f` has order zero iff it does not vanish at
`x`.

See `AnalyticAt.order_eq_zero_iff` for an analogous statement about analytic functions. -/
theorem MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff (hf : MeromorphicNFAt f x) :
    meromorphicOrderAt f x = 0 ↔ f x ≠ 0 := by
  constructor
  · intro h₁f
    have h₂f := hf.meromorphicOrderAt_nonneg_iff_analyticAt.1 (le_of_eq h₁f.symm)
    rw [← h₂f.analyticOrderAt_eq_zero, ← ENat.map_natCast_eq_zero (α := ℤ)]
    rwa [h₂f.meromorphicOrderAt_eq] at h₁f
  · intro h
    rcases id hf with h₁ | ⟨n, g, h₁g, h₂g, h₃g⟩
    · have := h₁.eq_of_nhds
      tauto
    · have : n = 0 := by
        by_contra hContra
        have := h₃g.eq_of_nhds
        simp only [Pi.smul_apply', Pi.pow_apply, sub_self, zero_zpow n hContra, zero_smul] at this
        tauto
      simp only [this, zpow_zero] at h₃g
      apply (meromorphicOrderAt_eq_int_iff hf.meromorphicAt).2
      use g, h₁g, h₂g
      simp only [zpow_zero]
      exact h₃g.filter_mono nhdsWithin_le_nhds

/-!
### Local nature of the definition and local identity theorem
-/

/-- **Local identity theorem**: two meromorphic functions in normal form agree in a
neighborhood iff they agree in a pointed neighborhood.

See `ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE` for the analogous
statement for continuous functions.
-/
theorem MeromorphicNFAt.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds {g : 𝕜 → E}
    (hf : MeromorphicNFAt f x) (hg : MeromorphicNFAt g x) :
    f =ᶠ[𝓝[≠] x] g ↔ f =ᶠ[𝓝 x] g := by
  constructor
  · intro h
    have t₀ := meromorphicOrderAt_congr h
    by_cases cs : meromorphicOrderAt f x = 0
    · rw [cs] at t₀
      have Z := (hf.meromorphicOrderAt_nonneg_iff_analyticAt.1 (le_of_eq cs.symm)).continuousAt
      have W := (hg.meromorphicOrderAt_nonneg_iff_analyticAt.1 (le_of_eq t₀)).continuousAt
      exact (Z.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE W).1 h
    · apply eventuallyEq_nhds_of_eventuallyEq_nhdsNE h
      let h₁f := cs
      rw [hf.meromorphicOrderAt_eq_zero_iff] at h₁f
      let h₁g := cs
      rw [t₀, hg.meromorphicOrderAt_eq_zero_iff] at h₁g
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
### Criteria to guarantee normal form
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
    MeromorphicNFAt (g • f) x ↔ MeromorphicNFAt f x where
  mp hprod := by
    have : f =ᶠ[𝓝 x] g⁻¹ • g • f := by
      filter_upwards [h₁g.continuousAt.preimage_mem_nhds (compl_singleton_mem_nhds_iff.mpr h₂g)]
      intro y hy
      rw [Set.preimage_compl, Set.mem_compl_iff, Set.mem_preimage,
        Set.mem_singleton_iff] at hy
      simp [hy]
    rw [meromorphicNFAt_congr this]
    exact hprod.smul_analytic (h₁g.inv h₂g) (inv_ne_zero h₂g)
  mpr hf := hf.smul_analytic h₁g h₂g

/-- If `f` is any function and `g` is analytic without zero at `z₀`, then `f` is meromorphic in
normal form at `z₀` iff `g * f` is meromorphic in normal form at `z₀`. -/
theorem meromorphicNFAt_mul_iff_right {f : 𝕜 → 𝕜} (h₁g : AnalyticAt 𝕜 g x)
    (h₂g : g x ≠ 0) :
    MeromorphicNFAt (g * f) x ↔ MeromorphicNFAt f x :=
  meromorphicNFAt_smul_iff_right_of_analyticAt h₁g h₂g

/-- If `f` is any function and `g` is analytic without zero at `z₀`, then `f` is meromorphic in
normal form at `z₀` iff `f * g` is meromorphic in normal form at `z₀`. -/
theorem meromorphicNFAt_mul_iff_left {f : 𝕜 → 𝕜} (h₁g : AnalyticAt 𝕜 g x)
    (h₂g : g x ≠ 0) :
    MeromorphicNFAt (f * g) x ↔ MeromorphicNFAt f x := by
  rw [mul_comm, ← smul_eq_mul]
  exact meromorphicNFAt_smul_iff_right_of_analyticAt h₁g h₂g

/--
A product of meromorphic functions in normal form is in normal form if at most one of the factors
vanishes.
-/
theorem meromorphicNFAt_prod {x : 𝕜} {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜}
    (h₁f : ∀ i ∈ s, MeromorphicNFAt (f i) x)
    (h₂f : Set.Subsingleton {σ ∈ s | f σ x = 0}) :
    MeromorphicNFAt (∏ i ∈ s, f i) x := by
  classical
  have h₃f {τ : ι} (h₁τ : τ ∈ s) (h₂τ : τ ∉ {σ ∈ s | f σ x = 0}) :
      AnalyticAt 𝕜 (f τ) x := by
    rw [← (h₁f τ h₁τ).meromorphicOrderAt_nonneg_iff_analyticAt]
    apply ((h₁f τ h₁τ).meromorphicOrderAt_eq_zero_iff.2 _).symm.le
    grind
  by_cases h₄f : {σ ∈ s | f σ x = 0} = ∅
  · exact (Finset.analyticAt_prod _ (fun σ hσ ↦ h₃f hσ (by aesop))).meromorphicNFAt
  rw [Finset.filter_eq_empty_iff] at h₄f
  push Not at h₄f
  obtain ⟨τ, h₁τ, h₂τ⟩ := h₄f
  have {μ : ι} (hμ : μ ∈ s.erase τ) : f μ x ≠ 0 := by
    by_contra
    have : τ = μ := h₂f (by aesop) (by aesop)
    aesop
  rw [← Finset.mul_prod_erase _ _ h₁τ, meromorphicNFAt_mul_iff_left]
  · apply h₁f τ h₁τ
  · apply Finset.analyticAt_prod _ (fun μ hμ ↦ h₃f (Finset.mem_of_mem_erase hμ) (by aesop))
  · rw [Finset.prod_apply, Finset.prod_ne_zero_iff]
    aesop

/--
A product of meromorphic functions in normal form is in normal form if at most one of the factors
vanishes.
-/
theorem meromorphicNFAt_fun_prod {x : 𝕜} {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜}
    (h₁f : ∀ i ∈ s, MeromorphicNFAt (f i) x)
    (h₂f : Set.Subsingleton {σ ∈ s | f σ x = 0}) :
    MeromorphicNFAt (fun a ↦ ∏ i ∈ s, f i a) x := by
  convert meromorphicNFAt_prod h₁f h₂f
  exact (Finset.prod_apply _ s f).symm

/--
A finprod of meromorphic functions in normal form is in normal form if at most one of the factors
vanishes.
-/
theorem meromorphicNFAt_finprod {x : 𝕜} {ι : Type*} {f : ι → 𝕜 → 𝕜}
    (h₁f : ∀ i, MeromorphicNFAt (f i) x) (h₂f : Set.Subsingleton {σ | f σ x = 0}) :
    MeromorphicNFAt (∏ᶠ i, f i) x := by
  by_cases h₃f : Function.HasFiniteMulSupport f
  · simp_rw [finprod_eq_prod f h₃f]
    exact meromorphicNFAt_prod (by aesop) (fun _ _ _ _ ↦ by aesop)
  · exact finprod_of_not_hasFiniteMulSupport h₃f ▸ analyticAt_const.meromorphicNFAt

/--
Integer powers of meromorphic functions in normal form are in normal form.
-/
@[to_fun]
theorem MeromorphicNFAt.zpow {f : 𝕜 → 𝕜} {n : ℤ} {x : 𝕜} (hf : MeromorphicNFAt f x) :
    MeromorphicNFAt (f ^ n) x := by
  by_cases hn : n = 0
  · simp_all only [zpow_zero]
    apply AnalyticAt.meromorphicNFAt
    apply analyticAt_const
  rcases hf with hf | hf
  · left
    filter_upwards [hf] with z hz
    simp_all only [Pi.zero_apply, Pi.pow_apply, zero_zpow n hn]
  · obtain ⟨m, g, h₁g, h₂g, h₃g⟩ := hf
    right
    use n * m, g ^ n, h₁g.zpow h₂g
    constructor
    · rw [Pi.pow_apply]
      exact zpow_ne_zero n h₂g
    · filter_upwards [h₃g] with z hz
      simp [hz, mul_zpow, (zpow_mul' (z - x) n m).symm]

/--
If `f` is meromorphic in normal form, then so is its inverse.
-/
theorem MeromorphicNFAt.inv {f : 𝕜 → 𝕜} (hf : MeromorphicNFAt f x) :
    MeromorphicNFAt f⁻¹ x := by
  rcases hf with h | ⟨n, g, h₁, h₂, h₃⟩
  · left
    filter_upwards [h] with x hx
    simp [hx]
  · right
    use -n, g⁻¹, h₁.inv h₂, (by simp_all)
    filter_upwards [h₃] with y hy
    simp only [Pi.inv_apply, hy, Pi.smul_apply', Pi.pow_apply, smul_eq_mul, mul_inv_rev, zpow_neg]
    ring

/--
A function to 𝕜 is meromorphic in normal form at a point iff its inverse is.
-/
@[simp] theorem meromorphicNFAt_inv {f : 𝕜 → 𝕜} : MeromorphicNFAt f⁻¹ x ↔ MeromorphicNFAt f x where
  mp hf := inv_inv f ▸ hf.inv
  mpr hf := hf.inv

theorem MeromorphicNFOn.div {f : 𝕜 → 𝕜} {g : 𝕜 → 𝕜} {x : 𝕜} (hf : AnalyticAt 𝕜 f x)
    (hg : MeromorphicNFAt g x) (hor : g x ≠ 0 ∨ f x ≠ 0) : MeromorphicNFAt (f / g) x := by
  rw [div_eq_mul_inv]
  rcases hor with hgne | hfne
  · have hf := hf.meromorphicNFAt
    have hgAnalytic : AnalyticAt 𝕜 g x := by grind [meromorphicNFAt_iff_analyticAt_or]
    have hgInvAnalytic : AnalyticAt 𝕜 g⁻¹ x := hgAnalytic.inv hgne
    rwa [← meromorphicNFAt_mul_iff_left hgInvAnalytic (inv_ne_zero hgne)] at hf
  · grind [meromorphicNFAt_mul_iff_right, hg.inv]

/-!
### Continuous extension and conversion to normal form
-/

variable (f x) in
/-- If `f` is meromorphic at `x`, convert `f` to normal form at `x` by changing its value at `x`.
Otherwise, returns the 0 function. -/
noncomputable def toMeromorphicNFAt :
    𝕜 → E := by
  by_cases hf : MeromorphicAt f x
  · classical -- do not complain about decidability issues in Function.update
    apply Function.update f x
    by_cases h₁f : meromorphicOrderAt f x = (0 : ℤ)
    · rw [meromorphicOrderAt_eq_int_iff hf] at h₁f
      exact (Classical.choose h₁f) x
    · exact 0
  · exact 0

/-- Conversion to normal form at `x` changes the value only at x. -/
lemma MeromorphicAt.eqOn_compl_singleton_toMeromorphicNFAt (hf : MeromorphicAt f x) :
    Set.EqOn f (toMeromorphicNFAt f x) {x}ᶜ :=
  fun _ _ ↦ by simp_all [toMeromorphicNFAt]

/-- If `f` is not meromorphic, conversion to normal form at `x` maps the function to `0`. -/
@[simp] lemma toMeromorphicNFAt_of_not_meromorphicAt (hf : ¬MeromorphicAt f x) :
    toMeromorphicNFAt f x = 0 := by
  simp [toMeromorphicNFAt, hf]

/-- Conversion to normal form at `x` changes the value only at x. -/
lemma MeromorphicAt.eq_nhdsNE_toMeromorphicNFAt (hf : MeromorphicAt f x) :
    f =ᶠ[𝓝[≠] x] toMeromorphicNFAt f x :=
  eventually_nhdsWithin_of_forall (fun _ hz ↦ hf.eqOn_compl_singleton_toMeromorphicNFAt hz)

/-- After conversion to normal form at `x`, the function has normal form. -/
theorem meromorphicNFAt_toMeromorphicNFAt :
    MeromorphicNFAt (toMeromorphicNFAt f x) x := by
  by_cases hf : MeromorphicAt f x
  · by_cases h₂f : meromorphicOrderAt f x = ⊤
    · have : toMeromorphicNFAt f x =ᶠ[𝓝 x] 0 := by
        apply eventuallyEq_nhds_of_eventuallyEq_nhdsNE
        · exact hf.eq_nhdsNE_toMeromorphicNFAt.symm.trans (meromorphicOrderAt_eq_top_iff.1 h₂f)
        · simp [h₂f, toMeromorphicNFAt, hf]
      apply AnalyticAt.meromorphicNFAt
      rw [analyticAt_congr this]
      exact analyticAt_const
    · lift meromorphicOrderAt f x to ℤ using h₂f with n hn
      obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOrderAt_eq_int_iff hf).1 hn.symm
      right
      use n, g, h₁g, h₂g
      apply eventuallyEq_nhds_of_eventuallyEq_nhdsNE (hf.eq_nhdsNE_toMeromorphicNFAt.symm.trans h₃g)
      simp only [toMeromorphicNFAt, hf, ↓reduceDIte, ← hn, WithTop.coe_zero,
        WithTop.coe_eq_zero, ne_eq, Function.update_self, sub_self]
      split_ifs with h₃f
      · obtain ⟨h₁G, _, h₃G⟩ :=
          Classical.choose_spec ((meromorphicOrderAt_eq_int_iff hf).1 (h₃f ▸ hn.symm))
        apply Filter.EventuallyEq.eq_of_nhds
        apply (h₁G.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE (by fun_prop)).1
        filter_upwards [h₃g, h₃G]
        simp_all
      · simp [h₃f, zero_zpow]
  · simp only [toMeromorphicNFAt, hf, ↓reduceDIte]
    exact analyticAt_const.meromorphicNFAt

/-- If `f` has normal form at `x`, then `f` equals `f.toNF`. -/
@[simp] theorem toMeromorphicNFAt_eq_self :
    toMeromorphicNFAt f x = f ↔ MeromorphicNFAt f x where
  mp hf := by
    rw [hf.symm]
    exact meromorphicNFAt_toMeromorphicNFAt
  mpr hf := by
    funext z
    by_cases hz : z = x
    · rw [hz]
      simp only [toMeromorphicNFAt, hf.meromorphicAt, WithTop.coe_zero, ne_eq]
      have h₀f := hf
      rcases hf with h₁f | h₁f
      · simpa [meromorphicOrderAt_eq_top_iff.2 (h₁f.filter_mono nhdsWithin_le_nhds)]
          using h₁f.eq_of_nhds.symm
      · obtain ⟨n, g, h₁g, h₂g, h₃g⟩ := h₁f
        rw [Filter.EventuallyEq.eq_of_nhds h₃g]
        have : meromorphicOrderAt f x = n := by
          rw [meromorphicOrderAt_eq_int_iff h₀f.meromorphicAt]
          use g, h₁g, h₂g
          exact eventually_nhdsWithin_of_eventually_nhds h₃g
        by_cases h₃f : meromorphicOrderAt f x = 0
        · simp only [Pi.smul_apply', Pi.pow_apply, sub_self, h₃f, ↓reduceDIte]
          have hn : n = (0 : ℤ) := by
            rw [h₃f] at this
            exact WithTop.coe_eq_zero.mp this.symm
          simp_rw [hn]
          simp only [zpow_zero, one_smul]
          have : g =ᶠ[𝓝 x]
              Classical.choose ((meromorphicOrderAt_eq_int_iff h₀f.meromorphicAt).1 h₃f) := by
            obtain ⟨h₀, h₁, h₂⟩ := Classical.choose_spec
              ((meromorphicOrderAt_eq_int_iff h₀f.meromorphicAt).1 h₃f)
            rw [← h₁g.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE h₀.continuousAt]
            rw [hn] at h₃g
            simp only [zpow_zero, one_smul, ne_eq] at h₃g h₂
            exact (h₃g.filter_mono nhdsWithin_le_nhds).symm.trans h₂
          simp only [Function.update_self]
          exact Filter.EventuallyEq.eq_of_nhds this.symm
        · rw [eq_comm]
          simp only [Pi.smul_apply', Pi.pow_apply, sub_self, h₃f, ↓reduceDIte, smul_eq_zero,
            Function.update_self, smul_eq_zero]
          left
          apply zero_zpow n
          by_contra hn
          rw [hn] at this
          tauto
    · exact (hf.meromorphicAt.eqOn_compl_singleton_toMeromorphicNFAt hz).symm

/-!
## Normal form of meromorphic functions on a given set

### Definition
-/

/--
A function is 'meromorphic in normal form' on `U` if has normal form at every
point of `U`.
-/
def MeromorphicNFOn (f : 𝕜 → E) (U : Set 𝕜) := ∀ ⦃z⦄, z ∈ U → MeromorphicNFAt f z

/-!
### Relation to other properties of functions
-/

/--
If a function is meromorphic in normal form on `U`, then it is meromorphic on
`U`.
-/
theorem MeromorphicNFOn.meromorphicOn (hf : MeromorphicNFOn f U) :
    MeromorphicOn f U := fun _ hz ↦ (hf hz).meromorphicAt

/--
If a function is meromorphic in normal form on `U`, then its divisor is
non-negative iff it is analytic.
-/
theorem MeromorphicNFOn.divisor_nonneg_iff_analyticOnNhd
    (h₁f : MeromorphicNFOn f U) :
    0 ≤ MeromorphicOn.divisor f U ↔ AnalyticOnNhd 𝕜 f U := by
  constructor <;> intro h x
  · intro hx
    rw [← (h₁f hx).meromorphicOrderAt_nonneg_iff_analyticAt]
    have := h x
    simp only [Function.LocallyFinsuppWithin.coe_zero, Pi.zero_apply, h₁f.meromorphicOn, hx,
      MeromorphicOn.divisor_apply, untop₀_nonneg] at this
    assumption
  · by_cases hx : x ∈ U
    · simp only [Function.LocallyFinsuppWithin.coe_zero, Pi.zero_apply, h₁f.meromorphicOn, hx,
        MeromorphicOn.divisor_apply, untop₀_nonneg]
      exact (h₁f hx).meromorphicOrderAt_nonneg_iff_analyticAt.2 (h x hx)
    · simp [hx]

/-- Analytic functions are meromorphic in normal form. -/
theorem AnalyticOnNhd.meromorphicNFOn (h₁f : AnalyticOnNhd 𝕜 f U) :
    MeromorphicNFOn f U := fun z hz ↦ (h₁f z hz).meromorphicNFAt

/-!
### Divisors and zeros of meromorphic functions in normal form.
-/

/--
If `f` is meromorphic in normal form on `U` and nowhere locally constant zero,
then its zero set equals the support of the associated divisor.
-/
theorem MeromorphicNFOn.zero_set_eq_divisor_support (h₁f : MeromorphicNFOn f U)
    (h₂f : ∀ u : U, meromorphicOrderAt f u ≠ ⊤) :
    U ∩ f ⁻¹' {0} = Function.support (MeromorphicOn.divisor f U) := by
  ext u
  constructor <;> intro hu
  · simp_all only [ne_eq, Subtype.forall, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff, Function.mem_support, h₁f.meromorphicOn, MeromorphicOn.divisor_apply,
      WithTop.untop₀_eq_zero, (h₁f hu.1).meromorphicOrderAt_eq_zero_iff, not_true_eq_false, or_self,
      not_false_eq_true]
  · simp only [Function.mem_support, ne_eq] at hu
    constructor
    · exact (MeromorphicOn.divisor f U).supportWithinDomain hu
    · rw [Set.mem_preimage, Set.mem_singleton_iff]
      have := h₁f ((MeromorphicOn.divisor f U).supportWithinDomain hu)
        |>.meromorphicOrderAt_eq_zero_iff.not
      simp only [h₁f.meromorphicOn, (MeromorphicOn.divisor f U).supportWithinDomain hu,
        MeromorphicOn.divisor_apply, WithTop.untop₀_eq_zero, not_or] at hu
      simp_all [hu.1]

/-!
### Criteria to guarantee normal form
-/

/--
If `f` is any function and `g` is analytic without zero on `U`, then `f` is
meromorphic in normal form on `U` iff `g • f` is meromorphic in normal form on
`U`.
-/
theorem meromorphicNFOn_smul_iff_right_of_analyticOnNhd {g : 𝕜 → 𝕜} (h₁g : AnalyticOnNhd 𝕜 g U)
    (h₂g : ∀ u ∈ U, g u ≠ 0) :
    MeromorphicNFOn (g • f) U ↔ MeromorphicNFOn f U := by
  constructor <;> intro h z hz
  · rw [← meromorphicNFAt_smul_iff_right_of_analyticAt (h₁g z hz) (h₂g z hz)]
    exact h hz
  · apply (h hz).smul_analytic (h₁g z hz)
    exact h₂g z hz

/--
If `f` is any function and `g` is analytic without zero in `U`, then `f` is
meromorphic in normal form on `U` iff `g * f` is meromorphic in normal form on
`U`.
-/
theorem meromorphicNFOn_mul_iff_right_of_analyticOnNhd {f g : 𝕜 → 𝕜} (h₁g : AnalyticOnNhd 𝕜 g U)
    (h₂g : ∀ u ∈ U, g u ≠ 0) :
    MeromorphicNFOn (g * f) U ↔ MeromorphicNFOn f U := by
  rw [← smul_eq_mul]
  exact meromorphicNFOn_smul_iff_right_of_analyticOnNhd h₁g h₂g

/--
If `f` is any function and `g` is analytic without zero in `U`, then `f` is
meromorphic in normal form on `U` iff `f * g` is meromorphic in normal form on
`U`.
-/
theorem meromorphicNFOn_mul_iff_left_of_analyticOnNhd {f g : 𝕜 → 𝕜} (h₁g : AnalyticOnNhd 𝕜 g U)
    (h₂g : ∀ u ∈ U, g u ≠ 0) :
    MeromorphicNFOn (f * g) U ↔ MeromorphicNFOn f U := by
  rw [mul_comm, ← smul_eq_mul]
  exact meromorphicNFOn_mul_iff_right_of_analyticOnNhd h₁g h₂g

/--
A product of meromorphic functions in normal form is in normal form if at most one of the factors
vanishes.
-/
theorem meromorphicNFOn_prod {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜}
    (h₁f : ∀ i ∈ s, MeromorphicNFOn (f i) U)
    (h₂f : ∀ x ∈ U, Set.Subsingleton {σ ∈ s | f σ x = 0}) :
    MeromorphicNFOn (∏ i ∈ s, f i) U :=
  fun x hx ↦ meromorphicNFAt_prod (h₁f · · hx) (h₂f x hx)

/--
A product of meromorphic functions in normal form is in normal form if at most one of the factors
vanishes.
-/
theorem meromorphicNFOn_fun_prod {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜}
    (h₁f : ∀ i ∈ s, MeromorphicNFOn (f i) U)
    (h₂f : ∀ x ∈ U, Set.Subsingleton {σ ∈ s | f σ x = 0}) :
    MeromorphicNFOn (fun x ↦ ∏ i ∈ s, f i x) U := by
  convert meromorphicNFOn_prod h₁f h₂f
  exact (Finset.prod_apply _ s f).symm

/--
A finprod of meromorphic functions in normal form is in normal form if at most one of the factors
vanishes.
-/
theorem meromorphicNFOn_finprod {ι : Type*} {f : ι → 𝕜 → 𝕜} (h₁f : ∀ i, MeromorphicNFOn (f i) U)
    (h₂f : ∀ x ∈ U, Set.Subsingleton {σ | f σ x = 0}) :
  MeromorphicNFOn (∏ᶠ i, f i) U :=
  fun x hx ↦ meromorphicNFAt_finprod (h₁f · hx) (h₂f x hx)

/--
Integer powers of meromorphic functions in normal form are in normal form.
-/
@[to_fun]
theorem MeromorphicNFOn.zpow {f : 𝕜 → 𝕜} {n : ℤ} {U : Set 𝕜} (hf : MeromorphicNFOn f U) :
    MeromorphicNFOn (f ^ n) U := fun _ hz ↦ (hf hz).zpow

/--
A function to 𝕜 is meromorphic in normal form on `U` iff its inverse is.
-/
theorem meromorphicNFOn_inv {f : 𝕜 → 𝕜} :
    MeromorphicNFOn f⁻¹ U ↔ MeromorphicNFOn f U where
  mp h _ hx := meromorphicNFAt_inv.1 (h hx)
  mpr h _ hx := meromorphicNFAt_inv.2 (h hx)

/--
A function to 𝕜 is meromorphic in normal form on `U` iff its inverse is.
-/
theorem meromorphicNFOn_fun_inv {f : 𝕜 → 𝕜} :
    MeromorphicNFOn (fun x ↦ (f x)⁻¹) U ↔ MeromorphicNFOn f U :=
  meromorphicNFOn_inv

/-!
### Continuous extension and conversion to normal form
-/

variable (f U) in
/--
If `f` is meromorphic on `U`, convert `f` to normal form on `U` by changing its
values along a discrete subset within `U`. Otherwise, returns the 0 function.
-/
noncomputable def toMeromorphicNFOn :
    𝕜 → E := by
  by_cases h₁f : MeromorphicOn f U
  · intro z
    by_cases hz : z ∈ U
    · exact toMeromorphicNFAt f z z
    · exact f z
  · exact 0

/--
If `f` is not meromorphic on `U`, conversion to normal form maps the function
to `0`.
-/
@[simp] lemma toMeromorphicNFOn_of_not_meromorphicOn (hf : ¬MeromorphicOn f U) :
    toMeromorphicNFOn f U = 0 := by
  simp [toMeromorphicNFOn, hf]

/--
Conversion to normal form on `U` does not change values outside of `U`.
-/
@[simp] lemma toMeromorphicNFOn_eq_self_on_compl (hf : MeromorphicOn f U) :
    Set.EqOn (toMeromorphicNFOn f U) f Uᶜ := by
  intro x hx
  simp_all [toMeromorphicNFOn]

/--
Conversion to normal form on `U` changes the value only along a discrete subset
of `U`.
-/
theorem toMeromorphicNFOn_eqOn_codiscrete (hf : MeromorphicOn f U) :
    f =ᶠ[Filter.codiscreteWithin U] toMeromorphicNFOn f U := by
  have : U ∈ Filter.codiscreteWithin U := by simp
  filter_upwards [hf.analyticAt_mem_codiscreteWithin, this] with a h₁a h₂a
  simp [toMeromorphicNFOn, hf, ← (toMeromorphicNFAt_eq_self.2 h₁a.meromorphicNFAt).symm]

/--
If `f` is meromorphic on `U` and `x ∈ U`, then `f` and its conversion to normal
form on `U` agree in a punctured neighborhood of `x`.
-/
theorem MeromorphicOn.toMeromorphicNFOn_eq_self_on_nhdsNE
    (hf : MeromorphicOn f U) (hx : x ∈ U) :
    toMeromorphicNFOn f U =ᶠ[𝓝[≠] x] f := by
  filter_upwards [hf.eventually_analyticAt_or_mem_compl hx] with a ha
  rcases ha with ha | ha
  · simp [toMeromorphicNFOn, hf, ← (toMeromorphicNFAt_eq_self.2 ha.meromorphicNFAt).symm]
  · simp only [Set.mem_compl_iff] at ha
    simp [toMeromorphicNFOn, ha, hf]

/--
If `f` is meromorphic on `U` and `x ∈ U`, then conversion to normal form at `x`
and conversion to normal form on `U` agree in a neighborhood of `x`.
-/
theorem toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds (hf : MeromorphicOn f U)
    (hx : x ∈ U) :
    toMeromorphicNFOn f U =ᶠ[𝓝 x] toMeromorphicNFAt f x := by
  apply eventuallyEq_nhds_of_eventuallyEq_nhdsNE
  · exact (hf.toMeromorphicNFOn_eq_self_on_nhdsNE hx).trans (hf x hx).eq_nhdsNE_toMeromorphicNFAt
  · simp [toMeromorphicNFOn, hf, hx]

/--
If `f` is meromorphic on `U` and `x ∈ U`, then conversion to normal form at `x`
and conversion to normal form on `U` agree at `x`.
-/
theorem toMeromorphicNFOn_eq_toMeromorphicNFAt (hf : MeromorphicOn f U)
    (hx : x ∈ U) :
    toMeromorphicNFOn f U x = toMeromorphicNFAt f x x := by
  apply Filter.EventuallyEq.eq_of_nhds (g := toMeromorphicNFAt f x)
  simp [(toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds hf hx).trans]

variable (f U) in
/--
After conversion to normal form on `U`, the function has normal form.
-/
theorem meromorphicNFOn_toMeromorphicNFOn :
    MeromorphicNFOn (toMeromorphicNFOn f U) U := by
  by_cases hf : MeromorphicOn f U
  · intro z hz
    rw [meromorphicNFAt_congr (toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds hf hz)]
    exact meromorphicNFAt_toMeromorphicNFAt
  · simpa [hf] using analyticOnNhd_const.meromorphicNFOn

/--
If `f` has normal form on `U`, then `f` equals `toMeromorphicNFOn f U`.
-/
@[simp] theorem toMeromorphicNFOn_eq_self :
    toMeromorphicNFOn f U = f ↔ MeromorphicNFOn f U := by
  constructor <;> intro h
  · rw [h.symm]
    apply meromorphicNFOn_toMeromorphicNFOn
  · ext x
    by_cases hx : x ∈ U
    · simp only [toMeromorphicNFOn, h.meromorphicOn, ↓reduceDIte, hx]
      rw [toMeromorphicNFAt_eq_self.2 (h hx)]
    · simp [toMeromorphicNFOn, h.meromorphicOn, hx]

/--
Conversion of normal form does not affect orders.
-/
@[simp] theorem meromorphicOrderAt_toMeromorphicNFOn (hf : MeromorphicOn f U) (hx : x ∈ U) :
    meromorphicOrderAt (toMeromorphicNFOn f U) x = meromorphicOrderAt f x := by
  apply meromorphicOrderAt_congr
  exact hf.toMeromorphicNFOn_eq_self_on_nhdsNE hx

/--
Conversion of normal form does not affect divisors.
-/
@[simp] theorem MeromorphicOn.divisor_of_toMeromorphicNFOn (hf : MeromorphicOn f U) :
    divisor (toMeromorphicNFOn f U) U = divisor f U := by
  ext z
  by_cases hz : z ∈ U <;> simp [hf, (meromorphicNFOn_toMeromorphicNFOn f U).meromorphicOn, hz]
