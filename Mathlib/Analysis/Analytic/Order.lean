/-
Copyright (c) 2022 Vincent Beffara. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Beffara, Stefan Kebekus
-/
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Vanishing Order of Analytic Functions

This file defines the order of vanishing of an analytic function `f` at a point `z₀`, as an element
of `ℕ∞`.

## TODO

Uniformize API between analytic and meromorphic functions
-/

open Filter  Set
open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E]

/-!
## Vanishing Order at a Point: Definition and Characterization
-/

section NormedSpace
variable {f g : 𝕜 → E} {n : ℕ} {z₀ : 𝕜}

open scoped Classical in

/-- The order of vanishing of `f` at `z₀`, as an element of `ℕ∞`.

The order is defined to be `∞` if `f` is identically 0 on a neighbourhood of `z₀`, and otherwise the
unique `n` such that `f` can locally be written as `f z = (z - z₀) ^ n • g z`, where `g` is analytic
and does not vanish at `z₀`. See `AnalyticAt.eanalyticOrderAt_eq_top` and
`AnalyticAt.eanalyticOrderAt_eq_natCast` for these equivalences. -/
noncomputable def eanalyticOrderAt (f : 𝕜 → E) (z₀ : 𝕜) : ℕ∞ :=
  if hf : AnalyticAt 𝕜 f z₀ then
    if h : ∀ᶠ z in 𝓝 z₀, f z = 0 then ⊤
    else ↑(hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr h).choose
  else 0

/-- The order of vanishing of `f` at `z₀`, as an element of `ℕ∞`.

The order is defined to be `∞` if `f` is identically 0 on a neighbourhood of `z₀`, and otherwise the
unique `n` such that `f` can locally be written as `f z = (z - z₀) ^ n • g z`, where `g` is analytic
and does not vanish at `z₀`. See `AnalyticAt.eanalyticOrderAt_eq_top` and
`AnalyticAt.eanalyticOrderAt_eq_natCast` for these equivalences. -/
noncomputable def analyticOrderAt (f : 𝕜 → E) (z₀ : 𝕜) : ℕ := (eanalyticOrderAt f z₀).toNat

@[simp]
lemma eanalyticOrderAt_of_not_analyticAt (hf : ¬ AnalyticAt 𝕜 f z₀) : eanalyticOrderAt f z₀ = 0 :=
  dif_neg hf

@[simp]
lemma analyticOrderAt_of_not_analyticAt (hf : ¬ AnalyticAt 𝕜 f z₀) : analyticOrderAt f z₀ = 0 := by
  simp [analyticOrderAt, hf]

@[simp] lemma Nat.cast_analyticOrderAt (hf : eanalyticOrderAt f z₀ ≠ ⊤) :
    analyticOrderAt f z₀ = eanalyticOrderAt f z₀ := ENat.coe_toNat hf

lemma eanalyticOrderAt_eq_top :
    eanalyticOrderAt f z₀ = ⊤ ↔ AnalyticAt 𝕜 f z₀ ∧ ∀ᶠ z in 𝓝 z₀, f z = 0 := by
  unfold eanalyticOrderAt; split_ifs with hf h <;> simp [*]

/-- The order of an analytic function `f` at a `z₀` is infinity iff `f` vanishes locally around
`z₀`. -/
protected lemma AnalyticAt.eanalyticOrderAt_eq_top (hf : AnalyticAt 𝕜 f z₀) :
    eanalyticOrderAt f z₀ = ⊤ ↔ ∀ᶠ z in 𝓝 z₀, f z = 0 := by simp [eanalyticOrderAt_eq_top, hf]

@[deprecated (since := "2025-03-16")]
alias AnalyticAt.order_eq_top_iff := AnalyticAt.eanalyticOrderAt_eq_top

/-- The order of an analytic function `f` at `z₀` equals a natural number `n` iff `f` can locally
be written as `f z = (z - z₀) ^ n • g z`, where `g` is analytic and does not vanish at `z₀`. -/
lemma AnalyticAt.eanalyticOrderAt_eq_natCast (hf : AnalyticAt 𝕜 f z₀) :
    eanalyticOrderAt f z₀ = n ↔
      ∃ (g : 𝕜 → E), AnalyticAt 𝕜 g z₀ ∧ g z₀ ≠ 0 ∧ ∀ᶠ z in 𝓝 z₀, f z = (z - z₀) ^ n • g z := by
  unfold eanalyticOrderAt
  split_ifs with h
  · simp only [ENat.top_ne_coe, false_iff]
    contrapose! h
    rw [← hf.exists_eventuallyEq_pow_smul_nonzero_iff]
    exact ⟨n, h⟩
  · rw [← hf.exists_eventuallyEq_pow_smul_nonzero_iff] at h
    refine ⟨fun hn ↦ (WithTop.coe_inj.mp hn : h.choose = n) ▸ h.choose_spec, fun h' ↦ ?_⟩
    rw [AnalyticAt.unique_eventuallyEq_pow_smul_nonzero h.choose_spec h']

/-- The order of an analytic function `f` at `z₀` equals a natural number `n` iff `f` can locally
be written as `f z = (z - z₀) ^ n • g z`, where `g` is analytic and does not vanish at `z₀`. -/
lemma AnalyticAt.analyticOrderAt_eq_iff (hf : AnalyticAt 𝕜 f z₀) (hf' : eanalyticOrderAt f z₀ ≠ ⊤)
    {n : ℕ} :
    analyticOrderAt f z₀ = n ↔
      ∃ (g : 𝕜 → E), AnalyticAt 𝕜 g z₀ ∧ g z₀ ≠ 0 ∧ ∀ᶠ z in 𝓝 z₀, f z = (z - z₀) ^ n • g z := by
  simp [← Nat.cast_inj (R := ℕ∞), Nat.cast_analyticOrderAt hf', hf.eanalyticOrderAt_eq_natCast]

/-- The order of an analytic function `f` at `z₀` is finite iff `f` can locally be written as `f z =
  (z - z₀) ^ analyticOrderAt f z₀ • g z`, where `g` is analytic and does not vanish at `z₀`.

See `MeromorphicNFAt.order_eq_zero_iff` for an analogous statement about meromorphic functions in
normal form.
-/
lemma AnalyticAt.eanalyticOrderAt_ne_top (hf : AnalyticAt 𝕜 f z₀) :
    eanalyticOrderAt f z₀ ≠ ⊤ ↔
      ∃ (g : 𝕜 → E), AnalyticAt 𝕜 g z₀ ∧ g z₀ ≠ 0 ∧
        f =ᶠ[𝓝 z₀] fun z ↦ (z - z₀) ^ analyticOrderAt f z₀ • g z := by
  simp only [← ENat.coe_toNat_eq_self, Eq.comm, EventuallyEq, ← hf.eanalyticOrderAt_eq_natCast,
    analyticOrderAt]

@[deprecated (since := "2025-02-03")]
alias order_neq_top_iff := AnalyticAt.eanalyticOrderAt_ne_top

lemma eanalyticOrderAt_eq_zero : eanalyticOrderAt f z₀ = 0 ↔ ¬ AnalyticAt 𝕜 f z₀ ∨ f z₀ ≠ 0 := by
  by_cases hf : AnalyticAt 𝕜 f z₀
  · rw [← ENat.coe_zero, hf.eanalyticOrderAt_eq_natCast]
    constructor
    · intro ⟨g, _, _, hg⟩
      simpa [hf, hg.self_of_nhds]
    · exact fun hz ↦ ⟨f, hf, hz.resolve_left <| not_not_intro hf, by simp⟩
  · simp [hf]

lemma eanalyticOrderAt_ne_zero : eanalyticOrderAt f z₀ ≠ 0 ↔ AnalyticAt 𝕜 f z₀ ∧ f z₀ = 0 := by
  simp [eanalyticOrderAt_eq_zero]

/-- The order of an analytic function `f` at `z₀` is zero iff `f` does not vanish at `z₀`. -/
protected lemma AnalyticAt.eanalyticOrderAt_eq_zero (hf : AnalyticAt 𝕜 f z₀) :
    eanalyticOrderAt f z₀ = 0 ↔ f z₀ ≠ 0 := by simp [hf, eanalyticOrderAt_eq_zero]

/-- The order of an analytic function `f` at `z₀` is zero iff `f` does not vanish at `z₀`. -/
protected lemma AnalyticAt.eanalyticOrderAt_ne_zero (hf : AnalyticAt 𝕜 f z₀) :
    eanalyticOrderAt f z₀ ≠ 0 ↔ f z₀ = 0 := hf.eanalyticOrderAt_eq_zero.not_left

/-- An analytic function vanishes at a point if its order is nonzero when converted to ℕ. -/
lemma apply_eq_zero_of_analyticOrderAt_ne_zero (hf : analyticOrderAt f z₀ ≠ 0) : f z₀ = 0 := by
  by_cases hf' : AnalyticAt 𝕜 f z₀ <;> simp_all [analyticOrderAt, eanalyticOrderAt_eq_zero]

end NormedSpace

/-!
## Vanishing Order at a Point: Behaviour under Ring Operations

The theorem `AnalyticAt.order_mul` and `AnalyticAt.order_pow` establish additivity of the order
under multiplication and taking powers.

TODO: Behaviour under Addition/Subtraction
-/

section NontriviallyNormedField
variable {f g : 𝕜 → 𝕜} {z₀ : 𝕜}

/-- Helper lemma for `eanalyticOrderAt_mul` -/
lemma eanalyticOrderAt_mul_eq_top_of_left (hg : AnalyticAt 𝕜 g z₀)
    (hf : eanalyticOrderAt f z₀ = ⊤) : eanalyticOrderAt (f * g) z₀ = ⊤ := by
  rw [eanalyticOrderAt_eq_top, eventually_nhds_iff] at *
  obtain ⟨hf, t, h₁t, h₂t, h₃t⟩ := hf
  exact ⟨hf.mul hg, t, fun y hy ↦ by simp [h₁t y hy], h₂t, h₃t⟩

/-- Helper lemma for `eanalyticOrderAt_mul` -/
lemma eanalyticOrderAt_mul_eq_top_of_right (hf : AnalyticAt 𝕜 f z₀)
    (hg : eanalyticOrderAt g z₀ = ⊤) : eanalyticOrderAt (f * g) z₀ = ⊤ := by
  rw [eanalyticOrderAt_eq_top, eventually_nhds_iff] at *
  obtain ⟨hg, t, h₁t, h₂t, h₃t⟩ := hg
  exact ⟨hf.mul hg, t, fun y hy ↦ by simp [h₁t y hy], h₂t, h₃t⟩

/-- The order is additive when multiplying analytic functions. -/
theorem eanalyticOrderAt_mul (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀) :
    eanalyticOrderAt (f * g) z₀ = eanalyticOrderAt f z₀ + eanalyticOrderAt g z₀ := by
  -- Trivial cases: one of the functions vanishes around z₀
  by_cases hf' : eanalyticOrderAt f z₀ = ⊤
  · simp [eanalyticOrderAt_mul_eq_top_of_left, *]
  by_cases hg' : eanalyticOrderAt g z₀ = ⊤
  · simp [eanalyticOrderAt_mul_eq_top_of_right, *]
  -- Non-trivial case: both functions do not vanish around z₀
  obtain ⟨g₁, h₁g₁, h₂g₁, h₃g₁⟩ := hf.eanalyticOrderAt_ne_top.1 hf'
  obtain ⟨g₂, h₁g₂, h₂g₂, h₃g₂⟩ := hg.eanalyticOrderAt_ne_top.1 hg'
  rw [← Nat.cast_analyticOrderAt hf', ← Nat.cast_analyticOrderAt hg', ← ENat.coe_add,
      (hf.mul hg).eanalyticOrderAt_eq_natCast]
  refine ⟨g₁ * g₂, h₁g₁.mul h₁g₂, ?_, ?_⟩
  · simp
    tauto
  · obtain ⟨t, h₁t, h₂t, h₃t⟩ := eventually_nhds_iff.1 h₃g₁
    obtain ⟨s, h₁s, h₂s, h₃s⟩ := eventually_nhds_iff.1 h₃g₂
    exact eventually_nhds_iff.2
      ⟨t ∩ s, fun y hy ↦ (by simp [h₁t y hy.1, h₁s y hy.2]; ring_nf), h₂t.inter h₂s, h₃t, h₃s⟩

/-- The order is additive when multiplying analytic functions. -/
theorem analyticOrderAt_mul (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀)
    (hf' : eanalyticOrderAt f z₀ ≠ ⊤) (hg' : eanalyticOrderAt g z₀ ≠ ⊤) :
    analyticOrderAt (f * g) z₀ = analyticOrderAt f z₀ + analyticOrderAt g z₀ := by
  simp [analyticOrderAt, eanalyticOrderAt_mul, ENat.toNat_add, *]

/-- The order multiplies by `n` when taking an analytic function to its `n`th power. -/
theorem eanalyticOrderAt_pow (hf : AnalyticAt 𝕜 f z₀) :
    ∀ n, eanalyticOrderAt (f ^ n) z₀ = n • eanalyticOrderAt f z₀
  | 0 => by simp [eanalyticOrderAt_eq_zero]
  | n + 1 => by simp [add_mul, pow_add, eanalyticOrderAt_mul (hf.pow n), eanalyticOrderAt_pow, hf]

/-- The order multiplies by `n` when taking an analytic function to its `n`th power. -/
theorem analyticOrderAt_pow (hf : AnalyticAt 𝕜 f z₀) (n : ℕ) :
    analyticOrderAt (f ^ n) z₀ = n • analyticOrderAt f z₀ := by
  simp [analyticOrderAt, eanalyticOrderAt_pow, hf]

end NontriviallyNormedField

/-!
## Level Sets of the Order Function
-/

namespace AnalyticOnNhd

variable {U : Set 𝕜} {f : 𝕜 → E} (hf : AnalyticOnNhd 𝕜 f U)
include hf

/-- The set where an analytic function has infinite order is clopen in its domain of analyticity. -/
theorem isClopen_setOf_order_eq_top : IsClopen {u : U | eanalyticOrderAt f u = ⊤} := by
  constructor
  · rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro z hz
    rcases (hf z.1 z.2).eventually_eq_zero_or_eventually_ne_zero with h | h
    · -- Case: f is locally zero in a punctured neighborhood of z
      rw [← (hf z.1 z.2).eanalyticOrderAt_eq_top] at h
      tauto
    · -- Case: f is locally nonzero in a punctured neighborhood of z
      obtain ⟨t', h₁t', h₂t', h₃t'⟩ := eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 h)
      use Subtype.val ⁻¹' t'
      constructor
      · intro w hw
        simp only [mem_compl_iff, mem_setOf_eq]
        by_cases h₁w : w = z
        · rwa [h₁w]
        · rw [(hf _ w.2).eanalyticOrderAt_eq_zero.2 ((h₁t' w hw) (Subtype.coe_ne_coe.mpr h₁w))]
          exact ENat.zero_ne_top
      · exact ⟨isOpen_induced h₂t', h₃t'⟩
  · apply isOpen_iff_forall_mem_open.mpr
    intro z hz
    conv =>
      arg 1; intro; left; right; arg 1; intro
      rw [(hf _ <| Subtype.prop _).eanalyticOrderAt_eq_top, eventually_nhds_iff]
    simp only [mem_setOf_eq] at hz
    rw [(hf _ <| Subtype.prop _).eanalyticOrderAt_eq_top, eventually_nhds_iff] at hz
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
    use t' \ {z.1}, fun y h₁y ↦ h₁t' y h₁y.1, h₂t'.sdiff isClosed_singleton
    apply (mem_diff w).1
    exact ⟨hw, mem_singleton_iff.not.1 (Subtype.coe_ne_coe.2 h₁w)⟩

/-- On a connected set, there exists a point where a meromorphic function `f` has finite order iff
`f` has finite order at every point. -/
theorem exists_order_ne_top_iff_forall (hU : IsConnected U) :
    (∃ u : U, eanalyticOrderAt f u ≠ ⊤) ↔ (∀ u : U, eanalyticOrderAt f u ≠ ⊤) := by
  have : ConnectedSpace U := Subtype.connectedSpace hU
  obtain ⟨v⟩ : Nonempty U := inferInstance
  suffices (∀ (u : U), eanalyticOrderAt f u ≠ ⊤) ∨ ∀ (u : U), eanalyticOrderAt f u = ⊤ by tauto
  simpa [Set.eq_empty_iff_forall_not_mem, Set.eq_univ_iff_forall] using
      isClopen_iff.1 hf.isClopen_setOf_order_eq_top

/-- On a preconnected set, a meromorphic function has finite order at one point if it has finite
order at another point. -/
theorem order_ne_top_of_isPreconnected {x y : 𝕜} (hU : IsPreconnected U) (h₁x : x ∈ U) (hy : y ∈ U)
    (h₂x : eanalyticOrderAt f x ≠ ⊤) : eanalyticOrderAt f y ≠ ⊤ :=
  (hf.exists_order_ne_top_iff_forall ⟨nonempty_of_mem h₁x, hU⟩).1 (by use ⟨x, h₁x⟩) ⟨y, hy⟩

/-- The set where an analytic function has zero or infinite order is discrete within its domain of
analyticity. -/
theorem codiscrete_setOf_order_eq_zero_or_top :
    {u : U | eanalyticOrderAt f u = 0 ∨ eanalyticOrderAt f u = ⊤} ∈ Filter.codiscrete U := by
  rw [mem_codiscrete_subtype_iff_mem_codiscreteWithin, mem_codiscreteWithin]
  intro x hx
  rw [Filter.disjoint_principal_right]
  rcases (hf x hx).eventually_eq_zero_or_eventually_ne_zero with h₁f | h₁f
  · filter_upwards [eventually_nhdsWithin_of_eventually_nhds h₁f.eventually_nhds] with a ha
    simp +contextual [(hf a _).eanalyticOrderAt_eq_top, ha]
  · filter_upwards [h₁f] with a ha
    simp +contextual [(hf a _).eanalyticOrderAt_eq_zero, ha]

end AnalyticOnNhd
