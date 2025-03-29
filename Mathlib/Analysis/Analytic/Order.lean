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

TODO: Uniformize API between analytic and meromorphic functions
-/

open Filter  Set
open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {f g : 𝕜 → E} {n : ℕ} {z₀ : 𝕜}

/-!
## Vanishing Order at a Point: Definition and Characterization
-/

namespace AnalyticAt

open scoped Classical in

/-- The order of vanishing of `f` at `z₀`, as an element of `ℕ∞`.

The order is defined to be `∞` if `f` is identically 0 on a neighbourhood of `z₀`, and otherwise the
unique `n` such that `f` can locally be written as `f z = (z - z₀) ^ n • g z`, where `g` is analytic
and does not vanish at `z₀`. See `AnalyticAt.order_eq_top_iff` and `AnalyticAt.order_eq_nat_iff` for
these equivalences. -/
noncomputable def order (hf : AnalyticAt 𝕜 f z₀) : ENat :=
  if h : ∀ᶠ z in 𝓝 z₀, f z = 0 then ⊤
  else ↑(hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr h).choose

/-- The order of an analytic function `f` at a `z₀` is infinity iff `f` vanishes locally around
`z₀`. -/
lemma order_eq_top_iff (hf : AnalyticAt 𝕜 f z₀) : hf.order = ⊤ ↔ ∀ᶠ z in 𝓝 z₀, f z = 0 := by
  unfold order
  split_ifs with h
  · rwa [eq_self, true_iff]
  · simpa only [ne_eq, ENat.coe_ne_top, false_iff] using h

/-- The order of an analytic function `f` at `z₀` equals a natural number `n` iff `f` can locally
be written as `f z = (z - z₀) ^ n • g z`, where `g` is analytic and does not vanish at `z₀`. -/
lemma order_eq_nat_iff {n : ℕ} (hf : AnalyticAt 𝕜 f z₀) :
    hf.order = ↑n ↔
    ∃ (g : 𝕜 → E), AnalyticAt 𝕜 g z₀ ∧ g z₀ ≠ 0 ∧ ∀ᶠ z in 𝓝 z₀, f z = (z - z₀) ^ n • g z := by
  unfold order
  split_ifs with h
  · simp only [ENat.top_ne_coe, false_iff]
    contrapose! h
    rw [← hf.exists_eventuallyEq_pow_smul_nonzero_iff]
    exact ⟨n, h⟩
  · rw [← hf.exists_eventuallyEq_pow_smul_nonzero_iff] at h
    refine ⟨fun hn ↦ (WithTop.coe_inj.mp hn : h.choose = n) ▸ h.choose_spec, fun h' ↦ ?_⟩
    rw [unique_eventuallyEq_pow_smul_nonzero h.choose_spec h']

/-- The order of an analytic function `f` at `z₀` is finite iff `f` can locally be written as `f z =
  (z - z₀) ^ order • g z`, where `g` is analytic and does not vanish at `z₀`.

See `MeromorphicNFAt.order_eq_zero_iff` for an analogous statement about meromorphic functions in
normal form.
-/
lemma order_ne_top_iff (hf : AnalyticAt 𝕜 f z₀) :
    hf.order ≠ ⊤ ↔ ∃ (g : 𝕜 → E), AnalyticAt 𝕜 g z₀ ∧ g z₀ ≠ 0
      ∧ f =ᶠ[𝓝 z₀] fun z ↦ (z - z₀) ^ (hf.order.toNat) • g z := by
  simp only [← ENat.coe_toNat_eq_self, Eq.comm, EventuallyEq, ← hf.order_eq_nat_iff]

@[deprecated (since := "2025-02-03")]
alias order_neq_top_iff := order_ne_top_iff

/-- The order of an analytic function `f` at `z₀` is zero iff `f` does not vanish at `z₀`. -/
lemma order_eq_zero_iff (hf : AnalyticAt 𝕜 f z₀) :
    hf.order = 0 ↔ f z₀ ≠ 0 := by
  rw [← ENat.coe_zero, hf.order_eq_nat_iff]
  constructor
  · intro ⟨g, _, _, hg⟩
    simpa [hg.self_of_nhds]
  · exact fun hz ↦ ⟨f, hf, hz, by simp⟩

/-- An analytic function vanishes at a point if its order is nonzero when converted to ℕ. -/
lemma apply_eq_zero_of_order_toNat_ne_zero (hf : AnalyticAt 𝕜 f z₀) :
    hf.order.toNat ≠ 0 → f z₀ = 0 := by
  simp [hf.order_eq_zero_iff]
  tauto

/-!
## Vanishing Order at a Point: Behaviour under Ring Operations

The theorem `AnalyticAt.order_mul` and `AnalyticAt.order_pow` establish additivity of the order
under multiplication and taking powers.

TODO: Behaviour under Addition/Subtraction
-/

/-- Helper lemma for `AnalyticAt.order_smul` -/
lemma order_smul_of_order_eq_top₁ {f : 𝕜 → 𝕜} {g : 𝕜 → E} (hf : AnalyticAt 𝕜 f z₀)
    (hg : AnalyticAt 𝕜 g z₀) (h₁f : hf.order = ⊤) :
    (hf.smul hg).order = ⊤ := by
  rw [AnalyticAt.order_eq_top_iff] at *
  filter_upwards [h₁f]
  exact fun _ ha ↦ by simp [ha]

/-- Helper lemma for `AnalyticAt.order_smul` -/
lemma order_smul_of_order_eq_top₂ {f : 𝕜 → 𝕜} {g : 𝕜 → E} (hf : AnalyticAt 𝕜 f z₀)
    (hg : AnalyticAt 𝕜 g z₀) (h₁g : hg.order = ⊤) :
    (hf.smul hg).order = ⊤ := by
  rw [AnalyticAt.order_eq_top_iff] at *
  filter_upwards [h₁g]
  exact fun _ ha ↦ by simp [ha]

/-- The order is additive when scalar multiplying analytic functions. -/
theorem order_smul {f : 𝕜 → 𝕜} {g : 𝕜 → E} (hf : AnalyticAt 𝕜 f z₀)
    (hg : AnalyticAt 𝕜 g z₀) :
    (hf.smul hg).order = hf.order + hg.order := by
  -- Trivial cases: one of the functions vanishes around z₀
  by_cases h₂f : hf.order = ⊤
  · simp [hf.order_smul_of_order_eq_top₁ hg h₂f, h₂f]
  by_cases h₂g : hg.order = ⊤
  · simp [hf.order_smul_of_order_eq_top₂ hg h₂g, h₂g]
  -- Non-trivial case: both functions do not vanish around z₀
  obtain ⟨g₁, h₁g₁, h₂g₁, h₃g₁⟩ := hf.order_ne_top_iff.1 h₂f
  obtain ⟨g₂, h₁g₂, h₂g₂, h₃g₂⟩ := hg.order_ne_top_iff.1 h₂g
  rw [← ENat.coe_toNat h₂f, ← ENat.coe_toNat h₂g, ← ENat.coe_add, (hf.smul hg).order_eq_nat_iff]
  use g₁ • g₂, by exact h₁g₁.smul h₁g₂
  constructor
  · simp only [Pi.smul_apply', ne_eq, smul_eq_zero, not_or]
    tauto
  · filter_upwards [h₃g₁, h₃g₂]
    intro a h₁a h₂a
    rw [Pi.smul_apply', Pi.smul_apply', h₂a, ← smul_assoc, ← smul_assoc]
    congr 1
    rw [h₁a, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    ring

/-- Helper lemma for `AnalyticAt.order_mul` -/
@[deprecated (since := "2025-03-26")]
alias order_mul_of_order_eq_top := order_smul_of_order_eq_top₁

/-- The order is additive when multiplying analytic functions. -/
theorem order_mul {f g : 𝕜 → 𝕜} (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀) :
    (hf.mul hg).order = hf.order + hg.order := order_smul hf hg

/-- The order multiplies by `n` when taking an analytic function to its `n`th power. -/
theorem order_pow {f : 𝕜 → 𝕜} (hf : AnalyticAt 𝕜 f z₀) {n : ℕ} :
    (hf.pow n).order = n • hf.order := by
  induction n
  case zero =>
    simp [AnalyticAt.order_eq_zero_iff]
  case succ n hn =>
    simp [add_mul, pow_add, (hf.pow n).order_mul hf, hn]

end AnalyticAt

/-!
## Level Sets of the Order Function
-/

namespace AnalyticOnNhd

variable {U : Set 𝕜} (hf : AnalyticOnNhd 𝕜 f U)

/-- The set where an analytic function has infinite order is clopen in its domain of analyticity. -/
theorem isClopen_setOf_order_eq_top :
    IsClopen { u : U | (hf u.1 u.2).order = ⊤ } := by
  constructor
  · rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro z hz
    rcases (hf z.1 z.2).eventually_eq_zero_or_eventually_ne_zero with h | h
    · -- Case: f is locally zero in a punctured neighborhood of z
      rw [← (hf z.1 z.2).order_eq_top_iff] at h
      tauto
    · -- Case: f is locally nonzero in a punctured neighborhood of z
      obtain ⟨t', h₁t', h₂t', h₃t'⟩ := eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 h)
      use Subtype.val ⁻¹' t'
      constructor
      · intro w hw
        simp only [mem_compl_iff, mem_setOf_eq]
        by_cases h₁w : w = z
        · rwa [h₁w]
        · rw [(hf _ w.2).order_eq_zero_iff.2 ((h₁t' w hw) (Subtype.coe_ne_coe.mpr h₁w))]
          exact ENat.zero_ne_top
      · exact ⟨isOpen_induced h₂t', h₃t'⟩
  · apply isOpen_iff_forall_mem_open.mpr
    intro z hz
    conv =>
      arg 1; intro; left; right; arg 1; intro
      rw [AnalyticAt.order_eq_top_iff, eventually_nhds_iff]
    simp only [mem_setOf_eq] at hz
    rw [AnalyticAt.order_eq_top_iff, eventually_nhds_iff] at hz
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
    (∃ u : U, (hf u u.2).order ≠ ⊤) ↔ (∀ u : U, (hf u u.2).order ≠ ⊤) := by
  have : ConnectedSpace U := Subtype.connectedSpace hU
  obtain ⟨v⟩ : Nonempty U := inferInstance
  suffices (∀ (u : U), (hf u u.2).order ≠ ⊤) ∨ ∀ (u : U), (hf u u.2).order = ⊤ by tauto
  simpa [Set.eq_empty_iff_forall_not_mem, Set.eq_univ_iff_forall] using
      isClopen_iff.1 hf.isClopen_setOf_order_eq_top

/-- On a preconnected set, a meromorphic function has finite order at one point if it has finite
order at another point. -/
theorem order_ne_top_of_isPreconnected {x y : 𝕜} (hU : IsPreconnected U) (h₁x : x ∈ U) (hy : y ∈ U)
    (h₂x : (hf x h₁x).order ≠ ⊤) :
    (hf y hy).order ≠ ⊤ :=
  (hf.exists_order_ne_top_iff_forall ⟨nonempty_of_mem h₁x, hU⟩).1 (by use ⟨x, h₁x⟩) ⟨y, hy⟩

/-- The set where an analytic function has zero or infinite order is discrete within its domain of
analyticity. -/
theorem codiscrete_setOf_order_eq_zero_or_top :
    {u : U | (hf u u.2).order = 0 ∨ (hf u u.2).order = ⊤} ∈ Filter.codiscrete U := by
  rw [mem_codiscrete_subtype_iff_mem_codiscreteWithin, mem_codiscreteWithin]
  intro x hx
  rw [Filter.disjoint_principal_right]
  rcases (hf x hx).eventually_eq_zero_or_eventually_ne_zero with h₁f | h₁f
  · filter_upwards [eventually_nhdsWithin_of_eventually_nhds h₁f.eventually_nhds] with a ha
    simp +contextual [(hf a _).order_eq_top_iff, ha]
  · filter_upwards [h₁f] with a ha
    simp +contextual [(hf a _).order_eq_zero_iff, ha]

end AnalyticOnNhd
