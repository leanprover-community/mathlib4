/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler, Stefan Kebekus
-/
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Meromorphic.Basic

/-!
# Orders of Meromorphic Functions

This file defines the order of a meromorphic function `f` at a point `z₀`, as an element of
`ℤ ∪ {∞}`.

TODO: Uniformize API between analytic and meromorphic functions
-/

open Filter Set WithTop.LinearOrderedAddCommGroup
open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-!
## Order at a Point: Definition and Characterization

This file defines the order of a meromorphic analytic function `f` at a point `z₀`, as an element of
`ℤ ∪ {∞}`.

TODO: Uniformize API between analytic and meromorphic functions
-/

/-!
## Order at a Point: Definition and Characterization
-/

namespace MeromorphicAt

/-- The order of a meromorphic function `f` at `z₀`, as an element of `ℤ ∪ {∞}`.

The order is defined to be `∞` if `f` is identically 0 on a neighbourhood of `z₀`, and otherwise the
unique `n` such that `f` can locally be written as `f z = (z - z₀) ^ n • g z`, where `g` is analytic
and does not vanish at `z₀`. See `MeromorphicAt.order_eq_top_iff` and
`MeromorphicAt.order_eq_nat_iff` for these equivalences. -/
noncomputable def order {f : 𝕜 → E} {x : 𝕜} (hf : MeromorphicAt f x) : WithTop ℤ :=
  (hf.choose_spec.order.map (↑· : ℕ → ℤ)) - hf.choose

/-- The order of a meromorphic function `f` at a `z₀` is infinity iff `f` vanishes locally around
`z₀`. -/
lemma order_eq_top_iff {f : 𝕜 → E} {x : 𝕜} (hf : MeromorphicAt f x) :
    hf.order = ⊤ ↔ ∀ᶠ z in 𝓝[≠] x, f z = 0 := by
  unfold order
  by_cases h : hf.choose_spec.order = ⊤
  · rw [h, ENat.map_top, ← WithTop.coe_natCast,
      top_sub, eq_self, true_iff, eventually_nhdsWithin_iff]
    rw [AnalyticAt.order_eq_top_iff] at h
    filter_upwards [h] with z hf hz
    rwa [smul_eq_zero_iff_right <| pow_ne_zero _ (sub_ne_zero.mpr hz)] at hf
  · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp h
    simp only [← hm, ENat.map_coe, WithTop.coe_natCast, sub_eq_top_iff, WithTop.natCast_ne_top,
      or_self, false_iff]
    contrapose! h
    rw [AnalyticAt.order_eq_top_iff]
    rw [← hf.choose_spec.frequently_eq_iff_eventually_eq analyticAt_const]
    apply Eventually.frequently
    filter_upwards [h] with z hfz
    rw [hfz, smul_zero]

/-- The order of a meromorphic function `f` at `z₀` equals an integer `n` iff `f` can locally be
written as `f z = (z - z₀) ^ n • g z`, where `g` is analytic and does not vanish at `z₀`. -/
lemma order_eq_int_iff {f : 𝕜 → E} {x : 𝕜} (hf : MeromorphicAt f x) (n : ℤ) : hf.order = n ↔
    ∃ g : 𝕜 → E, AnalyticAt 𝕜 g x ∧ g x ≠ 0 ∧ ∀ᶠ z in 𝓝[≠] x, f z = (z - x) ^ n • g z := by
  unfold order
  by_cases h : hf.choose_spec.order = ⊤
  · rw [h, ENat.map_top, ← WithTop.coe_natCast, top_sub,
      eq_false_intro WithTop.top_ne_coe, false_iff]
    rw [AnalyticAt.order_eq_top_iff] at h
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
    obtain ⟨g, hg_an, hg_ne, hg_eq⟩ := (AnalyticAt.order_eq_nat_iff _ _).mp h.symm
    replace hg_eq : ∀ᶠ (z : 𝕜) in 𝓝[≠] x, f z = (z - x) ^ (↑m - ↑hf.choose : ℤ) • g z := by
      rw [eventually_nhdsWithin_iff]
      filter_upwards [hg_eq] with z hg_eq hz
      rwa [← smul_right_inj <| zpow_ne_zero _ (sub_ne_zero.mpr hz), ← mul_smul,
        ← zpow_add₀ (sub_ne_zero.mpr hz), ← add_sub_assoc, add_sub_cancel_left, zpow_natCast,
        zpow_natCast]
    exact ⟨fun h ↦ ⟨g, hg_an, hg_ne, h ▸ hg_eq⟩,
      AnalyticAt.unique_eventuallyEq_zpow_smul_nonzero ⟨g, hg_an, hg_ne, hg_eq⟩⟩

/-- The order of a meromorphic function `f` at `z₀` is finite iff f can locally be written as
`f z = (z - z₀) ^ order • g z`, where `g` is analytic and does not vanish at `z₀`. -/
theorem order_ne_top_iff {f : 𝕜 → E} {z₀ : 𝕜} (hf : MeromorphicAt f z₀) :
    hf.order ≠ ⊤ ↔ ∃ (g : 𝕜 → E), AnalyticAt 𝕜 g z₀ ∧ g z₀ ≠ 0 ∧
      f =ᶠ[𝓝[≠] z₀] fun z ↦ (z - z₀) ^ (hf.order.untopD 0) • g z :=
  ⟨fun h ↦ (hf.order_eq_int_iff (hf.order.untopD 0)).1 (WithTop.untopD_of_ne_top h).symm,
    fun h ↦ Option.ne_none_iff_exists'.2 ⟨hf.order.untopD 0,
      (hf.order_eq_int_iff (hf.order.untopD 0)).2 h⟩⟩

/-- The order of a meromorphic function `f` depends only on its behaviour on a pointed
neighborhood. -/
theorem order_congr {f₁ f₂ : 𝕜 → E} {z₀ : 𝕜} (hf₁ : MeromorphicAt f₁ z₀) (h : f₁ =ᶠ[𝓝[≠] z₀] f₂):
    hf₁.order = (hf₁.congr h).order := by
  by_cases hord : hf₁.order = ⊤
  · rw [hord, eq_comm, (hf₁.congr h).order_eq_top_iff]
    rw [hf₁.order_eq_top_iff] at hord
    exact EventuallyEq.rw hord (fun x => Eq (f₂ x)) h.symm
  · obtain ⟨n, hn : hf₁.order = n⟩ := Option.ne_none_iff_exists'.mp hord
    obtain ⟨g, h₁g, h₂g, h₃g⟩ := (hf₁.order_eq_int_iff n).1 hn
    rw [hn, eq_comm, (hf₁.congr h).order_eq_int_iff]
    use g, h₁g, h₂g
    exact EventuallyEq.rw h₃g (fun x => Eq (f₂ x)) h.symm

/-- Compatibility of notions of `order` for analytic and meromorphic functions. -/
lemma _root_.AnalyticAt.meromorphicAt_order {f : 𝕜 → E} {x : 𝕜} (hf : AnalyticAt 𝕜 f x) :
    hf.meromorphicAt.order = hf.order.map (↑) := by
  rcases eq_or_ne hf.order ⊤ with ho | ho
  · rw [ho, ENat.map_top, order_eq_top_iff]
    exact (hf.order_eq_top_iff.mp ho).filter_mono nhdsWithin_le_nhds
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp ho
    simp_rw [← hn, ENat.map_coe, order_eq_int_iff, zpow_natCast]
    rcases (hf.order_eq_nat_iff _).mp hn.symm with ⟨g, h1, h2, h3⟩
    exact ⟨g, h1, h2, h3.filter_mono nhdsWithin_le_nhds⟩

/-- Analytic functions have non-negative orders. -/
theorem _root_.AnalyticAt.meromorphicAt_order_nonneg {f : 𝕜 → E} {z₀ : 𝕜} (hf : AnalyticAt 𝕜 f z₀) :
    0 ≤ hf.meromorphicAt.order := by
  simp [hf.meromorphicAt_order, (by rfl : (0 : WithTop ℤ) = WithTop.map Nat.cast (0 : ℕ∞))]

/-!
## Order at a Point: Behaviour under Ring Operations

We establish additivity of the order under multiplication and taking powers.

TODO: Behaviour under Addition/Subtraction. API unification with analytic functions
-/

/-- The order is additive when multiplying scalar-valued and vector-valued meromorphic functions. -/
theorem order_smul {f : 𝕜 → 𝕜} {g : 𝕜 → E} {x : 𝕜}
    (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    (hf.smul hg).order = hf.order + hg.order := by
  -- Trivial cases: one of the functions vanishes around z₀
  cases h₂f : hf.order with
  | top =>
    simp only [top_add, order_eq_top_iff] at h₂f ⊢
    filter_upwards [h₂f] with z hz using by simp [hz]
  | coe m =>
    cases h₂g : hg.order with
    | top =>
      simp only [add_top, order_eq_top_iff] at h₂g ⊢
      filter_upwards [h₂g] with z hz using by simp [hz]
    | coe n => -- Non-trivial case: both functions do not vanish around z₀
      rw [← WithTop.coe_add, order_eq_int_iff]
      obtain ⟨F, h₁F, h₂F, h₃F⟩ := (hf.order_eq_int_iff _).1 h₂f
      obtain ⟨G, h₁G, h₂G, h₃G⟩ := (hg.order_eq_int_iff _).1 h₂g
      use F • G, h₁F.smul h₁G, by simp [h₂F, h₂G]
      filter_upwards [self_mem_nhdsWithin, h₃F, h₃G] with a ha hfa hga
      simp [hfa, hga, smul_comm (F a), zpow_add₀ (sub_ne_zero.mpr ha), mul_smul]

/-- The order is additive when multiplying meromorphic functions. -/
theorem order_mul {f g : 𝕜 → 𝕜} {x : 𝕜} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    (hf.mul hg).order = hf.order + hg.order :=
  hf.order_smul hg

/-- The order multiplies by `n` when taking a meromorphic function to its `n`th power. -/
theorem order_pow {f : 𝕜 → 𝕜} {x : 𝕜} (hf : MeromorphicAt f x) {n : ℕ} :
    (hf.pow n).order = n * hf.order := by
  induction' n with n hn
  · simp
    rw [← WithTop.coe_zero, MeromorphicAt.order_eq_int_iff]
    use 1, analyticAt_const
    simp
  · simp only [pow_add, pow_one, (hf.pow n).order_mul hf, hn, Nat.cast_add, Nat.cast_one]
    cases hf.order
    · rw [add_top]
      rfl
    · norm_cast
      simp only [Nat.cast_add, Nat.cast_one]
      ring

/-- The order multiplies by `n` when taking a meromorphic function to its `n`th power. -/
theorem order_zpow {f : 𝕜 → 𝕜} {x : 𝕜} (hf : MeromorphicAt f x) {n : ℤ} :
    (hf.zpow n).order = n * hf.order := by
  -- Trivial case: n = 0
  by_cases hn : n = 0
  · simp only [hn, zpow_zero, WithTop.coe_zero, zero_mul]
    rw [← WithTop.coe_zero, MeromorphicAt.order_eq_int_iff]
    use 1
    simp only [Pi.one_apply, ne_eq, one_ne_zero, not_false_eq_true, zpow_zero, smul_eq_mul, mul_one,
      eventually_true, and_self, and_true]
    apply analyticAt_const
  -- Trivial case: f locally zero
  by_cases h : hf.order = ⊤
  · rw [h]
    simp only [ne_eq, WithTop.coe_eq_zero, hn, not_false_eq_true, WithTop.mul_top]
    rw [MeromorphicAt.order_eq_top_iff] at *
    filter_upwards [h]
    intro y hy
    simp only [Pi.pow_apply, hy]
    exact zero_zpow n hn
  -- General case
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := hf.order_ne_top_iff.1 h
  have : ↑n * hf.order = ↑(n * (WithTop.untopD 0 hf.order)) := by
    rw [WithTop.coe_mul]
    congr
    exact (WithTop.untopD_of_ne_top h).symm
  rw [this, MeromorphicAt.order_eq_int_iff]
  use g ^ n, h₁g.zpow h₂g
  constructor
  · simp only [Pi.pow_apply, ne_eq]
    rwa [zpow_eq_zero_iff hn]
  · filter_upwards [h₃g]
    intro y hy
    rw [Pi.pow_apply, hy, smul_eq_mul, mul_zpow]
    congr 1
    rw [mul_comm, zpow_mul]

/-- The order of the inverse is the negative of the order. -/
theorem order_inv {f : 𝕜 → 𝕜} {z₀ : 𝕜} (hf : MeromorphicAt f z₀) :
    hf.order = -hf.inv.order := by
  -- Trivial case: f locally zero
  by_cases h₂f : hf.order = ⊤
  · rw [h₂f, ← LinearOrderedAddCommGroupWithTop.neg_top, neg_eq_iff_eq_neg, neg_neg, eq_comm]
    rw [MeromorphicAt.order_eq_top_iff] at *
    filter_upwards [h₂f]
    simp
  rw [(WithTop.untopD_of_ne_top h₂f).symm, eq_comm, neg_eq_iff_eq_neg]
  apply (hf.inv.order_eq_int_iff (-hf.order.untopD 0)).2
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := (hf.order_eq_int_iff (hf.order.untopD 0)).1
    (WithTop.untopD_of_ne_top h₂f).symm
  use g⁻¹, h₁g.inv h₂g, inv_eq_zero.not.2 h₂g
  rw [eventually_nhdsWithin_iff] at *
  filter_upwards [h₃g]
  intro _ h₁a h₂a
  simp only [Pi.inv_apply, h₁a h₂a, smul_eq_mul, mul_inv_rev, zpow_neg]
  ring

end MeromorphicAt

/-!
## Level Sets of the Order Function

TODO: Prove that the set where an analytic function has order in [1,∞) is discrete within its domain
of meromorphy.
-/

namespace MeromorphicOn

variable {f : 𝕜 → E} {U : Set 𝕜} (hf : MeromorphicOn f U)

/-- The set where a meromorphic function has infinite order is clopen in its domain of meromorphy.
-/
theorem isClopen_setOf_order_eq_top : IsClopen { u : U | (hf u.1 u.2).order = ⊤ } := by
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
        · rw [MeromorphicAt.order_eq_top_iff, not_eventually]
          apply Filter.Eventually.frequently
          rw [eventually_nhdsWithin_iff, eventually_nhds_iff]
          use t' \ {z.1}, fun y h₁y h₂y ↦ h₁t' y h₁y.1 h₁y.2, h₂t'.sdiff isClosed_singleton, hw,
            mem_singleton_iff.not.2 (Subtype.coe_ne_coe.mpr h₁w)
      · exact ⟨isOpen_induced h₂t', h₃t'⟩
  · apply isOpen_iff_forall_mem_open.mpr
    intro z hz
    conv =>
      arg 1; intro; left; right; arg 1; intro
      rw [MeromorphicAt.order_eq_top_iff, eventually_nhdsWithin_iff, eventually_nhds_iff]
    simp only [mem_setOf_eq] at hz
    rw [MeromorphicAt.order_eq_top_iff, eventually_nhdsWithin_iff, eventually_nhds_iff] at hz
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

/-- On a connected set, there exists a point where a meromorphic function `f` has finite order iff
`f` has finite order at every point. -/
theorem exists_order_ne_top_iff_forall (hU : IsConnected U) :
    (∃ u : U, (hf u u.2).order ≠ ⊤) ↔ (∀ u : U, (hf u u.2).order ≠ ⊤) := by
  constructor
  · intro h₂f
    have := isPreconnected_iff_preconnectedSpace.1 hU.isPreconnected
    rcases isClopen_iff.1 hf.isClopen_setOf_order_eq_top with h | h
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

/-- On a preconnected set, a meromorphic function has finite order at one point if it has finite
order at another point. -/
theorem order_ne_top_of_isPreconnected {x y : 𝕜} (hU : IsPreconnected U) (h₁x : x ∈ U) (hy : y ∈ U)
    (h₂x : (hf x h₁x).order ≠ ⊤) :
    (hf y hy).order ≠ ⊤ :=
  (hf.exists_order_ne_top_iff_forall ⟨nonempty_of_mem h₁x, hU⟩).1 (by use ⟨x, h₁x⟩) ⟨y, hy⟩

end MeromorphicOn
