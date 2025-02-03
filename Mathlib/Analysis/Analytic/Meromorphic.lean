/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler, Stefan Kebekus
-/
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Algebra.Order.AddGroupWithTop

/-!
# Meromorphic functions

Main statements:

* `MeromorphicAt`: definition of meromorphy at a point
* `MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt`: `f` is meromorphic at `z₀` iff we have
  `f z = (z - z₀) ^ n • g z` on a punctured nhd of `z₀`, for some `n : ℤ` and `g` analytic at z₀.
* `MeromorphicAt.order`: order of vanishing at `z₀`, as an element of `ℤ ∪ {∞}`
-/

open Filter

open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Meromorphy of `f` at `x` (more precisely, on a punctured neighbourhood of `x`; the value at
`x` itself is irrelevant). -/
@[fun_prop]
def MeromorphicAt (f : 𝕜 → E) (x : 𝕜) :=
  ∃ (n : ℕ), AnalyticAt 𝕜 (fun z ↦ (z - x) ^ n • f z) x

@[fun_prop]
lemma AnalyticAt.meromorphicAt {f : 𝕜 → E} {x : 𝕜} (hf : AnalyticAt 𝕜 f x) :
    MeromorphicAt f x :=
  ⟨0, by simpa only [pow_zero, one_smul]⟩

/- Analogue of the principle of isolated zeros for an analytic function: if a function is
meromorphic at `z₀`, then either it is identically zero in a punctured neighborhood of `z₀`, or it
does not vanish there at all. -/
theorem MeromorphicAt.eventually_eq_zero_or_eventually_ne_zero {f : 𝕜 → E} {z₀ : 𝕜}
    (hf : MeromorphicAt f z₀) :
    (∀ᶠ z in 𝓝[≠] z₀, f z = 0) ∨ (∀ᶠ z in 𝓝[≠] z₀, f z ≠ 0) := by
  obtain ⟨n, h⟩ := hf
  rcases h.eventually_eq_zero_or_eventually_ne_zero with h₁ | h₂
  · left
    filter_upwards [nhdsWithin_le_nhds h₁, self_mem_nhdsWithin] with y h₁y h₂y
    rcases (smul_eq_zero.1 h₁y) with h₃ | h₄
    · exact False.elim (h₂y (sub_eq_zero.1 (pow_eq_zero_iff'.1 h₃).1))
    · assumption
  · right
    filter_upwards [h₂, self_mem_nhdsWithin] with y h₁y h₂y
    exact (smul_ne_zero_iff.1 h₁y).2

namespace MeromorphicAt

lemma id (x : 𝕜) : MeromorphicAt id x := analyticAt_id.meromorphicAt

@[fun_prop]
lemma const (e : E) (x : 𝕜) : MeromorphicAt (fun _ ↦ e) x :=
  analyticAt_const.meromorphicAt

@[fun_prop]
lemma add {f g : 𝕜 → E} {x : 𝕜} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    MeromorphicAt (f + g) x := by
  rcases hf with ⟨m, hf⟩
  rcases hg with ⟨n, hg⟩
  refine ⟨max m n, ?_⟩
  have : (fun z ↦ (z - x) ^ max m n • (f + g) z) = fun z ↦ (z - x) ^ (max m n - m) •
      ((z - x) ^ m • f z) + (z - x) ^ (max m n - n) • ((z - x) ^ n • g z) := by
    simp_rw [← mul_smul, ← pow_add, Nat.sub_add_cancel (Nat.le_max_left _ _),
      Nat.sub_add_cancel (Nat.le_max_right _ _), Pi.add_apply, smul_add]
  rw [this]
  exact (((analyticAt_id.sub analyticAt_const).pow _).smul hf).add
   (((analyticAt_id.sub analyticAt_const).pow _).smul hg)

@[fun_prop]
lemma add' {f g : 𝕜 → E} {x : 𝕜} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    MeromorphicAt (fun z ↦ f z + g z) x :=
  hf.add hg

@[fun_prop]
lemma smul {f : 𝕜 → 𝕜} {g : 𝕜 → E} {x : 𝕜} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    MeromorphicAt (f • g) x := by
  rcases hf with ⟨m, hf⟩
  rcases hg with ⟨n, hg⟩
  refine ⟨m + n, ?_⟩
  convert hf.smul' hg using 2 with z
  rw [Pi.smul_apply', smul_eq_mul]
  module

@[fun_prop]
lemma smul' {f : 𝕜 → 𝕜} {g : 𝕜 → E} {x : 𝕜} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    MeromorphicAt (fun z ↦ f z • g z) x :=
  hf.smul hg

@[fun_prop]
lemma mul {f g : 𝕜 → 𝕜} {x : 𝕜} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    MeromorphicAt (f * g) x :=
  hf.smul hg

@[fun_prop]
lemma mul' {f g : 𝕜 → 𝕜} {x : 𝕜} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    MeromorphicAt (fun z ↦ f z * g z) x :=
  hf.smul hg

@[fun_prop]
lemma neg {f : 𝕜 → E} {x : 𝕜} (hf : MeromorphicAt f x) : MeromorphicAt (-f) x := by
  convert (MeromorphicAt.const (-1 : 𝕜) x).smul hf using 1
  ext1 z
  simp only [Pi.neg_apply, Pi.smul_apply', neg_smul, one_smul]

@[fun_prop]
lemma neg' {f : 𝕜 → E} {x : 𝕜} (hf : MeromorphicAt f x) : MeromorphicAt (fun z ↦ -f z) x :=
  hf.neg

@[simp]
lemma neg_iff {f : 𝕜 → E} {x : 𝕜} :
    MeromorphicAt (-f) x ↔ MeromorphicAt f x :=
  ⟨fun h ↦ by simpa only [neg_neg] using h.neg, MeromorphicAt.neg⟩

@[fun_prop]
lemma sub {f g : 𝕜 → E} {x : 𝕜} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    MeromorphicAt (f - g) x := by
  convert hf.add hg.neg using 1
  ext1 z
  simp_rw [Pi.sub_apply, Pi.add_apply, Pi.neg_apply, sub_eq_add_neg]

@[fun_prop]
lemma sub' {f g : 𝕜 → E} {x : 𝕜} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    MeromorphicAt (fun z ↦ f z - g z) x :=
  hf.sub hg

/-- With our definitions, `MeromorphicAt f x` depends only on the values of `f` on a punctured
neighbourhood of `x` (not on `f x`) -/
lemma congr {f g : 𝕜 → E} {x : 𝕜} (hf : MeromorphicAt f x) (hfg : f =ᶠ[𝓝[≠] x] g) :
    MeromorphicAt g x := by
  rcases hf with ⟨m, hf⟩
  refine ⟨m + 1, ?_⟩
  have : AnalyticAt 𝕜 (fun z ↦ z - x) x := analyticAt_id.sub analyticAt_const
  refine (this.smul' hf).congr ?_
  rw [eventuallyEq_nhdsWithin_iff] at hfg
  filter_upwards [hfg] with z hz
  rcases eq_or_ne z x with rfl | hn
  · simp
  · rw [hz (Set.mem_compl_singleton_iff.mp hn), pow_succ', mul_smul]

@[fun_prop]
lemma inv {f : 𝕜 → 𝕜} {x : 𝕜} (hf : MeromorphicAt f x) : MeromorphicAt f⁻¹ x := by
  rcases hf with ⟨m, hf⟩
  by_cases h_eq : (fun z ↦ (z - x) ^ m • f z) =ᶠ[𝓝 x] 0
  · -- silly case: f locally 0 near x
    refine (MeromorphicAt.const 0 x).congr ?_
    rw [eventuallyEq_nhdsWithin_iff]
    filter_upwards [h_eq] with z hfz hz
    rw [Pi.inv_apply, (smul_eq_zero_iff_right <| pow_ne_zero _ (sub_ne_zero.mpr hz)).mp hfz,
      inv_zero]
  · -- interesting case: use local formula for `f`
    obtain ⟨n, g, hg_an, hg_ne, hg_eq⟩ := hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr h_eq
    have : AnalyticAt 𝕜 (fun z ↦ (z - x) ^ (m + 1)) x :=
      (analyticAt_id.sub analyticAt_const).pow _
    -- use `m + 1` rather than `m` to damp out any silly issues with the value at `z = x`
    refine ⟨n + 1, (this.smul' <| hg_an.inv hg_ne).congr ?_⟩
    filter_upwards [hg_eq, hg_an.continuousAt.eventually_ne hg_ne] with z hfg hg_ne'
    rcases eq_or_ne z x with rfl | hz_ne
    · simp only [sub_self, pow_succ, mul_zero, zero_smul]
    · simp_rw [smul_eq_mul] at hfg ⊢
      have aux1 : f z ≠ 0 := by
        have : (z - x) ^ n * g z ≠ 0 := mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hz_ne)) hg_ne'
        rw [← hfg, mul_ne_zero_iff] at this
        exact this.2
      field_simp [sub_ne_zero.mpr hz_ne]
      rw [pow_succ', mul_assoc, hfg]
      ring

@[fun_prop]
lemma inv' {f : 𝕜 → 𝕜} {x : 𝕜} (hf : MeromorphicAt f x) : MeromorphicAt (fun z ↦ (f z)⁻¹) x :=
  hf.inv

@[simp]
lemma inv_iff {f : 𝕜 → 𝕜} {x : 𝕜} :
    MeromorphicAt f⁻¹ x ↔ MeromorphicAt f x :=
  ⟨fun h ↦ by simpa only [inv_inv] using h.inv, MeromorphicAt.inv⟩

@[fun_prop]
lemma div {f g : 𝕜 → 𝕜} {x : 𝕜} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    MeromorphicAt (f / g) x :=
  (div_eq_mul_inv f g).symm ▸ (hf.mul hg.inv)

@[fun_prop]
lemma div' {f g : 𝕜 → 𝕜} {x : 𝕜} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    MeromorphicAt (fun z ↦ f z / g z) x :=
  hf.div hg

@[fun_prop]
lemma pow {f : 𝕜 → 𝕜} {x : 𝕜} (hf : MeromorphicAt f x) (n : ℕ) : MeromorphicAt (f ^ n) x := by
  induction n with
  | zero => simpa only [pow_zero] using MeromorphicAt.const 1 x
  | succ m hm => simpa only [pow_succ] using hm.mul hf

@[fun_prop]
lemma pow' {f : 𝕜 → 𝕜} {x : 𝕜} (hf : MeromorphicAt f x) (n : ℕ) :
    MeromorphicAt (fun z ↦ (f z) ^ n) x :=
  hf.pow n

@[fun_prop]
lemma zpow {f : 𝕜 → 𝕜} {x : 𝕜} (hf : MeromorphicAt f x) (n : ℤ) : MeromorphicAt (f ^ n) x := by
  induction n with
  | ofNat m => simpa only [Int.ofNat_eq_coe, zpow_natCast] using hf.pow m
  | negSucc m => simpa only [zpow_negSucc, inv_iff] using hf.pow (m + 1)

@[fun_prop]
lemma zpow' {f : 𝕜 → 𝕜} {x : 𝕜} (hf : MeromorphicAt f x) (n : ℤ) :
    MeromorphicAt (fun z ↦ (f z) ^ n) x :=
  hf.zpow n

theorem eventually_analyticAt [CompleteSpace E] {f : 𝕜 → E} {x : 𝕜}
    (h : MeromorphicAt f x) : ∀ᶠ y in 𝓝[≠] x, AnalyticAt 𝕜 f y := by
  rw [MeromorphicAt] at h
  obtain ⟨n, h⟩ := h
  apply AnalyticAt.eventually_analyticAt at h
  refine (h.filter_mono ?_).mp ?_
  · simp [nhdsWithin]
  · rw [eventually_nhdsWithin_iff]
    apply Filter.Eventually.of_forall
    intro y hy hf
    rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hy
    have := ((analyticAt_id (𝕜 := 𝕜).sub analyticAt_const).pow n).inv
      (pow_ne_zero _ (sub_ne_zero_of_ne hy))
    apply (this.smul hf).congr ∘ (eventually_ne_nhds hy).mono
    intro z hz
    simp [smul_smul, hz, sub_eq_zero]

/-- The order of vanishing of a meromorphic function, as an element of `ℤ ∪ ∞` (to include the
case of functions identically 0 near `x`). -/
noncomputable def order {f : 𝕜 → E} {x : 𝕜} (hf : MeromorphicAt f x) : WithTop ℤ :=
  (hf.choose_spec.order.map (↑· : ℕ → ℤ)) - hf.choose

open WithTop.LinearOrderedAddCommGroup

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

/-- The order is additive when multiplying scalar-valued and vector-valued meromorphic functions. -/
theorem order_smul {f : 𝕜 → 𝕜} {g : 𝕜 → E} {x : 𝕜}
    (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    (hf.smul hg).order = hf.order + hg.order := by
  -- Trivial cases: one of the functions vanishes around z₀
  cases' h₂f : hf.order with m h₂f
  · simp only [top_add, order_eq_top_iff] at h₂f ⊢
    filter_upwards [h₂f] with z hz using by simp [hz]
  cases' h₂g : hg.order with n h₂f
  · simp only [add_top, order_eq_top_iff] at h₂g ⊢
    filter_upwards [h₂g] with z hz using by simp [hz]
  -- Non-trivial case: both functions do not vanish around z₀
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

lemma iff_eventuallyEq_zpow_smul_analyticAt {f : 𝕜 → E} {x : 𝕜} : MeromorphicAt f x ↔
    ∃ (n : ℤ) (g : 𝕜 → E), AnalyticAt 𝕜 g x ∧ ∀ᶠ z in 𝓝[≠] x, f z = (z - x) ^ n • g z := by
  refine ⟨fun ⟨n, hn⟩ ↦ ⟨-n, _, ⟨hn, eventually_nhdsWithin_iff.mpr ?_⟩⟩, ?_⟩
  · filter_upwards with z hz
    match_scalars
    field_simp [sub_ne_zero.mpr hz]
  · refine fun ⟨n, g, hg_an, hg_eq⟩ ↦ MeromorphicAt.congr ?_ (EventuallyEq.symm hg_eq)
    exact (((MeromorphicAt.id x).sub (.const _ x)).zpow _).smul hg_an.meromorphicAt

end MeromorphicAt

/-- Meromorphy of a function on a set. -/
def MeromorphicOn (f : 𝕜 → E) (U : Set 𝕜) : Prop := ∀ x ∈ U, MeromorphicAt f x

lemma AnalyticOnNhd.meromorphicOn {f : 𝕜 → E} {U : Set 𝕜} (hf : AnalyticOnNhd 𝕜 f U) :
    MeromorphicOn f U :=
  fun x hx ↦ (hf x hx).meromorphicAt

@[deprecated (since := "2024-09-26")]
alias AnalyticOn.meromorphicOn := AnalyticOnNhd.meromorphicOn

namespace MeromorphicOn

variable {s t : 𝕜 → 𝕜} {f g : 𝕜 → E} {U : Set 𝕜}
  (hs : MeromorphicOn s U) (ht : MeromorphicOn t U)
  (hf : MeromorphicOn f U) (hg : MeromorphicOn g U)

lemma id {U : Set 𝕜} : MeromorphicOn id U := fun x _ ↦ .id x

lemma const (e : E) {U : Set 𝕜} : MeromorphicOn (fun _ ↦ e) U :=
  fun x _ ↦ .const e x

/-- The set where a meromorphic function has infinite order is clopen in its domain of meromorphy.
-/
theorem isClopen_setOf_order_eq_top {U : Set 𝕜} (hf : MeromorphicOn f U) :
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
        simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
        by_cases h₁w : w = z
        · rwa [h₁w]
        · rw [MeromorphicAt.order_eq_top_iff, not_eventually]
          apply Filter.Eventually.frequently
          rw [eventually_nhdsWithin_iff, eventually_nhds_iff]
          use t' \ {z.1}, fun y h₁y h₂y ↦ h₁t' y h₁y.1 h₁y.2, h₂t'.sdiff isClosed_singleton, hw,
            Set.mem_singleton_iff.not.2 (Subtype.coe_ne_coe.mpr h₁w)
      · exact ⟨isOpen_induced h₂t', h₃t'⟩
  · apply isOpen_iff_forall_mem_open.mpr
    intro z hz
    conv =>
      arg 1; intro; left; right; arg 1; intro
      rw [MeromorphicAt.order_eq_top_iff, eventually_nhdsWithin_iff, eventually_nhds_iff]
    simp only [Set.mem_setOf_eq] at hz
    rw [MeromorphicAt.order_eq_top_iff, eventually_nhdsWithin_iff, eventually_nhds_iff] at hz
    obtain ⟨t', h₁t', h₂t', h₃t'⟩ := hz
    use Subtype.val ⁻¹' t'
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, isOpen_induced h₂t', Set.mem_preimage,
      h₃t', and_self, and_true]
    intro w hw
    simp only [Set.mem_setOf_eq]
    -- Trivial case: w = z
    by_cases h₁w : w = z
    · rw [h₁w]
      tauto
    -- Nontrivial case: w ≠ z
    use t' \ {z.1}, fun y h₁y _ ↦ h₁t' y (Set.mem_of_mem_diff h₁y) (Set.mem_of_mem_inter_right h₁y)
    constructor
    · exact h₂t'.sdiff isClosed_singleton
    · apply (Set.mem_diff w).1
      exact ⟨hw, Set.mem_singleton_iff.not.1 (Subtype.coe_ne_coe.2 h₁w)⟩

/-- On a connected set, there exists a point where a meromorphic function `f` has finite order iff
`f` has finite order at every point. -/
theorem exists_order_ne_top_iff_forall {U : Set 𝕜} (hf : MeromorphicOn f U) (hU : IsConnected U) :
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
      have : u ∈ Set.univ := by trivial
      rw [← h] at this
      tauto
  · intro h₂f
    obtain ⟨v, hv⟩ := hU.nonempty
    use ⟨v, hv⟩, h₂f ⟨v, hv⟩

/-- On a preconnected set, a meromorphic function has finite order at one point if it has finite
order at another point. -/
theorem order_ne_top_of_isPreconnected {U : Set 𝕜} {x y : 𝕜} (hf : MeromorphicOn f U)
    (hU : IsPreconnected U) (h₁x : x ∈ U) (hy : y ∈ U) (h₂x : (hf x h₁x).order ≠ ⊤) :
    (hf y hy).order ≠ ⊤ :=
  (hf.exists_order_ne_top_iff_forall ⟨Set.nonempty_of_mem h₁x, hU⟩).1 (by use ⟨x, h₁x⟩) ⟨y, hy⟩

section arithmetic

include hf in
lemma mono_set {V : Set 𝕜} (hv : V ⊆ U) : MeromorphicOn f V := fun x hx ↦ hf x (hv hx)

include hf hg in
lemma add : MeromorphicOn (f + g) U := fun x hx ↦ (hf x hx).add (hg x hx)

include hf hg in
lemma sub : MeromorphicOn (f - g) U := fun x hx ↦ (hf x hx).sub (hg x hx)

include hf in
lemma neg : MeromorphicOn (-f) U := fun x hx ↦ (hf x hx).neg

@[simp] lemma neg_iff : MeromorphicOn (-f) U ↔ MeromorphicOn f U :=
  ⟨fun h ↦ by simpa only [neg_neg] using h.neg, neg⟩

include hs hf in
lemma smul : MeromorphicOn (s • f) U := fun x hx ↦ (hs x hx).smul (hf x hx)

include hs ht in
lemma mul : MeromorphicOn (s * t) U := fun x hx ↦ (hs x hx).mul (ht x hx)

include hs in
lemma inv : MeromorphicOn s⁻¹ U := fun x hx ↦ (hs x hx).inv

@[simp] lemma inv_iff : MeromorphicOn s⁻¹ U ↔ MeromorphicOn s U :=
  ⟨fun h ↦ by simpa only [inv_inv] using h.inv, inv⟩

include hs ht in
lemma div : MeromorphicOn (s / t) U := fun x hx ↦ (hs x hx).div (ht x hx)

include hs in
lemma pow (n : ℕ) : MeromorphicOn (s ^ n) U := fun x hx ↦ (hs x hx).pow _

include hs in
lemma zpow (n : ℤ) : MeromorphicOn (s ^ n) U := fun x hx ↦ (hs x hx).zpow _

end arithmetic

include hf in
lemma congr (h_eq : Set.EqOn f g U) (hu : IsOpen U) : MeromorphicOn g U := by
  refine fun x hx ↦ (hf x hx).congr (EventuallyEq.filter_mono ?_ nhdsWithin_le_nhds)
  exact eventually_of_mem (hu.mem_nhds hx) h_eq

theorem eventually_codiscreteWithin_analyticAt
    [CompleteSpace E] (f : 𝕜 → E) (h : MeromorphicOn f U) :
    ∀ᶠ (y : 𝕜) in codiscreteWithin U, AnalyticAt 𝕜 f y := by
  rw [eventually_iff, mem_codiscreteWithin]
  intro x hx
  rw [disjoint_principal_right]
  apply Filter.mem_of_superset ((h x hx).eventually_analyticAt)
  intro x hx
  simp [hx]

end MeromorphicOn
