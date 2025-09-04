/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler, Stefan Kebekus
-/
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Meromorphic functions

Main statements:

* `MeromorphicAt`: definition of meromorphy at a point
* `MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt`: `f` is meromorphic at `z₀` iff we have
  `f z = (z - z₀) ^ n • g z` on a punctured neighborhood of `z₀`, for some `n : ℤ`
  and `g` analytic at `z₀`.
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
    rw [Set.mem_compl_iff, Set.mem_singleton_iff, ← sub_eq_zero] at h₂y
    exact smul_eq_zero_iff_right (pow_ne_zero n h₂y) |>.mp h₁y
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
lemma fun_add {f g : 𝕜 → E} {x : 𝕜} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    MeromorphicAt (fun z ↦ f z + g z) x :=
  hf.add hg

@[fun_prop]
lemma smul {f : 𝕜 → 𝕜} {g : 𝕜 → E} {x : 𝕜} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    MeromorphicAt (f • g) x := by
  rcases hf with ⟨m, hf⟩
  rcases hg with ⟨n, hg⟩
  refine ⟨m + n, ?_⟩
  convert hf.fun_smul hg using 2 with z
  rw [Pi.smul_apply', smul_eq_mul]
  module

@[fun_prop]
lemma fun_smul {f : 𝕜 → 𝕜} {g : 𝕜 → E} {x : 𝕜} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    MeromorphicAt (fun z ↦ f z • g z) x :=
  hf.smul hg

@[fun_prop]
lemma mul {f g : 𝕜 → 𝕜} {x : 𝕜} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    MeromorphicAt (f * g) x :=
  hf.smul hg

@[fun_prop]
lemma fun_mul {f g : 𝕜 → 𝕜} {x : 𝕜} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    MeromorphicAt (fun z ↦ f z * g z) x :=
  hf.smul hg

/-- Finite products of meromorphic functions are analytic. -/
@[fun_prop]
theorem prod {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜} {x : 𝕜}
    (h : ∀ σ, MeromorphicAt (f σ) x) :
    MeromorphicAt (∏ n ∈ s, f n) x := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [Finset.prod_empty]
    exact analyticAt_const.meromorphicAt
  | insert σ s hσ hind =>
    rw [Finset.prod_insert hσ]
    exact (h σ).mul hind

/-- Finite products of meromorphic functions are analytic. -/
@[fun_prop]
theorem fun_prod {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜} {x : 𝕜}
    (h : ∀ σ, MeromorphicAt (f σ) x) :
    MeromorphicAt (fun z ↦ ∏ n ∈ s, f n z) x := by
  convert prod h (s := s)
  simp

@[fun_prop]
lemma neg {f : 𝕜 → E} {x : 𝕜} (hf : MeromorphicAt f x) : MeromorphicAt (-f) x := by
  convert (MeromorphicAt.const (-1 : 𝕜) x).smul hf using 1
  ext1 z
  simp only [Pi.neg_apply, Pi.smul_apply', neg_smul, one_smul]

@[fun_prop]
lemma fun_neg {f : 𝕜 → E} {x : 𝕜} (hf : MeromorphicAt f x) : MeromorphicAt (fun z ↦ -f z) x :=
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
lemma fun_sub {f g : 𝕜 → E} {x : 𝕜} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    MeromorphicAt (fun z ↦ f z - g z) x :=
  hf.sub hg

/-- With our definitions, `MeromorphicAt f x` depends only on the values of `f` on a punctured
neighbourhood of `x` (not on `f x`) -/
lemma congr {f g : 𝕜 → E} {x : 𝕜} (hf : MeromorphicAt f x) (hfg : f =ᶠ[𝓝[≠] x] g) :
    MeromorphicAt g x := by
  rcases hf with ⟨m, hf⟩
  refine ⟨m + 1, ?_⟩
  have : AnalyticAt 𝕜 (fun z ↦ z - x) x := analyticAt_id.sub analyticAt_const
  refine (this.fun_smul hf).congr ?_
  rw [eventuallyEq_nhdsWithin_iff] at hfg
  filter_upwards [hfg] with z hz
  rcases eq_or_ne z x with rfl | hn
  · simp
  · rw [hz (Set.mem_compl_singleton_iff.mp hn), pow_succ', mul_smul]

/--
If two functions agree on a punctured neighborhood, then one is meromorphic iff the other is so.
-/
lemma meromorphicAt_congr {f g : 𝕜 → E} {x : 𝕜} (h : f =ᶠ[𝓝[≠] x] g) :
    MeromorphicAt f x ↔ MeromorphicAt g x :=
  ⟨fun hf ↦ hf.congr h, fun hg ↦ hg.congr h.symm⟩

@[simp]
lemma update_iff [DecidableEq 𝕜] {f : 𝕜 → E} {z w : 𝕜} {e : E} :
    MeromorphicAt (Function.update f w e) z ↔ MeromorphicAt f z :=
  meromorphicAt_congr (Function.update_eventuallyEq_nhdsNE f w z e)

@[fun_prop]
lemma update [DecidableEq 𝕜] {f : 𝕜 → E} {z} (hf : MeromorphicAt f z) (w e) :
    MeromorphicAt (Function.update f w e) z :=
  update_iff.mpr hf

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
    refine ⟨n + 1, (this.fun_smul <| hg_an.inv hg_ne).congr ?_⟩
    filter_upwards [hg_eq, hg_an.continuousAt.eventually_ne hg_ne] with z hfg hg_ne'
    rcases eq_or_ne z x with rfl | hz_ne
    · simp only [sub_self, pow_succ, mul_zero, zero_smul]
    · simp_rw [smul_eq_mul] at hfg ⊢
      have aux1 : f z ≠ 0 := by
        have : (z - x) ^ n * g z ≠ 0 := mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hz_ne)) hg_ne'
        rw [← hfg, mul_ne_zero_iff] at this
        exact this.2
      simp [field, pow_succ', mul_assoc, hfg]

@[fun_prop]
lemma fun_inv {f : 𝕜 → 𝕜} {x : 𝕜} (hf : MeromorphicAt f x) : MeromorphicAt (fun z ↦ (f z)⁻¹) x :=
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
lemma fun_div {f g : 𝕜 → 𝕜} {x : 𝕜} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    MeromorphicAt (fun z ↦ f z / g z) x :=
  hf.div hg

@[fun_prop]
lemma pow {f : 𝕜 → 𝕜} {x : 𝕜} (hf : MeromorphicAt f x) (n : ℕ) : MeromorphicAt (f ^ n) x := by
  induction n with
  | zero => simpa only [pow_zero] using MeromorphicAt.const 1 x
  | succ m hm => simpa only [pow_succ] using hm.mul hf

@[fun_prop]
lemma fun_pow {f : 𝕜 → 𝕜} {x : 𝕜} (hf : MeromorphicAt f x) (n : ℕ) :
    MeromorphicAt (fun z ↦ (f z) ^ n) x :=
  hf.pow n

@[fun_prop]
lemma zpow {f : 𝕜 → 𝕜} {x : 𝕜} (hf : MeromorphicAt f x) (n : ℤ) : MeromorphicAt (f ^ n) x := by
  cases n with
  | ofNat m => simpa only [Int.ofNat_eq_coe, zpow_natCast] using hf.pow m
  | negSucc m => simpa only [zpow_negSucc, inv_iff] using hf.pow (m + 1)

@[fun_prop]
lemma fun_zpow {f : 𝕜 → 𝕜} {x : 𝕜} (hf : MeromorphicAt f x) (n : ℤ) :
    MeromorphicAt (fun z ↦ (f z) ^ n) x :=
  hf.zpow n

/-- If a function is meromorphic at a point, then it is continuous at nearby points. -/
theorem eventually_continuousAt {f : 𝕜 → E} {x : 𝕜}
    (h : MeromorphicAt f x) : ∀ᶠ y in 𝓝[≠] x, ContinuousAt f y := by
  obtain ⟨n, h⟩ := h
  have : ∀ᶠ y in 𝓝[≠] x, ContinuousAt (fun z ↦ (z - x) ^ n • f z) y :=
    nhdsWithin_le_nhds h.eventually_continuousAt
  filter_upwards [this, self_mem_nhdsWithin] with y hy h'y
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at h'y
  have : ContinuousAt (fun z ↦ ((z - x) ^ n)⁻¹) y :=
    ContinuousAt.inv₀ (by fun_prop) (by simp [sub_eq_zero, h'y])
  apply (this.smul hy).congr
  filter_upwards [eventually_ne_nhds h'y] with z hz
  simp [smul_smul, hz, sub_eq_zero]

/-- In a complete space, a function which is meromorphic at a point is analytic at all nearby
points. The completeness assumption can be dispensed with if one assumes that `f` is meromorphic
on a set around `x`, see `MeromorphicOn.eventually_analyticAt`. -/
theorem eventually_analyticAt [CompleteSpace E] {f : 𝕜 → E} {x : 𝕜}
    (h : MeromorphicAt f x) : ∀ᶠ y in 𝓝[≠] x, AnalyticAt 𝕜 f y := by
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

lemma iff_eventuallyEq_zpow_smul_analyticAt {f : 𝕜 → E} {x : 𝕜} : MeromorphicAt f x ↔
    ∃ (n : ℤ) (g : 𝕜 → E), AnalyticAt 𝕜 g x ∧ ∀ᶠ z in 𝓝[≠] x, f z = (z - x) ^ n • g z := by
  refine ⟨fun ⟨n, hn⟩ ↦ ⟨-n, _, ⟨hn, eventually_nhdsWithin_iff.mpr ?_⟩⟩, ?_⟩
  · filter_upwards with z hz
    match_scalars
    simp [sub_ne_zero.mpr hz]
  · refine fun ⟨n, g, hg_an, hg_eq⟩ ↦ MeromorphicAt.congr ?_ (EventuallyEq.symm hg_eq)
    exact (((MeromorphicAt.id x).sub (.const _ x)).zpow _).smul hg_an.meromorphicAt

end MeromorphicAt

/-- Meromorphy of a function on a set. -/
def MeromorphicOn (f : 𝕜 → E) (U : Set 𝕜) : Prop := ∀ x ∈ U, MeromorphicAt f x

lemma AnalyticOnNhd.meromorphicOn {f : 𝕜 → E} {U : Set 𝕜} (hf : AnalyticOnNhd 𝕜 f U) :
    MeromorphicOn f U :=
  fun x hx ↦ (hf x hx).meromorphicAt

namespace MeromorphicOn

variable {s t : 𝕜 → 𝕜} {f g : 𝕜 → E} {U : Set 𝕜}
  (hs : MeromorphicOn s U) (ht : MeromorphicOn t U)
  (hf : MeromorphicOn f U) (hg : MeromorphicOn g U)

/--
If `f` is meromorphic on `U`, if `g` agrees with `f` on a codiscrete subset of `U` and outside of
`U`, then `g` is also meromorphic on `U`.
-/
theorem congr_codiscreteWithin_of_eqOn_compl (hf : MeromorphicOn f U)
    (h₁ : f =ᶠ[codiscreteWithin U] g) (h₂ : Set.EqOn f g Uᶜ) :
    MeromorphicOn g U := by
  intro x hx
  apply (hf x hx).congr
  simp_rw [EventuallyEq, Filter.Eventually, mem_codiscreteWithin,
    disjoint_principal_right] at h₁
  filter_upwards [h₁ x hx] with a ha
  simp at ha
  tauto

/--
If `f` is meromorphic on an open set `U`, if `g` agrees with `f` on a codiscrete subset of `U`, then
`g` is also meromorphic on `U`.
-/
theorem congr_codiscreteWithin (hf : MeromorphicOn f U) (h₁ : f =ᶠ[codiscreteWithin U] g)
    (h₂ : IsOpen U) :
    MeromorphicOn g U := by
  intro x hx
  apply (hf x hx).congr
  simp_rw [EventuallyEq, Filter.Eventually, mem_codiscreteWithin,
    disjoint_principal_right] at h₁
  have : U ∈ 𝓝[≠] x := by
    apply mem_nhdsWithin.mpr
    use U, h₂, hx, Set.inter_subset_left
  filter_upwards [this, h₁ x hx] with a h₁a h₂a
  simp only [Set.mem_compl_iff, Set.mem_diff, Set.mem_setOf_eq, not_and] at h₂a
  tauto

lemma id {U : Set 𝕜} : MeromorphicOn id U := fun x _ ↦ .id x

lemma const (e : E) {U : Set 𝕜} : MeromorphicOn (fun _ ↦ e) U :=
  fun x _ ↦ .const e x

section arithmetic

include hf in
lemma mono_set {V : Set 𝕜} (hv : V ⊆ U) : MeromorphicOn f V := fun x hx ↦ hf x (hv hx)

include hf hg in
lemma add : MeromorphicOn (f + g) U := fun x hx ↦ (hf x hx).add (hg x hx)

include hf hg in
lemma fun_add : MeromorphicOn (fun z ↦ f z + g z) U := fun x hx ↦ (hf x hx).add (hg x hx)

include hf hg in
lemma sub : MeromorphicOn (f - g) U := fun x hx ↦ (hf x hx).sub (hg x hx)

include hf hg in
lemma fun_sub : MeromorphicOn (fun z ↦ f z - g z) U := fun x hx ↦ (hf x hx).sub (hg x hx)

include hf in
lemma neg : MeromorphicOn (-f) U := fun x hx ↦ (hf x hx).neg

include hf in
lemma fun_neg : MeromorphicOn (fun z ↦ -f z) U := fun x hx ↦ (hf x hx).neg

@[simp] lemma neg_iff : MeromorphicOn (-f) U ↔ MeromorphicOn f U :=
  ⟨fun h ↦ by simpa only [neg_neg] using h.neg, neg⟩

include hs hf in
lemma smul : MeromorphicOn (s • f) U := fun x hx ↦ (hs x hx).smul (hf x hx)

include hs hf in
lemma fun_smul : MeromorphicOn (fun z ↦ s z • f z) U := fun x hx ↦ (hs x hx).smul (hf x hx)

include hs ht in
lemma mul : MeromorphicOn (s * t) U := fun x hx ↦ (hs x hx).mul (ht x hx)

include hs ht in
lemma fun_mul : MeromorphicOn (fun z ↦ s z * t z) U := fun x hx ↦ (hs x hx).mul (ht x hx)

/-- Finite products of meromorphic functions are analytic. -/
lemma prod {U : Set 𝕜} {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜}
    (h : ∀ σ, MeromorphicOn (f σ) U) :
    MeromorphicOn (∏ n ∈ s, f n) U :=
  fun z hz ↦ MeromorphicAt.prod (fun σ ↦ h σ z hz)

/-- Finite products of meromorphic functions are analytic. -/
lemma fun_prod {U : Set 𝕜} {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜}
    (h : ∀ σ, MeromorphicOn (f σ) U) :
    MeromorphicOn (fun z ↦ ∏ n ∈ s, f n z) U :=
  fun z hz ↦ MeromorphicAt.fun_prod (fun σ ↦ h σ z hz)

include hs in
lemma inv : MeromorphicOn s⁻¹ U := fun x hx ↦ (hs x hx).inv

include hs in
lemma fun_inv : MeromorphicOn (fun z ↦ s⁻¹ z) U := fun x hx ↦ (hs x hx).inv

@[simp] lemma inv_iff : MeromorphicOn s⁻¹ U ↔ MeromorphicOn s U :=
  ⟨fun h ↦ by simpa only [inv_inv] using h.inv, inv⟩

include hs ht in
lemma div : MeromorphicOn (s / t) U := fun x hx ↦ (hs x hx).div (ht x hx)

include hs ht in
lemma fun_div : MeromorphicOn (fun z ↦ s z / t z) U := fun x hx ↦ (hs x hx).div (ht x hx)

include hs in
lemma pow (n : ℕ) : MeromorphicOn (s ^ n) U := fun x hx ↦ (hs x hx).pow _

include hs in
lemma fun_pow (n : ℕ) : MeromorphicOn (fun z ↦ s z ^ n) U := fun x hx ↦ (hs x hx).pow _

include hs in
lemma zpow (n : ℤ) : MeromorphicOn (s ^ n) U := fun x hx ↦ (hs x hx).zpow _

include hs in
lemma fun_zpow (n : ℤ) : MeromorphicOn (fun z ↦ s z ^ n) U := fun x hx ↦ (hs x hx).zpow _

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
