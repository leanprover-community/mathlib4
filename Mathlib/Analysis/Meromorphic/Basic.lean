/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler, Stefan Kebekus
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Calculus.Deriv.ZPow
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Meromorphic functions

Main statements:

* `MeromorphicAt`: definition of meromorphy at a point
* `MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt`: `f` is meromorphic at `z₀` iff we have
  `f z = (z - z₀) ^ n • g z` on a punctured neighborhood of `z₀`, for some `n : ℤ`
  and `g` analytic at `z₀`.
-/

@[expose] public section

open Filter Set

open scoped Topology

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜'] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

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

variable {ι : Type*} {s : Finset ι} {F : ι → 𝕜 → 𝕜'} {G : ι → 𝕜 → E}

@[fun_prop]
lemma id (x : 𝕜) : MeromorphicAt id x := analyticAt_id.meromorphicAt

@[fun_prop, simp]
lemma const (e : E) (x : 𝕜) : MeromorphicAt (fun _ ↦ e) x :=
  analyticAt_const.meromorphicAt

variable {x : 𝕜}

@[to_fun (attr := fun_prop)]
lemma add {f g : 𝕜 → E} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
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

@[to_fun (attr := fun_prop)]
lemma smul {f : 𝕜 → 𝕜} {g : 𝕜 → E} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    MeromorphicAt (f • g) x := by
  rcases hf with ⟨m, hf⟩
  rcases hg with ⟨n, hg⟩
  refine ⟨m + n, ?_⟩
  convert hf.smul hg using 2 with z
  simp
  module

@[to_fun (attr := fun_prop)]
lemma mul {f g : 𝕜 → 𝕜'} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    MeromorphicAt (f * g) x := by
  rcases hf with ⟨m, hf⟩
  rcases hg with ⟨n, hg⟩
  refine ⟨m + n, ?_⟩
  convert hf.mul hg using 2 with z
  simp
  module

/-- Finite products of meromorphic functions are meromorphic. -/
@[fun_prop] -- TODO: to_fun generates an unreadable statement, see #32866
theorem prod (hf : ∀ σ ∈ s, MeromorphicAt (F σ) x) :
    MeromorphicAt (∏ i ∈ s, F i) x := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [Finset.prod_empty]
    apply MeromorphicAt.const
  | insert a s ha hs =>
    rw [Finset.prod_insert ha]
    apply (hf a (Finset.mem_insert_self a s)).mul
      (hs (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)))

/-- Finite products of meromorphic functions are meromorphic. -/
@[fun_prop]
theorem fun_prod (h : ∀ σ ∈ s, MeromorphicAt (F σ) x) :
    MeromorphicAt (fun z ↦ ∏ n ∈ s, F n z) x := by
  convert prod h (s := s)
  simp

/-- Finprods of meromorphic functions are meromorphic. -/
@[fun_prop]
theorem finprod {x : 𝕜} (hf : ∀ i, MeromorphicAt (F i) x) :
    MeromorphicAt (∏ᶠ i, F i) x := by
  by_cases h₂f : Function.HasFiniteMulSupport F
  · simp_rw [finprod_eq_prod F h₂f]
    apply prod
    aesop
  simp_rw [finprod_of_not_hasFiniteMulSupport h₂f]
  apply MeromorphicAt.const

/-- Finite sums of meromorphic functions are meromorphic. -/
@[fun_prop] -- TODO: to_fun generates an unreadable statement, see #32866
theorem sum (h : ∀ σ ∈ s, MeromorphicAt (G σ) x) :
    MeromorphicAt (∑ n ∈ s, G n) x := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    exact analyticAt_const.meromorphicAt
  | insert σ s hσ hind =>
    rw [Finset.sum_insert hσ]
    apply (h σ (Finset.mem_insert_self σ s)).add
      (hind (fun τ hτ ↦ h τ (Finset.mem_insert_of_mem hτ)))

/-- Finite sums of meromorphic functions are meromorphic. -/
@[fun_prop]
theorem fun_sum (h : ∀ σ ∈ s, MeromorphicAt (G σ) x) :
    MeromorphicAt (fun z ↦ ∑ n ∈ s, G n z) x := by
  convert sum h (s := s)
  simp

/-- Finsums of meromorphic functions are meromorphic. -/
@[fun_prop]
theorem finsum (hF : ∀ i, MeromorphicAt (F i) x) :
    MeromorphicAt (∑ᶠ i, F i) x := by
  by_cases h : Function.HasFiniteSupport F
  · simp_rw [finsum_eq_sum F h]
    apply sum
    aesop
  simp_rw [finsum_of_not_hasFiniteSupport h]
  apply MeromorphicAt.const

@[to_fun (attr := fun_prop)]
lemma neg {f : 𝕜 → E} (hf : MeromorphicAt f x) : MeromorphicAt (-f) x := by
  convert (MeromorphicAt.const (-1 : 𝕜) x).smul hf using 1
  ext1 z
  simp only [Pi.neg_apply, Pi.smul_apply', neg_smul, one_smul]

@[simp]
lemma neg_iff {f : 𝕜 → E} :
    MeromorphicAt (-f) x ↔ MeromorphicAt f x :=
  ⟨fun h ↦ by simpa only [neg_neg] using h.neg, MeromorphicAt.neg⟩

@[to_fun (attr := fun_prop)]
lemma sub {f g : 𝕜 → E} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    MeromorphicAt (f - g) x := by
  convert hf.add hg.neg using 1
  ext1 z
  simp_rw [Pi.sub_apply, Pi.add_apply, Pi.neg_apply, sub_eq_add_neg]

/--
If `f` is meromorphic at `x`, then `f + g` is meromorphic at `x` if and only if `g` is meromorphic
at `x`.
-/
lemma meromorphicAt_add_iff_meromorphicAt₁ {f g : 𝕜 → E} (hf : MeromorphicAt f x) :
    MeromorphicAt (f + g) x ↔ MeromorphicAt g x := by
  exact ⟨fun h ↦ by simpa using h.sub hf, fun _ ↦ by fun_prop⟩

/--
If `g` is meromorphic at `x`, then `f + g` is meromorphic at `x` if and only if `f` is meromorphic
at `x`.
-/
lemma meromorphicAt_add_iff_meromorphicAt₂ {f g : 𝕜 → E} (hg : MeromorphicAt g x) :
    MeromorphicAt (f + g) x ↔ MeromorphicAt f x := by
  rw [add_comm]
  exact meromorphicAt_add_iff_meromorphicAt₁ hg

/--
If `f` is meromorphic at `x`, then `f - g` is meromorphic at `x` if and only if `g` is meromorphic
at `x`.
-/
lemma meromorphicAt_sub_iff_meromorphicAt₁ {f g : 𝕜 → E} (hf : MeromorphicAt f x) :
    MeromorphicAt (f - g) x ↔ MeromorphicAt g x := by
  exact ⟨fun h ↦ by simpa using h.sub hf, fun _ ↦ by fun_prop⟩

/--
If `g` is meromorphic at `x`, then `f - g` is meromorphic at `x` if and only if `f` is meromorphic
at `x`.
-/
lemma meromorphicAt_sub_iff_meromorphicAt₂ {f g : 𝕜 → E} (hg : MeromorphicAt g x) :
    MeromorphicAt (f - g) x ↔ MeromorphicAt f x := by
  exact ⟨fun h ↦ by simpa using h.add hg, fun _ ↦ by fun_prop⟩

/-- With our definitions, `MeromorphicAt f x` depends only on the values of `f` on a punctured
neighbourhood of `x` (not on `f x`) -/
lemma congr {f g : 𝕜 → E} (hf : MeromorphicAt f x) (hfg : f =ᶠ[𝓝[≠] x] g) :
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
lemma meromorphicAt_congr {f g : 𝕜 → E} (h : f =ᶠ[𝓝[≠] x] g) :
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

@[to_fun (attr := fun_prop)]
lemma inv {f : 𝕜 → 𝕜'} (hf : MeromorphicAt f x) : MeromorphicAt f⁻¹ x := by
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
    · replace hfg := congr_arg (·⁻¹) hfg
      simp only [smul_inv₀] at hfg
      rw [inv_smul_eq_iff₀ (pow_ne_zero m (sub_ne_zero.mpr hz_ne)), smul_comm,
        eq_inv_smul_iff₀ (pow_ne_zero n (sub_ne_zero.mpr hz_ne))] at hfg
      simp [pow_succ', mul_smul, hfg]

@[simp]
lemma inv_iff {f : 𝕜 → 𝕜'} :
    MeromorphicAt f⁻¹ x ↔ MeromorphicAt f x :=
  ⟨fun h ↦ by simpa only [inv_inv] using h.inv, MeromorphicAt.inv⟩

@[to_fun (attr := fun_prop)]
lemma div {f g : 𝕜 → 𝕜'} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    MeromorphicAt (f / g) x :=
  (div_eq_mul_inv f g).symm ▸ (hf.mul hg.inv)

@[to_fun (attr := fun_prop)]
lemma pow {f : 𝕜 → 𝕜'} (hf : MeromorphicAt f x) (n : ℕ) : MeromorphicAt (f ^ n) x := by
  induction n with
  | zero => simpa only [pow_zero] using MeromorphicAt.const 1 x
  | succ m hm => simpa only [pow_succ] using hm.mul hf

@[to_fun (attr := fun_prop)]
lemma zpow {f : 𝕜 → 𝕜'} (hf : MeromorphicAt f x) (n : ℤ) : MeromorphicAt (f ^ n) x := by
  cases n with
  | ofNat m => simpa only [Int.ofNat_eq_natCast, zpow_natCast] using hf.pow m
  | negSucc m => simpa only [zpow_negSucc, inv_iff] using hf.pow (m + 1)

/-- If a function is meromorphic at a point, then it is continuous at nearby points. -/
theorem eventually_continuousAt {f : 𝕜 → E}
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
theorem eventually_analyticAt [CompleteSpace E] {f : 𝕜 → E}
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

lemma iff_eventuallyEq_zpow_smul_analyticAt {f : 𝕜 → E} : MeromorphicAt f x ↔
    ∃ (n : ℤ) (g : 𝕜 → E), AnalyticAt 𝕜 g x ∧ ∀ᶠ z in 𝓝[≠] x, f z = (z - x) ^ n • g z := by
  refine ⟨fun ⟨n, hn⟩ ↦ ⟨-n, _, ⟨hn, eventually_nhdsWithin_iff.mpr ?_⟩⟩, ?_⟩
  · filter_upwards with z hz
    match_scalars
    simp [sub_ne_zero.mpr hz]
  · refine fun ⟨n, g, hg_an, hg_eq⟩ ↦ MeromorphicAt.congr ?_ (EventuallyEq.symm hg_eq)
    exact (((MeromorphicAt.id x).sub (.const _ x)).zpow _).smul hg_an.meromorphicAt

/--
Derivatives of meromorphic functions are meromorphic.
-/
@[fun_prop]
protected theorem deriv [CompleteSpace E] {f : 𝕜 → E} {x : 𝕜} (h : MeromorphicAt f x) :
    MeromorphicAt (deriv f) x := by
  rw [MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt] at h
  obtain ⟨n, g, h₁g, h₂g⟩ := h
  have : _root_.deriv (fun z ↦ (z - x) ^ n • g z)
      =ᶠ[𝓝[≠] x] fun z ↦ (n * (z - x) ^ (n - 1)) • g z + (z - x) ^ n • _root_.deriv g z := by
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds h₁g.eventually_analyticAt,
      eventually_nhdsWithin_of_forall fun _ a ↦ a] with z₀ h₁ h₂
    rw [deriv_fun_smul (DifferentiableAt.zpow (by fun_prop) (by simp_all [sub_ne_zero_of_ne h₂]))
      (by fun_prop), add_comm, deriv_comp_sub_const (f := (· ^ n))]
    aesop
  rw [MeromorphicAt.meromorphicAt_congr (Filter.EventuallyEq.nhdsNE_deriv h₂g),
    MeromorphicAt.meromorphicAt_congr this]
  fun_prop

@[deprecated MeromorphicAt.deriv (since := "2025-12-21")]
theorem fun_deriv [CompleteSpace E] {f : 𝕜 → E} {x : 𝕜} (h : MeromorphicAt f x) :
    MeromorphicAt (fun z ↦ _root_.deriv f z) x :=
  h.deriv

/--
Iterated derivatives of meromorphic functions are meromorphic.
-/
@[fun_prop] theorem iterated_deriv [CompleteSpace E] {n : ℕ} {f : 𝕜 → E} {x : 𝕜}
    (h : MeromorphicAt f x) :
    MeromorphicAt (_root_.deriv^[n] f) x := by
  induction n with
  | zero => exact h
  | succ n IH => simpa only [Function.iterate_succ', Function.comp_apply] using IH.deriv

@[deprecated MeromorphicAt.iterated_deriv (since := "2025-12-21")]
theorem fun_iterated_deriv [CompleteSpace E] {n : ℕ} {f : 𝕜 → E} {x : 𝕜}
    (h : MeromorphicAt f x) :
    MeromorphicAt (fun z ↦ _root_.deriv^[n] f z) x :=
  h.iterated_deriv

end MeromorphicAt

section smul_iff

variable {g : 𝕜 → 𝕜} {x : 𝕜}

lemma meromorphicAt_smul_iff_of_ne_zero {f : 𝕜 → E} (hg : AnalyticAt 𝕜 g x) (hg' : g x ≠ 0) :
    MeromorphicAt (g • f) x ↔ MeromorphicAt f x := by
  refine ⟨fun hfg ↦ ?_, hg.meromorphicAt.smul⟩
  refine (hg.inv hg').meromorphicAt.smul hfg |>.congr ?_
  filter_upwards [(hg.continuousAt.mono_left nhdsWithin_le_nhds).eventually_ne hg'] with z hz
  simp [inv_smul_smul₀ hz]

lemma meromorphicAt_mul_iff_of_ne_zero {f : 𝕜 → 𝕜} (hg : AnalyticAt 𝕜 g x) (hg' : g x ≠ 0) :
    MeromorphicAt (g * f) x ↔ MeromorphicAt f x :=
  meromorphicAt_smul_iff_of_ne_zero hg hg'

end smul_iff

section composition
/-!
### Composition with an analytic function
-/

variable
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace 𝕜' F] [IsScalarTower 𝕜 𝕜' F]
  {x : 𝕜}

/--
The composition of a meromorphic and an analytic function is meromorphic.
-/
lemma MeromorphicAt.comp_analyticAt {f : 𝕜' → F} {g : 𝕜 → 𝕜'}
    (hf : MeromorphicAt f (g x)) (hg : AnalyticAt 𝕜 g x) :
    MeromorphicAt (f ∘ g) x := by
  obtain ⟨r, hr⟩ := hf
  by_cases hg' : analyticOrderAt (g · - g x) x = ⊤
  · -- trivial case: `g` is locally constant near `x`
    refine .congr (.const (f (g x)) x) ?_
    filter_upwards [nhdsWithin_le_nhds <| analyticOrderAt_eq_top.mp hg'] with z hz
    grind
  · -- interesting case: `g z - g x` looks like `(z - x) ^ n` times a non-vanishing function
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hg'
    obtain ⟨h, han, hne, heq⟩ := (hg.fun_sub analyticAt_const).analyticOrderAt_eq_natCast.mp hn.symm
    set j := fun z ↦ (z - g x) ^ r • f z
    have : AnalyticAt 𝕜 (fun i ↦ (h i)⁻¹ ^ r • j (g i)) x :=
      ((han.fun_inv hne).fun_pow r).fun_smul (hr.restrictScalars.comp' hg)
    refine ⟨n * r, this.congr ?_⟩
    filter_upwards [heq, han.continuousAt.tendsto.eventually_ne hne] with z hz hzne
    simp only [j, inv_pow, Function.comp_apply, inv_smul_eq_iff₀ (pow_ne_zero r hzne)]
    rw [hz, smul_comm, ← smul_assoc, pow_mul, smul_pow]

lemma meromorphicAt_comp_iff_of_deriv_ne_zero [CompleteSpace 𝕜] [CharZero 𝕜] {f : 𝕜 → E}
    {g : 𝕜 → 𝕜} (hg : AnalyticAt 𝕜 g x) (hg' : deriv g x ≠ 0) :
    MeromorphicAt (f ∘ g) x ↔ MeromorphicAt f (g x) := by
  refine ⟨fun hf ↦ ?_, (MeromorphicAt.comp_analyticAt · hg)⟩
  let r := hg.hasStrictDerivAt.localInverse _ _ _ hg'
  have hra : AnalyticAt 𝕜 r (g x) := hg.analyticAt_localInverse hg'
  have : r (g x) = x := HasStrictFDerivAt.localInverse_apply_image ..
  rw [← this] at hf
  refine (hf.comp_analyticAt hra).congr (.filter_mono ?_ nhdsWithin_le_nhds)
  exact EventuallyEq.fun_comp (HasStrictDerivAt.eventually_right_inverse ..) f

end composition


/-- Meromorphy of a function on a set. -/
def MeromorphicOn (f : 𝕜 → E) (U : Set 𝕜) : Prop := ∀ x ∈ U, MeromorphicAt f x

lemma AnalyticOnNhd.meromorphicOn {f : 𝕜 → E} {U : Set 𝕜} (hf : AnalyticOnNhd 𝕜 f U) :
    MeromorphicOn f U :=
  fun x hx ↦ (hf x hx).meromorphicAt

namespace MeromorphicOn

variable {s t : 𝕜 → 𝕜'} {f g : 𝕜 → E} {U : Set 𝕜}
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

/--
If two functions differ only on a discrete set of an open, then one is meromorphic iff so is the
other.
-/
theorem _root_.meromorphicOn_congr_codiscreteWithin {f g : 𝕜 → E} (h₁ : f =ᶠ[codiscreteWithin U] g)
    (h₂ : IsOpen U) :
    MeromorphicOn f U ↔ MeromorphicOn g U :=
  ⟨(·.congr_codiscreteWithin h₁ h₂), (·.congr_codiscreteWithin h₁.symm h₂)⟩

lemma id {U : Set 𝕜} : MeromorphicOn id U := fun x _ ↦ .id x

lemma const (e : E) {U : Set 𝕜} : MeromorphicOn (fun _ ↦ e) U :=
  fun x _ ↦ .const e x

section arithmetic

include hf in
lemma mono_set {V : Set 𝕜} (hv : V ⊆ U) : MeromorphicOn f V := fun x hx ↦ hf x (hv hx)

include hf hg in
@[to_fun] lemma add : MeromorphicOn (f + g) U := fun x hx ↦ (hf x hx).add (hg x hx)

include hf hg in
@[to_fun] lemma sub : MeromorphicOn (f - g) U := fun x hx ↦ (hf x hx).sub (hg x hx)

include hf in
@[to_fun] lemma neg : MeromorphicOn (-f) U := fun x hx ↦ (hf x hx).neg

@[simp] lemma neg_iff : MeromorphicOn (-f) U ↔ MeromorphicOn f U :=
  ⟨fun h ↦ by simpa only [neg_neg] using h.neg, neg⟩

@[to_fun] lemma smul {s : 𝕜 → 𝕜} (hs : MeromorphicOn s U) {f : 𝕜 → E} (hf : MeromorphicOn f U) :
    MeromorphicOn (s • f) U :=
  fun x hx ↦ (hs x hx).smul (hf x hx)

include hs ht in
@[to_fun] lemma mul : MeromorphicOn (s * t) U := fun x hx ↦ (hs x hx).mul (ht x hx)

/-- Finite products of meromorphic functions are meromorphic. -/
lemma prod {U : Set 𝕜} {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜'}
    (h : ∀ σ ∈ s, MeromorphicOn (f σ) U) :
    MeromorphicOn (∏ n ∈ s, f n) U :=
  fun z hz ↦ MeromorphicAt.prod (h · · z hz)

/-- Finite products of meromorphic functions are meromorphic. -/
lemma fun_prod {U : Set 𝕜} {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜'}
    (h : ∀ σ ∈ s, MeromorphicOn (f σ) U) :
    MeromorphicOn (fun z ↦ ∏ n ∈ s, f n z) U :=
  fun z hz ↦ MeromorphicAt.fun_prod (h · · z hz)

/-- Finprods of meromorphic functions are meromorphic. -/
lemma finprod {U : Set 𝕜} {ι : Type*} {f : ι → 𝕜 → 𝕜'} (h : ∀ σ, MeromorphicOn (f σ) U) :
    MeromorphicOn (∏ᶠ n, f n) U :=
  fun z hz ↦ MeromorphicAt.finprod (h · z hz)

/-- Finite sums of meromorphic functions are meromorphic. -/
lemma sum {U : Set 𝕜} {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → E}
    (h : ∀ σ ∈ s, MeromorphicOn (f σ) U) :
    MeromorphicOn (∑ n ∈ s, f n) U :=
  fun z hz ↦ MeromorphicAt.sum (h · · z hz)

/-- Finite sums of meromorphic functions are meromorphic. -/
lemma fun_sum {U : Set 𝕜} {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → E}
    (h : ∀ σ, MeromorphicOn (f σ) U) :
    MeromorphicOn (fun z ↦ ∑ n ∈ s, f n z) U :=
  fun z hz ↦ MeromorphicAt.fun_sum (fun σ _ ↦ h σ z hz)

/-- Finsums of meromorphic functions are meromorphic. -/
lemma finsum {U : Set 𝕜} {ι : Type*} {f : ι → 𝕜 → 𝕜'} (h : ∀ σ, MeromorphicOn (f σ) U) :
    MeromorphicOn (∑ᶠ n, f n) U :=
  fun z hz ↦ MeromorphicAt.finsum (h · z hz)

include hs in
@[to_fun] lemma inv : MeromorphicOn s⁻¹ U := fun x hx ↦ (hs x hx).inv

@[simp] lemma inv_iff : MeromorphicOn s⁻¹ U ↔ MeromorphicOn s U :=
  ⟨fun h ↦ by simpa only [inv_inv] using h.inv, inv⟩

include hs ht in
@[to_fun] lemma div : MeromorphicOn (s / t) U := fun x hx ↦ (hs x hx).div (ht x hx)

include hs in
@[to_fun] lemma pow (n : ℕ) : MeromorphicOn (s ^ n) U := fun x hx ↦ (hs x hx).pow _

include hs in
@[to_fun] lemma zpow (n : ℤ) : MeromorphicOn (s ^ n) U := fun x hx ↦ (hs x hx).zpow _

include hf in
/-- Derivatives of meromorphic functions are meromorphic. -/
protected theorem deriv [CompleteSpace E] : MeromorphicOn (deriv f) U := fun z hz ↦ (hf z hz).deriv

include hf in
@[deprecated MeromorphicOn.deriv (since := "2025-12-21")]
theorem fun_deriv [CompleteSpace E] : MeromorphicOn (fun z ↦ _root_.deriv f z) U := hf.deriv

include hf in
/-- Iterated derivatives of meromorphic functions are meromorphic. -/
theorem iterated_deriv [CompleteSpace E] {n : ℕ} : MeromorphicOn (_root_.deriv^[n] f) U :=
  fun z hz ↦ (hf z hz).iterated_deriv

include hf in
@[deprecated MeromorphicOn.iterated_deriv (since := "2025-12-21")]
theorem fun_iterated_deriv [CompleteSpace E] {n : ℕ} :
    MeromorphicOn (fun z ↦ _root_.deriv^[n] f z) U :=
  hf.iterated_deriv

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

/--
The singular set of a meromorphic function is countable.
-/
theorem countable_compl_analyticAt_inter [SecondCountableTopology 𝕜] [CompleteSpace E]
    (h : MeromorphicOn f U) :
    ({z | AnalyticAt 𝕜 f z}ᶜ ∩ U).Countable := by
  apply (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete
    (isDiscrete_of_codiscreteWithin _)
  simpa using eventually_codiscreteWithin_analyticAt f h

end MeromorphicOn

/-- Meromorphy of a function on all of 𝕜. -/
@[fun_prop]
def Meromorphic (f : 𝕜 → E) := ∀ x, MeromorphicAt f x

/-- A function is meromorphic iff it is meromorphic on Set.univ. -/
@[simp]
lemma meromorphicOn_univ {f : 𝕜 → E} : MeromorphicOn f Set.univ ↔ Meromorphic f := by tauto

namespace Meromorphic

variable
  {ι : Type*} {s : Finset ι}
  {f g : 𝕜 → E} {F : ι → 𝕜 → 𝕜'} {G : ι → 𝕜 → E}

@[fun_prop]
lemma meromorphicAt {x : 𝕜} (hf : Meromorphic f) : MeromorphicAt f x := hf x

lemma meromorphicOn {s : Set 𝕜} (hf : Meromorphic f) : MeromorphicOn f s := fun x _ ↦ hf x

@[fun_prop]
lemma const (x : E) : Meromorphic fun _ : 𝕜 ↦ x := fun _ ↦ .const _ _

@[to_fun (attr := fun_prop)]
lemma neg (hf : Meromorphic f) : Meromorphic (-f) := fun x ↦ (hf x).neg

@[to_fun (attr := fun_prop)]
lemma add (hf : Meromorphic f) (hg : Meromorphic g) :
    Meromorphic (f + g) := fun x ↦ (hf x).add (hg x)

@[to_fun (attr := fun_prop)]
theorem sum (h : ∀ σ ∈ s, Meromorphic (G σ)) :
    Meromorphic (∑ n ∈ s, G n) := fun x ↦ MeromorphicAt.sum (h · · x)

@[fun_prop]
theorem finsum (h : ∀ σ, Meromorphic (F σ)) :
    Meromorphic (∑ᶠ σ , F σ) := fun x ↦ MeromorphicAt.finsum (h · x)

@[to_fun (attr := fun_prop)]
lemma sub (hf : Meromorphic f) (hg : Meromorphic g) :
    Meromorphic (f - g) := fun x ↦ (hf x).sub (hg x)

@[to_fun (attr := fun_prop)]
lemma smul {f : 𝕜 → 𝕜} (hf : Meromorphic f) (hg : Meromorphic g) :
    Meromorphic (f • g) := fun x ↦ (hf x).smul (hg x)

@[to_fun (attr := fun_prop)]
lemma mul {f g : 𝕜 → 𝕜'} (hf : Meromorphic f) (hg : Meromorphic g) :
    Meromorphic (f * g) := fun x ↦ (hf x).mul (hg x)

@[to_fun (attr := fun_prop)]
lemma inv {f : 𝕜 → 𝕜'} (hf : Meromorphic f) : Meromorphic f⁻¹ := fun x ↦ (hf x).inv

@[to_fun (attr := fun_prop)]
theorem prod (h : ∀ σ ∈ s, Meromorphic (F σ)) :
    Meromorphic (∏ n ∈ s, F n) := fun x ↦ MeromorphicAt.prod (h · · x)

@[fun_prop]
theorem finprod (h : ∀ σ, Meromorphic (F σ)) :
    Meromorphic (∏ᶠ σ , F σ) := fun x ↦ MeromorphicAt.finprod (h · x)

@[to_fun (attr := fun_prop)]
lemma div {f g : 𝕜 → 𝕜'} (hf : Meromorphic f) (hg : Meromorphic g) :
    Meromorphic (f / g) := fun x ↦ (hf x).div (hg x)

@[to_fun (attr := fun_prop)]
lemma pow {f : 𝕜 → 𝕜'} {n : ℕ} (hf : Meromorphic f) : Meromorphic (f ^ n) := fun x ↦ (hf x).pow n

@[to_fun (attr := fun_prop)]
lemma zpow {f : 𝕜 → 𝕜'} {n : ℤ} (hf : Meromorphic f) : Meromorphic (f ^ n) := fun x ↦ (hf x).zpow n

@[fun_prop]
protected lemma deriv [CompleteSpace E] (hf : Meromorphic f) : Meromorphic (deriv f) :=
  fun x ↦ (hf x).deriv

@[fun_prop]
lemma iterated_deriv [CompleteSpace E] {n : ℕ} (hf : Meromorphic f) :
    Meromorphic (deriv^[n] f) := fun x ↦ (hf x).iterated_deriv

/--
If `f` is meromorphic, if `g` agrees with `f` on a codiscrete set, then `g` is also meromorphic.
-/
theorem congr_codiscrete (hf : Meromorphic f) (h₁ : f =ᶠ[codiscrete 𝕜] g) :
    Meromorphic g := by
  rw [← meromorphicOn_univ] at *
  exact hf.congr_codiscreteWithin (eventuallyEq_of_mem h₁ fun ⦃x⦄ a ↦ a) isOpen_univ

/--
If two functions differ only on a discrete set, then one is meromorphic iff so is the other.
-/
theorem _root_.meromorphic_congr_codiscrete (h₁ : f =ᶠ[codiscrete 𝕜] g) :
    Meromorphic f ↔ Meromorphic g :=
  ⟨(·.congr_codiscrete h₁), (·.congr_codiscrete h₁.symm)⟩

/--
The singular set of a meromorphic function is countable.
-/
theorem countable_compl_analyticAt [SecondCountableTopology 𝕜] [CompleteSpace E]
    (h : Meromorphic f) :
    {z | AnalyticAt 𝕜 f z}ᶜ.Countable := by
  simpa using (h.meromorphicOn (s := univ)).countable_compl_analyticAt_inter

@[deprecated (since := "2025-12-21")] alias MeromorphicOn.countable_compl_analyticAt :=
  countable_compl_analyticAt
@[deprecated (since := "2025-12-21")] alias _root_.MeromorphicOn.countable_compl_analyticAt :=
  countable_compl_analyticAt

/--
Meromorphic functions are measurable.
-/
theorem measurable [MeasurableSpace 𝕜] [SecondCountableTopology 𝕜] [BorelSpace 𝕜]
    [MeasurableSpace E] [CompleteSpace E] [BorelSpace E] (h : Meromorphic f) :
    Measurable f := by
  set s := {z : 𝕜 | AnalyticAt 𝕜 f z}
  have h₁ : sᶜ.Countable := by simpa using h.countable_compl_analyticAt
  have h₁' := h₁.to_subtype
  have h₂ : IsOpen s := isOpen_analyticAt 𝕜 f
  have h₃ : ContinuousOn f s := fun z hz ↦ hz.continuousAt.continuousWithinAt
  exact .of_union_range_cover (.subtype_coe h₂.measurableSet) (.subtype_coe h₁.measurableSet)
    (by simp [-mem_compl_iff]) h₃.restrict.measurable (measurable_of_countable _)

@[deprecated (since := "2025-12-21")] alias MeromorphicOn.measurable := measurable
@[deprecated (since := "2025-12-21")] alias _root_.MeromorphicOn.measurable := measurable

end Meromorphic
