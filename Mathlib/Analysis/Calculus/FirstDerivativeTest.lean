/-
Copyright (c) 2024 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The First-Derivative Test

We prove the first-derivative test in the strong form given on Wikipedia.

The test is proved over the real numbers ℝ
using `monotoneOn_of_deriv_nonneg` from [Mathlib.Analysis.Calculus.MeanValue].

## Main results

* `first_derivative_test_max`: Suppose `f` is a real-valued function of a real variable
  defined on some interval containing the point `a`.
  Further suppose that `f` is continuous at `a` and differentiable on some open interval
  containing `a`, except possibly at `a` itself.

  If there exists a positive number `r > 0` such that for every `x` in `(a − r, a)`
  we have `f′(x) ≥ 0`, and for every `x` in `(a, a + r)` we have `f′(x) ≤ 0`,
  then `f` has a local maximum at `a`.

* `first_derivative_test_min`: The dual of `first_derivative_max`, for minima.

## Tags

derivative test, calculus
-/



/-!
### Some facts about differentiability and continuity

We prove a couple of auxiliary lemmas elaborating on facts such as
"differentiable implies continuous",
"an open interval is an open set", and "`fun x => -x` is antitone". -/


/-- If `f` is differentiable on `(a,b)`, and `x ∈ (a,b)`, then `f` is differentiable at `x`.-/
theorem differentiableOn_differentiableAt_Ioo {𝕜 : Type u_1} [NontriviallyNormedField 𝕜]
  {E : Type u_2} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [LinearOrder E] [OrderClosedTopology E]
    {a x b : E} (hab : x ∈ Set.Ioo a b)
    {F : Type u_3} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E → F}
    (hd₀ : DifferentiableOn 𝕜 f (Set.Ioo a b)) :
    DifferentiableAt 𝕜 f x := by
  apply DifferentiableOn.differentiableAt
  exact hd₀
  refine IsOpen.mem_nhds ?hs.hs hab
  apply isOpen_Ioo

/-- If `f` is continuous at `b` and differentiable on `(a,b)` then `f` is
  continuous on the half-open interval `(a,b]`. -/
theorem continuous_Ioc {𝕜 : Type u_1} [NontriviallyNormedField 𝕜]
  {E : Type u_2} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [LinearOrder E] [OrderClosedTopology E]
    {F : Type u_3} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E → F}
    {a b : E}
    (g₀ : a < b) (h : ContinuousAt f b)
    (hd₀ : DifferentiableOn 𝕜 f (Set.Ioo a b)) : ContinuousOn f (Set.Ioc a b) := by
  intro x hx
  by_cases H : x = b
  · subst H;simp_all;exact ContinuousAt.continuousWithinAt h
  · have hab: x ∈ Set.Ioo a b := by
      contrapose H
      simp_all only [Set.mem_Ioo, and_imp, Set.mem_Ioc, true_and, not_lt, Decidable.not_not]
      apply le_antisymm
      tauto;tauto
    have hD : DifferentiableAt 𝕜 f x := by
      apply differentiableOn_differentiableAt_Ioo;repeat tauto
    apply ContinuousAt.continuousWithinAt
    exact DifferentiableAt.continuousAt hD

/-- If `f` is continuous at `b` and differentiable on `(b,c)` then `f` is
  continuous on the half-open interval `[b,c)`. -/
theorem continuous_Ico {𝕜 : Type u_1} [NontriviallyNormedField 𝕜]
  {E : Type u_2} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [LinearOrder E] [OrderClosedTopology E]
    {F : Type u_3} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E → F}
    {b c : E} (g₁ : b < c)
    (h : ContinuousAt f b) (hd₁ : DifferentiableOn 𝕜 f (Set.Ioo b c)) :
    ContinuousOn f (Set.Ico b c) := by
  intro x hx
  by_cases H : x = b
  · subst H;simp_all;exact ContinuousAt.continuousWithinAt h
  · have hab: x ∈ Set.Ioo b c := by
      refine Set.mem_Ioo.mpr ?_;
      constructor
      · contrapose H; simp_all;
        apply le_antisymm;tauto;tauto
      · exact hx.2
    have hD : DifferentiableAt 𝕜 f x := by
      apply differentiableOn_differentiableAt_Ioo;repeat tauto
    apply ContinuousAt.continuousWithinAt
    · exact DifferentiableAt.continuousAt hD

/-- If `f` is differentiable on a set `s` then so is `-f`. -/
theorem differentiableOn_neg_Ioo
  {f : ℝ → ℝ} {s : Set ℝ} (hd₀ : DifferentiableOn ℝ f s) :
    DifferentiableOn ℝ (-f) s := by
  show DifferentiableOn ℝ ((fun x => -x) ∘ (fun x => f x)) s
  apply DifferentiableOn.comp
  · apply differentiableOn_neg
  · tauto
  · show Set.MapsTo f s Set.univ
    exact fun ⦃x⦄ _ ↦ trivial

/-- If `f'` is the derivative of `f` then  `f' x ≤ 0 → 0 ≤ (-f)' x`. -/
theorem deriv_neg_nonneg {f : ℝ → ℝ} {a b : ℝ}
  (hd₀ : DifferentiableOn ℝ f (Set.Ioo a b))
    (h₀ : ∀ x ∈ Set.Ioo a b, deriv f x ≤ 0) :
    x ∈ Set.Ioo a b → 0 ≤ deriv (-f) x := by
  intro hx
  show 0 ≤ deriv (((fun x => -x) ∘ (fun x => f x))) x
  rw [deriv.comp]
  simp
  apply h₀
  tauto
  refine Differentiable.differentiableAt ?hh₂.h
  · exact differentiable_neg
  · apply DifferentiableOn.differentiableAt
    · exact hd₀
    · refine Ioo_mem_nhds ?hh.hs.ha ?hh.hs.hb
      · exact hx.1
      · linarith[hx.2]

/-- If `f'` is the derivative of `f` then  `0 ≤ f' x → (-f)' x ≤ 0`. -/
theorem deriv_neg_nonpos {f : ℝ → ℝ} {b c : ℝ}
  (hd₁ : DifferentiableOn ℝ f (Set.Ioo b c))
  (h₁ : ∀ x ∈ Set.Ioo b c, 0 ≤ deriv f x) (x : ℝ) :
  x ∈ Set.Ioo b c → deriv (-f) x ≤ 0 := by
        intro hx
        show deriv (((fun x => -x) ∘ (fun x => f x))) x ≤ 0
        rw [deriv.comp]
        simp
        apply h₁;tauto

        apply differentiable_neg
        apply DifferentiableOn.differentiableAt
        exact hd₁
        apply Ioo_mem_nhds
        exact hx.1
        linarith[hx.2]

/-!
### The First-Derivative Test

Using the connection beetween monotonicity and derivatives we obtain the familiar
First-Derivative Test from calculus.
-/

/-- If `f` is monotone on `(a,b]` and antitone on `[b,c)` then `f` has
a local maximum at `b`. -/
lemma isLocalMax_of_mono_anti
  {α : Type u} [TopologicalSpace α] [LinearOrder α] [OrderClosedTopology α]
    {β : Type v} [Preorder β]
    {a b c : α} (g₀ : a < b) (g₁ : b < c)
    {f : α → β}
    (h₀ : MonotoneOn f (Set.Ioc a b))
    (h₁ : AntitoneOn f (Set.Ico b c)) : IsLocalMax f b := by
  unfold IsLocalMax IsMaxFilter Filter.Eventually
  rw [nhds_def, Filter.mem_iInf]
  exists {Set.Ioo a c}, (Set.toFinite _), (fun _ ↦ Set.Ioo a c ∪ {x | f x ≤ f b})
  simp only [Set.mem_setOf_eq, Subtype.forall, Set.mem_singleton_iff, forall_eq, Set.mem_Ioo,
    Set.iInter_coe_set, Set.iInter_iInter_eq_left]

  constructor
  apply Filter.mem_iInf_of_mem
  · simp_all
  · simp_all only [and_self, true_and]; apply isOpen_Ioo
  · ext u
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Ioo, iff_or_self, and_imp]
    intros
    by_cases u < b
    · apply h₀
      · simp_all only [Set.mem_Ioc, true_and]
        apply le_of_lt; tauto
      · simp_all only [Set.mem_Ioc, le_refl, and_self]
      · apply le_of_lt; tauto
    · apply h₁
      · simp_all
      · simp_all
      · apply le_of_not_lt
        tauto

 /-- The First-Derivative Test from calculus, maxima version.
  Suppose `a < b < c`,
    `f : ℝ → ℝ` is continuous at `b`,
    the derivative `f'` is nonnegative on `(a,b)`, and
    the derivative `f'` is nonpositive on `(b,c)`.
  Then `f` has a local maximum at `a`. -/
lemma first_derivative_test_max {f : ℝ → ℝ} {a b c : ℝ}
    (g₀ : a < b) (g₁ : b < c)
    (h : ContinuousAt f b)
    (hd₀ : DifferentiableOn ℝ f (Set.Ioo a b))
    (hd₁ : DifferentiableOn ℝ f (Set.Ioo b c))
    (h₀ :  ∀ x ∈ Set.Ioo a b, 0 ≤ deriv f x)
    (h₁ :  ∀ x ∈ Set.Ioo b c, deriv f x ≤ 0)
    : IsLocalMax f b := by
  apply isLocalMax_of_mono_anti
  exact g₀;exact g₁;
  · apply monotoneOn_of_deriv_nonneg
    · exact convex_Ioc a b
    · apply @continuous_Ioc ℝ;repeat tauto
    · simp_all
    · intro x hx; simp_all;
  · apply antitoneOn_of_deriv_nonpos
    · exact convex_Ico b c
    · apply @continuous_Ico ℝ; repeat tauto
    · simp_all
    · intro x hx; simp_all

/-- The First-Derivative Test from calculus, minima version. -/
lemma first_derivative_test_min {f : ℝ → ℝ} {a b c : ℝ}
  (h : ContinuousAt f b)
    {g₀ : a < b} {g₁ : b < c}
    (hd₀ : DifferentiableOn ℝ f (Set.Ioo a b))
    (hd₁ : DifferentiableOn ℝ f (Set.Ioo b c))
    (h₀ : ∀ x ∈ Set.Ioo a b, deriv f x ≤ 0)
    (h₁ : ∀ x ∈ Set.Ioo b c, 0 ≤ deriv f x)
    : IsLocalMin f b := by
    have Q := @first_derivative_test_max (-f) a b c g₀ g₁
      (by simp_all)
      (by simp_all[differentiableOn_neg_Ioo])
      (by simp_all[differentiableOn_neg_Ioo])
      (by intro x;apply deriv_neg_nonneg;repeat tauto)
      (by intro x;apply deriv_neg_nonpos;repeat tauto)
    unfold IsLocalMin IsMinFilter
    unfold IsLocalMax IsMaxFilter at Q
    simp only [Pi.neg_apply, neg_le_neg_iff] at Q; exact Q
