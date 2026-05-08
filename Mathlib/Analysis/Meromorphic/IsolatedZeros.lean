/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Meromorphic.Basic

/-!
# Principles of Isolated Zeros and Identity Principles for Meromorphic Functions

In line with results in `Mathlib.Analysis.Analytic.IsolatedZeros` and
`Mathlib.Analysis.Analytic.Uniqueness`, this file establishes principles of isolated zeros and
identity principles for meromorphic functions.

Compared to the results for analytic functions, the principles established here are a little more
complicated to state. This is because meromorphic functions can be modified at will along discrete
subsets and still remain meromorphic.
-/

public section

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {U : Set 𝕜} {x : 𝕜} {f g : 𝕜 → E}

open Filter Topology

namespace MeromorphicAt

/-!
## Principles of Isolated Zeros
-/

/--
The principle of isolated zeros: If `f` is meromorphic at `x`, then `f` vanishes eventually in a
punctured neighborhood of `x` iff it vanishes frequently in punctured neighborhoods.

See `AnalyticAt.frequently_zero_iff_eventually_zero` for a stronger result in the analytic case.
-/
theorem frequently_zero_iff_eventuallyEq_zero (hf : MeromorphicAt f x) :
    (∃ᶠ z in 𝓝[≠] x, f z = 0) ↔ f =ᶠ[𝓝[≠] x] 0 :=
  ⟨hf.eventually_eq_zero_or_eventually_ne_zero.resolve_right, fun h ↦ h.frequently⟩

/--
Variant of the principle of isolated zeros: Let `U` be a subset of `𝕜` and assume that `x ∈ U` is
not an isolated point of `U`. If a function `f` is meromorphic at `x` and vanishes along a subset
that is codiscrete within `U`, then `f` vanishes in a punctured neighbourhood of `f`.

For a typical application, let `U` be a path in the complex plane and let `x` be one of the end
points. If `f` is meromorphic at `x` and vanishes on `U`, then it will vanish in a punctured
neighbourhood of `x`, which intersects `U` non-trivially but is not contained in `U`.

The assumption that `x` is not an isolated point of `U` is expressed as `AccPt x (𝓟 U)`. See
`accPt_iff_frequently` and `accPt_iff_frequently_nhdsNE` for useful reformulations.
-/
theorem eventuallyEq_zero_nhdsNE_of_eventuallyEq_zero_codiscreteWithin (hf : MeromorphicAt f x)
    (h₁x : x ∈ U) (h₂x : AccPt x (𝓟 U)) (h : f =ᶠ[codiscreteWithin U] 0) :
    f =ᶠ[𝓝[≠] x] 0 := by
  rw [← hf.frequently_zero_iff_eventuallyEq_zero]
  apply ((accPt_iff_frequently_nhdsNE.1 h₂x).and_eventually
    (mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 h x h₁x)).mp
  filter_upwards
  intro a
  simp_rw [Pi.zero_apply]
  rw [(by rfl : ({x | f x = 0} ∪ Uᶜ) a ↔ a ∈ {x | f x = 0} ∪ Uᶜ)]
  simp_all

/-!
## Identity Principles
-/

/--
Formulation of `MeromorphicAt.frequently_zero_iff_eventuallyEq_zero` as an identity principle: If
`f` and `g` are meromorphic at `x`, then `f` and `g` agree eventually in a punctured neighborhood of
`x` iff they agree at points arbitrarily close to (but different from) `x`.
-/
theorem frequently_eq_iff_eventuallyEq (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    (∃ᶠ z in 𝓝[≠] x, f z = g z) ↔ f =ᶠ[𝓝[≠] x] g := by
  rw [eventuallyEq_iff_sub, ← (hf.sub hg).frequently_zero_iff_eventuallyEq_zero]
  simp_rw [Pi.sub_apply, sub_eq_zero]

/--
Formulation of `MeromorphicAt.eventuallyEq_zero_nhdsNE_of_eventuallyEq_zero_codiscreteWithin` as an
identity principle: Let `U` be a subset of `𝕜` and assume that `x ∈ U` is not an isolated point of
`U`. If function `f` and `g` are meromorphic at `x` and agree along a subset that is codiscrete
within `U`, then `f` and `g` agree in a punctured neighbourhood of `f`.
-/
theorem eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin (hf : MeromorphicAt f x)
    (hg : MeromorphicAt g x) (h₁x : x ∈ U) (h₂x : AccPt x (𝓟 U)) (h : f =ᶠ[codiscreteWithin U] g) :
    f =ᶠ[𝓝[≠] x] g := by
  rw [eventuallyEq_iff_sub] at *
  apply (hf.sub hg).eventuallyEq_zero_nhdsNE_of_eventuallyEq_zero_codiscreteWithin h₁x h₂x h

/-
Variant of `MeromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin`, as a statement
about meromorphic functions that agree outside a set codiscrete within a perfect set.
-/
theorem eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect (hf : MeromorphicAt f x)
    (hg : MeromorphicAt g x) (hx : x ∈ U) (hU : Preperfect U) (h : f =ᶠ[codiscreteWithin U] g) :
    f =ᶠ[𝓝[≠] x] g :=
  hf.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin hg hx (hU x hx) h

/-
Variant of `MeromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin`, as a statement
about meromorphic functions agreeing in a neighborhood of a preperfect set.
-/
theorem eventually_nhdsSet_eventuallyEq_codiscreteWithin (hf : MeromorphicOn f U)
    (hg : MeromorphicOn g U) (hU : Preperfect U) (h : f =ᶠ[codiscreteWithin U] g) :
    ∀ᶠ x in 𝓝ˢ U, f =ᶠ[𝓝[≠] x] g := by
  rw [eventually_nhdsSet_iff_exists]
  use {x | f =ᶠ[𝓝[≠] x] g}
  simp only [Set.mem_setOf_eq, imp_self, implies_true, and_true]
  constructor
  · apply isOpen_setOf_eventually_nhdsWithin
  · intro x hx
    rw [Set.mem_setOf]
    exact eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin (hf x hx) (hg x hx) hx (hU x hx) h

end MeromorphicAt
