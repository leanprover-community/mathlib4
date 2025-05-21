/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Meromorphic.Basic

/-!
# Principles of Isolated Zeros and Identitiy Principles for Meromorphic Functions

In line with results in `Mathlib.Analysis.Analytic.IsolatedZeros` and
`Mathlib.Analysis.Analytic.Uniqueness`, this file establishes principles of isolated zeros and
identitiy principles for meromorphic functions.

Compared to the results for analytic function, the principles established here are a litte more
complicated to state. This is because meromorphic functions can be modified at will along discrete
subsets and still remain meromorphic.
-/

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
If `f` is mermorphic at `x`, then `f` vanishes in a punctured neighborhood of `x` iff it vanishes at
points arbitrarily close to (but different from) `x`.

See `AnalyticAt.frequently_zero_iff_eventually_zero` for a stronger result in the analytic case.
-/
theorem frequently_zero_iff_eventually_zero (hf : MeromorphicAt f x) :
    (∃ᶠ z in 𝓝[≠] x, f z = 0) ↔ ∀ᶠ z in 𝓝[≠] x, f z = 0 :=
  ⟨hf.eventually_eq_zero_or_eventually_ne_zero.resolve_right, fun h ↦ h.frequently⟩

/--
Variant of `MeromorphicAt.frequently_zero_iff_eventuallyEq_zero`: If `f` is mermorphic at `x`, then
`f` vanishes eventually in a punctured neighborhood of `x` iff it vanishes at points arbitrarily
close to (but different from) `x`.

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
neighbourhood of `x`, which intersects `U` non-trivally but is not contained in `U`.

The assumption that `x` is not an isolated point of `U` is expressed as `Uᶜ ∉ 𝓝[≠] x`.
-/
theorem eventuallyEq_zero_nhdNE_of_eventuallyEq_zero_codiscreteWithin (hf : MeromorphicAt f x)
    (h₁x : x ∈ U) (h₂x : Uᶜ ∉ 𝓝[≠] x) (h : f =ᶠ[codiscreteWithin U] 0) :
    f =ᶠ[𝓝[≠] x] 0 := by
  rw [← hf.frequently_zero_iff_eventuallyEq_zero]
  by_contra hCon
  rw [EventuallyEq, Filter.Eventually, mem_codiscreteWithin] at h
  have := h x h₁x
  simp only [Pi.zero_apply, disjoint_principal_right, Set.compl_diff] at this
  have := inter_mem (not_frequently.1 hCon) this
  simp_all [Set.inter_union_distrib_left, (by tauto_set : {x | ¬f x = 0} ∩ {x | f x = 0} = ∅)]

/-!
## Identity Principles
-/

/--
Formulation of `MeromorphicAt.frequently_zero_iff_eventuallyEq_zero` as an identity principle: If
`f` and `g` are mermorphic at `x`, then `f` and `g` agree eventually in a punctured neighborhood of
`x` iff they agree at points arbitrarily close to (but different from) `x`.
-/
theorem frequently_eq_iff_eventuallyEq (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    (∃ᶠ z in 𝓝[≠] x, f z = g z) ↔ f =ᶠ[𝓝[≠] x] g := by
  rw [eventuallyEq_iff_sub, ← (hf.sub hg).frequently_zero_iff_eventuallyEq_zero]
  simp_rw [Pi.sub_apply, sub_eq_zero]

/--
Formulation of `MeromorphicAt.eventuallyEq_zero_nhdNE_of_eventuallyEq_zero_codiscreteWithin` as an
identity principle: Let `U` be a subset of `𝕜` and assume that `x ∈ U` is not an isolated point of
`U`. If function `f` and `g` are meromorphic at `x` and agree along a subset that is codiscrete
within `U`, then `f` and `g` agree in a punctured neighbourhood of `f`.
-/
theorem eventuallyEq_nhdNE_of_eventuallyEq_codiscreteWithin (hf : MeromorphicAt f x)
    (hg : MeromorphicAt g x) (h₁x : x ∈ U) (h₂x : Uᶜ ∉ 𝓝[≠] x) (h : f =ᶠ[codiscreteWithin U] g) :
    f =ᶠ[𝓝[≠] x] g := by
  rw [eventuallyEq_iff_sub] at *
  apply (hf.sub hg).eventuallyEq_zero_nhdNE_of_eventuallyEq_zero_codiscreteWithin h₁x h₂x h

end MeromorphicAt
