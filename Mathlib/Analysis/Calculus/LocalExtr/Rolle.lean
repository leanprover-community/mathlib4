/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Anatole Dedecker
-/
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Algebra.Order.Rolle

open Set Filter Topology

variable {f f' : ℝ → ℝ} {a b l : ℝ}

/-- **Rolle's Theorem** `HasDerivAt` version -/
theorem exists_hasDerivAt_eq_zero (hab : a < b) (hfc : ContinuousOn f (Icc a b)) (hfI : f a = f b)
    (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) : ∃ c ∈ Ioo a b, f' c = 0 :=
  let ⟨c, cmem, hc⟩ := exists_isLocalExtr_Ioo hab hfc hfI
  ⟨c, cmem, hc.hasDerivAt_eq_zero <| hff' c cmem⟩
#align exists_has_deriv_at_eq_zero exists_hasDerivAt_eq_zero

/-- **Rolle's Theorem** `deriv` version -/
theorem exists_deriv_eq_zero (hab : a < b) (hfc : ContinuousOn f (Icc a b)) (hfI : f a = f b) :
    ∃ c ∈ Ioo a b, deriv f c = 0 :=
  let ⟨c, cmem, hc⟩ := exists_isLocalExtr_Ioo hab hfc hfI
  ⟨c, cmem, hc.deriv_eq_zero⟩
#align exists_deriv_eq_zero exists_deriv_eq_zero

/-- **Rolle's Theorem**, a version for a function on an open interval: if `f` has derivative `f'`
on `(a, b)` and has the same limit `l` at `𝓝[>] a` and `𝓝[<] b`, then `f' c = 0`
for some `c ∈ (a, b)`.  -/
theorem exists_hasDerivAt_eq_zero' (hab : a < b) (hfa : Tendsto f (𝓝[>] a) (𝓝 l))
    (hfb : Tendsto f (𝓝[<] b) (𝓝 l)) (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) :
    ∃ c ∈ Ioo a b, f' c = 0 :=
  let ⟨c, cmem, hc⟩ := exists_isLocalExtr_Ioo_of_tendsto hab
    (fun x hx ↦ (hff' x hx).continuousAt.continuousWithinAt) hfa hfb
  ⟨c, cmem, hc.hasDerivAt_eq_zero <| hff' c cmem⟩
#align exists_has_deriv_at_eq_zero' exists_hasDerivAt_eq_zero'

/-- **Rolle's Theorem**, a version for a function on an open interval: if `f` has the same limit
`l` at `𝓝[>] a` and `𝓝[<] b`, then `deriv f c = 0` for some `c ∈ (a, b)`. This version
does not require differentiability of `f` because we define `deriv f c = 0` whenever `f` is not
differentiable at `c`. -/
theorem exists_deriv_eq_zero' (hab : a < b) (hfa : Tendsto f (𝓝[>] a) (𝓝 l))
    (hfb : Tendsto f (𝓝[<] b) (𝓝 l)) : ∃ c ∈ Ioo a b, deriv f c = 0 := by
  by_cases h : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x
  · exact exists_hasDerivAt_eq_zero' hab hfa hfb fun x hx => (h x hx).hasDerivAt
  · obtain ⟨c, hc, hcdiff⟩ : ∃ x ∈ Ioo a b, ¬DifferentiableAt ℝ f x
    · push_neg at h; exact h
    exact ⟨c, hc, deriv_zero_of_not_differentiableAt hcdiff⟩
#align exists_deriv_eq_zero' exists_deriv_eq_zero'
