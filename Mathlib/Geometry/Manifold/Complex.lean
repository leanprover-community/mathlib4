/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth

! This file was ported from Lean 3 source module geometry.manifold.complex
! leanprover-community/mathlib commit f2ce6086713c78a7f880485f7917ea547a215982
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Geometry.Manifold.Mfderiv
import Mathlib.Topology.LocallyConstant.Basic

/-! # Holomorphic functions on complex manifolds

Thanks to the rigidity of complex-differentiability compared to real-differentiability, there are
many results about complex manifolds with no analogue for manifolds over a general normed field. For
now, this file contains just two (closely related) such results:

## Main results

* `mdifferentiable.is_locally_constant`: A complex-differentiable function on a compact complex
  manifold is locally constant.
* `mdifferentiable.exists_eq_const_of_compact_space`: A complex-differentiable function on a compact
  preconnected complex manifold is constant.

## TODO

There is a whole theory to develop here.  Maybe a next step would be to develop a theory of
holomorphic vector/line bundles, including:
* the finite-dimensionality of the space of sections of a holomorphic vector bundle
* Siegel's theorem: for any `n + 1` formal ratios `g 0 / h 0`, `g 1 / h 1`, .... `g n / h n` of
  sections of a fixed line bundle `L` over a complex `n`-manifold, there exists a polynomial
  relationship `P (g 0 / h 0, g 1 / h 1, .... g n / h n) = 0`

Another direction would be to develop the relationship with sheaf theory, building the sheaves of
holomorphic and meromorphic functions on a complex manifold and proving algebraic results about the
stalks, such as the Weierstrass preparation theorem.

-/


open scoped Manifold Topology

open Complex

namespace Mdifferentiable

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℂ E]

variable {F : Type _} [NormedAddCommGroup F] [NormedSpace ℂ F] [StrictConvexSpace ℝ F]

variable {M : Type _} [TopologicalSpace M] [CompactSpace M] [ChartedSpace E M]
  [SmoothManifoldWithCorners 𝓘(ℂ, E) M]

/-- A holomorphic function on a compact complex manifold is locally constant. -/
protected theorem isLocallyConstant {f : M → F} (hf : Mdifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) f) :
    IsLocallyConstant f := by
  haveI : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace E M
  apply IsLocallyConstant.of_constant_on_preconnected_clopens
  intro s hs₂ hs₃ a ha b hb
  have hs₁ : IsCompact s := hs₃.2.IsCompact
  -- for an empty set this fact is trivial
  rcases s.eq_empty_or_nonempty with (rfl | hs')
  · exact False.ndrec _ ha
  -- otherwise, let `p₀` be a point where the value of `f` has maximal norm
  obtain ⟨p₀, hp₀s, hp₀⟩ := hs₁.exists_forall_ge hs' hf.continuous.norm.continuous_on
  -- we will show `f` agrees everywhere with `f p₀`
  suffices s ⊆ {r : M | f r = f p₀} ∩ s by exact (this hb).1.trans (this ha).1.symm;
  clear ha hb a b
  refine' hs₂.subset_clopen _ ⟨p₀, hp₀s, ⟨rfl, hp₀s⟩⟩
  -- closedness of the set of points sent to `f p₀`
  refine' ⟨_, (is_closed_singleton.preimage hf.continuous).inter hs₃.2⟩
  -- we will show this set is open by showing it is a neighbourhood of each of its members
  rw [isOpen_iff_mem_nhds]
  rintro p ⟨hp : f p = _, hps⟩
  -- let `p` be  in this set
  have hps' : s ∈ 𝓝 p := hs₃.1.mem_nhds hps
  have key₁ : (chart_at E p).symm ⁻¹' s ∈ 𝓝 (chart_at E p p) := by
    rw [← Filter.mem_map, (chart_at E p).symm_map_nhds_eq (mem_chart_source E p)]
    exact hps'
  have key₂ : (chart_at E p).target ∈ 𝓝 (chart_at E p p) :=
    (LocalHomeomorph.open_target _).mem_nhds (mem_chart_target E p)
  -- `f` pulled back by the chart at `p` is differentiable around `chart_at E p p`
  have hf' : ∀ᶠ z : E in 𝓝 (chart_at E p p), DifferentiableAt ℂ (f ∘ (chart_at E p).symm) z := by
    refine' Filter.eventually_of_mem key₂ fun z hz => _
    have H₁ : (chart_at E p).symm z ∈ (chart_at E p).source := (chart_at E p).map_target hz
    have H₂ : f ((chart_at E p).symm z) ∈ (chart_at F (0 : F)).source := trivial
    have H := (mdifferentiableAt_iff_of_mem_source H₁ H₂).mp (hf ((chart_at E p).symm z))
    simp only [differentiableWithinAt_univ, mfld_simps] at H 
    simpa [LocalHomeomorph.right_inv _ hz] using H.2
  -- `f` pulled back by the chart at `p` has a local max at `chart_at E p p`
  have hf'' : IsLocalMax (norm ∘ f ∘ (chart_at E p).symm) (chart_at E p p) := by
    refine' Filter.eventually_of_mem key₁ fun z hz => _
    refine' (hp₀ ((chart_at E p).symm z) hz).trans (_ : ‖f p₀‖ ≤ ‖f _‖)
    rw [← hp, LocalHomeomorph.left_inv _ (mem_chart_source E p)]
  -- so by the maximum principle `f` is equal to `f p` near `p`
  obtain ⟨U, hU, hUf⟩ := (Complex.eventually_eq_of_isLocalMax_norm hf' hf'').exists_mem
  have H₁ : chart_at E p ⁻¹' U ∈ 𝓝 p := (chart_at E p).ContinuousAt (mem_chart_source E p) hU
  have H₂ : (chart_at E p).source ∈ 𝓝 p :=
    (LocalHomeomorph.open_source _).mem_nhds (mem_chart_source E p)
  apply Filter.mem_of_superset (Filter.inter_mem hps' (Filter.inter_mem H₁ H₂))
  rintro q ⟨hqs, hq : chart_at E p q ∈ _, hq'⟩
  refine' ⟨_, hqs⟩
  simpa [LocalHomeomorph.left_inv _ hq', hp, -norm_eq_abs] using hUf (chart_at E p q) hq
#align mdifferentiable.is_locally_constant Mdifferentiable.isLocallyConstant

/-- A holomorphic function on a compact connected complex manifold is constant. -/
theorem apply_eq_of_compactSpace [PreconnectedSpace M] {f : M → F}
    (hf : Mdifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) f) (a b : M) : f a = f b :=
  hf.IsLocallyConstant.apply_eq_of_preconnectedSpace _ _
#align mdifferentiable.apply_eq_of_compact_space Mdifferentiable.apply_eq_of_compactSpace

/-- A holomorphic function on a compact connected complex manifold is the constant function `f ≡ v`,
for some value `v`. -/
theorem exists_eq_const_of_compactSpace [PreconnectedSpace M] {f : M → F}
    (hf : Mdifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) f) : ∃ v : F, f = Function.const M v :=
  hf.IsLocallyConstant.exists_eq_const
#align mdifferentiable.exists_eq_const_of_compact_space Mdifferentiable.exists_eq_const_of_compactSpace

end Mdifferentiable

