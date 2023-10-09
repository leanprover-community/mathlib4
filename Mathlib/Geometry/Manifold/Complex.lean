/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Uniqueness
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Geometry.Manifold.MFDeriv
import Mathlib.Topology.LocallyConstant.Basic

#align_import geometry.manifold.complex from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-! # Holomorphic functions on complex manifolds

Thanks to the rigidity of complex-differentiability compared to real-differentiability, there are
many results about complex manifolds with no analogue for manifolds over a general normed field. For
now, this file contains just two (closely related) such results:

## Main results

* `MDifferentiable.isLocallyConstant`: A complex-differentiable function on a compact complex
  manifold is locally constant.
* `MDifferentiable.exists_eq_const_of_compactSpace`: A complex-differentiable function on a compact
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

open scoped Manifold Topology Filter
open Function Set Filter Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]

variable {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℂ F H'}

variable {M : Type*} [TopologicalSpace M] [CompactSpace M] [ChartedSpace H M]
  [SmoothManifoldWithCorners I M]

variable {N : Type*} [TopologicalSpace N] [CompactSpace N] [ChartedSpace H' N]
  [SmoothManifoldWithCorners I' N]


/-- **Maximum modulus principle**: if `f : M → F` is complex differentiable in a neighborhood of `c`
and the norm `‖f z‖` has a local maximum at `c`, then `‖f z‖` is locally constant in a neighborhood
of `c`. This is a manifold version of `Complex.norm_eventually_eq_of_isLocalMax`. -/
theorem Complex.norm_eventually_eq_of_mdifferentiableAt_of_isLocalMax {f : M → F} {c : M}
    (hd : ∀ᶠ z in 𝓝 c, MDifferentiableAt I 𝓘(ℂ, F) f z) (hc : IsLocalMax (norm ∘ f) c) :
    ∀ᶠ y in 𝓝 c, ‖f y‖ = ‖f c‖ := by
  set e := extChartAt I c
  have hI : range I = univ := ModelWithCorners.Boundaryless.range_eq_univ
  have H₁ : 𝓝[range I] (e c) = 𝓝 (e c) := by rw [hI, nhdsWithin_univ]
  have H₂ : map e.symm (𝓝 (e c)) = 𝓝 c
  · rw [← map_extChartAt_symm_nhdsWithin_range I c, H₁]
  rw [← H₂, eventually_map]
  replace hd : ∀ᶠ y in 𝓝 (e c), DifferentiableAt ℂ (f ∘ e.symm) y
  · have : e.target ∈ 𝓝 (e c) := H₁ ▸ extChartAt_target_mem_nhdsWithin I c
    filter_upwards [this, Tendsto.eventually H₂.le hd] with y hyt hy₂
    have hys : e.symm y ∈ (chartAt H c).source
    · rw [← extChartAt_source I c]
      exact (extChartAt I c).map_target hyt
    have hfy : f (e.symm y) ∈ (chartAt F (0 : F)).source := mem_univ _
    rw [mdifferentiableAt_iff_of_mem_source hys hfy, hI, differentiableWithinAt_univ,
      e.right_inv hyt] at hy₂
    exact hy₂.2
  convert norm_eventually_eq_of_isLocalMax hd _
  · exact congr_arg f (extChartAt_to_inv _ _).symm
  · simpa only [IsLocalMax, IsMaxFilter, ← H₂, (· ∘ ·), extChartAt_to_inv] using hc

/-!
### Functions holomorphic on a set
-/

namespace MDifferentiableOn

/-- **Maximum modulus principle** on a connected set. Let `U` be a (pre)connected open set in a
complex normed space. Let `f : E → F` be a function that is complex differentiable on `U`. Suppose
that `‖f x‖` takes its maximum value on `U` at `c ∈ U`. Then `‖f x‖ = ‖f c‖` for all `x ∈ U`. -/
theorem norm_eqOn_of_isPreconnected_of_isMaxOn {f : M → F} {U : Set M} {c : M}
    (hd : MDifferentiableOn I 𝓘(ℂ, F) f U) (hc : IsPreconnected U) (ho : IsOpen U)
    (hcU : c ∈ U) (hm : IsMaxOn (norm ∘ f) U c) : EqOn (norm ∘ f) (const M ‖f c‖) U := by
  set V := {z ∈ U | ‖f z‖ = ‖f c‖}
  suffices : U ⊆ V; exact fun x hx => (this hx).2
  have hVo : IsOpen V
  · refine isOpen_iff_mem_nhds.2 fun x hx ↦ inter_mem (ho.mem_nhds hx.1) ?_
    replace hm : IsLocalMax (‖f ·‖) x :=
      mem_of_superset (ho.mem_nhds hx.1) fun z hz ↦ (hm hz).out.trans_eq hx.2.symm
    replace hd : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℂ, F) f y :=
      (eventually_mem_nhds.2 (ho.mem_nhds hx.1)).mono fun z ↦ hd.mdifferentiableAt
    exact (Complex.norm_eventually_eq_of_mdifferentiableAt_of_isLocalMax hd hm).mono fun _ ↦
      (Eq.trans · hx.2)
  have hVne : (U ∩ V).Nonempty := ⟨c, hcU, hcU, rfl⟩
  set W := U ∩ {z | ‖f z‖ = ‖f c‖}ᶜ
  have hWo : IsOpen W := hd.continuousOn.norm.preimage_open_of_open ho isOpen_ne
  have hdVW : Disjoint V W := disjoint_compl_right.mono inf_le_right inf_le_right
  have hUVW : U ⊆ V ∪ W := fun x hx => (eq_or_ne ‖f x‖ ‖f c‖).imp (.intro hx) (.intro hx)
  exact hc.subset_left_of_subset_union hVo hWo hdVW hUVW hVne

/-- **Maximum modulus principle** on a connected set. Let `U` be a (pre)connected open set in a
complex normed space.  Let `f : E → F` be a function that is complex differentiable on `U`. Suppose
that `‖f x‖` takes its maximum value on `U` at `c ∈ U`. Then `f x = f c` for all `x ∈ U`.

TODO: change assumption from `IsMaxOn` to `IsLocalMax`. -/
theorem eqOn_of_isPreconnected_of_isMaxOn_norm [StrictConvexSpace ℝ F] {f : M → F} {U : Set M}
    {c : M} (hd : MDifferentiableOn I 𝓘(ℂ, F) f U) (hc : IsPreconnected U) (ho : IsOpen U)
    (hcU : c ∈ U) (hm : IsMaxOn (norm ∘ f) U c) : EqOn f (const M (f c)) U := fun x hx =>
  have H₁ : ‖f x‖ = ‖f c‖ := hd.norm_eqOn_of_isPreconnected_of_isMaxOn hc ho hcU hm hx
  -- TODO: Add `MDifferentiableOn.add` etc; does it mean importing `Manifold.Algebra.Monoid`?
  have hd' : MDifferentiableOn I 𝓘(ℂ, F) (f · + f c) U := fun x hx ↦
    ⟨(hd x hx).1.add continuousWithinAt_const, (hd x hx).2.add_const _⟩
  have H₂ : ‖f x + f c‖ = ‖f c + f c‖ :=
    hd'.norm_eqOn_of_isPreconnected_of_isMaxOn hc ho hcU hm.norm_add_self hx
  eq_of_norm_eq_of_norm_add_eq H₁ <| by simp only [H₂, SameRay.rfl.norm_add, H₁, Function.const]

/-- If a function `f : M → F` from a complex manifold to a complex normed space is holomorphic on a
(pre)connected compact open set, then it is a constant on this set. -/
theorem apply_eq_of_isPreconnected_isCompact_isOpen {f : M → F} {U : Set M} {a b : M}
     (hd : MDifferentiableOn I 𝓘(ℂ, F) f U) (hpc : IsPreconnected U) (hc : IsCompact U)
     (ho : IsOpen U) (ha : a ∈ U) (hb : b ∈ U) : f a = f b := by
  refine ?_
  -- Subtract `f b` to avoid the assumption `[StrictConvexSpace ℝ F]`
  wlog hb₀ : f b = 0 generalizing f
  · have hd' : MDifferentiableOn I 𝓘(ℂ, F) (f · - f b) U := fun x hx ↦
      ⟨(hd x hx).1.sub continuousWithinAt_const, (hd x hx).2.sub_const _⟩
    simpa [sub_eq_zero] using this hd' (sub_self _)
  rcases hc.exists_isMaxOn ⟨a, ha⟩ hd.continuousOn.norm with ⟨c, hcU, hc⟩
  have : ∀ x ∈ U, ‖f x‖ = ‖f c‖ :=
    norm_eqOn_of_isPreconnected_of_isMaxOn hd hpc ho hcU hc
  rw [hb₀, ← norm_eq_zero, this a ha, ← this b hb, hb₀, norm_zero]

end MDifferentiableOn

/-!
### Functions holomorphic on the whole manifold

Porting note: lemmas in this section were generalized from `𝓘(ℂ, E)` to an unspecified boundaryless
model so that it works, e.g., on a product of two manifolds without a boundary. This can break
`apply MDifferentiable.apply_eq_of_compactSpace`, use
`apply MDifferentiable.apply_eq_of_compactSpace (I := I)` instead or dot notation on an existing
`MDifferentiable` hypothesis.
-/

namespace MDifferentiable

/-- A holomorphic function on a compact complex manifold is locally constant. -/
protected theorem isLocallyConstant {f : M → F} (hf : MDifferentiable I 𝓘(ℂ, F) f) :
    IsLocallyConstant f :=
  haveI : LocallyConnectedSpace H := I.toHomeomorph.locallyConnectedSpace
  haveI : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace H M
  IsLocallyConstant.of_constant_on_preconnected_clopens fun _ hpc hclo _a ha _b hb ↦
    hf.mdifferentiableOn.apply_eq_of_isPreconnected_isCompact_isOpen hpc
      hclo.isClosed.isCompact hclo.isOpen hb ha
#align mdifferentiable.is_locally_constant MDifferentiable.isLocallyConstant

/-- A holomorphic function on a compact connected complex manifold is constant. -/
theorem apply_eq_of_compactSpace [PreconnectedSpace M] {f : M → F}
    (hf : MDifferentiable I 𝓘(ℂ, F) f) (a b : M) : f a = f b :=
  hf.isLocallyConstant.apply_eq_of_preconnectedSpace _ _
#align mdifferentiable.apply_eq_of_compact_space MDifferentiable.apply_eq_of_compactSpace

/-- A holomorphic function on a compact connected complex manifold is the constant function `f ≡ v`,
for some value `v`. -/
theorem exists_eq_const_of_compactSpace [PreconnectedSpace M] {f : M → F}
    (hf : MDifferentiable I 𝓘(ℂ, F) f) : ∃ v : F, f = Function.const M v :=
  hf.isLocallyConstant.exists_eq_const
#align mdifferentiable.exists_eq_const_of_compact_space MDifferentiable.exists_eq_const_of_compactSpace

end MDifferentiable

namespace MDifferentiableOn

-- move to Mathlib.Topology.ContinuousOn
theorem eventually_nhds_subtype_iff_eventually_nhdsWithin {α : Type*} [TopologicalSpace α]
    (s : Set α) (a : s) (P : α → Prop) :
    (∀ᶠ x in 𝓝[s] (a:α), P x) ↔ (∀ᶠ x : s in 𝓝 a, P x) := by
  trans ∀ᶠ x in 𝓝[s] (a:α), ∃ b : s, P b ∧ (b:α) = x
  · constructor
    · intro H
      have H' : ∀ᶠ x in 𝓝[s] (a:α), x ∈ s := eventually_mem_nhdsWithin
      filter_upwards [H, H'] with x hx hx'
      exact ⟨⟨x, hx'⟩, hx, rfl⟩
    · intro H
      filter_upwards [H]
      rintro _ ⟨x, hx, rfl⟩
      exact hx
  · simp_rw [eventually_iff, mem_nhds_subtype_iff_nhdsWithin]
    rfl

theorem frequently_nhds_subtype_iff_frequently_nhdsWithin {α : Type*} [TopologicalSpace α]
    (s : Set α) (a : s) (P : α → Prop) :
    (∃ᶠ x in 𝓝[s] (a:α), P x) ↔ (∃ᶠ x : s in 𝓝 a, P x) := by
  rw [← not_iff_not, not_frequently, not_frequently]
  apply eventually_nhds_subtype_iff_eventually_nhdsWithin

/-- The **identity principle** for holomorphic functions on a complex manifold: If a holomorphic
function vanishes in a whole neighborhood of a point `z₀`, then it is uniformly zero along a
connected set. -/
theorem eventuallyEq_zero_of_preconnected_of_eventuallyEq_zero {f : M → F} {U V : Set M}
    (hUV : U ⊆ V) (hV : ∀ x ∈ U, V ∈ 𝓝 x) (hf : MDifferentiableOn I 𝓘(ℂ, F) f V)
    (hU : IsPreconnected U) {z₀ : M} (h₀ : z₀ ∈ U) (hfz₀ : f =ᶠ[𝓝 z₀] 0) {z₁ : M} (h₁ : z₁ ∈ U) :
    f =ᶠ[𝓝 z₁] 0 := by
  change ∀ᶠ x in 𝓝 z₀, f x = 0 at hfz₀
  have : PreconnectedSpace U := Subtype.preconnectedSpace hU
  have hI : range I = univ := ModelWithCorners.Boundaryless.range_eq_univ
  let s : Set U := {x : U | ∀ᶠ y in 𝓝 (x:M), f y = 0}
  show ⟨z₁, h₁⟩ ∈ s
  suffices s = univ by convert mem_univ _
  refine IsClopen.eq_univ ⟨?_, ?_⟩ ⟨⟨z₀, h₀⟩, hfz₀⟩
  · rw [isOpen_iff_eventually]
    intro x hx
    let P : M → Prop := fun x ↦ f =ᶠ[𝓝 x] 0
    refine (eventually_nhds_subtype_iff_eventually_nhdsWithin _ x P).mp ?_
    apply eventually_nhdsWithin_of_eventually_nhds (hx.eventually_nhds)
  · rw [isClosed_iff_frequently]
    intro a ha
    have ha' := (frequently_nhds_subtype_iff_frequently_nhdsWithin U a (fun x ↦ ∀ᶠ y in 𝓝 x, f y = 0)).mpr ha
    rw [frequently_iff] at ha'
    let φ := extChartAt I (a:M)
    let W : Set M := connectedComponentIn (φ.source ∩ U) a
    have H1 : W ∈ 𝓝[U] (a:M) := sorry
    have H2 : IsPreconnected (φ '' W ∩ φ.target) := sorry
    have H3 : φ a ∈ φ '' W ∩ φ.target := sorry
    have H6 : φ '' W ∩ φ.target ⊆ φ '' V ∩ φ.target := sorry
    have H7 : ∀ x : E, x ∈ φ '' W ∩ φ.target → φ '' V ∩ φ.target ∈ 𝓝 x := sorry
    let ff := f ∘ φ.symm
    have hff : DifferentiableOn ℂ ff (φ '' V ∩ φ.target) := sorry
    obtain ⟨b, hbU, hbf⟩ := ha' H1
    have hbφ : b ∈ φ.source := sorry
    have H4 : φ b ∈ φ '' W ∩ φ.target := sorry
    have H5 : ∀ᶠ x in 𝓝 (φ b), ff x = 0 := by
      simpa only [← map_extChartAt_symm_nhdsWithin_range' I (a:M) hbφ,
        eventually_map, hI, nhdsWithin_univ] using hbf
    have : ∀ᶠ x in 𝓝 (φ a), ff x = 0 :=
      hff.eventuallyEq_zero_of_preconnected_of_eventuallyEq_zero H6 H7 H2 H4 H5 H3
    simpa only [mem_setOf_eq, ← map_extChartAt_symm_nhdsWithin_range I, hI, nhdsWithin_univ,
      eventually_map]

theorem eqOn_zero_of_preconnected_of_eventuallyEq_zero {f : M → F} {U : Set M} (hU : IsOpen U)
    (hU' : IsPreconnected U) (hf : MDifferentiableOn I 𝓘(ℂ, F) f U) {z₀ : M} (h₀ : z₀ ∈ U)
    (hfz₀ : f =ᶠ[𝓝 z₀] 0) :
    EqOn f 0 U := by
  intro x hx
  refine Filter.Eventually.self_of_nhds (α := M) <|
    hf.eventuallyEq_zero_of_preconnected_of_eventuallyEq_zero (le_refl _) ?_ hU' h₀ hfz₀ hx
  exact fun _ ↦ hU.mem_nhds

/-- The **identity principle** for holomorphic functions on a complex manifold: If two holomorphic
functions coincide in a whole neighborhood of a point `z₀`, then they coincide globally along a
connected set. Also known as **unique continuation** of holomorphic functions. -/
theorem eqOn_of_preconnected_of_eventuallyEq {f g : M → N} {U V : Set M}
    (hUV : U ⊆ V) (hV : ∀ x ∈ U, V ∈ 𝓝 x) (hf : MDifferentiableOn I I' f V)
    (hg : MDifferentiableOn I I' g V) (hU : IsPreconnected U) {z₀ : M} (h₀ : z₀ ∈ U)
    (hfg : f =ᶠ[𝓝 z₀] g) :
    EqOn f g U :=
  sorry

/-- Let `W` be an open set in a complex manifold `M`, and let `f` and `g` be holomorphic
functions on `W` with `f * g ≡ 0` on `W`. Let `x` be a point in `W`.  Then either `f` or `g` is zero
in a neighbourhood of `x`. -/
theorem eventually_zero_or_eventually_zero_of_mul_eq_zero {W : Set M} (hW : IsOpen W)
    {f g : M → ℂ} (hf : MDifferentiableOn I 𝓘(ℂ) f W) (hg : MDifferentiableOn I 𝓘(ℂ) g W)
    (H : ∀ x ∈ W, f x * g x = 0) {a : M} (ha : a ∈ W) :
    (∀ᶠ x in 𝓝 a, f x = 0) ∨ ∀ᶠ x in 𝓝 a, g x = 0 := by
  have : LocallyConnectedSpace M := sorry
  -- In either case we will prove the "eventually" by proving the result on the connected component
  -- of `W` containing `a`. We record the properties of this connected component.
  simp only [eventually_nhds_iff]
  have haW : connectedComponentIn W a ⊆ W := connectedComponentIn_subset W a
  have haW' : IsOpen (connectedComponentIn W a) := hW.connectedComponentIn
  have haW'' : a ∈ connectedComponentIn W a := mem_connectedComponentIn ha
  by_cases H : ∀ x ∈ connectedComponentIn W a, f x = 0
  · -- If `f` vanishes on the connected component, then we are done.
    left
    exact ⟨connectedComponentIn W a, H, haW', haW''⟩
  · right
    refine ⟨connectedComponentIn W a, ?_, haW', haW''⟩
    -- Otherwise there is some `b` in the connected component of `a` at which `f` does not vanish
    push_neg at H
    obtain ⟨b, hbWa, hbf⟩ := H
    have hbW : W ∈ 𝓝 b := hW.mem_nhds (haW hbWa)
    -- By continuity, actually `f` is nonvanishing on a neighbourhood of `f`
    have hbf' : ∀ᶠ x in 𝓝 b, f x ≠ 0 := (hf.continuousOn.continuousAt hbW).eventually_ne hbf
    -- Since `f * g ≡ 0`. `g` vanishes throughout this neighbourhood.
    have hbf' : ∀ᶠ x in 𝓝 b, g x = 0 := by
      filter_upwards [hbf', (hbW : ∀ᶠ x in 𝓝 b, x ∈ W)] with x hxf hxW
      exact (eq_zero_or_eq_zero_of_mul_eq_zero (H x hxW)).resolve_left hxf
    -- So by unique continuation, `g` vanishes on the whole connected component.
    rw [← isConnected_connectedComponentIn_iff] at ha
    exact (hg.mono haW).eqOn_zero_of_preconnected_of_eventuallyEq_zero haW'
      isPreconnected_connectedComponentIn hbWa hbf'

end MDifferentiableOn
