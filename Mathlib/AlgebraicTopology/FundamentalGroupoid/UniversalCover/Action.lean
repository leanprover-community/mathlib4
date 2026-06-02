/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.UniversalCover.Covering
public import Mathlib.Topology.Covering.Quotient

/-!
# The action of `π₁(X, x₀)` on `UniversalCover x₀`

The fundamental group `FundamentalGroup X x₀` acts on `UniversalCover x₀` by deck
transformations: an element `g` acts on a point represented by a homotopy class of paths
from `x₀` by prepending a loop representing `g⁻¹`. We show the action is **free**,
continuous in the second variable, and **properly discontinuous** (in the local form
required by `IsQuotientCoveringMap`). As a corollary, `proj` is a quotient covering map.

## Convention

`FundamentalGroup X x₀ = End (FundamentalGroupoid.mk x₀)` and mathlib's `End` reverses
multiplication: `g * h = h ≫ g`. Consequently `(g * h).toPath = h.toPath.trans g.toPath`.
The geometric concatenation `[γ] · [p] = [γ.trans p]` is therefore a *right* action of
`FundamentalGroup X x₀`. To present it as a *left* `MulAction`, we use the inverse:

  `g • mk x q := mk x (g⁻¹.toPath.trans q)`.

With this convention, `(g * h) • p = g • (h • p)` follows from `(g * h)⁻¹ = h⁻¹ * g⁻¹`,
`toPath_mul`, and `Path.Homotopic.Quotient.trans_assoc`.

## Main definitions and results

* `instance : MulAction (FundamentalGroup X x₀) (UniversalCover x₀)` —
  the action, with `FaithfulSMul`, `ContinuousConstSMul`, and **freeness** as
  `IsCancelSMul` (all stated without geometric hypotheses on `X`).
  Freeness in the form `g • e = e → g = 1` is then `IsCancelSMul.eq_one_of_smul`.
* `UniversalCover.proj_eq_iff_mem_orbit` — two points have the same projection iff they
  lie in the same orbit.
* `UniversalCover.exists_nhds_smul_disjoint` — **proper discontinuity**: every point has
  a neighborhood whose non-identity translates are disjoint from it.
* `UniversalCover.isQuotientCoveringMap` — packages it all: `proj` is a quotient covering
  map for the `π₁(X, x₀)`-action.
-/

public section
noncomputable section

open scoped unitInterval
open Topology

variable {X : Type*} [TopologicalSpace X] {x₀ : X}

namespace UniversalCover

/-- The `π₁(X, x₀)`-action on the universal cover: a deck transformation by `g` sends
`mk x q` to `mk x (g⁻¹.toPath.trans q)`, i.e. prepends a loop representing `g⁻¹` to the
homotopy class.

The inverse is needed because `End` reverses multiplication; see the module docstring. -/
instance : SMul (FundamentalGroup X x₀) (UniversalCover x₀) where
  smul g p := mk p.proj (g⁻¹.toPath.trans p.path)

@[simp]
theorem smul_mk (g : FundamentalGroup X x₀) (x : X) (q : Path.Homotopic.Quotient x₀ x) :
    g • mk x q = mk x (g⁻¹.toPath.trans q) := rfl

@[simp]
theorem proj_smul (g : FundamentalGroup X x₀) (p : UniversalCover x₀) :
    proj (g • p) = proj p := rfl

instance : MulAction (FundamentalGroup X x₀) (UniversalCover x₀) where
  one_smul p := by
    rcases p with ⟨x, q⟩
    rw [smul_mk, inv_one, FundamentalGroup.toPath_one, Path.Homotopic.Quotient.refl_trans]
  mul_smul g h p := by
    rcases p with ⟨x, q⟩
    rw [smul_mk, smul_mk, smul_mk, mul_inv_rev, FundamentalGroup.toPath_mul,
      Path.Homotopic.Quotient.trans_assoc]

instance : FaithfulSMul (FundamentalGroup X x₀) (UniversalCover x₀) where
  eq_of_smul_eq_smul {g₁ g₂} h := by
    have h' := h (mk x₀ (Path.Homotopic.Quotient.refl x₀))
    rw [smul_mk, smul_mk, Path.Homotopic.Quotient.trans_refl,
      Path.Homotopic.Quotient.trans_refl, mk_inj] at h'
    exact inv_injective h'

instance : ContinuousConstSMul (FundamentalGroup X x₀) (UniversalCover x₀) where
  continuous_const_smul g := by
    rw [(isQuotientMap_ofBasedPath x₀).continuous_iff]
    obtain ⟨γ, hγ⟩ := Quotient.exists_rep (g⁻¹.toPath : Path.Homotopic.Quotient x₀ x₀)
    have hγ' : Path.Homotopic.Quotient.mk γ = g⁻¹.toPath := hγ
    suffices h_cont : Continuous (fun β : BasedPath x₀ ↦
        ofBasedPath x₀ (BasedPath.ofPath (γ.trans β.toPath))) by
      apply h_cont.congr
      intro β
      rw [ofBasedPath_ofPath, Function.comp_apply, ofBasedPath_eq, smul_mk,
        Path.Homotopic.Quotient.mk_trans, hγ']
    refine (continuous_ofBasedPath x₀).comp ?_
    refine Continuous.subtype_mk ?_ _
    refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
    have h_eval : Continuous fun p : BasedPath x₀ × I ↦ p.1.1 p.2 :=
      continuous_eval.comp (continuous_subtype_val.prodMap continuous_id)
    simpa using
      Path.trans_continuous_family (a := fun _ : BasedPath x₀ ↦ x₀)
        (b := fun _ : BasedPath x₀ ↦ x₀)
        (c := fun β : BasedPath x₀ ↦ BasedPath.endpoint β)
        (fun _ ↦ γ) (Path.continuous_uncurry_iff.mpr continuous_const)
        (fun β ↦ β.toPath) h_eval

/-- The action of `π₁(X, x₀)` is **free**: it is a cancellative `SMul`. The proof is
purely algebraic, using right-cancellation in the path-homotopy-class groupoid. -/
instance : IsCancelSMul (FundamentalGroup X x₀) (UniversalCover x₀) where
  right_cancel' a b c h := by
    rcases c with ⟨x, q⟩
    rw [smul_mk, smul_mk, mk_inj] at h
    have h' := congrArg (fun r ↦ r.trans q.symm) h
    simp only [Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.trans_symm,
      Path.Homotopic.Quotient.trans_refl] at h'
    exact inv_injective h'

/-- The action of `π₁(X, x₀)` is transitive on each fiber: two points with the same projection
are in the same orbit. -/
theorem proj_eq_iff_mem_orbit {p₁ p₂ : UniversalCover x₀} :
    proj p₁ = proj p₂ ↔ p₁ ∈ MulAction.orbit (FundamentalGroup X x₀) p₂ := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · rcases p₁ with ⟨x₁, q₁⟩
    rcases p₂ with ⟨x₂, q₂⟩
    have hx : x₁ = x₂ := h
    subst hx
    refine ⟨(FundamentalGroup.fromPath (q₁.trans q₂.symm))⁻¹, ?_⟩
    simp only [smul_mk, inv_inv, Path.Homotopic.Quotient.trans_assoc,
      Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.trans_refl]
  · rintro ⟨g, hg⟩
    rw [← hg, proj_smul]

/-- The endpoint projection is surjective when `X` is path-connected. -/
theorem proj_surjective [PathConnectedSpace X] :
    Function.Surjective (proj : UniversalCover x₀ → X) := fun x ↦
  ⟨mk x (Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x₀ x)), rfl⟩

/-- **Proper discontinuity** of the action (in the local form `IsQuotientCoveringMap`
consumes): every point of the universal cover has a neighborhood whose non-identity
translates are disjoint from it. -/
theorem exists_nhds_smul_disjoint [LocPathConnectedSpace X] [SemilocallySimplyConnectedSpace X]
    (e : UniversalCover x₀) :
    ∃ U ∈ 𝓝 e, ∀ g : FundamentalGroup X x₀,
      ((g • ·) '' U ∩ U).Nonempty → g = 1 := by
  rcases e with ⟨x, q⟩
  obtain ⟨baseU, hU_open, hxU, -, hU_slsc⟩ := exists_pathConnected_slsc_neighborhood x
  let U := sheet baseU hxU q
  have hU_open' : IsOpen U := isOpen_sheet baseU hU_open hxU q
  have hU_mem : mk x q ∈ U := by
    induction q using Quotient.inductionOn with
    | h p => exact ofBasedPath_ofPath p ▸ mem_sheet_self hxU p
  refine ⟨U, hU_open'.mem_nhds hU_mem, fun g hgU ↦ ?_⟩
  obtain ⟨_, ⟨y, hyU, rfl⟩, hgyU⟩ := hgU
  -- The sheet is injective on fibers, so `g • y = y`; freeness (`IsCancelSMul`) gives `g = 1`.
  exact IsCancelSMul.eq_one_of_smul
    (sheet_proj_injOn hU_slsc hxU q hgyU hyU (proj_smul g y))

/-- The endpoint projection from the universal cover is a quotient covering map for the
`π₁(X, x₀)`-action. Combines the action's continuity, transitivity on fibers, and proper
discontinuity into the standard `IsQuotientCoveringMap` package. -/
theorem isQuotientCoveringMap
    [LocPathConnectedSpace X] [PathConnectedSpace X] [SemilocallySimplyConnectedSpace X] :
    IsQuotientCoveringMap (proj : UniversalCover x₀ → X) (FundamentalGroup X x₀) where
  __ := (isCoveringMap x₀).isOpenMap.isQuotientMap (continuous_proj x₀) proj_surjective
  apply_eq_iff_mem_orbit := proj_eq_iff_mem_orbit
  disjoint := exists_nhds_smul_disjoint

end UniversalCover
