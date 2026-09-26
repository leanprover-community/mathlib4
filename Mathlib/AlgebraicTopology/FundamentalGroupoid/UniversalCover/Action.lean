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
# The action of the fundamental group on the universal cover

The fundamental group `FundamentalGroup X x₀` acts on `UniversalCover x₀` by deck
transformations: `g` acts on the homotopy class of a path from `x₀` by prepending a loop
representing `g⁻¹`. The action is free, continuous and transitive on fibers. If `X` is
path-connected, locally path-connected and semilocally simply connected, then `proj` is a
quotient covering map for this action.

## Main statements

* `UniversalCover.instMulAction`: the action, together with the instances `FaithfulSMul`,
  `ContinuousConstSMul` and `IsCancelSMul` (freeness). These need no hypotheses on `X`.
* `UniversalCover.proj_eq_iff_mem_orbit`: two points have the same projection iff they lie in
  the same orbit.
* `UniversalCover.exists_nhds_smul_disjoint`: every point has a neighborhood whose non-identity
  translates are disjoint from it.
* `UniversalCover.isQuotientCoveringMap`: `proj` is a quotient covering map for this action.

## Implementation notes

Multiplication in `FundamentalGroup X x₀ = End (FundamentalGroupoid.mk x₀)` reverses
composition: `g * h = h ≫ g`, so `(g * h).toPath = h.toPath.trans g.toPath`. Prepending loops
is therefore a right action, and we turn it into a left action by prepending `g⁻¹` instead:
`g • mk x q = mk x (g⁻¹.toPath.trans q)`. The inverse-free form is `inv_smul_mk`. A left action
is what Mathlib's orbit, subgroup and `IsQuotientCoveringMap` API consume.
-/

public section
noncomputable section

open scoped unitInterval
open Topology

variable {X : Type*} [TopologicalSpace X] {x₀ : X}

namespace UniversalCover

/-- `g` acts on the universal cover by prepending a loop representing `g⁻¹`; see the module
docstring for why the inverse appears. -/
instance instSMul : SMul (FundamentalGroup X x₀) (UniversalCover x₀) where
  smul g p := mk p.proj (g⁻¹.toPath.trans p.path)

@[simp]
theorem smul_mk (g : FundamentalGroup X x₀) (x : X) (q : Path.Homotopic.Quotient x₀ x) :
    g • mk x q = mk x (g⁻¹.toPath.trans q) := rfl

/-- Inverse-free form of `smul_mk`, convenient for explicit computations. -/
theorem inv_smul_mk (g : FundamentalGroup X x₀) (x : X) (q : Path.Homotopic.Quotient x₀ x) :
    g⁻¹ • mk x q = mk x (g.toPath.trans q) := by rw [smul_mk, inv_inv]

@[simp]
theorem proj_smul (g : FundamentalGroup X x₀) (p : UniversalCover x₀) :
    proj (g • p) = proj p := rfl

instance instMulAction : MulAction (FundamentalGroup X x₀) (UniversalCover x₀) where
  one_smul p := by
    rcases p with ⟨x, q⟩
    rw [smul_mk, inv_one, FundamentalGroup.one_def, Path.Homotopic.Quotient.refl_trans]
  mul_smul g h p := by
    rcases p with ⟨x, q⟩
    rw [smul_mk, smul_mk, smul_mk, mul_inv_rev, FundamentalGroup.mul_def,
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
    refine (continuous_ofBasedPath x₀).comp (BasedPath.continuous_iff.mpr ?_)
    have h_eval : Continuous fun p : BasedPath x₀ × I ↦ p.1 p.2 :=
      BasedPath.continuous_iff.mp continuous_id
    exact Path.trans_continuous_family (a := fun _ : BasedPath x₀ ↦ x₀)
      (b := fun _ : BasedPath x₀ ↦ x₀)
      (c := fun β : BasedPath x₀ ↦ BasedPath.endpoint β)
      (fun _ ↦ γ) (Path.continuous_uncurry_iff.mpr continuous_const)
      (fun β ↦ β.toPath) h_eval

/-- The action of the fundamental group on the universal cover is free. -/
instance : IsCancelSMul (FundamentalGroup X x₀) (UniversalCover x₀) where
  right_cancel' a b c h := by
    rcases c with ⟨x, q⟩
    rw [smul_mk, smul_mk, mk_inj] at h
    have h' := congrArg (fun r ↦ r.trans q.symm) h
    simp only [Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.trans_symm,
      Path.Homotopic.Quotient.trans_refl] at h'
    exact inv_injective h'

/-- The action is transitive on fibers. -/
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

/-- The action is properly discontinuous: every point of the universal cover has a neighborhood
whose non-identity translates are disjoint from it. -/
theorem exists_nhds_smul_disjoint [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X]
    (e : UniversalCover x₀) :
    ∃ U ∈ 𝓝 e, ∀ g : FundamentalGroup X x₀, ((g • ·) '' U ∩ U).Nonempty → g = 1 := by
  rcases e with ⟨x, q⟩
  obtain ⟨V, hV_open, hxV, -, hV_triv⟩ :=
    SemilocallySimplyConnectedSpace.exists_isPathHomotopyTrivial_neighborhood x
  have hmem : mk x q ∈ sheet V hxV q := by
    induction q using Quotient.inductionOn with
    | h p => exact ofBasedPath_ofPath p ▸ mem_sheet_self hxV p
  refine ⟨sheet V hxV q, (isOpen_sheet V hV_open hxV q).mem_nhds hmem, fun g hg ↦ ?_⟩
  obtain ⟨_, ⟨y, hy, rfl⟩, hgy⟩ := hg
  -- `proj` is injective on the sheet, so `g • y = y`, and the action is free.
  exact IsCancelSMul.eq_one_of_smul (injOn_proj_sheet hV_triv hxV q hgy hy (proj_smul g y))

/-- The projection from the universal cover is a quotient covering map for the action of the
fundamental group. -/
theorem isQuotientCoveringMap
    [LocallyPathConnectedSpace X] [PathConnectedSpace X] [SemilocallySimplyConnectedSpace X] :
    IsQuotientCoveringMap (proj : UniversalCover x₀ → X) (FundamentalGroup X x₀) where
  __ := (isCoveringMap x₀).isOpenMap.isQuotientMap (continuous_proj x₀) surjective_proj
  apply_eq_iff_mem_orbit := proj_eq_iff_mem_orbit
  disjoint := exists_nhds_smul_disjoint

end UniversalCover
