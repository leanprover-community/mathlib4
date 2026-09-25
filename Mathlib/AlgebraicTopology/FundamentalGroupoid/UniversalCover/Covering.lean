/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.UniversalCover.Basic
public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.Homotopy.Lifting

/-!
# The universal cover is a simply connected covering space

Using the sheets constructed in
`Mathlib/AlgebraicTopology/FundamentalGroupoid/UniversalCover/Basic.lean`, we show that the
projection `UniversalCover.proj` is a covering map when `X` is path-connected, locally
path-connected and semilocally simply connected, and that the universal cover is path-connected
and simply connected.

## Main statements

* `UniversalCover.isCoveringMap`: `UniversalCover.proj` is a covering map.
* `UniversalCover.instPathConnectedSpace`: the universal cover is path-connected (for any `X`).
* `UniversalCover.instSimplyConnectedSpace`: the universal cover is simply connected.
* `UniversalCover.existsUnique_continuousMap_lifts`: the universal lifting property.
-/

open scoped unitInterval
open Topology

variable {X : Type*} [TopologicalSpace X]

namespace UniversalCover

variable {x₀ x : X}

/-- The projection `UniversalCover x₀ → X` is a covering map when `X` is path-connected, locally
path-connected and semilocally simply connected. -/
public theorem isCoveringMap [LocallyPathConnectedSpace X] [PathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] (x₀ : X) :
    IsCoveringMap (proj (x₀ := x₀)) := by
  intro x
  obtain ⟨U, hU_open, hxU, hU_pc, hU_triv⟩ :=
    SemilocallySimplyConnectedSpace.exists_isPathHomotopyTrivial_neighborhood x
  have : Nonempty (Path.Homotopic.Quotient x₀ x) :=
    ⟨Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x₀ x)⟩
  have : Nonempty (X → UniversalCover x₀) :=
    ⟨fun _ ↦ ofBasedPath x₀ (BasedPath.ofPath (PathConnectedSpace.somePath x₀ x₀))⟩
  have h_open_iff : ∀ q : Path.Homotopic.Quotient x₀ x, ∀ {W : Set X}, W ⊆ U →
      (IsOpen W ↔ IsOpen (proj (x₀ := x₀) ⁻¹' W ∩ sheet U hxU q)) := by
    intro q W hWU
    refine ⟨fun hW ↦ (hW.preimage (continuous_proj x₀)).inter (isOpen_sheet U hU_open hxU q),
      fun h ↦ ?_⟩
    have h := isOpenMap_proj x₀ _ h
    rwa [Set.image_preimage_inter, Set.inter_eq_left.mpr (hWU.trans (sheet_surjOn hU_pc hxU q))]
      at h
  refine ((IsEvenlyCovered.of_trivialization (t :=
    IsOpen.trivializationDiscrete (f := proj (x₀ := x₀)) (sheet U hxU) U hU_open h_open_iff
      (sheet_proj_injOn hU_triv hxU) (sheet_surjOn hU_pc hxU) (sheet_pairwise_disjoint hU_triv hxU)
      (sheet_exhaustive hU_pc hxU)) ?_).to_isEvenlyCovered_preimage)
  rw [IsOpen.trivializationDiscrete_baseSet]
  exact hxU

public instance discreteTopology_fiber [LocallyPathConnectedSpace X] [PathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] (x₀ x : X) :
    DiscreteTopology (proj (x₀ := x₀) ⁻¹' {x}) :=
  (isCoveringMap x₀ x).discreteTopology_fiber

/-- Every point of the universal cover is joined to the basepoint, along the family of initial
segments `t ↦ α|_[0, t]`. -/
theorem joined_ofBasedPath_refl (α : BasedPath x₀) :
    Joined (ofBasedPath x₀ (BasedPath.refl x₀)) (ofBasedPath x₀ α) :=
  ⟨{  toFun t := ofBasedPath x₀ (α.initialSegmentFamily t)
      continuous_toFun := by fun_prop
      source' := by simp
      target' := by simp }⟩

/-- The universal cover is path-connected, with no hypotheses on `X`. -/
public instance instPathConnectedSpace (x₀ : X) : PathConnectedSpace (UniversalCover x₀) := by
  refine ⟨⟨ofBasedPath x₀ (BasedPath.refl x₀)⟩, fun z₁ z₂ ↦ ?_⟩
  obtain ⟨α₁, rfl⟩ := surjective_ofBasedPath x₀ z₁
  obtain ⟨α₂, rfl⟩ := surjective_ofBasedPath x₀ z₂
  exact (joined_ofBasedPath_refl α₁).symm.trans (joined_ofBasedPath_refl α₂)

/-- The lift of a path `γ` out of `endpoint α` starting at `ofBasedPath α` ends at
`ofBasedPath (append α γ)`. -/
theorem liftPath_apply_one_eq_ofBasedPath_append [LocallyPathConnectedSpace X]
    [PathConnectedSpace X] [SemilocallySimplyConnectedSpace X] {α : BasedPath x₀} {y : X}
    (γ : Path (BasedPath.endpoint α) y) :
    (isCoveringMap x₀).liftPath γ (ofBasedPath x₀ α) (by simp) 1 =
      ofBasedPath x₀ (BasedPath.append α γ) := by
  -- The lift is `t ↦ ofBasedPath (append α γ|_[0, t])`.
  let Γ : C(I, UniversalCover x₀) :=
    ⟨fun t ↦ ofBasedPath x₀ (BasedPath.append α (γ.initialSegmentFamily t)),
      (continuous_ofBasedPath x₀).comp (BasedPath.continuous_append_initialSegmentFamily α γ)⟩
  have hΓ_lifts : proj (x₀ := x₀) ∘ Γ = γ := by
    ext t
    simpa [Γ] using BasedPath.endpoint_append α (γ.initialSegmentFamily t)
  have hΓ_zero : Γ 0 = ofBasedPath x₀ α := by
    have h0 : ((α.toPath.trans (γ.initialSegmentFamily 0)).cast rfl (by simp)).Homotopic
        α.toPath := by
      rw [Path.initialSegmentFamily_zero]
      simpa using! Path.Homotopic.trans_refl_cast α.toPath rfl (by simp)
    exact ofBasedPath_eq_of_homotopic_toPath (by rw [BasedPath.endpoint_append]; simp) h0
  rw [← ((isCoveringMap x₀).eq_liftPath_iff' (γ := γ) (γ_0 := by simp) (Γ := Γ)).2
    ⟨hΓ_lifts, hΓ_zero⟩]
  simpa [Γ] using!
    congrArg (fun δ ↦ ofBasedPath x₀ (BasedPath.append α δ)) γ.initialSegmentFamily_one

/-- The universal cover is simply connected. -/
public instance instSimplyConnectedSpace [LocallyPathConnectedSpace X] [PathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] (x₀ : X) :
    SimplyConnectedSpace (UniversalCover x₀) := by
  rw [simply_connected_iff_loops_nullhomotopic]
  refine ⟨inferInstance, ?_⟩
  intro z p
  obtain ⟨α, rfl⟩ := surjective_ofBasedPath x₀ z
  let γ : Path (BasedPath.endpoint α) (BasedPath.endpoint α) :=
    (p.map (continuous_proj x₀)).cast
      (proj_ofBasedPath x₀ α).symm (proj_ofBasedPath x₀ α).symm
  have hγ0 : γ 0 = proj (ofBasedPath x₀ α) := by rw [proj_ofBasedPath]; exact γ.source
  have hp_eq_lift :
      (p : C(I, UniversalCover x₀)) =
        (isCoveringMap x₀).liftPath γ (ofBasedPath x₀ α) hγ0 :=
    ((isCoveringMap x₀).eq_liftPath_iff' (γ := γ)
      (e := ofBasedPath x₀ α) (γ_0 := hγ0) (Γ := p)).2
      ⟨by ext t; rfl, p.source⟩
  have h_end : ofBasedPath x₀ (BasedPath.append α γ) = ofBasedPath x₀ α := by
    rw [← liftPath_apply_one_eq_ofBasedPath_append, ← hp_eq_lift]; exact p.target
  have h_append_eq :
      Path.Homotopic.Quotient.mk (α.toPath.trans γ) = Path.Homotopic.Quotient.mk α.toPath := by
    have h_end' : ofBasedPath x₀ (BasedPath.ofPath (α.toPath.trans γ)) =
        ofBasedPath x₀ (BasedPath.ofPath α.toPath) := by
      rw [BasedPath.ofPath_toPath_self]
      exact h_end
    rw [ofBasedPath_ofPath, ofBasedPath_ofPath] at h_end'
    simpa using h_end'
  have hγ_null :
      (Path.Homotopic.Quotient.mk γ : Path.Homotopic.Quotient
          (BasedPath.endpoint α) (BasedPath.endpoint α)) =
        Path.Homotopic.Quotient.refl (BasedPath.endpoint α) := by
    -- Insert α⁻¹·α in front of γ and re-associate; then `α·γ` has the same class as `α`
    -- (by `h_append_eq`), so we're left with `α⁻¹·α`, which is the identity.
    let qα : Path.Homotopic.Quotient x₀ (BasedPath.endpoint α) :=
      Path.Homotopic.Quotient.mk α.toPath
    calc
      Path.Homotopic.Quotient.mk γ
          = (Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.symm qα) qα).trans
              (Path.Homotopic.Quotient.mk γ) := by simp
      _ = (Path.Homotopic.Quotient.symm qα).trans
            (qα.trans (Path.Homotopic.Quotient.mk γ)) :=
          Path.Homotopic.Quotient.trans_assoc _ _ _
      _ = (Path.Homotopic.Quotient.symm qα).trans
            (Path.Homotopic.Quotient.mk (α.toPath.trans γ)) := by
          rw [Path.Homotopic.Quotient.mk_trans]
      _ = (Path.Homotopic.Quotient.symm qα).trans qα := by rw [h_append_eq]
      _ = Path.Homotopic.Quotient.refl (BasedPath.endpoint α) := by simp
  rw [← Path.Homotopic.Quotient.eq]
  apply (isCoveringMap x₀).injective_path_homotopic_map
    (ofBasedPath x₀ α) (ofBasedPath x₀ α)
  -- Cast `hγ_null` from `Quotient α.endpoint α.endpoint` to `Quotient (proj e) (proj e)`;
  -- `cast_refl` and `← mk_map` then align it with the goal.
  have hcast :=
    congrArg (Path.Homotopic.Quotient.cast · (proj_ofBasedPath x₀ α) (proj_ofBasedPath x₀ α))
      hγ_null
  simpa [γ, ← Path.Homotopic.Quotient.mk_map] using! hcast

/-- The universal property of the universal cover: a continuous map `f : A → X` from a simply
connected, locally path-connected space lifts uniquely to `UniversalCover x₀`, once the lift of
one point is specified. -/
public theorem existsUnique_continuousMap_lifts {A : Type*} [TopologicalSpace A]
    [SimplyConnectedSpace A] [LocallyPathConnectedSpace A]
    [LocallyPathConnectedSpace X] [PathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] (x₀ : X)
    (f : C(A, X)) (a₀ : A) (e₀ : UniversalCover x₀) (he : proj e₀ = f a₀) :
    ∃! F : C(A, UniversalCover x₀), F a₀ = e₀ ∧ proj ∘ F = f :=
  (isCoveringMap x₀).existsUnique_continuousMap_lifts f a₀ e₀ he

end UniversalCover
