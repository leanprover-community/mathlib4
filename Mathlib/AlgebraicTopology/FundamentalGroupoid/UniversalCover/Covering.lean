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
# Universal cover: covering map, simple connectedness, universal property

Building on the sheet decomposition in
`Mathlib.AlgebraicTopology.FundamentalGroupoid.UniversalCover.Basic`, this file shows that the
endpoint projection `UniversalCover.proj` is a covering map, and derives path-connectedness,
simple connectedness, and the universal lifting property of the universal cover.

## Main results

* `UniversalCover.isCoveringMap`: in a semilocally simply connected, locally path-connected,
  path-connected space, `UniversalCover.proj` is a covering map.
* `UniversalCover.discreteTopology_fiber`: fibers of the universal cover are discrete.
* `UniversalCover.pathConnectedSpace`: the universal cover is path-connected.
* `UniversalCover.simplyConnectedSpace`: the universal cover is simply connected.
* `UniversalCover.existsUnique_continuousMap_lifts`: the universal lifting property.
-/

@[expose] public section

open scoped unitInterval
open Topology

variable {X : Type*} [TopologicalSpace X]

namespace UniversalCover

variable {x₀ x : X}

/-- The endpoint projection `proj` is a covering map, assuming `X` is semilocally simply
connected, locally path-connected, and path-connected. -/
theorem isCoveringMap [LocPathConnectedSpace X] [PathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] (x₀ : X) :
    IsCoveringMap (proj (x₀ := x₀)) := by
  intro x
  -- Get a good neighborhood of `x`.
  obtain ⟨U, hU_open, hxU, hU_pathConn, hU_slsc⟩ := exists_pathConnected_slsc_neighborhood x
  -- Shorthand.
  let S : Path.Homotopic.Quotient x₀ x → Set (UniversalCover x₀) := fun q => sheet U hxU q
  -- Nonempty instances needed by `trivializationDiscrete`.
  have _ne_ι : Nonempty (Path.Homotopic.Quotient x₀ x) :=
    ⟨Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x₀ x)⟩
  have _ne_fun : Nonempty (X → UniversalCover x₀) :=
    ⟨fun _ => ofBasedPath x₀ (BasedPath.ofPath (PathConnectedSpace.somePath x₀ x₀))⟩
  -- Build the trivialization.
  have h_open_iff : ∀ q : Path.Homotopic.Quotient x₀ x, ∀ {W : Set X}, W ⊆ U →
      (IsOpen W ↔ IsOpen (proj (x₀ := x₀) ⁻¹' W ∩ S q)) := by
    intro q W hWU
    constructor
    · intro hW_open
      exact (hW_open.preimage (continuous_proj x₀)).inter (isOpen_sheet U hU_open hxU q)
    · intro h_open_inter
      -- Use surjectivity of sheet → U and `isOpenMap_proj`.
      have h_image_eq : proj (x₀ := x₀) '' (proj (x₀ := x₀) ⁻¹' W ∩ S q) = W := by
        ext v
        constructor
        · rintro ⟨e, ⟨hv1, _⟩, rfl⟩
          exact hv1
        · intro hvW
          have hvU : v ∈ U := hWU hvW
          obtain ⟨e, he_sheet, he_proj⟩ := sheet_surjOn hU_pathConn hxU q hvU
          refine ⟨e, ⟨?_, he_sheet⟩, he_proj⟩
          change proj (x₀ := x₀) e ∈ W
          rw [he_proj]; exact hvW
      rw [← h_image_eq]
      exact isOpenMap_proj x₀ _ h_open_inter
  have h_inj : ∀ q, (S q).InjOn (proj (x₀ := x₀)) :=
    fun q => sheet_proj_injOn hU_slsc hxU q
  have h_surj : ∀ q, (S q).SurjOn (proj (x₀ := x₀)) U :=
    fun q => sheet_surjOn hU_pathConn hxU q
  have h_disjoint : Pairwise (Function.onFun Disjoint S) := by
    unfold Function.onFun
    exact sheet_pairwise_disjoint hU_slsc hxU
  have h_exhaustive : proj (x₀ := x₀) ⁻¹' U ⊆ ⋃ q, S q :=
    sheet_exhaustive hU_pathConn hxU
  haveI _disc : DiscreteTopology (Path.Homotopic.Quotient x₀ x) :=
    Path.Homotopic.Quotient.discreteTopology x₀ x
  refine (IsEvenlyCovered.of_trivialization (t :=
    IsOpen.trivializationDiscrete (f := proj (x₀ := x₀))
      S U hU_open h_open_iff h_inj h_surj h_disjoint h_exhaustive) ?_).to_isEvenlyCovered_preimage
  rw [IsOpen.trivializationDiscrete_baseSet]
  exact hxU

/-- Fibers of the universal cover are discrete, as for any covering map. -/
theorem discreteTopology_fiber [LocPathConnectedSpace X] [PathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] (x₀ x : X) :
    DiscreteTopology (proj (x₀ := x₀) ⁻¹' {x}) :=
  ((isCoveringMap x₀) x).discreteTopology_fiber

/-- Helper: every point of `UniversalCover x₀` is joined to the basepoint. -/
private theorem joined_basepoint_of_ofBasedPath (α : BasedPath x₀) :
    Joined (ofBasedPath x₀ (BasedPath.ofPath (Path.refl x₀))) (ofBasedPath x₀ α) := by
  -- Family of based paths: `F_fn t s = α(s * t)` — at `t = 0` constant at x₀, at `t = 1` α.
  have hst_mem : ∀ s t : I, (s : ℝ) * (t : ℝ) ∈ I := by
    intro s t
    refine ⟨mul_nonneg s.2.1 t.2.1, ?_⟩
    exact mul_le_one₀ s.2.2 t.2.1 t.2.2
  let F_cm : I → C(I, X) := fun t =>
    ⟨fun s => α.1 ⟨(s : ℝ) * (t : ℝ), hst_mem s t⟩, by
      refine α.1.continuous.comp ?_
      exact Continuous.subtype_mk (by fun_prop) _⟩
  have hF_cont : Continuous F_cm := by
    refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
    have hst_cont : Continuous (fun ts : I × I =>
        (⟨((ts.2 : ℝ) * (ts.1 : ℝ)), hst_mem ts.2 ts.1⟩ : I)) := by
      refine Continuous.subtype_mk ?_ _
      exact ((continuous_induced_dom.comp continuous_snd).mul
        (continuous_induced_dom.comp continuous_fst))
    exact α.1.continuous.comp hst_cont
  let F : I → BasedPath x₀ := fun t =>
    ⟨F_cm t, by
      change α.1 ⟨(0 : ℝ) * (t : ℝ), _⟩ = x₀
      have h0 : ((0 : I) : ℝ) * (t : ℝ) = 0 := by simp
      rw [show (⟨(0 : ℝ) * (t : ℝ), hst_mem 0 t⟩ : I) = (0 : I) from Subtype.ext (by simp)]
      exact α.2⟩
  have hF_bp_cont : Continuous F := by
    exact Continuous.subtype_mk hF_cont _
  -- Both boundary endpoints are `x₀`.
  have h_F0_end :
      BasedPath.endpoint (F 0) = BasedPath.endpoint (BasedPath.ofPath (Path.refl x₀)) := by
    change α.1 ⟨(1 : ℝ) * (0 : ℝ), _⟩ = (BasedPath.ofPath (Path.refl x₀)).1 1
    rw [show (⟨(1 : ℝ) * (0 : ℝ), hst_mem 1 0⟩ : I) = (0 : I) from Subtype.ext (by simp)]
    simpa [BasedPath.ofPath] using α.2
  have h_start :
      ofBasedPath x₀ (F 0) = ofBasedPath x₀ (BasedPath.ofPath (Path.refl x₀)) := by
    refine ofBasedPath_eq_of_homotopic_toPath h_F0_end ?_
    have h_paths_eq : (F 0).toPath.cast rfl h_F0_end.symm =
        (BasedPath.ofPath (Path.refl x₀)).toPath := by
      ext s
      change α.1 ⟨(s : ℝ) * (0 : ℝ), _⟩ = x₀
      rw [show (⟨(s : ℝ) * (0 : ℝ), hst_mem s 0⟩ : I) = (0 : I) from Subtype.ext (by simp)]
      exact α.2
    rw [h_paths_eq]
  have h_end : ofBasedPath x₀ (F 1) = ofBasedPath x₀ α := by
    congr 1
    ext s
    change α.1 ⟨(s : ℝ) * (1 : ℝ), _⟩ = α.1 s
    rw [show (⟨(s : ℝ) * (1 : ℝ), hst_mem s 1⟩ : I) = s from Subtype.ext (by simp)]
  refine ⟨⟨⟨fun t => ofBasedPath x₀ (F t), ?_⟩, ?_, ?_⟩⟩
  · exact (continuous_ofBasedPath x₀).comp hF_bp_cont
  · exact h_start
  · exact h_end

/-- The universal cover is path-connected. -/
theorem pathConnectedSpace [PathConnectedSpace X] (x₀ : X) :
    PathConnectedSpace (UniversalCover x₀) := by
  refine ⟨⟨ofBasedPath x₀ (BasedPath.ofPath (Path.refl x₀))⟩, fun z₁ z₂ => ?_⟩
  obtain ⟨α₁, rfl⟩ := surjective_ofBasedPath x₀ z₁
  obtain ⟨α₂, rfl⟩ := surjective_ofBasedPath x₀ z₂
  exact (joined_basepoint_of_ofBasedPath α₁).symm.trans (joined_basepoint_of_ofBasedPath α₂)

/-- The lift through the covering map `proj` of a path `γ : Path (endpoint α) y` starting at
`ofBasedPath α` ends at `ofBasedPath (append α γ)`. This is the key ingredient for the
simply-connectedness proof. -/
private theorem liftPath_apply_one_eq_ofBasedPath_append
    [LocPathConnectedSpace X] [PathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] {α : BasedPath x₀} {y : X}
    (γ : Path (BasedPath.endpoint α) y) :
    (isCoveringMap x₀).liftPath γ (ofBasedPath x₀ α)
      (by simpa [BasedPath.endpoint] using γ.source) 1 =
      ofBasedPath x₀ (BasedPath.append α γ) := by
  let Γ : C(I, UniversalCover x₀) := by
    refine ⟨fun t => ofBasedPath x₀ (BasedPath.append α (Path.initialSegmentFamily γ t)),
      ?_⟩
    exact (continuous_ofBasedPath x₀).comp <| Continuous.subtype_mk (by
      refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
      simpa [BasedPath.append, BasedPath.ofPath] using
        Path.trans_continuous_family (fun _ : I => α.toPath)
          (Path.continuous_uncurry_iff.mpr continuous_const) (Path.initialSegmentFamily γ)
          (Path.continuous_initialSegmentFamily_uncurry γ)) _
  have hΓ_lifts : proj (x₀ := x₀) ∘ Γ = γ := by
    ext t
    simpa [Γ, BasedPath.endpoint] using
      (BasedPath.endpoint_append α (Path.initialSegmentFamily γ t))
  have hΓ_zero : Γ 0 = ofBasedPath x₀ α := by
    have h0_hom :
        Path.Homotopic
          ((α.toPath.trans (Path.initialSegmentFamily γ 0)).cast rfl
            (by simpa [BasedPath.endpoint] using γ.source.symm))
          α.toPath := by
      rw [Path.initialSegmentFamily_zero]
      simpa using Path.Homotopic.trans_refl_cast α.toPath rfl
        (by simp)
    have h0_end : BasedPath.endpoint (BasedPath.append α (Path.initialSegmentFamily γ 0)) =
        BasedPath.endpoint α := by
      trans γ 0
      · exact BasedPath.endpoint_append α (Path.initialSegmentFamily γ 0)
      · simpa [BasedPath.endpoint] using γ.source
    exact ofBasedPath_eq_of_homotopic_toPath (x₀ := x₀) h0_end h0_hom
  have hΓ_eq_lift :
      Γ = (isCoveringMap x₀).liftPath γ (ofBasedPath x₀ α)
        (by simpa [BasedPath.endpoint] using γ.source) := by
    refine ((isCoveringMap x₀).eq_liftPath_iff' (γ := γ)
      (e := ofBasedPath x₀ α)
      (γ_0 := by simpa [BasedPath.endpoint] using γ.source) (Γ := Γ)).2 ?_
    exact ⟨hΓ_lifts, hΓ_zero⟩
  calc
    (isCoveringMap x₀).liftPath γ (ofBasedPath x₀ α)
        (by simpa [BasedPath.endpoint] using γ.source) 1 = Γ 1 := by
      simp [hΓ_eq_lift]
    _ = ofBasedPath x₀ (BasedPath.append α γ) := by
      simpa [Γ] using
        congrArg (fun δ => ofBasedPath x₀ (BasedPath.append α δ))
          (Path.initialSegmentFamily_one γ)

/-- The universal cover is simply connected. -/
theorem simplyConnectedSpace [LocPathConnectedSpace X] [PathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] (x₀ : X) :
    SimplyConnectedSpace (UniversalCover x₀) := by
  rw [simply_connected_iff_loops_nullhomotopic]
  refine ⟨pathConnectedSpace x₀, ?_⟩
  intro z p
  obtain ⟨α, rfl⟩ := surjective_ofBasedPath x₀ z
  let γ : Path (BasedPath.endpoint α) (BasedPath.endpoint α) := p.map (continuous_proj x₀)
  have hγ0 : γ 0 = BasedPath.endpoint α := by
    change proj (p 0) = BasedPath.endpoint α
    rw [p.source]
    rfl
  have hp_eq_lift :
      (p : C(I, UniversalCover x₀)) =
        (isCoveringMap x₀).liftPath γ (ofBasedPath x₀ α) hγ0 := by
    refine ((isCoveringMap x₀).eq_liftPath_iff' (γ := γ)
      (e := ofBasedPath x₀ α) (γ_0 := hγ0) (Γ := p)).2 ?_
    exact ⟨by ext t; rfl, p.source⟩
  have h_end : ofBasedPath x₀ (BasedPath.append α γ) = ofBasedPath x₀ α := by
    calc
      ofBasedPath x₀ (BasedPath.append α γ) =
          (isCoveringMap x₀).liftPath γ (ofBasedPath x₀ α) hγ0 1 := by
        symm
        exact liftPath_apply_one_eq_ofBasedPath_append γ
      _ = p 1 := by
        rw [← hp_eq_lift]
        rfl
      _ = ofBasedPath x₀ α := p.target
  have h_append_eq :
      Path.Homotopic.Quotient.mk (α.toPath.trans γ) = Path.Homotopic.Quotient.mk α.toPath := by
    have h_end' :
        ofBasedPath x₀ (BasedPath.ofPath (α.toPath.trans γ)) =
          ofBasedPath x₀ (BasedPath.ofPath α.toPath) := by
      simpa [BasedPath.append, BasedPath.ofPath] using h_end
    have h_end'' :
        (⟨BasedPath.endpoint α, Path.Homotopic.Quotient.mk (α.toPath.trans γ)⟩ :
          UniversalCover x₀) =
        ⟨BasedPath.endpoint α, Path.Homotopic.Quotient.mk α.toPath⟩ := by
      simpa [ofBasedPath_ofPath] using h_end'
    exact eq_of_heq ((Sigma.mk.injEq _ _ _ _).mp h_end'').2
  have hγ_null :
      (Path.Homotopic.Quotient.mk γ : Path.Homotopic.Quotient
          (BasedPath.endpoint α) (BasedPath.endpoint α)) =
        Path.Homotopic.Quotient.refl (BasedPath.endpoint α) := by
    let qα : Path.Homotopic.Quotient x₀ (BasedPath.endpoint α) :=
      Path.Homotopic.Quotient.mk α.toPath
    calc
      Path.Homotopic.Quotient.mk γ =
          Path.Homotopic.Quotient.trans
            (Path.Homotopic.Quotient.refl (BasedPath.endpoint α))
            (Path.Homotopic.Quotient.mk γ) := by simp
      _ = Path.Homotopic.Quotient.trans
            (Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.symm qα) qα)
            (Path.Homotopic.Quotient.mk γ) := by simp
      _ = Path.Homotopic.Quotient.trans
            (Path.Homotopic.Quotient.symm qα)
            (Path.Homotopic.Quotient.trans qα (Path.Homotopic.Quotient.mk γ)) := by
          exact Path.Homotopic.Quotient.trans_assoc _ _ _
      _ = Path.Homotopic.Quotient.trans
            (Path.Homotopic.Quotient.symm qα)
            (Path.Homotopic.Quotient.mk (α.toPath.trans γ)) := by
          rw [Path.Homotopic.Quotient.mk_trans]
      _ = Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.symm qα) qα := by
          rw [h_append_eq]
      _ = Path.Homotopic.Quotient.refl (BasedPath.endpoint α) := by simp
  rw [← Path.Homotopic.Quotient.eq]
  apply (isCoveringMap x₀).injective_path_homotopic_map
    (ofBasedPath x₀ α) (ofBasedPath x₀ α)
  simpa [γ, Path.Homotopic.Quotient.mk_map] using hγ_null

/-- Universal property of the universal cover: any continuous map `f : A → X` from a simply
connected, locally path-connected space `A` lifts uniquely to the universal cover, after
specifying a lift `e₀ : UniversalCover x₀` of any point `a₀ : A`.

This is a thin wrapper over `IsCoveringMap.existsUnique_continuousMap_lifts` applied to
`UniversalCover.isCoveringMap`. -/
theorem existsUnique_continuousMap_lifts {A : Type*} [TopologicalSpace A]
    [SimplyConnectedSpace A] [LocPathConnectedSpace A]
    [LocPathConnectedSpace X] [PathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] (x₀ : X)
    (f : C(A, X)) (a₀ : A) (e₀ : UniversalCover x₀) (he : proj e₀ = f a₀) :
    ∃! F : C(A, UniversalCover x₀), F a₀ = e₀ ∧ proj ∘ F = f :=
  (isCoveringMap x₀).existsUnique_continuousMap_lifts f a₀ e₀ he

end UniversalCover
