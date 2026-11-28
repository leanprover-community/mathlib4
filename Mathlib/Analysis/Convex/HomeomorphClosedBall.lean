/-
Copyright (c) 2026 Ruize Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruize Chen
-/
module

public import Mathlib.Analysis.Convex.Body
public import Mathlib.Analysis.Convex.Intrinsic
public import Mathlib.Analysis.Normed.Module.FiniteDimension

import Mathlib.Analysis.Convex.GaugeRescale

/-!
# Homeomorphism type of convex bodies

A convex body (a nonempty compact convex set) in a finite-dimensional real normed space is
determined up to homeomorphism by the dimension of its affine span.

## Main results

* `ConvexBody.nonempty_homeomorph`: two convex bodies in finite-dimensional real normed spaces are
  homeomorphic if their affine spans have the same dimension.

As special cases, closed balls are models for these homeomorphism types:

* `ConvexBody.nonempty_homeomorph_closedBall`: a convex body `K` in a finite-dimensional real
  normed space is homeomorphic to the closed unit ball of any finite-dimensional real normed space
  `F` with `finrank ℝ F = finrank ℝ (vectorSpan ℝ K)`.
* `nonempty_homeomorph_closedBall_of_finrank_eq`: the closed unit balls of two finite-dimensional
  real normed spaces of the same dimension are homeomorphic.
* `Convex.nonempty_homeomorph_closedBall`: in a real normed space `E`, possibly
  infinite-dimensional, a closed bounded convex set with nonempty interior is homeomorphic to the
  closed unit ball of `E`.
-/

public section

open Metric Module

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

namespace ConvexBody

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- A convex body `K` in a finite-dimensional real normed space is homeomorphic to a convex body
with nonempty interior in the direction of its affine span. -/
private theorem exists_homeomorph_direction (K : ConvexBody E) :
    ∃ K' : ConvexBody (affineSpan ℝ (K : Set E)).direction,
      (interior (K' : Set (affineSpan ℝ (K : Set E)).direction)).Nonempty ∧ Nonempty (K' ≃ₜ K) := by
  obtain ⟨-, ⟨p, hp, rfl⟩⟩ := K.nonempty.intrinsicInterior K.convex
  have : Nonempty (affineSpan ℝ (K : Set E)) := ⟨p⟩
  let φ := (AffineIsometryEquiv.constVSub ℝ p).symm
  let g := (affineSpan ℝ (K : Set E)).subtypeₐᵢ.comp φ.toAffineIsometry
  have hgK : g '' (g ⁻¹' K) = K := Set.image_preimage_eq_of_subset fun x hx ↦
    ⟨φ.symm ⟨x, subset_affineSpan ℝ _ hx⟩, by simp [g]⟩
  have hint : (interior (g ⁻¹' K)).Nonempty :=
    (Set.Nonempty.preimage ⟨p, hp⟩ φ.surjective).mono
      (preimage_interior_subset_interior_preimage (t := Subtype.val ⁻¹' K) φ.continuous)
  exact ⟨⟨g ⁻¹' K, K.convex.affine_preimage g.toAffineMap,
    g.isometry.isClosedEmbedding.isCompact_preimage K.isCompact, hint.mono interior_subset⟩,
    hint, ⟨(g.isometry.isEmbedding.homeomorphImage _).trans (.setCongr hgK)⟩⟩

/-- Two convex bodies in finite-dimensional real normed spaces are homeomorphic as soon as their
affine spans have the same dimension. -/
theorem nonempty_homeomorph (K : ConvexBody E) (L : ConvexBody F)
    (h : finrank ℝ (vectorSpan ℝ (K : Set E)) = finrank ℝ (vectorSpan ℝ (L : Set F))) :
    Nonempty (K ≃ₜ L) := by
  obtain ⟨K', hK', ⟨e₁⟩⟩ := K.exists_homeomorph_direction
  obtain ⟨L', hL', ⟨e₂⟩⟩ := L.exists_homeomorph_direction
  -- Move `K'` into the space of `L'`, then rescale it radially onto `L'`.
  rw [← direction_affineSpan, ← direction_affineSpan] at h
  let e := ContinuousLinearEquiv.ofFinrankEq h
  let φ := e.toHomeomorph
  let K'' := φ '' (K' : Set (affineSpan ℝ (K : Set E)).direction)
  have hK'' : IsCompact K'' := K'.isCompact.image φ.continuous
  have hK''c : Convex ℝ K'' := K'.convex.linear_image e.toLinearMap
  obtain ⟨ψ, -, hψ, -⟩ := exists_homeomorph_image_eq hK''c (φ.image_interior _ ▸ hK'.image φ)
    (hK''.isVonNBounded (𝕜 := ℝ)) L'.convex hL' (L'.isCompact.isVonNBounded (𝕜 := ℝ))
  rw [hK''.isClosed.closure_eq, L'.isCompact.isClosed.closure_eq] at hψ
  exact ⟨e₁.symm.trans <| (φ.image _).trans <| (ψ.image K'').trans <|
    (Homeomorph.setCongr hψ).trans e₂⟩

/-- The closed unit ball, as a convex body. -/
private def unitClosedBall : ConvexBody F :=
  ⟨closedBall 0 1, convex_closedBall 0 1, isCompact_closedBall 0 1,
    ⟨0, mem_closedBall_self zero_le_one⟩⟩

private theorem coe_unitClosedBall : ((unitClosedBall : ConvexBody F) : Set F) = closedBall 0 1 :=
  rfl

private theorem finrank_vectorSpan_unitClosedBall :
    finrank ℝ (vectorSpan ℝ ((unitClosedBall : ConvexBody F) : Set F)) = finrank ℝ F := by
  have : affineSpan ℝ (closedBall (0 : F) 1) = ⊤ :=
    (convex_closedBall 0 1).interior_nonempty_iff_affineSpan_eq_top.1
      ⟨0, ball_subset_interior_closedBall (mem_ball_self one_pos)⟩
  rw [coe_unitClosedBall, ← direction_affineSpan, this, AffineSubspace.direction_top, finrank_top]

/-- A convex body `K` in a finite-dimensional real normed space is homeomorphic to the closed unit
ball of any finite-dimensional real normed space `F` whose dimension is that of `vectorSpan ℝ K`. -/
theorem nonempty_homeomorph_closedBall (K : ConvexBody E)
    (h : finrank ℝ (vectorSpan ℝ (K : Set E)) = finrank ℝ F) :
    Nonempty (K ≃ₜ closedBall (0 : F) 1) :=
  K.nonempty_homeomorph unitClosedBall (h.trans finrank_vectorSpan_unitClosedBall.symm)

end ConvexBody

/-- The closed unit balls of two finite-dimensional real normed spaces of the same dimension are
homeomorphic. -/
theorem nonempty_homeomorph_closedBall_of_finrank_eq [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] (h : finrank ℝ E = finrank ℝ F) :
    Nonempty (closedBall (0 : E) 1 ≃ₜ closedBall (0 : F) 1) :=
  ConvexBody.unitClosedBall.nonempty_homeomorph_closedBall
    (ConvexBody.finrank_vectorSpan_unitClosedBall.trans h)

/-- A closed bounded convex set with nonempty interior in a real normed space `E` is homeomorphic
to the closed unit ball of `E`. -/
theorem Convex.nonempty_homeomorph_closedBall {K : Set E} (hc : Convex ℝ K) (hK : IsClosed K)
    (hb : Bornology.IsBounded K) (hne : (interior K).Nonempty) :
    Nonempty (K ≃ₜ closedBall (0 : E) 1) := by
  obtain ⟨h, -, hh, -⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall hc hne hb
  rw [hK.closure_eq] at hh
  exact ⟨(h.image K).trans (.setCongr hh)⟩
