/-
Copyright (c) 2024 Elliot Dean Young and Jiazhen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiazhen Xia, Elliot Dean Young
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Category.TopCat.EpiMono

/-!
# Euclidean spheres

This file defines the `n`-sphere `𝕊 n`, the `n`-disk `𝔻 n`, its boundary `∂𝔻 n` and its interior
`𝔹 n` as objects in `TopCat`.

-/

universe u

namespace TopCat
open CategoryTheory

/-- The `n`-disk is the set of points in ℝⁿ whose norm is at most `1`,
endowed with the subspace topology. -/
noncomputable def disk (n : ℕ) : TopCat.{u} :=
  TopCat.of <| ULift <| Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1

/-- The boundary of the `n`-disk. -/
noncomputable def diskBoundary (n : ℕ) : TopCat.{u} :=
  TopCat.of <| ULift <| Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1

/-- The `n`-sphere is the set of points in ℝⁿ⁺¹ whose norm equals `1`,
endowed with the subspace topology. -/
noncomputable def sphere (n : ℕ) : TopCat.{u} :=
  diskBoundary (n + 1)

/-- The `n`-ball is the set of points in ℝⁿ whose norm is strictly less than `1`,
endowed with the subspace topology. -/
noncomputable def ball (n : ℕ) : TopCat.{u} :=
  TopCat.of <| ULift <| Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1

/-- `𝔻 n` denotes the `n`-disk. -/
scoped prefix:arg "𝔻 " => disk

/-- `∂𝔻 n` denotes the boundary of the `n`-disk. -/
scoped prefix:arg "∂𝔻 " => diskBoundary

/-- `𝕊 n` denotes the `n`-sphere. -/
scoped prefix:arg "𝕊 " => sphere

/-- `𝔹 n` denotes the `n`-ball, the interior of the `n`-disk. -/
scoped prefix:arg "𝔹 " => ball

/-- The inclusion `∂𝔻 n ⟶ 𝔻 n` of the boundary of the `n`-disk. -/
def diskBoundaryInclusion (n : ℕ) : ∂𝔻 n ⟶ 𝔻 n :=
  ofHom
    { toFun := fun ⟨p, hp⟩ ↦ ⟨p, le_of_eq hp⟩
      continuous_toFun := ⟨fun t ⟨s, ⟨r, hro, hrs⟩, hst⟩ ↦ by
        rw [isOpen_induced_iff, ← hst, ← hrs]
        tauto⟩ }

/-- The inclusion `𝔹 n ⟶ 𝔻 n` of the interior of the `n`-disk. -/
def ballInclusion (n : ℕ) : 𝔹 n ⟶ 𝔻 n :=
  ofHom
    { toFun := fun ⟨p, hp⟩ ↦ ⟨p, Metric.ball_subset_closedBall hp⟩
      continuous_toFun := ⟨fun t ⟨s, ⟨r, hro, hrs⟩, hst⟩ ↦ by
        rw [isOpen_induced_iff, ← hst, ← hrs]
        tauto⟩ }

instance {n : ℕ} : Mono (diskBoundaryInclusion n) := mono_iff_injective _ |>.mpr <| by
  intro ⟨x, hx⟩ ⟨y, hy⟩ h
  obtain rfl : x = y := by simpa [diskBoundaryInclusion, disk] using h
  congr

instance {n : ℕ} : Mono (ballInclusion n) := TopCat.mono_iff_injective _ |>.mpr <| by
  intro ⟨x, hx⟩ ⟨y, hy⟩ h
  obtain rfl : x = y := by simpa [ballInclusion, disk] using h
  congr

instance (n : ℕ) : CompactSpace (𝔻 n) := by
  convert Homeomorph.compactSpace Homeomorph.ulift.symm
  infer_instance

instance (n : ℕ) : CompactSpace (∂𝔻 n) := by
  convert Homeomorph.compactSpace Homeomorph.ulift.symm
  infer_instance

end TopCat
