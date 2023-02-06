/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov

! This file was ported from Lean 3 source module topology.algebra.order.archimedean
! leanprover-community/mathlib commit 4c19a16e4b705bf135cf9a80ac18fcc99c438514
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Topology.Order.Basic
import Mathlib.Algebra.Order.Archimedean

/-!
# Rational numbers are dense in a linear ordered archimedean field

In this file we prove that coercion from `ℚ` to a linear ordered archimedean field has dense range.
This lemma is in a separate file because `Mathlib.Topology.Order.Basic` does not import
`Mathlib.Algebra.Order.Archimedean`.
-/


variable {𝕜 : Type _} [LinearOrderedField 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] [Archimedean 𝕜]

/-- Rational numbers are dense in a linear ordered archimedean field. -/
theorem Rat.denseRange_cast : DenseRange ((↑) : ℚ → 𝕜) :=
  dense_of_exists_between fun _ _ h => Set.exists_range_iff.2 <| exists_rat_btwn h
#align rat.dense_range_cast Rat.denseRange_cast

