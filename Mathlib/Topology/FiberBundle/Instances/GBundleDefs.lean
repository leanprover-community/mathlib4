/-
Copyright (c) 2025 Dominic Steinitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Steinitz
-/
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.FiberBundle.Basic

open Matrix Bundle

structure GBundleCore (ι : Type*) (B : Type*) [TopologicalSpace B]
  (F : Type*) [TopologicalSpace F]
  (G : Type*) [Group G] [MulAction G F] extends FiberBundleCore ι B F where
  coordChange_structure_group :
    ∀ i j, ∀ x ∈ baseSet i ∩ baseSet j, ∃ g : G, ∀ v : F, coordChange i j x v = g • v

-- TODO: move to better location
instance {α : Type*} [DecidableEq α] [Fintype α] : MulAction (orthogonalGroup α ℝ) (α -> ℝ) where
  smul g x := g.1.mulVec x
  one_smul x := by
    change (1 : orthogonalGroup α ℝ).1.mulVec x = x
    simp [Matrix.mulVec_one]
  mul_smul := fun f g x => by
    show (f * g).1.mulVec x = f.1.mulVec (g.1.mulVec x)
    simp [Matrix.mulVec_mulVec]
