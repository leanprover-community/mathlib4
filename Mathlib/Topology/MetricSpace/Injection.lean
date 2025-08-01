/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Topology.MetricSpace.Isometry

/-!
# Injections in product spaces are isometries
-/

section Pi

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : ι → Type*}

lemma Isometry.single [∀ i, PseudoEMetricSpace (E i)] [∀ i, Zero (E i)] (i : ι) :
    Isometry (Pi.single (M := E) i) := by
  intro x y
  rw [edist_pi_def, Finset.sup_univ_eq_ciSup]
  refine le_antisymm (iSup_le fun j ↦ ?_) (le_iSup_of_le i (by simp))
  obtain rfl | h := eq_or_ne i j
  · simp
  · simp [h]

end Pi

section Prod

variable {E F : Type*} [PseudoEMetricSpace E] [PseudoEMetricSpace F]
    [AddZeroClass E] [AddZeroClass F]

lemma Isometry.inl : Isometry (AddMonoidHom.inl E F) := by
  intro x y
  rw [Prod.edist_eq]
  simp

lemma Isometry.inr : Isometry (AddMonoidHom.inr E F) := by
  intro x y
  rw [Prod.edist_eq]
  simp

end Prod
