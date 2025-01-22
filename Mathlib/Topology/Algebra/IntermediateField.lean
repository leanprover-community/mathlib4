/-
Copyright (c) 2024 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.Topology.Algebra.Field

/-!
# Topology on intermediate fields

In this file we define the instances related to topology and continuous actions on
intermediate fields. The topology is already defined in earlier files as the subspace topology.
-/

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
    [TopologicalSpace L] [TopologicalRing L]

variable (X : Type*) [TopologicalSpace X] [MulAction L X] [ContinuousSMul L X]

instance IntermediateField.continuousSMul (M : IntermediateField K L) : ContinuousSMul M X :=
  M.toSubfield.continuousSMul X

instance IntermediateField.botContinuousSMul (M : IntermediateField K L) :
    ContinuousSMul (⊥ : IntermediateField K L) M :=
  Topology.IsInducing.continuousSMul (X := L) (N := (⊥ : IntermediateField K L)) (Y := M)
    (M := (⊥ : IntermediateField K L)) Topology.IsInducing.subtypeVal continuous_id rfl
