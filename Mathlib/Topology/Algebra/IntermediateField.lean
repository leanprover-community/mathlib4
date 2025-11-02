/-
Copyright (c) 2024 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.Topology.Algebra.Field

/-!
# Continuous actions related to intermediate fields

In this file we define the instances related to continuous actions of
intermediate fields. The topology on intermediate fields is already defined
in earlier file `Mathlib/Topology/Algebra/Field.lean` as the subspace topology.
-/

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
    [TopologicalSpace L] [IsTopologicalRing L]

variable (X : Type*) [TopologicalSpace X] [MulAction L X] [ContinuousSMul L X]
variable (M : IntermediateField K L)

instance IntermediateField.continuousSMul (M : IntermediateField K L) : ContinuousSMul M X :=
  M.toSubfield.continuousSMul X

instance IntermediateField.botContinuousSMul (M : IntermediateField K L) :
    ContinuousSMul (⊥ : IntermediateField K L) M :=
  Topology.IsInducing.continuousSMul (X := L) (N := (⊥ : IntermediateField K L)) (Y := M)
    (M := (⊥ : IntermediateField K L)) Topology.IsInducing.subtypeVal continuous_id rfl
