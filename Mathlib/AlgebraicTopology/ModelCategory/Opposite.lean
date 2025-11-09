/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.ModelCategory.Basic

/-!
# The opposite of a model category structure

-/

universe v u

open CategoryTheory

namespace HomotopicalAlgebra

variable (C : Type u) [Category.{v} C] [ModelCategory C]

instance [(weakEquivalences C).HasTwoOutOfThreeProperty] :
    (weakEquivalences Cᵒᵖ).HasTwoOutOfThreeProperty := by
  rw [weakEquivalences_op]
  infer_instance

instance [(weakEquivalences C).IsStableUnderRetracts] :
    (weakEquivalences Cᵒᵖ).IsStableUnderRetracts := by
  rw [weakEquivalences_op]
  infer_instance

instance [(cofibrations C).IsStableUnderRetracts] :
    (fibrations Cᵒᵖ).IsStableUnderRetracts := by
  rw [fibrations_op]
  infer_instance

instance [(fibrations C).IsStableUnderRetracts] :
    (cofibrations Cᵒᵖ).IsStableUnderRetracts := by
  rw [cofibrations_op]
  infer_instance

instance [(trivialCofibrations C).HasFactorization (fibrations C)] :
    (cofibrations Cᵒᵖ).HasFactorization (trivialFibrations Cᵒᵖ) := by
  rw [cofibrations_op, trivialFibrations_op]
  infer_instance

instance [(cofibrations C).HasFactorization (trivialFibrations C)] :
    (trivialCofibrations Cᵒᵖ).HasFactorization (fibrations Cᵒᵖ) := by
  rw [trivialCofibrations_op, fibrations_op, ]
  infer_instance

instance : ModelCategory Cᵒᵖ where
  cm4a i p _ _ _ := (HasLiftingProperty.iff_unop i p).2 inferInstance
  cm4b i p _ _ _ := (HasLiftingProperty.iff_unop i p).2 inferInstance

end HomotopicalAlgebra
