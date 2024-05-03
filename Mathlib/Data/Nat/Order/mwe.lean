

import Mathlib.Algebra.Module.Prod
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Algebra.Module.Submodule.Map
import Mathlib.LinearAlgebra.Prod

universe u v

open Submodule

open BigOperators

variable {K : Type u} {V W : Type v}

variable [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

def subspacesBijection2 : {X : Submodule K (V × W) | ¬ Submodule.map (LinearMap.inr K V W) ⊤ ≤ X} ≃
  {((X, φ) : (Submodule K V × W) × (V × W →ₗ[K] W)) | ∀ x ∈ X, x.2 = 0 ∧ ∀ x ∉ X, φ x = 0} where
    toFun := sorry
    invFun := sorry
    left_inv := sorry
    right_inv := sorry
