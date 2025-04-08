/-
Copyright (c) 2025 Hanliu Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shanwen Wang, Hanliu Jiang
-/

import Mathlib.NumberTheory.Padics.MahlerBasis
import Mathlib.RingTheory.PowerSeries.Basic
/-!
# The Amice Transform of p-adic measure


## References

* [P. Colmez, *Fonctions d'une variable p-adique*][colmez2010]

## Tags

Bojanic
-/

open Finset IsUltrametricDist NNReal Filter PowerSeries

open scoped fwdDiff ZeroAtInfty Topology

variable {p : ℕ} [hp : Fact p.Prime]

namespace PadicInt
section norm_1
noncomputable def to_Bound_function :
 (ℕ → ℤ_[p]) →ₗ[ℤ_[p]] ( BoundedContinuousFunction ℕ ℤ_[p]) where
  toFun a:= {
    toFun := a
    continuous_toFun :=continuous_of_discreteTopology
    map_bounded' := sorry
  }
  map_add' _ _:=rfl
  map_smul' _ _ := rfl

noncomputable def to_Bound_norm :  AddGroupNorm (ℕ → ℤ_[p])where
  toFun f := ‖to_Bound_function f‖
  map_zero' :=by

       unfold to_Bound_function
       simp
       rfl

  add_le' a b:=by
    simp
    exact norm_add_le (to_Bound_function a) (to_Bound_function b)
  neg' a:=by
    simp

  eq_zero_of_map_eq_zero' x sx:=by
       have:to_Bound_function x=0 :=by sorry
       unfold to_Bound_function at this
       simp at this
       sorry
noncomputable instance:  SeminormedAddCommGroup (ℕ → ℤ_[p])
 :=AddGroupSeminorm.toSeminormedAddCommGroup
( AddGroupNorm.toAddGroupSeminorm (to_Bound_norm))
end norm_1
section norm_2
`
noncomputable def Amice_iso :
ℤ_[p] ≃ₗᵢ[ℤ_[p]]
   ℕ→ ℤ_[p] :=sorry
