/-
Copyright (c) 2025 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.NumberTheory.NumberField.ProductFormula
public import Mathlib.NumberTheory.Height.Basic

/-!
# Instances of AdmissibleAbsValues

We provide instances of `Height.AdmissibleAbsValues` for

* algebraic number fields.

## TODO

* Fields of rational functions in `n` variables.

* Finite extensions of fields with `Height.AdmissibleAbsValues`.

-/

@[expose] public section

/-!
### Instance for number fields
-/

section number_field

open NumberField Height

noncomputable
instance NumberField.instAdmissibleAbsValues {K : Type*} [Field K] [NumberField K] :
    AdmissibleAbsValues K where
  ArchAbsVal := InfinitePlace K
  archAbsVal v := v.val
  archAbsVal_fintype := inferInstance
  weight := InfinitePlace.mult
  weight_pos _ := InfinitePlace.mult_pos
  NonarchAbsVal := FinitePlace K
  nonarchAbsVal v := v.val
  strong_triangle_ineq := FinitePlace.add_le
  mulSupport_nonarchAbsVal_finite := FinitePlace.mulSupport_finite
  product_formula := prod_abs_eq_one

end number_field

end
