/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Data.Polynomial.Taylor
import Mathlib.FieldTheory.RatFunc

#align_import field_theory.laurent from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# Laurent expansions of rational functions

## Main declarations

* `RatFunc.laurent`: the Laurent expansion of the rational function `f` at `r`, as an `AlgHom`.
* `RatFunc.laurent_injective`: the Laurent expansion at `r` is unique

## Implementation details

Implemented as the quotient of two Taylor expansions, over domains.
An auxiliary definition is provided first to make the construction of the `AlgHom` easier,
  which works on `CommRing` which are not necessarily domains.
-/


universe u

namespace RatFunc

noncomputable section

open Polynomial

open scoped Classical nonZeroDivisors Polynomial

variable {R : Type u} [CommRing R] [hdomain : IsDomain R] (r s : R) (p q : R[X]) (f : RatFunc R)

theorem taylor_mem_nonZeroDivisors (hp : p ∈ R[X]⁰) : taylor r p ∈ R[X]⁰ := by
  rw [mem_nonZeroDivisors_iff]
  intro x hx
  have : x = taylor (r - r) x := by simp
  rwa [this, sub_eq_add_neg, ← taylor_taylor, ← taylor_mul,
    LinearMap.map_eq_zero_iff _ (taylor_injective _), mul_right_mem_nonZeroDivisors_eq_zero_iff hp,
    LinearMap.map_eq_zero_iff _ (taylor_injective _)] at hx
#align ratfunc.taylor_mem_non_zero_divisors RatFunc.taylor_mem_nonZeroDivisors

/-- The Laurent expansion of rational functions about a value.
Auxiliary definition, usage when over integral domains should prefer `RatFunc.laurent`. -/
def laurentAux : RatFunc R →+* RatFunc R :=
  RatFunc.mapRingHom
    ( { toFun := taylor r
        map_add' := map_add (taylor r)
        map_mul' := taylor_mul _
        map_zero' := map_zero (taylor r)
        map_one' := taylor_one r } : R[X] →+* R[X])
    (taylor_mem_nonZeroDivisors _)
#align ratfunc.laurent_aux RatFunc.laurentAux

theorem laurentAux_ofFractionRing_mk (q : R[X]⁰) :
    laurentAux r (ofFractionRing (Localization.mk p q)) =
      ofFractionRing (.mk (taylor r p) ⟨taylor r q, taylor_mem_nonZeroDivisors r q q.prop⟩) :=
  map_apply_ofFractionRing_mk _ _ _ _
#align ratfunc.laurent_aux_of_fraction_ring_mk RatFunc.laurentAux_ofFractionRing_mk

theorem laurentAux_div :
    laurentAux r (algebraMap _ _ p / algebraMap _ _ q) =
      algebraMap _ _ (taylor r p) / algebraMap _ _ (taylor r q) :=
  -- porting note: added `by exact taylor_mem_nonZeroDivisors r`
  map_apply_div _ (by exact taylor_mem_nonZeroDivisors r) _ _
#align ratfunc.laurent_aux_div RatFunc.laurentAux_div

@[simp]
theorem laurentAux_algebraMap : laurentAux r (algebraMap _ _ p) = algebraMap _ _ (taylor r p) := by
  rw [← mk_one, ← mk_one, mk_eq_div, laurentAux_div, mk_eq_div, taylor_one, map_one, map_one,
    map_one]
#align ratfunc.laurent_aux_algebra_map RatFunc.laurentAux_algebraMap

/-- The Laurent expansion of rational functions about a value. -/
def laurent : RatFunc R →ₐ[R] RatFunc R :=
  RatFunc.mapAlgHom (.ofLinearMap (taylor r) (taylor_one _) (taylor_mul _))
    (taylor_mem_nonZeroDivisors _)
#align ratfunc.laurent RatFunc.laurent

theorem laurent_div :
    laurent r (algebraMap _ _ p / algebraMap _ _ q) =
      algebraMap _ _ (taylor r p) / algebraMap _ _ (taylor r q) :=
  laurentAux_div r p q
#align ratfunc.laurent_div RatFunc.laurent_div

@[simp]
theorem laurent_algebraMap : laurent r (algebraMap _ _ p) = algebraMap _ _ (taylor r p) :=
  laurentAux_algebraMap _ _
#align ratfunc.laurent_algebra_map RatFunc.laurent_algebraMap

@[simp]
theorem laurent_X : laurent r X = X + C r := by
  rw [← algebraMap_X, laurent_algebraMap, taylor_X, _root_.map_add, algebraMap_C]
set_option linter.uppercaseLean3 false in
#align ratfunc.laurent_X RatFunc.laurent_X

@[simp]
theorem laurent_C (x : R) : laurent r (C x) = C x := by
  rw [← algebraMap_C, laurent_algebraMap, taylor_C]
set_option linter.uppercaseLean3 false in
#align ratfunc.laurent_C RatFunc.laurent_C

@[simp]
theorem laurent_at_zero : laurent 0 f = f := by induction f using RatFunc.induction_on; simp
#align ratfunc.laurent_at_zero RatFunc.laurent_at_zero

theorem laurent_laurent : laurent r (laurent s f) = laurent (r + s) f := by
  induction f using RatFunc.induction_on
  simp_rw [laurent_div, taylor_taylor]
#align ratfunc.laurent_laurent RatFunc.laurent_laurent

theorem laurent_injective : Function.Injective (laurent r) := fun _ _ h => by
  simpa [laurent_laurent] using congr_arg (laurent (-r)) h
#align ratfunc.laurent_injective RatFunc.laurent_injective

end

end RatFunc
