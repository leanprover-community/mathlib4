/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.FieldTheory.RatFunc.AsPolynomial

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

open scoped nonZeroDivisors

variable {R : Type u} [CommRing R] (r s : R) (p q : R[X]) (f : RatFunc R)

theorem taylor_mem_nonZeroDivisors (hp : p ∈ R[X]⁰) : taylor r p ∈ R[X]⁰ := by
  rw [mem_nonZeroDivisors_iff]
  intro x hx
  have : x = taylor (r - r) x := by simp
  rwa [this, sub_eq_add_neg, ← taylor_taylor, ← taylor_mul,
    LinearMap.map_eq_zero_iff _ (taylor_injective _), mul_right_mem_nonZeroDivisors_eq_zero_iff hp,
    LinearMap.map_eq_zero_iff _ (taylor_injective _)] at hx

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

theorem laurentAux_ofFractionRing_mk (q : R[X]⁰) :
    laurentAux r (ofFractionRing (Localization.mk p q)) =
      ofFractionRing (.mk (taylor r p) ⟨taylor r q, taylor_mem_nonZeroDivisors r q q.prop⟩) :=
  map_apply_ofFractionRing_mk _ _ _ _

variable [IsDomain R]

theorem laurentAux_div :
    laurentAux r (algebraMap _ _ p / algebraMap _ _ q) =
      algebraMap _ _ (taylor r p) / algebraMap _ _ (taylor r q) :=
  -- Porting note: added `by exact taylor_mem_nonZeroDivisors r`
  map_apply_div _ (by exact taylor_mem_nonZeroDivisors r) _ _

@[simp]
theorem laurentAux_algebraMap : laurentAux r (algebraMap _ _ p) = algebraMap _ _ (taylor r p) := by
  rw [← mk_one, ← mk_one, mk_eq_div, laurentAux_div, mk_eq_div, taylor_one, map_one, map_one]

/-- The Laurent expansion of rational functions about a value. -/
def laurent : RatFunc R →ₐ[R] RatFunc R :=
  RatFunc.mapAlgHom (.ofLinearMap (taylor r) (taylor_one _) (taylor_mul _))
    (taylor_mem_nonZeroDivisors _)

theorem laurent_div :
    laurent r (algebraMap _ _ p / algebraMap _ _ q) =
      algebraMap _ _ (taylor r p) / algebraMap _ _ (taylor r q) :=
  laurentAux_div r p q

@[simp]
theorem laurent_algebraMap : laurent r (algebraMap _ _ p) = algebraMap _ _ (taylor r p) :=
  laurentAux_algebraMap _ _

@[simp]
theorem laurent_X : laurent r X = X + C r := by
  rw [← algebraMap_X, laurent_algebraMap, taylor_X, map_add, algebraMap_C]

@[simp]
theorem laurent_C (x : R) : laurent r (C x) = C x := by
  rw [← algebraMap_C, laurent_algebraMap, taylor_C]

@[simp]
theorem laurent_at_zero : laurent 0 f = f := by induction f using RatFunc.induction_on; simp

theorem laurent_laurent : laurent r (laurent s f) = laurent (r + s) f := by
  induction f using RatFunc.induction_on
  simp_rw [laurent_div, taylor_taylor]

theorem laurent_injective : Function.Injective (laurent r) := fun _ _ h => by
  simpa [laurent_laurent] using congr_arg (laurent (-r)) h

end

end RatFunc
