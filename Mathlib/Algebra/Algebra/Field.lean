/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Data.Rat.Cast.Defs

/-!
# Facts about `algebraMap` when the coefficient ring is a field.
-/

namespace algebraMap

universe u v w u₁ v₁
section FieldNontrivial

variable {R A : Type*} [Field R] [CommSemiring A] [Nontrivial A] [Algebra R A]

@[norm_cast, simp]
theorem coe_inj {a b : R} : (↑a : A) = ↑b ↔ a = b :=
  (algebraMap R A).injective.eq_iff
#align algebra_map.coe_inj algebraMap.coe_inj

@[norm_cast]
theorem lift_map_eq_zero_iff (a : R) : (↑a : A) = 0 ↔ a = 0 := map_eq_zero _
#align algebra_map.lift_map_eq_zero_iff algebraMap.lift_map_eq_zero_iff

end FieldNontrivial

section SemifieldSemidivisionRing

variable {R : Type*} (A : Type*) [Semifield R] [DivisionSemiring A] [Algebra R A]

@[norm_cast]
theorem coe_inv (r : R) : ↑r⁻¹ = ((↑r)⁻¹ : A) :=
  map_inv₀ (algebraMap R A) r
#align algebra_map.coe_inv algebraMap.coe_inv

@[norm_cast]
theorem coe_div (r s : R) : ↑(r / s) = (↑r / ↑s : A) :=
  map_div₀ (algebraMap R A) r s
#align algebra_map.coe_div algebraMap.coe_div

@[norm_cast]
theorem coe_zpow (r : R) (z : ℤ) : ↑(r ^ z) = (r : A) ^ z :=
  map_zpow₀ (algebraMap R A) r z
#align algebra_map.coe_zpow algebraMap.coe_zpow

end SemifieldSemidivisionRing

section FieldDivisionRing

variable (R A : Type*) [Field R] [DivisionRing A] [Algebra R A]

@[norm_cast]
theorem coe_ratCast (q : ℚ) : ↑(q : R) = (q : A) := map_ratCast (algebraMap R A) q
#align algebra_map.coe_rat_cast algebraMap.coe_ratCast

end FieldDivisionRing

end algebraMap
