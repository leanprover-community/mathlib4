import Mathlib.Algebra.Field.Defs

/-!
# Facts about `algebraMap` when the coefficient ring is a field.
-/

public section

namespace algebraMap

universe u v w u₁ v₁

section SemifieldSemidivisionRing

variable {R : Type*} (A : Type*) [Semifield R] [DivisionSemiring A] [Algebra R A]

@[norm_cast]
theorem coe_inv (r : R) : ↑r⁻¹ = ((↑r)⁻¹ : A) :=
  map_inv₀ (algebraMap R A) r

@[norm_cast]
theorem coe_div (r s : R) : ↑(r / s) = (↑r / ↑s : A) :=
  map_div₀ (algebraMap R A) r s

@[norm_cast]
theorem coe_zpow (r : R) (z : ℤ) : ↑(r ^ z) = (r : A) ^ z :=
  map_zpow₀ (algebraMap R A) r z

end SemifieldSemidivisionRing

section FieldDivisionRing

variable (R A : Type*) [Field R] [DivisionRing A] [Algebra R A]

@[norm_cast]
theorem coe_ratCast (q : ℚ) : ↑(q : R) = (q : A) := map_ratCast (algebraMap R A) q

end FieldDivisionRing

end algebraMap
