/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen

! This file was ported from Lean 3 source module number_theory.number_field.class_number
! leanprover-community/mathlib commit d0259b01c82eed3f50390a60404c63faf9e60b1f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.NumberTheory.ClassNumber.AdmissibleAbs
import Mathbin.NumberTheory.ClassNumber.Finite
import Mathbin.NumberTheory.NumberField.Basic

/-!
# Class numbers of number fields

This file defines the class number of a number field as the (finite) cardinality of
the class group of its ring of integers. It also proves some elementary results
on the class number.

## Main definitions
- `number_field.class_number`: the class number of a number field is the (finite)
cardinality of the class group of its ring of integers
-/


namespace NumberField

variable (K : Type _) [Field K] [NumberField K]

namespace RingOfIntegers

noncomputable instance : Fintype (ClassGroup (ringOfIntegers K)) :=
  ClassGroup.fintypeOfAdmissibleOfFinite ℚ K AbsoluteValue.absIsAdmissible

end RingOfIntegers

/-- The class number of a number field is the (finite) cardinality of the class group. -/
noncomputable def classNumber : ℕ :=
  Fintype.card (ClassGroup (ringOfIntegers K))
#align number_field.class_number NumberField.classNumber

variable {K}

/-- The class number of a number field is `1` iff the ring of integers is a PID. -/
theorem classNumber_eq_one_iff : classNumber K = 1 ↔ IsPrincipalIdealRing (ringOfIntegers K) :=
  card_classGroup_eq_one_iff
#align number_field.class_number_eq_one_iff NumberField.classNumber_eq_one_iff

end NumberField

namespace Rat

open NumberField

theorem classNumber_eq : NumberField.classNumber ℚ = 1 :=
  classNumber_eq_one_iff.mpr <| by
    convert
      IsPrincipalIdealRing.of_surjective
        (rat.ring_of_integers_equiv.symm : ℤ →+* ring_of_integers ℚ)
        rat.ring_of_integers_equiv.symm.surjective
#align rat.class_number_eq Rat.classNumber_eq

end Rat

