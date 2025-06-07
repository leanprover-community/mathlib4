/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.NumberTheory.ClassNumber.AdmissibleCardPowDegree
import Mathlib.NumberTheory.ClassNumber.Finite
import Mathlib.NumberTheory.FunctionField

/-!
# Class numbers of function fields

This file defines the class number of a function field as the (finite) cardinality of
the class group of its ring of integers. It also proves some elementary results
on the class number.

## Main definitions
- `FunctionField.classNumber`: the class number of a function field is the (finite)
cardinality of the class group of its ring of integers
-/


namespace FunctionField

open scoped Polynomial

variable (Fq F : Type*) [Field Fq] [Fintype Fq] [Field F]
variable [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
variable [IsScalarTower Fq[X] (RatFunc Fq) F]
variable [FunctionField Fq F] [Algebra.IsSeparable (RatFunc Fq) F]

namespace RingOfIntegers

open FunctionField

open scoped Classical in
noncomputable instance : Fintype (ClassGroup (ringOfIntegers Fq F)) :=
  ClassGroup.fintypeOfAdmissibleOfFinite (RatFunc Fq) F
    (Polynomial.cardPowDegreeIsAdmissible :
      AbsoluteValue.IsAdmissible (Polynomial.cardPowDegree : AbsoluteValue Fq[X] ℤ))

end RingOfIntegers

/-- The class number in a function field is the (finite) cardinality of the class group. -/
noncomputable def classNumber : ℕ :=
  Fintype.card (ClassGroup (ringOfIntegers Fq F))

/-- The class number of a function field is `1` iff the ring of integers is a PID. -/
theorem classNumber_eq_one_iff :
    classNumber Fq F = 1 ↔ IsPrincipalIdealRing (ringOfIntegers Fq F) :=
  card_classGroup_eq_one_iff

end FunctionField
