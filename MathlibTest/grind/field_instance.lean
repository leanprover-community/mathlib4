import Mathlib.FieldTheory.IntermediateField.Basic

example {K L : Type*} [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L) :
    (Field.toGrindField.toInv : Inv E) = InvMemClass.inv := by
  with_reducible_and_instances rfl
