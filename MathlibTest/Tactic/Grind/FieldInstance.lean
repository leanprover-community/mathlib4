import Mathlib.FieldTheory.IntermediateField.Basic

#adaptation_note /-- This is currently broken by changes to Lean.
The test case doesn't seem to be essential elsewhere in Mathlib.
It can be made to work again by add `inv a := a⁻¹` back to `toGrindField`,
but that then causes breakages elsewhere. We are still investigating.
See https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/backward.2EisDefEq.2ErespectTransparency/near/576563746
-/
-- example {K L : Type*} [Field K] [Field L] [Algebra K L]
--     (E : IntermediateField K L) :
--     (Field.toGrindField.toInv : Inv E) = InvMemClass.inv := by
--   with_reducible_and_instances rfl
