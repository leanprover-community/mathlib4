import Mathlib.FieldTheory.LinearDisjoint

variable {k L : Type*} [Field k] [Field L] [Algebra k L]
variable (E F : IntermediateField k L)

@[implicit_reducible] def foo : Algebra ↥(E ⊓ F) ↥E := inferInstance

#print IntermediateField.instAlgebraSubtypeMemMin

#exit

#print foo

example : True := by
  let E' : IntermediateField ↥(E ⊓ F) L := E.extendScalars (F := E ⊓ F) inf_le_left
  let F' : IntermediateField ↥(E ⊓ F) L := F.extendScalars (F := E ⊓ F) inf_le_right
  let : Algebra ↥E' ↥(E' ⊔ F') := (IntermediateField.inclusion le_sup_left).toRingHom.toAlgebra
  have := Module.finrank ↥E' ↥(E' ⊔ F')
  trivial
