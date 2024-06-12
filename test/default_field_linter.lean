import Mathlib.Algebra.Ring.Defs

def Foo := Unit


/--
error: While evaluating default nsmul := nsmulRec:
  failed to synthesize instance
    Zero Foo
---
error: While evaluating default zsmul := zsmulRec:
  failed to synthesize instance
    Zero Foo
-/
#guard_msgs in
instance : Ring Foo where
  add_assoc _ _ _ := rfl
  zero := ()
  zero_add _ := rfl
  add_zero _ := rfl
  add_comm _ _ := rfl
  mul _ _ := ()
  left_distrib _ _ _ := rfl
  right_distrib _ _ _ := rfl
  zero_mul _ := rfl
  mul_zero _ := rfl
  mul_assoc _ _ _:= rfl
  one := ()
  one_mul _ := rfl
  mul_one _ := rfl
  add_left_neg _ := rfl

-- this is the fix to the errors above
instance : Zero Foo where
  zero := ()

instance : Add Foo where
  add _ _ := ()

instance : Neg Foo where
  neg _ := ()

/--
warning: Using default value
  nsmul := nsmulRec
which may cause typeclass diamonds for `Module ℕ _`.
To silence this warning, write the above in your instance definition, optionally replacing nsmulRec with a better implementation. [linter.structureDiamondDefaults]
---
warning: Using default value
  zsmul := zsmulRec
which may cause typeclass diamonds for `Module ℤ _`.
To silence this warning, write the above in your instance definition, optionally replacing zsmulRec with a better implementation. [linter.structureDiamondDefaults]
-/
#guard_msgs in
instance : Ring Foo where
  add_assoc _ _ _ := rfl
  zero := ()
  zero_add _ := rfl
  add_zero _ := rfl
  add_comm _ _ := rfl
  mul _ _ := ()
  left_distrib _ _ _ := rfl
  right_distrib _ _ _ := rfl
  zero_mul _ := rfl
  mul_zero _ := rfl
  mul_assoc _ _ _:= rfl
  one := ()
  one_mul _ := rfl
  mul_one _ := rfl
  add_left_neg _ := rfl
