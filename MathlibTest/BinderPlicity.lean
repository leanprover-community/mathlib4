module

import Mathlib.Util.BinderPlicity

/-!

Test file for the binder plicity code action.

  WARNING 
  This file is not meant to be merged!
  WARNING 

This file is just provided for the convenience of reviewers 
to test the correct functionality of the code action.
It should be removed before PR 40641 is merged.

In the future, a proper code action testing framework
should eliminate the need for these kinds of files.
-/


/- Switch works in the usual case -/
example (nat : Nat) : Nat := nat + 1

/- Switch works when no type is specified -/
example {nat} := nat + 1

/- Switch preserves whitespace -/
example  (nat : Nat)  : Nat := nat + 1
example /- My perfect comment -/ (nat : Nat)  : Nat := nat + 1
example /-1-/ (/-2-/nat/-3-/ : /-4-/Nat/-5-/) /-6-/: Nat := nat + 1
example/-1-/(/-2-/nat/-3-/)/-4-/:= nat + 1

/- Switch doesn't work when there's a default value -/
example (nat : Nat := 0) : Nat := nat + 1
