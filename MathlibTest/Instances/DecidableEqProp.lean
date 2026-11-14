module -- shake: keep-all
import Mathlib

/-!
# No decidable equality for `Prop`

We import everything to verify that nothing exposes a `DecidableEq` instance for `Prop`.
-/

/--
error: failed to synthesize
  DecidableEq Prop

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth DecidableEq Prop
