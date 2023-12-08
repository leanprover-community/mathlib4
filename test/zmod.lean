import Mathlib.Data.ZMod.Defs

-- We ensure here that the `@[csimp]` attribute successfully replaces (at runtime)
-- the default value of `npowRec` for the exponentation operation in `Monoid`
-- with a tail-recursive implementation by repeated squaring.
/-- info: 1 -/
#guard_msgs in
#eval (3 : ZMod 49999)^49998
