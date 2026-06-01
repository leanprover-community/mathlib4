import Mathlib.Data.ZMod.Defs

-- A Mersenne exponent, chosen so the test below takes no more than a few seconds
-- but should be enough to trigger a stack overflow from a non-tail-recursive implementation
-- of exponentiation by repeated squaring.
def k := 11213
def p := 2^k - 1

set_option exponentiation.threshold 100000 in
-- We ensure here that the `@[csimp]` attribute successfully replaces (at runtime)
-- the default value of `npowRec` for the exponentiation operation in `Monoid`
-- with a tail-recursive implementation by repeated squaring.
/-- info: 1 -/
#guard_msgs in
#eval (37 : ZMod p)^(p-1)
