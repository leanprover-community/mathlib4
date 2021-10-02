import Mathlib.Tactic.Find

-- TODO Write an "internal" version of `find` that returns a list of results,
-- rather than printing, and use this to set up silent tests.

-- #find _ + _ = _ + _
-- #find ?n + _ = _ + ?n
-- #find (_ : Nat) + _ = _ + _
-- #find Nat → Nat
-- #find ?n ≤ ?m → ?n + _ ≤ ?m + _
