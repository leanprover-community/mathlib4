import Mathlib

#adaptation_note /-- This test is disabled until lean4#15392 is fixed.
Since v4.35.0-rc2, Lean builds the Sine Qua Non indexes on the first query in each process,
and with `import Mathlib` this test takes about 520 s.
Re-enable it after the toolchain bump that includes the fix.
See https://github.com/leanprover/lean4/issues/15392
and https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/lean4.2315159.20causes.20significant.20regression.20in.20MathlibTests/with/627571608
-/

-- set_library_suggestions Lean.LibrarySuggestions.sineQuaNonSelector

-- -- Verify that basic functionality of `sineQuaNon` still works after importing Mathlib.
-- example {x : Dyadic} {prec : Int} : x.roundDown prec ≤ x := by
--   fail_if_success grind
--   grind +suggestions

-- -- Verify that `sineQuaNon` finds Mathlib theorems, too.
-- open Real
-- -- This is exactly `rpowIntegrand₀₁_nonneg`
-- example (hp : 0 < p) (ht : 0 ≤ t) (hx : 0 ≤ x) :
--     0 ≤ rpowIntegrand₀₁ p t x := by
--   fail_if_success grind
--   grind +suggestions
