import Mathlib.Data.Finset.Sort

-- FIXME temporarily commented out: unsafe can't run outside of a declaration.
-- Fixed in https://github.com/leanprover/lean4/pull/3324, which will land in nightly-2024-02-15.
-- Mathlib tracking issue at https://github.com/leanprover-community/mathlib4/issues/10535

-- run_cmd Lean.Elab.Command.liftTermElabM do
--   unsafe guard <|
--    (repr (0 : Multiset (List ℕ)) |>.pretty 15) = "0"
--   unsafe guard <|
--     (repr ({[1, 2, 3], [4, 5, 6]} : Multiset (List ℕ)) |>.pretty 15) = "{[1, 2, 3],\n [4, 5, 6]}"
--   unsafe guard <|
--     (repr (∅ : Finset (List ℕ)) |>.pretty 15) = "∅"
--   unsafe guard <|
--     (repr ({[1, 2, 3], [4, 5, 6]} : Finset (List ℕ)) |>.pretty 15) = "{[1, 2, 3],\n [4, 5, 6]}"
