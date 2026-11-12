import Mathlib.Data.Finset.Sort

run_cmd Lean.Elab.Command.liftTermElabM do
  unsafe guard <|
   (repr (0 : Multiset (List ℕ)) |>.pretty 15) = "0"
  unsafe guard <|
    (repr ({[1, 2, 3], [4, 5, 6]} : Multiset (List ℕ)) |>.pretty 15) = "{[1, 2, 3],\n [4, 5, 6]}"
  unsafe guard <|
    (repr (∅ : Finset (List ℕ)) |>.pretty 15) = "∅"
  unsafe guard <|
    (repr ({[1, 2, 3], [4, 5, 6]} : Finset (List ℕ)) |>.pretty 15) = "{[1, 2, 3],\n [4, 5, 6]}"
