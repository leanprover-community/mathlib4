import Mathlib.Data.Finset.Sort

#eval show Lean.MetaM Unit from guard <|
  (repr (0 : Multiset (List ℕ)) |>.pretty 15) = "0"
#eval show Lean.MetaM Unit from guard <|
  (repr ({[1, 2, 3], [4, 5, 6]} : Multiset (List ℕ)) |>.pretty 15) = "{[1, 2, 3],\n [4, 5, 6]}"

#eval show Lean.MetaM Unit from guard <|
  (repr (∅ : Finset (List ℕ)) |>.pretty 15) = "∅"
#eval show Lean.MetaM Unit from guard <|
  (repr ({[1, 2, 3], [4, 5, 6]} : Finset (List ℕ)) |>.pretty 15) = "{[1, 2, 3],\n [4, 5, 6]}"
