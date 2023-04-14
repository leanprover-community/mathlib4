import Mathlib.Data.Fin.VecNotation

/-! These tests are testing `PiFin.toExpr` and fail with
`local attribute [-instance] PiFin.toExpr` -/

open Lean.Meta

#eval do
  let x : Fin 0 → ℕ := ![]
  isDefEq `(x) `(![] : Fin 0 → ℕ)

#eval do
  let x := ![1, 2, 3]
  isDefEq `(x) `(![1, 2, 3])

#eval do
  let x := ![![1, 2], ![3, 4]]
  isDefEq `(x) `(![![1, 2], ![3, 4]])

/-! These tests are testing `PiFin.repr` -/

#eval show MetaM Unit from guard (toString (repr (![] : _ → ℕ)) = "![]")
#eval show MetaM Unit from guard (toString (repr ![1, 2, 3]) = "![1, 2, 3]")
#eval show MetaM Unit from guard (toString (repr ![![1, 2], ![3, 4]]) = "![![1, 2], ![3, 4]]")
