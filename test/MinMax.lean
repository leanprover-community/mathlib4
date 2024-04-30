import Mathlib.Tactic.MinMax

open Mathlib.ToNatDegree

/-
true

-/
#eval do
  let res := "SemilatticeSup"
  IO.println (splitUpper res == ["Semilattice", "Sup"])

/-
"hello I am `WithTop' α` and also `top'`"

-/
#eval
  stringReplacements "hello I am `WithBot' α` and also `bot'`"

/-
[['a', 'b', 'c'], ['D', 'e'], ['F']]

-/
#eval "abcDeF".toList.groupBy fun a b => a.isUpper || (a.isLower && b.isLower)

/-
[le, inf]

-/
#eval do
  let res := ["le", "inf"]
  let res := ["inf", "le"]
  IO.println (swapWords res) -- == ["Semilattice", "Sup"])

/-
[NNReal, HHi, ,,  , but,  , it, ', s,  ]
false

-/
#eval do
  let res := "NNRealHHi, but it's "
  IO.println (splitUpper res)
  IO.println (splitUpper res == ["NNReal", "HHi"])

/-
[hello,  , I,  , am,  , `, aDocString,  , 0, `,  , and,  , I,  , have, ,,  , some,  , punctuation, .]

-/
#eval do
  let test := "hello I am `aDocString 0` and I have, some punctuation."
  let gps := test.toList.groupBy fun x y : Char => x.isAlpha && y.isAlpha
  IO.println <| gps.map fun w => (⟨w⟩ : String)
