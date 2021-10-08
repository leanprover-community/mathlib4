import Mathlib

example (x : Nat) : x ≠ x.succ := ne_of_lt (by librarySearch)
example : 0 ≠ 1 + 1 := ne_of_lt (by librarySearch)
example (x y : Nat) : x + y = y + x := by librarySearch
example (n m k : Nat) : n ≤ m → n + k ≤ m + k := by librarySearch
example (ha : a > 0) (w : b ∣ c) : a * b ∣ a * c := by librarySearch

example : Int := by librarySearch

example : x < x + 1 := librarySearch%
