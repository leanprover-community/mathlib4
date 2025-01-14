import Mathlib.Data.List.EditDistance.Defs
import Mathlib.Algebra.Group.Nat.Defs

#guard
  (suffixLevenshtein Levenshtein.defaultCost "kitten".toList "sitting".toList).1 =
    [3, 3, 4, 5, 6, 6, 7]

#guard levenshtein Levenshtein.defaultCost
  "but our fish said, 'no! no!'".toList
  "'put me down!' said the fish.".toList = 21
