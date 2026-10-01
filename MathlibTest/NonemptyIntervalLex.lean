import Mathlib.Order.Interval.Lex

-- Sanity check on the lexicographic ordering of `NonemptyInterval`.
/-- info: [(3, 3), (2, 2), (2, 3), (1, 1), (1, 2), (1, 3)] -/
#guard_msgs in
#eval [
  NonemptyInterval.mk (1, 1) (by grind),
  NonemptyInterval.mk (1, 2) (by grind),
  NonemptyInterval.mk (1, 3) (by grind),
  NonemptyInterval.mk (2, 2) (by grind),
  NonemptyInterval.mk (2, 3) (by grind),
  NonemptyInterval.mk (3, 3) (by grind)].map toLex |>.mergeSort.map (·.toProd)
