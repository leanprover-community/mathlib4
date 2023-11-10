import Mathlib.Data.MLList.DepthFirst

-- We perform a depth first search of the "proper divisors in descending order" tree.
#eval show Lean.MetaM Unit from do
  let r := depthFirstRemovingDuplicates' (fun n => List.range n |>.filter (n % · = 0) |>.reverse) 24
  guard $ r = [24, 12, 6, 3, 1, 2, 4, 8]
