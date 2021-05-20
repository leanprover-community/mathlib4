-- partial orders are in core Lean 3
-- this is from lib/library/init/algebra/prder.lean
class PartialOrder (P : Type u) extends LE P where
  refl (s : P) : s ≤ s
  antisymm (s t : P) : s ≤ t → t ≤ s → s = t
  trans (s t u : P) : s ≤ t → t ≤ u → s ≤ u
