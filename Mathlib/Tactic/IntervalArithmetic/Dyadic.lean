module

public import Mathlib.Order.Defs.LinearOrder

set_option linter.style.header false

@[expose] public section

theorem natAbs_eq_one_mod_two {n : Int} (hn : n % 2 = 1) : n.natAbs % 2 = 1 := by grind

instance : LinearOrder Dyadic where
  le_refl := Std.IsPreorder.le_refl
  le_trans := Std.IsPreorder.le_trans
  le_antisymm := Std.IsPartialOrder.le_antisymm
  lt_iff_le_not_ge := Std.LawfulOrderLT.lt_iff
  le_total := Std.IsLinearOrder.le_total
  toDecidableLE := Dyadic.instDecidableLE

def Dyadic.abs (x : Dyadic) : Dyadic :=
  match x with
  | zero => zero
  | .ofOdd n k h => .ofOdd n.natAbs k (by omega)
