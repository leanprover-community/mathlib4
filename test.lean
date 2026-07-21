module

public import Mathlib.Data.ZMod.IntUnitsPower

#check NPow

attribute [local implicit_reducible] Additive.ofMul Additive.toMul

lemma test : Int.instUnitsPow (R := ℕ) = NPow.toPow := by
  with_reducible rfl -- fails
