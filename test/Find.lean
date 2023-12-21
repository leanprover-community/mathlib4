import Mathlib.Tactic.Find

theorem add_comm_zero {n} : 0 + n = n + 0 := Nat.add_comm _ _

#find _ + _ = _ + _
#find ?n + _ = _ + ?n
#find (_ : Nat) + _ = _ + _
#find Nat → Nat
#find ?n ≤ ?m → ?n + _ ≤ ?m + _
