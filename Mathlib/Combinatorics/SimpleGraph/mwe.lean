import Mathlib.Tactic.Simps.Basic

structure Foo where
  bar : Nat
  Baz : Prop

@[simps]
def myFoo (n : Nat) : Foo where
  bar := n
  Baz := False

#check myFoo_bar
-- myFoo_Bar (n : Nat) : (myFoo n).Bar = n
#check myFoo_Baz
-- myFoo_Baz (n : Nat) : (myFoo n).Baz = False
