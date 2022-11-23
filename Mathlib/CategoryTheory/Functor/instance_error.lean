-- Reported as https://github.com/leanprover/lean4/issues/1876

class C (V : Type) where
  n : Nat
  m : Nat

structure F (V : Type) [C V]

variable {V : Type} [C V] -- failed to synthesize instance _root_.C ?m.152

def G.C : C (F V) where
  n := 5
  m := 7

def G.CC : C (F V) where
  n := 5
  -- No error about missing field!
