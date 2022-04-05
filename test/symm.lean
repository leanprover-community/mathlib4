import Mathlib.Tactic.Symm

-- testing that the attribute is recognized
@[symm] def eqSymm{α : Type} (a b: α) : a = b → b = a := Eq.symm

example : ∀ (a b : ℕ), a = b → b = a := by
  intro a
  intro b
  intro h
  symm
  assumption

def sameParity : Nat  → Nat  → Prop
| n, m => n % 2 = m % 2

@[symm] def sameParitySymm(n m : Nat) : sameParity n m → sameParity m n :=
    fun hyp => Eq.symm hyp

example : ∀ (a b : Nat), sameParity a  b → sameParity b  a := by
  intro a
  intro b
  intro h
  symm
  assumption
