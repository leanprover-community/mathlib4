import Mathlib.Tactic.Trans

-- testing that the attribute is recognized
@[trans] def nleqTrans {a b c : Nat} : a ≤ b → b ≤ c → a ≤ c := Nat.le_trans

@[trans] def eqTrans {α : Type}{a b c : α}:  a = b → b = c → a = c := by
    intro h₁ h₂
    apply Eq.trans h₁ h₂

example (a b c : Nat): a = b → b = c → a = c := by
    intro h₁ h₂
    trans
    assumption
    assumption

example (a b c : Nat): a = b → b = c → a = c := by
    intro h₁ h₂
    trans b
    assumption
    assumption

example : Trans ((. ≤ . : Nat → Nat → Prop))
        (. ≤ . : Nat → Nat → Prop) (. ≤ . : Nat → Nat → Prop) := inferInstance

example (a b c : Nat): a ≤  b → b ≤  c → a ≤  c := by
   intro h₁ h₂
   trans b
   assumption
   assumption

example (a b c : Nat): a ≤  b → b ≤  c → a ≤  c := by
   intro h₁ h₂
   trans
   assumption
   assumption

#check @Trans.trans
