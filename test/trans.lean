import Mathlib.Tactic.Trans

-- testing that the attribute is recognized and used
def nleq : Nat → Nat → Prop
| a, b => a ≤ b

@[trans] def nleqTrans {a b c : Nat} : nleq a b → nleq b c → nleq a c := Nat.le_trans

example (a b c : Nat): nleq a b → nleq b c → nleq a c := by
   intro h₁ h₂
   trans b
   assumption
   assumption

example (a b c : Nat): nleq a b → nleq b c → nleq a c :=
   by intros ; trans ; repeat (assumption)

-- using `Trans` typeclass
@[trans] def eqTrans {α : Type}{a b c : α}:  a = b → b = c → a = c := by
    intro h₁ h₂
    apply Eq.trans h₁ h₂


example (a b c : Nat): a = b → b = c → a = c :=
   by intros ; trans ; repeat (assumption)

example (a b c : Nat): a = b → b = c → a = c := by
    intro h₁ h₂
    trans b
    assumption
    assumption

example : Trans ((. ≤ . : Nat → Nat → Prop))
        (. ≤ . : Nat → Nat → Prop) (. ≤ . : Nat → Nat → Prop) := inferInstance

example (a b c : Nat): a ≤ b → b ≤ c → a ≤ c := by
   intro h₁ h₂
   trans b
   assumption
   assumption

example (a b c : Nat): a ≤ b → b ≤ c → a ≤ c :=
   by intros ; trans ; repeat (assumption)


example (a b c : Nat): a < b → b < c → a < c := by
   intro h₁ h₂
   trans b
   assumption
   assumption

example (a b c : Nat): a < b → b < c → a < c :=
   by intros ; trans ; repeat (assumption)


macro "transitivity" t?:(colGt term)? : tactic => do
   match t? with
   | none => `(tactic|trans)
   | some t => `(tactic|trans $t)

example (a b c : Nat): a < b → b < c → a < c := by
   intro h₁ h₂
   transitivity b
   assumption
   assumption

example (a b c : Nat): a < b → b < c → a < c :=
   by intros ; transitivity ; repeat (assumption)

example (a b c : Nat): a ≤ b → b ≤ c → a ≤ c :=
   by intros ; transitivity ; repeat (assumption)
