import Mathlib.Tactic.FindSyntax

infix:65 " #find_syntax_add " => Nat.add

/--
info: Found 2 uses among over 500 syntax declarations
In `MathlibTest.FindSyntax`:
  «term_#find_syntax_add_»: '#find_syntax_add'

In `Mathlib.Tactic.FindSyntax`:
  Mathlib.FindSyntax.«command#find_syntax_Approx»: '#find_syntax  _  approx'
-/
#guard_msgs in
#find_syntax "#find_syntax" approx  -- an `infix` in two files, one being the current one

/--
info: Found 1 use among over 500 syntax declarations
In `Init.Notation`:
  «term_∘_»: '∘'
-/
#guard_msgs in
#find_syntax "∘" approx  -- an `infixr`

/--
info: Found 1 use among over 500 syntax declarations
In `Init.Notation`:
  «term_∣_»: '∣'
-/
#guard_msgs in
#find_syntax "∣" approx  -- an `infix`

/--
info: Found 2 uses among over 500 syntax declarations
In `Init.Notation`:
  «stx_,*»: ',*'
  «stx_,*,?»: ',*,?'
-/
#guard_msgs in
#find_syntax ",*" approx  -- generated by a `macro`

/--
info: Found 1 use among over 500 syntax declarations
In `Init.Notation`:
  «term~~~_»: '~~~'
-/
#guard_msgs in
#find_syntax "~~~" approx  -- a `prefix`

/--
info: Found 4 uses among over 500 syntax declarations
In `Init.Tactics`:
  Lean.Parser.Tactic.refine: 'refine'
  Lean.Parser.Tactic.refine': 'refine''
  Lean.Parser.Tactic.tacticRefine_lift'_: 'refine_lift''
  Lean.Parser.Tactic.tacticRefine_lift_: 'refine_lift'
-/
#guard_msgs in
#find_syntax "refine" approx  -- a `nonReservedSymbol`
