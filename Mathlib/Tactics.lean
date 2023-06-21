import Mathlib.Data.Nat.Factorial.Basic

namespace Factorial!
open Lean Elab Term Meta

def elabIdentFactorial : TermElab := fun stx expectedType? =>
  match stx with
  | `($name:ident) => do
    let name := name.getId
    if name.hasMacroScopes then
      -- I think this would mean the name appears from within a quote.
      -- I'm not sure how to properly deal with this, and it seems ok to just not.
      throwUnsupportedSyntax
    else
      try
        elabIdent stx expectedType?
      catch e =>
        match name with
        | .str n s =>
          if s.endsWith "!" then
            let name' := Name.str n (s.dropRight 1)
            try
              elabTerm (← `(Nat.factorial $(mkIdent name'))) expectedType?
            catch _ =>
              throw e
          else
            throw e
        | _ => throw e
  | _ => throwUnsupportedSyntax

attribute [term_elab ident] elabIdentFactorial

end Factorial!

open scoped Nat Factorial!

variable (x : Nat)

set_option linter.unusedVariables false
def f (z : Nat) : Nat := z!

example : f 4 = 24 := rfl

def s := {n | n! ≤ 3}

example : s = {n | n ! ≤ 3} := rfl

instance : Coe Bool Nat where
  coe
    | true => 1
    | false => 0

example : true! = 1 := rfl
