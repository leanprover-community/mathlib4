/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/

import Lean

/-!
# Stub for implementation of the `@[simps]` attribute.

This file is currently just a stub that creates a no-operation `@[simps]` attribute.
Without this, all declarations in the mathport output for mathlib3 that use `@[simps]` fail.
With the no-operation attribute, the declarations can succeed,
but of course all later proofs that rely on the existence of the automatically generated lemmas
will fail.

Later we will need to port the implementation from mathlib3.

-/


open Lean Meta

namespace Lean.Parser
namespace Attr

syntax (name := simps) "simps" (" (" &"config" " := " term ")")? (ppSpace ident)* : attr
syntax (name := simps?) "simps?" (" (" &"config" " := " term ")")? (ppSpace ident)* : attr

end Attr

namespace Command

syntax simpsRule.rename := ident " → " ident
syntax simpsRule.erase := "-" ident
syntax simpsRule := (simpsRule.rename <|> simpsRule.erase) &" as_prefix"?
syntax simpsProj := ident (" (" simpsRule,+ ")")?
syntax (name := initializeSimpsProjections) "initialize_simps_projections"
  (ppSpace simpsProj)* : command
syntax (name := initializeSimpsProjections?) "initialize_simps_projections?"
  (ppSpace simpsProj)* : command

end Command
end Lean.Parser

-- Defines the user attribute `simps` for automatic generation of `@[simp]` lemmas for projections.
initialize simpsAttr : ParametricAttribute (Array Name) ←
  registerParametricAttribute {
    name := `simps
    descr := "Automatically derive lemmas specifying the projections of this declaration.",
    getParam := fun
    -- TODO implement support for `config := ...`
    | _, `(attr|simps $[$ids]*) => pure $ ids.map (·.getId.eraseMacroScopes)
    | _, stx => throwError "unexpected simps syntax {stx}"
  }
