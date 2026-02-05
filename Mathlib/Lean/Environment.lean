/-
Copyright (c) 2025 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

public import Lean.Environment
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
import Mathlib.Tactic.Linter.Header  --shake: keep

/-!
# Additional utilities for `Lean.Environment`

Including operations on `ConstantVal`, `ConstantKind`, `ConstantInfo`.
-/

public section

namespace Lean.Environment

/- The following declarations account for the fact that the `ConstantKind` of a declaration is
accessible when getting its `ConstantVal`, but is not recorded in said `ConstantVal`. -/

/--
Like `findConstVal?`, but also returns the declarations `ConstantKind`, which is known immediately.

Blocks on everything but the constant's body (if any), which is not accessible through the result.
-/
def findConstValWithKind? (env : Environment) (decl : Name) (skipRealize := false) :
    Option (ConstantVal × ConstantKind) := do
  let info ← env.findAsync? decl skipRealize
  return (info.toConstantVal, info.kind)

/--
Like `findConstVal?`, but only finds the `ConstantVal` for `decl` in `env` if its kind satisfies
`p`. Otherwise, returns `none`.

Blocks on everything but the constant's body (if any), which is not accessible through the result.
-/
def findConstValOfKind? (env : Environment) (p : ConstantKind → Bool) (decl : Name)
    (skipRealize := false) : Option ConstantVal := do
  let info ← env.findAsync? decl skipRealize
  if p info.kind then info.toConstantVal else none

/--
Like `findConstVal?`, but only finds the `ConstantVal` for `decl` in `env` if it is a theorem.

Blocks on everything but the constant's body (if any), which is not accessible through the result.
-/
def findTheoremConstVal? (env : Environment) (decl : Name)
    (skipRealize := false) : Option ConstantVal := do
  env.findConstValOfKind? (· matches .thm) decl skipRealize

end Lean.Environment

namespace Lean

/-- The name of each `ConstantKind`. -/
def ConstantKind.toString : ConstantKind → String
  | .defn     => "def"
  | .axiom    => "axiom"
  | .thm      => "theorem"
  | .opaque   => "opaque"
  | .quot     => "Quotient primitive"
  | .induct   => "inductive"
  | .ctor     => "constructor"
  | .recursor => "recursor"

instance : ToString ConstantKind := ⟨ConstantKind.toString⟩

/-- Alias for `ConstantKind.ofConstantInfo`, to enable dot notation. -/
def ConstantInfo.kind := @ConstantKind.ofConstantInfo

end Lean

end
