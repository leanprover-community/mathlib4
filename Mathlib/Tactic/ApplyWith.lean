import Lean.Elab.Eval
import Lean.Elab.Tactic.ElabTerm
import Std.Util.TermUnsafe

namespace Mathlib.Tactic
open Lean Meta Elab Tactic Term

/--
`apply (config := cfg) e` is like `apply e` but allows you to provide a configuration
`cfg : ApplyConfig` to pass to the underlying apply operation.
-/
elab (name := applyWith) "apply" " (" &"config" " := " cfg:term ") " e:term : tactic => do
  let cfg ← unsafe evalTerm ApplyConfig (mkConst ``ApplyConfig) cfg
  evalApplyLikeTactic (·.apply · cfg) e
