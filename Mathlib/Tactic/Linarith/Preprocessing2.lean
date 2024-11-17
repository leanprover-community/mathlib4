import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.Linarith.Datatypes2

namespace Linarith

/-! ### Preprocessing -/

open Lean

def defaultPreprocessors2 : List Preprocessor :=
  [filterComparisons, strengthenStrictInt, compWithZero, cancelDenoms]
-- HM FIXME how to deal with `cancelDenoms`?

def preprocessAugmented (pps : List Preprocessor) (g : MVarId) (l : List (Syntax.Term × Expr)) :
    MetaM (List (Syntax.Term × Expr)) := g.withContext <|
  pps.foldlM (fun l pp => return (← g.withContext (pp.globalTransformAugmented l))) l

end Linarith
