import Lean

open Lean.Meta

namespace Lean.Elab.Tactic

/-- Clear all hypotheses starting with `_`, like `_match` and `_let_match`. -/
elab (name := clear_) "clear_" : tactic =>
  liftMetaTactic1 fun goal => do
    let mut toClear := #[]
    for decl in ← getLCtx do
      if let Name.str _ str := decl.userName then
        if !str.isEmpty && str.front == '_' then
          if let none ← isClass? decl.type then
            toClear := toClear.push decl.fvarId
    tryClearMany goal toClear
