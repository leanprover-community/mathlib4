/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Util.PPBetaOption

/-! Add the `pp.beta` feature to the pretty printer

By importing this module, you can do
```lean
set_option pp.beta true
```
and then the pretty printer will beta reduce all expressions.
The option can see through mdata for beta reduction opportunities,
but it will otherwise preserve mdata.

This option is not recommended and can lead to very confusing situations.
For example:
```lean
example {α β : Type} (f : α → β) (a : α) (b : β) (h : f a = b) :
    (fun x ↦ f x) a = b := by
  /-
  α β : Type
  f : α → β
  a : α
  b : β
  h : f a = b
  ⊢ f a = b
  -/
  rw [h] -- fails
```

Additional caveats:
1. `pp.beta` is incompatible with pretty printer features that
   store data by expression position, for example `pp.analyze`.
2. Tooltips in the info view might display beta unreduced terms.
   This defect is expected to be limited to just the outermost expression.
-/

open Lean PrettyPrinter Delaborator

/-- Get the state of the `pp.beta` option. -/
def Lean.getPPBeta (o : Options) : Bool := o.get pp.beta.name false

namespace Mathlib.Util.PPBeta

/-- Beta reduce all expressions.
This is incompatible with the `pp.analyze` option.
In general it can clear `optionsPerPos`.
Note that tooltips might still display beta-unreduced terms. -/
def betaReduceFirst : Delab := whenPPOption getPPBeta do
  let e ← SubExpr.getExpr
  -- Check if there's anything beta reducible first:
  unless (e.find? Expr.isHeadBetaTarget).isSome do failure
  let e' ← Core.betaReduce e
  -- Clear the options since switching to `e'` invalidates them.
  withReader (fun ctx => {ctx with optionsPerPos := {}}) do
    -- set `pp.beta` to false at this position to prevent looping.
    withOptionAtCurrPos `pp.beta false do
      withTheReader SubExpr ({· with expr := e'}) delab

attribute [delab app, delab lam, delab forallE, delab letE, delab mdata, delab proj]
  betaReduceFirst
