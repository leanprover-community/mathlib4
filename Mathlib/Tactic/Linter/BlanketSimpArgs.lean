/-
Copyright (c) 2026 Sebastian Graf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

public meta import Lean.Elab.Command
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
public meta import Mathlib.Tactic.Linter.Header  -- shake: keep

/-!
# The `blanketSimpArgs` linter

The `blanketSimpArgs` linter flags simp arguments such as `simp [Subsingleton.eq_zero]`
whose rewrite source is a bare variable and whose remaining hypotheses `simp` must
discharge at every match.

## Example

```
example {M : Type} [Zero M] [Subsingleton M] (x : M) : x = 0 := by
  simp [Subsingleton.eq_zero]     -- linted against
```

## Why is this bad?

A lemma like `Subsingleton.eq_zero : ∀ {α} [Zero α] [Subsingleton α] (a : α), a = 0`
rewrites the bare variable `a`. Its discrimination tree key is `*`, so `simp` retrieves
and tries it at every visited subterm, and each attempted match triggers instance
searches for `Zero α` and `Subsingleton α`. Under binders these searches miss the
instance cache, so a single such simp argument can dominate the elaboration time of
a proof.

The fix is to determine the side conditions once, at elaboration time of the simp
argument: apply the lemma to a term, as in `simp [Subsingleton.eq_zero x]`, or fix
its implicit arguments, as in `simp [Subsingleton.eq_zero (α := M)]`.
-/

meta section

open Lean Elab Command Linter Meta

namespace Mathlib.Linter

/-- The `blanketSimpArgs` linter flags simp arguments whose rewrite source is a bare
variable and whose remaining hypotheses `simp` must discharge at every match. -/
public register_option linter.blanketSimpArgs : Bool := {
  defValue := false
  descr := "enable the blanketSimpArgs linter"
}

namespace BlanketSimpArgs

/-- The source term that using `declName` as a simp lemma rewrites, i.e. the left-hand
side of its conclusion, or the right-hand side when the lemma is used with `←`. -/
private def rewriteSource? (concl : Expr) (rev : Bool) : Option Expr :=
  if let some (_, lhs, rhs) := concl.eq? then
    some (if rev then rhs else lhs)
  else if let some (lhs, rhs) := concl.iff? then
    some (if rev then rhs else lhs)
  else if let some (_, lhs, _, rhs) := concl.heq? then
    some (if rev then rhs else lhs)
  else if rev then
    none
  else if let some p := concl.not? then
    some p
  else
    some concl

/--
Checks whether using `declName` as a simp lemma matches every subterm while leaving
side conditions for `simp` to discharge at each match: its rewrite source must be one
of its universally quantified variables, and at least one instance-implicit argument
or hypothesis must remain to be discharged.
-/
def isBlanketRewrite (declName : Name) (rev : Bool) : MetaM Bool := do
  let ci ← getConstInfo declName
  forallTelescopeReducing ci.type fun xs concl => do
    let some src := rewriteSource? concl rev | return false
    unless src.isFVar && xs.contains src do return false
    xs.anyM fun x => do
      if x == src then return false
      let fvarId := x.fvarId!
      return (← fvarId.getBinderInfo) == .instImplicit || (← isProp (← fvarId.getType))

/-- The syntax kind of the `simp_rw` tactic, whose module cannot be imported here. -/
private def simpRwKind : SyntaxNodeKind := `Mathlib.Tactic.tacticSimp_rw___

/-- The simp argument terms underneath `stx`, each paired with whether it is reversed
by `←`: the `simpLemma` nodes of the `simp`-like tactics, including `simpa`, `simp_all`,
`norm_num` and `nontriviality _ using`, and the rewrite rules of `simp_rw`. -/
partial def simpArgTerms (stx : Syntax) (inSimpRw : Bool := false) : Array (Syntax × Bool) :=
  let inSimpRw := inSimpRw || stx.isOfKind simpRwKind
  let rest := stx.getArgs.flatMap (simpArgTerms · inSimpRw)
  if stx.isOfKind ``Lean.Parser.Tactic.simpLemma then
    rest.push (stx[2], !stx[1].isNone)
  else if inSimpRw && stx.isOfKind ``Lean.Parser.Tactic.rwRule then
    rest.push (stx[1], !stx[0].isNone)
  else
    rest

@[inherit_doc Mathlib.Linter.linter.blanketSimpArgs]
def blanketSimpArgsLinter : Linter where run := withSetOptionIn fun stx => do
  unless getLinterValue linter.blanketSimpArgs (← getLinterOptions) do
    return
  if (← MonadState.get).messages.hasErrors then
    return
  for (term, rev) in simpArgTerms stx do
    unless term.isIdent do continue
    let some declName ← liftCoreM <|
        try some <$> realizeGlobalConstNoOverload term catch _ => pure none
      | continue
    if ← liftTermElabM (isBlanketRewrite declName rev) then
      logLint linter.blanketSimpArgs term
        m!"`{.ofConstName declName}` rewrites a bare variable, so `simp` tries it at every \
        subterm and attempts to discharge its side conditions at each match, which can \
        dominate the elaboration time of a proof.\n\
        Determine the side conditions at this use site instead, by applying the lemma to a \
        term or by fixing its implicit arguments with named arguments, as in \
        `Subsingleton.eq_zero (α := M)`."

initialize addLinter blanketSimpArgsLinter

end BlanketSimpArgs

end Mathlib.Linter
