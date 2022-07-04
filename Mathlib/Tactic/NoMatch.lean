/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import Mathlib.Tactic.OpenPrivate
import Lean

/-
This adds support for the alternative syntax `match x with.` instead of `nomatch x`. It is more
powerful because it supports pattern matching on multiple discriminants, like regular `match`, and
simply has no alternatives in the match.

Along the same lines, `fun.` is a nullary pattern matching function; it is equivalent to
`fun x y z => match x, y, z with.` where all variables are introduced in order to find an
impossible pattern. The `match x with.` and `intro.` tactics do the same thing but in tactic mode.
-/
namespace Lean

syntax:lead (name := Parser.Term.noMatch) "match " matchDiscr,* " with" "." : term

namespace Elab.Term

open private elabMatchAux waitExpectedType from Lean.Elab.Match in
@[termElab Parser.Term.noMatch] def elabNoMatch' : TermElab
| `(match $discrs,* with.), expectedType? => do
  let discrs := discrs.getElems
  for h : i in [0:discrs.size] do
    let i := ⟨i, (h : _ ∧ _).2⟩
    let `(matchDiscr| $[$n :]? $discr:term) := discrs[i] | throwUnsupportedSyntax
    if let some x ← isAtomicDiscr? discr then
      tryPostponeIfMVar (← Meta.inferType x)
    else
      let discrs := discrs.set i (← `(matchDiscr| $[$n :]? x))
      return ← elabTerm (← `(let x := $discr; match $discrs,* with.)) expectedType?
  let expectedType ← waitExpectedType expectedType?
  elabMatchAux none discrs #[] mkNullNode expectedType
| _, _ => throwUnsupportedSyntax

elab tk:"fun" "." : term <= expectedType => do
  let (binders, discrs) ← (·.unzip) <$>
    Meta.forallTelescopeReducing expectedType fun args _ =>
      args.mapM fun _ => withFreshMacroScope do
        return ((⟨← `(a)⟩ : Ident), ← `(matchDiscr| a))
  elabTerm (← `(@fun%$tk $binders:ident* => match%$tk $discrs:matchDiscr,* with.)) expectedType

macro tk:"λ" "." : term => `(fun%$tk .)

end Elab.Term

macro "match " discrs:matchDiscr,* " with" "." : tactic =>
  `(tactic| exact match $discrs,* with.)

macro "intro" "." : tactic => `(tactic| exact fun.)

end Lean
