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
syntax:lead (name := Parser.Tactic.introNoMatch) "intro" "." : tactic

namespace Elab.Term

open private elabMatchCore in elabMatch.elabMatchDefault in
open private elabMatchAux waitExpectedTypeAndDiscrs in elabMatchCore in
@[termElab Parser.Term.noMatch] def elabNoMatch' : TermElab
| stx@`(match $discrs,* with.), expectedType? => do
  let discrs := discrs.getElems
  if let some i ← discrs.findIdxM? fun discr =>
      return (← isAtomicDiscr? discr).isNone then
    let discr := discrs[i][1]
    let discrs := discrs.set! i (← `(x))
    return ← elabTerm (← `(let x := $discr; match $discrs,* with.)) expectedType?
  let expectedType ← waitExpectedTypeAndDiscrs stx expectedType?
  elabMatchAux none discrs #[] mkNullNode expectedType
| _, _ => throwUnsupportedSyntax

elab tk:"fun" "." : term <= expectedType =>
  Meta.forallTelescopeReducing expectedType fun args _ => do
    let mut discrs := #[]
    let mut binders := #[]
    for _ in args do
      let n ← mkFreshIdent tk
      binders := binders.push n
      discrs := discrs.push $
        mkNode ``Lean.Parser.Term.matchDiscr #[mkNullNode, n]
    elabTerm (← `(@fun $binders* => match $discrs,* with.)) (some expectedType)

macro tk:"λ" "." : term => `(fun%$tk .)

end Elab.Term

macro "match " discrs:matchDiscr,* " with" "." : tactic =>
  `(tactic| exact match $discrs,* with.)

macro "intro" "." : tactic => `(tactic| exact fun.)

end Lean
