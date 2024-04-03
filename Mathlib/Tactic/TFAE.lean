/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Reid Barton, Simon Hudon, Thomas Murrills, Mario Carneiro
-/
import Qq
import Mathlib.Init.Data.Nat.Notation
import Mathlib.Util.AtomM
import Mathlib.Data.List.TFAE
import Mathlib.Tactic.Have

/-!
# The Following Are Equivalent (TFAE)

This file provides the tactics `tfae`, `tfae_have`, and `tfae_finish` for proving goals of the form
`TFAE [P₁, P₂, ...]`.

The `tfae` block tactic is now preferred, but `tfae_have` and `tfae_finish` are still supported for
implementation purposes and backwards compatibility.

Example:
```lean
  tfae
    1 → 2 := /- proof of `P₁ → P₂` -/
    2 → 3 := /- proof of `P₂ → P₃` -/
    3 → 1 := /- proof of `P₃ → P₁` -/
```
See the dosctring for `tfae` for more information.
-/

namespace Mathlib.Tactic.TFAE

/-! # Parsing and syntax -/

open Lean.Parser Term

namespace Parser

/- An arrow of the form `←`, `→`, or `↔`. -/
private def impTo : Parser := leading_parser unicodeSymbol " → " " -> "
private def impFrom : Parser := leading_parser unicodeSymbol " ← " " <- "
private def impIff : Parser := leading_parser unicodeSymbol " ↔ " " <-> "
private def impArrow : Parser := leading_parser impTo <|> impFrom <|> impIff

/-- A `tfae` type specification, e.g. `1 ↔ 3`. The numbers refer to the proposition at the
corresponding position in the `TFAE` goal (starting at 1). -/
private def tfaeType := leading_parser num >> impArrow >> num

/-!

## 'Old-style' `tfae` (`tfae_have` and `tfae_finish`)

Although the `tfae` block tactic is now preferred (see below), we preserve the following parsers
for backwards compatibility and implementation.

We implement `tfae_have` in terms of a syntactic `have`. To support as much of the same syntax as
possible, we recreate the parsers for `have`, except with the changes necessary for `tfae_have`.
The following parsers are similar to those for `have` in `Lean.Parser.Term`, but
instead of `optType`, we use `tfaeType := num >> impArrow >> num` (as a `tfae_have` invocation must
always include this specification). Also, we disallow including extra binders, as that makes no
sense in this context; we also include `" : "` after the binder to avoid breaking `tfae_have 1 → 2`
syntax (which, unlike `have`, omits `" : "`).
-/

/- See `haveIdLhs`.

We omit `many (ppSpace >> letIdBinder)`, as it makes no sense to add extra arguments to a
`tfae_have` decl.  -/
private def tfaeHaveIdLhs := leading_parser
  ((ppSpace >> binderIdent >> " : ") <|> hygieneInfo)  >> tfaeType
/- See `haveIdDecl`. E.g. `h : 1 → 3 := term`. -/
private def tfaeHaveIdDecl   := leading_parser (withAnonymousAntiquot := false)
  atomic (tfaeHaveIdLhs >> " := ") >> termParser
/- See `haveEqnsDecl`. E.g. `h : 1 → 3 | p => f p`. -/
private def tfaeHaveEqnsDecl := leading_parser (withAnonymousAntiquot := false)
  tfaeHaveIdLhs >> matchAlts
/- See `letPatDecl`. E.g. `⟨mp, mpr⟩ : 1 ↔ 3 := term`. -/
private def tfaeHavePatDecl  := leading_parser (withAnonymousAntiquot := false)
  atomic (termParser >> pushNone >> " : " >> tfaeType >> " := ") >> termParser
/- See `haveDecl`. Any of `tfaeHaveIdDecl`, `tfaeHavePatDecl`, or `tfaeHaveEqnsDecl`. -/
private def tfaeHaveDecl     := leading_parser (withAnonymousAntiquot := false)
  tfaeHaveIdDecl <|> (ppSpace >> tfaeHavePatDecl) <|> tfaeHaveEqnsDecl

end Parser

open Parser

/--
NOTE: The `tfae` block tactic is now preferred in place of `tfae_have` and `tfae_finish`, e.g.
```lean
  tfae
    1 → 2 := /- proof of `P₁ → P₂` -/
    2 → 3 := /- proof of `P₂ → P₃` -/
    3 → 1 := /- proof of `P₃ → P₁` -/
```

See `tfae`.

---

`tfae_have` introduces hypotheses for proving goals of the form `TFAE [P₁, P₂, ...]`. Specifically,
`tfae_have i <arrow> j := ...` introduces a hypothesis of type `Pᵢ <arrow> Pⱼ` to the local
context, where `<arrow>` can be `→`, `←`, or `↔`. Note that `i` and `j` are natural number indices
(beginning at 1) used to specify the propositions `P₁, P₂, ...` that appear in the goal.

```lean
example (h : P → R) : TFAE [P, Q, R] := by
  tfae_have 1 → 3 := h
  ...
```
The resulting context now includes `tfae_1_to_3 : P → R`.

Once sufficient hypotheses have been introduced by `tfae_have`, `tfae_finish` can be used to close
the goal. For example,

```lean
example : TFAE [P, Q, R] := by
  tfae_have 1 → 2 := sorry /- proof of P → Q -/
  tfae_have 2 → 1 := sorry /- proof of Q → P -/
  tfae_have 2 ↔ 3 := sorry /- proof of Q ↔ R -/
  tfae_finish
```

All relevant features of `have` are supported by `tfae_have`, including naming, destructuring, goal
creation, and matching. These are demonstrated below.

```lean
example : TFAE [P, Q] := by
  -- `tfae_1_to_2 : P → Q`:
  tfae_have 1 → 2 := sorry
  -- `hpq : P → Q`:
  tfae_have hpq : 1 → 2 := sorry
  -- inaccessible `h✝ : P → Q`:
  tfae_have _ : 1 → 2 := sorry
  -- `tfae_1_to_2 : P → Q`, and `?a` is a new goal:
  tfae_have 1 → 2 := f ?a
  -- create a goal of type `P → Q`:
  tfae_have 1 → 2
  · exact (sorry : P → Q)
  -- match on `p : P` and prove `Q`:
  tfae_have 1 → 2
  | p => f p
  -- introduces `pq : P → Q`, `qp : Q → P`:
  tfae_have ⟨pq, qp⟩ : 1 ↔ 2 := sorry
  ...
```
-/
syntax (name := tfaeHave) "tfae_have " tfaeHaveDecl : tactic

@[inherit_doc tfaeHave]
syntax (name := tfaeHave') "tfae_have " tfaeHaveIdLhs : tactic

/--
NOTE: The `tfae` block tactic is now preferred in place of `tfae_have` and `tfae_finish`, e.g.
```lean
  tfae
    1 → 2 := /- proof of `P₁ → P₂` -/
    2 → 3 := /- proof of `P₂ → P₃` -/
    3 → 1 := /- proof of `P₃ → P₁` -/
```

See `tfae`.

---

`tfae_finish` is used to close goals of the form `TFAE [P₁, P₂, ...]` once a sufficient collection
of hypotheses of the form `Pᵢ → Pⱼ` or `Pᵢ ↔ Pⱼ` have been introduced to the local context.

`tfae_have` can be used to conveniently introduce these hypotheses; see `tfae_have`.

Example:
```lean
example : TFAE [P, Q, R] := by
  tfae_have 1 → 2 := sorry /- proof of P → Q -/
  tfae_have 2 → 1 := sorry /- proof of Q → P -/
  tfae_have 2 ↔ 3 := sorry /- proof of Q ↔ R -/
  tfae_finish
```
-/
syntax (name := tfaeFinish) "tfae_finish" : tactic

/-!

## The `tfae` block tactic

The following currently relies on the 'old-style' parsers for implementation.

`tfaeFields` parses e.g.
```
  1 → 2 := sorry
  2 → 3 := sorry
  ...
```
(including other variations of the `tfaeHaveDecl`) and is patterned loosely off of the
`structFields` parser used for declaring structures.
-/

private def tfaeFields := leading_parser manyIndent <| ppLine >> checkColGe >> ppGroup tfaeHaveDecl

/-- The `tfae` tactic is used for proving goals of the form `TFAE [P₁, P₂, ...]`. For example,
given a goal `TFAE [P₁, P₂, P₃]`, we can prove it with
```lean
  tfae
    1 → 2 := /- proof of `P₁ → P₂` -/
    2 → 3 := /- proof of `P₂ → P₃` -/
    3 → 1 := /- proof of `P₃ → P₁` -/
```
In `i → j := ...`, `i` and `j` are natural-number indices which refer to the proposition at the
corresponding position in the `TFAE` goal list, starting at `1` (not `0`).

Both `→` and `↔` can be used to specify subgoals, e.g. ```lean 2 ↔ 3 := /- proof of `P₂ ↔ P₃`-/``.
(`i ← j` can also be used as shorthand for `j → i`.)

`match`-style alternatives can also be used to prove an implication as usual, e.g.
```lean
  tfae
    1 → 2 := ...
    2 → 3
    | h₂ => /- proof of `P₃` -/
    3 → 1 -- given `P₁ := ∀(a : A), (b : B), (c : C), X`:
    | h₃, a, b, c => /- proof of `X` -/
```

Once e.g. `2 → 3` has been proved, it appears in the local context during proofs of subsequent
implications as `tfae_2_to_3 : P₂ → P₃`. If desired, a custom name can be given using the syntax
`h : 2 → 3 := ...` Patterns can also be used here to introduce `Iff` fields individually, e.g.
`⟨h_mp, h_mpr⟩ : 5 ↔ 6 := ...`.
-/
syntax (name := tfaeBlock) "tfae" tfaeFields : tactic


/-! # Setup -/

open List Lean Meta Expr Elab Tactic Mathlib.Tactic Qq

/-- Extract a list of `Prop` expressions from an expression of the form `TFAE [P₁, P₂, ...]` as
long as `[P₁, P₂, ...]` is an explicit list. -/
partial def getTFAEList (t : Expr) : MetaM (Q(List Prop) × List Q(Prop)) := do
  let .app tfae (l : Q(List Prop)) ← whnfR <|← instantiateMVars t
    | throwError "goal must be of the form TFAE [P₁, P₂, ...]"
  unless (← withNewMCtxDepth <| isDefEq tfae q(TFAE)) do
    throwError "goal must be of the form TFAE [P₁, P₂, ...]"
  return (l, ← getExplicitList l)
where
  /-- Convert an expression representing an explicit list into a list of expressions. -/
  getExplicitList (l : Q(List Prop)) : MetaM (List Q(Prop)) := do
    match l with
    | ~q([]) => return ([] : List Expr)
    | ~q($a :: $l') => return (a :: (← getExplicitList l'))
    | e => throwError "{e} must be an explicit list of propositions"

/-! # Proof construction -/

variable (hyps : Array (ℕ × ℕ × Expr)) (atoms : Array Q(Prop))

/-- Uses depth-first search to find a path from `P` to `P'`. -/
partial def dfs (i j : ℕ) (P P' : Q(Prop)) (hP : Q($P)) : StateT (HashSet ℕ) MetaM Q($P') := do
  if i == j then
    return hP
  modify (·.insert i)
  for (a, b, h) in hyps do
    if i == a then
      if !(← get).contains b then
        have Q := atoms[b]!
        have h : Q($P → $Q) := h
        try return ← dfs b j Q P' q($h $hP) catch _ => pure ()
  failure

/-- Prove an implication via depth-first traversal. -/
def proveImpl (i j : ℕ) (P P' : Q(Prop)) : MetaM Q($P → $P') := do
  try
    withLocalDeclD (← mkFreshUserName `h) P fun (h : Q($P)) => do
      mkLambdaFVars #[h] <|← dfs hyps atoms i j P P' h |>.run' {}
  catch _ =>
    throwError "couldn't prove {P} → {P'}"

/-- Generate a proof of `Chain (· → ·) P l`. We assume `P : Prop` and `l : List Prop`, and that `l`
is an explicit list. -/
partial def proveChain (i : ℕ) (is : List ℕ) (P : Q(Prop)) (l : Q(List Prop)) :
    MetaM Q(Chain (· → ·) $P $l) := do
  match l with
  | ~q([]) => return q(Chain.nil)
  | ~q($P' :: $l') =>
    -- `id` is a workaround for https://github.com/leanprover-community/quote4/issues/30
    let i' :: is' := id is | unreachable!
    have cl' : Q(Chain (· → ·) $P' $l') := ← proveChain i' is' q($P') q($l')
    let p ← proveImpl hyps atoms i i' P P'
    return q(Chain.cons $p $cl')

/-- Attempt to prove `getLastD l P' → P` given an explicit list `l`. -/
partial def proveGetLastDImpl (i i' : ℕ) (is : List ℕ) (P P' : Q(Prop)) (l : Q(List Prop)) :
    MetaM Q(getLastD $l $P' → $P) := do
  match l with
  | ~q([]) => proveImpl hyps atoms i' i P' P
  | ~q($P'' :: $l') =>
    -- `id` is a workaround for https://github.com/leanprover-community/quote4/issues/30
    let i'' :: is' := id is | unreachable!
    proveGetLastDImpl i i'' is' P P'' l'

/-- Attempt to prove a statement of the form `TFAE [P₁, P₂, ...]`. -/
def proveTFAE (is : List ℕ) (l : Q(List Prop)) : MetaM Q(TFAE $l) := do
  match l with
  | ~q([]) => return q(tfae_nil)
  | ~q([$P]) => return q(tfae_singleton $P)
  | ~q($P :: $P' :: $l') =>
    -- `id` is a workaround for https://github.com/leanprover-community/quote4/issues/30
    let i :: i' :: is' := id is | unreachable!
    let c ← proveChain hyps atoms i (i'::is') P q($P' :: $l')
    let il ← proveGetLastDImpl hyps atoms i i' is' P P' l'
    return q(tfae_of_cycle $c $il)

/-! # `tfae_have` components -/

/-- Construct a name for a hypothesis introduced by `tfae_have`. -/
def mkTFAEId : TSyntax ``tfaeType → MacroM Name
  | `(tfaeType|$i:num $arr:impArrow $j:num) => do
    let arr ← match arr with
    | `(impArrow| ← ) => pure "from"
    | `(impArrow| → ) => pure "to"
    | `(impArrow| ↔ ) => pure "iff"
    | _ => Macro.throwUnsupported
    return .mkSimple <| String.intercalate "_" ["tfae", s!"{i.getNat}", arr, s!"{j.getNat}"]
  | _ => Macro.throwUnsupported

/-- Turn syntax for a given index into a natural number, as long as it lies between `1` and
`maxIndex`. -/
def elabIndex (i : TSyntax `num) (maxIndex : ℕ) : MetaM ℕ := do
  let i' := i.getNat
  unless 1 ≤ i' && i' ≤ maxIndex do
    throwErrorAt i "{i} must be between 1 and {maxIndex}"
  return i'

/-! # Tactic implementation -/

/-- Accesses the propositions at indices `i` and `j` of `tfaeList`, and constructs the expression
`Pi <arr> Pj`, which will be the type of our `tfae_have` hypothesis -/
def elabTFAEType (tfaeList : List Q(Prop)) : TSyntax ``tfaeType → TermElabM Expr
  | stx@`(tfaeType|$i:num $arr:impArrow $j:num) => do
    let l := tfaeList.length
    let i' ← elabIndex i l
    let j' ← elabIndex j l
    let Pi := tfaeList.get! (i'-1)
    let Pj := tfaeList.get! (j'-1)
    Term.addTermInfo' i Pi q(Prop)
    Term.addTermInfo' j Pj q(Prop)
    match arr with
    | `(impArrow| ← ) => Term.addTermInfo stx q($Pj → $Pi) q(Prop)
    | `(impArrow| → ) => Term.addTermInfo stx q($Pi → $Pj) q(Prop)
    | `(impArrow| ↔ ) => Term.addTermInfo stx q($Pi ↔ $Pj) q(Prop)
    | _ => throwUnsupportedSyntax
  | _ => throwUnsupportedSyntax

/-! ## `tfae_have` -/

/- Convert `tfae_have i <arr> j ...` to `tfae_have tfae_i_arr_j : i <arr> j ...`. See
`expandHave`, which is responsible for inserting `this` in `have : A := ...`. Note that we
require some extra help for `tfaeHave'` (Mathlib `have`). -/
macro_rules
| `(tfaeHave|tfae_have $hy:hygieneInfo $t:tfaeType := $val) => do
  let id := HygieneInfo.mkIdent hy (← mkTFAEId t) (canonical := true)
  `(tfaeHave|tfae_have $id : $t := $val)
| `(tfaeHave|tfae_have $hy:hygieneInfo $t:tfaeType $alts:matchAlts) => do
  let id := HygieneInfo.mkIdent hy (← mkTFAEId t) (canonical := true)
  `(tfaeHave|tfae_have $id : $t $alts)

-- Mathlib `have`
| `(tfaeHave'|tfae_have $hy:hygieneInfo $t:tfaeType) => do
  let id := HygieneInfo.mkIdent hy (← mkTFAEId t) (canonical := true)
  `(tfaeHave'|tfae_have $id : $t)

elab_rules : tactic
| `(tfaeHave|tfae_have $d:tfaeHaveDecl) => withMainContext do
  let goal ← getMainGoal
  let (_, tfaeList) ← getTFAEList (← goal.getType)
  withRef d do
    match d with
    | `(tfaeHaveDecl| $b : $t:tfaeType := $pf:term) =>
      let type ← elabTFAEType tfaeList t
      evalTactic <|← `(tactic|have $b : $(← type.toSyntax) := $pf)
    | `(tfaeHaveDecl| $b : $t:tfaeType $alts:matchAlts) =>
      let type ← elabTFAEType tfaeList t
      evalTactic <|← `(tactic|have $b : $(← type.toSyntax) $alts:matchAlts)
    | `(tfaeHaveDecl| $pat:term : $t:tfaeType := $pf:term) =>
      let type ← elabTFAEType tfaeList t
      evalTactic <|← `(tactic|have $pat:term : $(← type.toSyntax) := $pf)
    | _ => throwUnsupportedSyntax

-- Mathlib `have`
| `(tfaeHave'|tfae_have $d:tfaeHaveIdLhs) => withMainContext do
  let goal ← getMainGoal
  let (_, tfaeList) ← getTFAEList (← goal.getType)
  match d with
  | `(tfaeHaveIdLhs| $b:ident : $t:tfaeType) =>
    let type ← elabTFAEType tfaeList t
    evalTactic <|← `(tactic|have $b:ident : $(← type.toSyntax))
  | _ => throwUnsupportedSyntax

/-! ## `tfae_finish` -/

elab_rules : tactic
| `(tactic| tfae_finish) => do
  let goal ← getMainGoal
  goal.withContext do
    let (tfaeListQ, tfaeList) ← getTFAEList (← goal.getType)
    closeMainGoal <|← AtomM.run .reducible do
      let is ← tfaeList.mapM AtomM.addAtom
      let mut hyps := #[]
      for hyp in ← getLocalHyps do
        let ty ← whnfR <|← instantiateMVars <|← inferType hyp
        if let (``Iff, #[p1, p2]) := ty.getAppFnArgs then
          let q1 ← AtomM.addAtom p1
          let q2 ← AtomM.addAtom p2
          hyps := hyps.push (q1, q2, ← mkAppM ``Iff.mp #[hyp])
          hyps := hyps.push (q2, q1, ← mkAppM ``Iff.mpr #[hyp])
        else if ty.isArrow then
          let q1 ← AtomM.addAtom ty.bindingDomain!
          let q2 ← AtomM.addAtom ty.bindingBody!
          hyps := hyps.push (q1, q2, hyp)
      proveTFAE hyps (← get).atoms is tfaeListQ

/-! ## `tfae` block tactic

This is currently implemented simply in terms of `tfae_have` and `tfae_finish`.

TODO: prevent `tfae_have` from being able to introduce new subgoals. Since `tfae_have` is defined
in terms of `have`, we're allowed to write e.g. `1 → 2 := f ?a`, which will introduce `?a` as a
subgoal.

TODO: eliminate `tfae_finish` and take advantage of the nature of the block tactic. `tfae_finish`
currently looks through the entire local context for implications, since it can't communicate
directly with prior uses of `tfae_have`. However, since we have all of the indices available to the
block tactic at once (and links between them), we can:
1. figure out the structure of the proof term more efficiently
2. (automatic from `1`) make sure all necessary implications are specified explicitly as fields.
Currently an implication in the local context not introduced by `tfae` could be used by
`tfae_finish`, which hampers readability. Although this doesn't happen in practice.
3. alert the user to unused fields (currently we wait on the "unused `have`" linter in CI)

-/

elab_rules : tactic
| `(tactic|tfae $[$ts:tfaeHaveDecl]*) => do
  for t in ts do
    evalTactic <|← withRef t `(tactic|tfae_have $t:tfaeHaveDecl)
  evalTactic <|← `(tactic|tfae_finish)
