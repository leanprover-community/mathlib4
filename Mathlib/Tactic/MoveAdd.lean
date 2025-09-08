/-
Copyright (c) 2023 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Damiano Testa
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Lean.Meta
import Mathlib.Order.Defs.LinearOrder

/-!

#  `move_add` a tactic for moving summands in expressions

The tactic `move_add` rearranges summands in expressions.

The tactic takes as input a list of terms, each one optionally preceded by `←`.
A term preceded by `←` gets moved to the left, while a term without `←` gets moved to the right.

* Empty input: `move_add []`

  In this case, the effect of `move_add []` is equivalent to `simp only [← add_assoc]`:
  essentially the tactic removes all visible parentheses.

* Singleton input: `move_add [a]` and `move_add [← a]`

  If `⊢ b + a + c` is (a summand in) the goal, then
  * `move_add [← a]` changes the goal to `a + b + c` (effectively, `a` moved to the left).
  * `move_add [a]` changes the goal to `b + c + a` (effectively, `a` moved to the right);

  The tactic reorders *all* sub-expressions of the target at the same same.
  For instance, if `⊢ 0 < if b + a < b + a + c then a + b else b + a` is the goal, then
  * `move_add [a]` changes the goal to `0 < if b + a < b + c + a then b + a else b + a`
    (`a` moved to the right in three sums);
  * `move_add [← a]` changes the goal to `0 < if a + b < a + b + c then a + b else a + b`
    (`a` again moved to the left in three sums).

* Longer inputs: `move_add [..., a, ..., ← b, ...]`

  If the list contains more than one term, the tactic effectively tries to move each term preceded
  by `←` to the left, each term not preceded by `←` to the right
  *maintaining the relative order in the call*.
  Thus, applying `move_add [a, b, c, ← d, ← e]` returns summands of the form
  `d + e + [...] + a + b + c`, i.e. `d` and `e` have the same relative position in the input list
  and in the final rearrangement (and similarly for `a, b, c`).
  In particular, `move_add [a, b]` likely has the same effect as
  `move_add [a]; move_add [b]`: first, we move `a` to the right, then we move `b` also to the
  right, *after* `a`.
  However, if the terms matched by `a` and `b` do not overlap, then `move_add [← a, ← b]`
  has the same effect as `move_add [b]; move_add [a]`:
  first, we move `b` to the left, then we move `a` also to the left, *before* `a`.
  The behaviour in the situation where `a` and `b` overlap is unspecified: `move_add`
  will descend into subexpressions, but the order in which they are visited depends
  on which rearrangements have already happened.
  Also note, though, that `move_add [a, b]` may differ `move_add [a]; move_add [b]`,
  for instance when `a` and `b` are `DefEq`.

* Unification of inputs and repetitions: `move_add [_, ← _, a * _]`

  The matching of the user inputs with the atoms of the summands in the target expression
  is performed via checking `DefEq` and selecting the first, still available match.
  Thus, if a sum in the target is `2 * 3 + 4 * (5 + 6) + 4 * 7 + 10 * 10`, then
  `move_add [4 * _]` moves the summand `4 * (5 + 6)` to the right.

  The unification of later terms only uses the atoms in the target that have not yet been unified.
  Thus, if again the target contains `2 * 3 + 4 * (5 + 6) + 4 * 7 + 10 * 10`, then
  `move_add [_, ← _, 4 * _]`
  matches
  * the first input (`_`) with `2 * 3`;
  * the second input (`_`) with `4 * (5 + 6)`;
  * the third input (`4 * _`) with `4 * 7`.

  The resulting permutation therefore places `2 * 3` and `4 * 7` to the left (in this order) and
  `4 * (5 + 6)` to the right: `2 * 3 + 4 * 7 + 10 * 10 + 4 * (5 + 6)`.

For the technical description, look at `Mathlib.MoveAdd.weight` and `Mathlib.MoveAdd.reorderUsing`.

`move_add` is the specialization of a more general `move_oper` tactic that takes a binary,
associative, commutative operation and a list of "operand atoms" and rearranges the operation.

## Extension notes

To work with a general associative, commutative binary operation, `move_oper`
needs to have inbuilt the lemmas asserting the analogues of
`add_comm, add_assoc, add_left_comm` for the new operation.
Currently, `move_oper` supports `HAdd.hAdd`, `HMul.hMul`, `And`, `Or`, `Max.max`, `Min.min`.

These lemmas should be added to `Mathlib.MoveAdd.move_oper_simpCtx`.

See `MathlibTest/MoveAdd.lean` for sample usage of `move_oper`.

## Implementation notes

The main driver behind the tactic is `Mathlib.MoveAdd.reorderAndSimp`.

The tactic takes the target, replaces the maximal subexpressions whose head symbol is the given
operation and replaces them by their reordered versions.
Once that is done, it tries to replace the initial goal with the permuted one by using `simp`.

Currently, no attempt is made at guiding `simp` by doing a `congr`-like destruction of the goal.
This will be the content of a later PR.
-/

open Lean Expr

/-- `getExprInputs e` inspects the outermost constructor of `e` and returns the array of all the
arguments to that constructor that are themselves `Expr`essions. -/
def Lean.Expr.getExprInputs : Expr → Array Expr
  | app fn arg        => #[fn, arg]
  | lam _ bt bb _     => #[bt, bb]
  | forallE _ bt bb _ => #[bt, bb]
  | letE _ t v b _    => #[t, v, b]
  | mdata _ e         => #[e]
  | proj _ _ e        => #[e]
  | _ => #[]

/-- `size e` returns the number of subexpressions of `e`. -/
@[deprecated Lean.Expr.sizeWithoutSharing (since := "2025-09-04")]
partial def Lean.Expr.size (e : Expr) : ℕ := (e.getExprInputs.map size).foldl (· + ·) 1

namespace Mathlib.MoveAdd

section ExprProcessing

section reorder
variable {α : Type*} [BEq α]

/-!
##  Reordering the variables

This section produces the permutations of the variables for `move_add`.

The user controls the final order by passing a list of terms to the tactic.
Each term can be preceded by `←` or not.
In the final ordering,
* terms preceded by `←` appear first,
* terms not preceded by `←` appear last,
* all remaining terms remain in their current relative order.
-/

/-- `uniquify L` takes a list `L : List α` as input and it returns a list `L' : List (α × ℕ)`.
The two lists `L` and `L'.map Prod.fst` coincide.
The second component of each entry `(a, n)` in `L'` is the number of times that `a` appears in `L`
before the current location.

The resulting list of pairs has no duplicates.
-/
def uniquify : List α → List (α × ℕ)
  | []    => []
  | m::ms =>
    let lms := uniquify ms
    (m, 0) :: (lms.map fun (x, n) => if x == m then (x, n + 1) else (x, n))

/-- Return a sorting key so that all `(a, true)`s are in the list's order
and sorted before all `(a, false)`s, which are also in the list's order.
Although `weight` does not require this, we use `weight` in the case where the list obtained
from `L` by only keeping the first component (i.e. `L.map Prod.fst`) has no duplicates.
The properties that we mention here assume that this is the case.

Thus, `weight L` is a function `α → ℤ` with the following properties:
* if `(a, true)  ∈ L`, then `weight L a` is strictly negative;
* if `(a, false) ∈ L`, then `weight L a` is strictly positive;
* if neither `(a, true)` nor `(a, false)` is in `L`, then `weight L a = 0`.

Moreover, the function `weight L` is strictly monotone increasing on both
`{a : α | (a, true) ∈ L}` and `{a : α | (a, false) ∈ L}`,
in the sense that if `a' = (a, true)` and `b' = (b, true)` are in `L`,
then `a'` appears before `b'` in `L` if and only if `weight L a < weight L b` and
similarly for the pairs with second coordinate equal to `false`.
-/
def weight (L : List (α × Bool)) (a : α) : ℤ :=
  let l := L.length
  match L.find? (Prod.fst · == a) with
    | some (_, b) => if b then - l + (L.idxOf (a, b) : ℤ) else (L.idxOf (a, b) + 1 : ℤ)
    | none => 0

/-- `reorderUsing toReorder instructions` produces a reordering of `toReorder : List α`,
following the requirements imposed by `instructions : List (α × Bool)`.

These are the requirements:
* elements of `toReorder` that appear with `true` in `instructions` appear at the
  *beginning* of the reordered list, in the order in which they appear in `instructions`;
* similarly, elements of `toReorder` that appear with `false` in `instructions` appear at the
  *end* of the reordered list, in the order in which they appear in `instructions`;
* finally, elements of `toReorder` that do not appear in `instructions` appear "in the middle"
  with the order that they had in `toReorder`.

For example,
* `reorderUsing [0, 1, 2] [(0, false)] = [1, 2, 0]`,
* `reorderUsing [0, 1, 2] [(1, true)] = [1, 0, 2]`,
* `reorderUsing [0, 1, 2] [(1, true), (0, false)] = [1, 2, 0]`.
-/
def reorderUsing (toReorder : List α) (instructions : List (α × Bool)) : List α :=
  let uInstructions :=
    let (as, as?) := instructions.unzip
    (uniquify as).zip as?
  let uToReorder := (uniquify toReorder).toArray
  let reorder := uToReorder.qsort fun x y =>
    match uInstructions.find? (Prod.fst · == x), uInstructions.find? (Prod.fst · == y) with
      | none, none =>
        (uToReorder.idxOf? x).get! ≤ (uToReorder.idxOf? y).get!
      | _, _ => weight uInstructions x ≤ weight uInstructions y
  (reorder.map Prod.fst).toList

end reorder

/-- `prepareOp sum` takes an `Expr`ession as input.  It assumes that `sum` is a well-formed
term representing a repeated application of a binary operation and that the summands are the
last two arguments passed to the operation.
It returns the expression consisting of the operation with all its arguments already applied,
except for the last two.
This is similar to `Lean.Meta.mkAdd, Lean.Meta.mkMul`, except that the resulting operation is
primed to work with operands of the same type as the ones already appearing in `sum`.

This is useful to rearrange the operands.
-/
def prepareOp (sum : Expr) : Expr :=
  let opargs := sum.getAppArgs
  (opargs.toList.take (opargs.size - 2)).foldl (fun x y => Expr.app x y) sum.getAppFn

/-- `sumList prepOp left_assoc? exs` assumes that `prepOp` is an `Expr`ession representing a
binary operation already fully applied up until its last two arguments and assumes that the
last two arguments are the operands of the operation.
Such an expression is the result of `prepareOp`.

If `exs` is the list `[e₁, e₂, ..., eₙ]` of `Expr`essions, then `sumList prepOp left_assoc? exs`
returns
* `prepOp (prepOp( ... prepOp (prepOp e₁ e₂) e₃) ... eₙ)`, if `left_assoc?` is `false`, and
* `prepOp e₁ (prepOp e₂ (... prepOp (prepOp eₙ₋₁  eₙ))`, if `left_assoc?` is `true`.
-/
partial
def sumList (prepOp : Expr) (left_assoc? : Bool) : List Expr → Expr
  | []    => default
  | [a]   => a
  | a::as =>
    if left_assoc? then
      Expr.app (prepOp.app a) (sumList prepOp true as)
    else
      as.foldl (fun x y => Expr.app (prepOp.app x) y) a

end ExprProcessing

open Meta

variable (op : Name)

variable (R : Expr) in
/-- If `sum` is an expression consisting of repeated applications of `op`, then `getAddends`
returns the Array of those recursively determined arguments whose type is DefEq to `R`. -/
partial def getAddends (sum : Expr) : MetaM (Array Expr) := do
  if sum.isAppOf op then
    let inR ← sum.getAppArgs.filterM fun r => do isDefEq R (← inferType r <|> pure R)
    let new ← inR.mapM (getAddends ·)
    return new.foldl Array.append  #[]
  else return #[sum]

/-- Recursively compute the Array of `getAddends` Arrays by recursing into the expression `sum`
looking for instance of the operation `op`.

Possibly returns duplicates!
-/
partial def getOps (sum : Expr) : MetaM (Array ((Array Expr) × Expr)) := do
  let summands ← getAddends op (← inferType sum <|> return sum) sum
  let (first, rest) := if summands.size == 1 then (#[], sum.getExprInputs) else
    (#[(summands, sum)], summands)
  let rest ← rest.mapM getOps
  return rest.foldl Array.append first

/-- `rankSums op tgt instructions` takes as input
* the name `op` of a binary operation,
* an `Expr`ession `tgt`,
* a list `instructions` of pair `(expression, boolean)`.

It extracts the maximal subexpressions of `tgt` whose head symbol is `op`
(i.e. the maximal subexpressions that consist only of applications of the binary operation `op`),
it rearranges the operands of such subexpressions following the order implied by `instructions`
(as in `reorderUsing`),
it returns the list of pairs of expressions `(old_sum, new_sum)`, for which `old_sum ≠ new_sum`
sorted by decreasing value of `Lean.Expr.size`.
In particular, a subexpression of an `old_sum` can only appear *after* its over-expression.
-/
def rankSums (tgt : Expr) (instructions : List (Expr × Bool)) : MetaM (List (Expr × Expr)) := do
  let sums ← getOps op (← instantiateMVars tgt)
  let candidates := sums.map fun (addends, sum) => do
    let reord := reorderUsing addends.toList instructions
    let left_assoc? := sum.getAppFn.isConstOf `And || sum.getAppFn.isConstOf `Or
    let resummed := sumList (prepareOp sum) left_assoc? reord
    if (resummed != sum) then some (sum, resummed) else none
  return (candidates.toList.reduceOption.toArray.qsort
    (fun x y : Expr × Expr ↦ (y.1.sizeWithoutSharing  ≤ x.1.sizeWithoutSharing))).toList

/-- `permuteExpr op tgt instructions` takes the same input as `rankSums` and returns the
expression obtained from `tgt` by replacing all `old_sum`s by the corresponding `new_sum`.
If there were no required changes, then `permuteExpr` reports this in its second factor. -/
def permuteExpr (tgt : Expr) (instructions : List (Expr × Bool)) : MetaM Expr := do
  let permInstructions ← rankSums op tgt instructions
  if permInstructions == [] then throwError "The goal is already in the required form"
  let mut permTgt := tgt
  -- We cannot do `Expr.replace` all at once here, we need to follow
  -- the order of the instructions.
  for (old, new) in permInstructions do
    permTgt := permTgt.replace (if · == old then new else none)
  return permTgt

/-- `pairUp L R` takes to lists `L R : List Expr` as inputs.
It scans the elements of `L`, looking for a corresponding `DefEq` `Expr`ession in `R`.
If it finds one such element `d`, then it sets the element `d : R` aside, removing it from `R`, and
it continues with the matching on the remainder of `L` and on `R.erase d`.

At the end, it returns the sublist of `R` of the elements that were matched to some element of `R`,
in the order in which they appeared in `L`,
as well as the sublist of `L` of elements that were not matched, also in the order in which they
appeared in `L`.

Example:
```lean
#eval do
  let L := [mkNatLit 0, (← mkFreshExprMVar (some (mkConst ``Nat))), mkNatLit 0] -- i.e. [0, _, 0]
  let R := [mkNatLit 0, mkNatLit 0,                                 mkNatLit 1] -- i.e. [0, 1]
  dbg_trace f!"{(← pairUp L R)}"
/- output:
`([0, 0], [0])`
the output LHS list `[0, 0]` consists of the first `0` and the `MVarId`.
the output RHS list `[0]` corresponds to the last `0` in `L`.
-/
```
-/
def pairUp : List (Expr × Bool × Syntax) → List Expr →
    MetaM ((List (Expr × Bool)) × List (Expr × Bool × Syntax))
  | (m::ms), l => do
    match ← l.findM? (isDefEq · m.1) with
      | none => let (found, unfound) ← pairUp ms l; return (found, m::unfound)
      | some d => let (found, unfound) ← pairUp ms (l.erase d)
                  return ((d, m.2.1)::found, unfound)
  | _, _ => return ([], [])

/-- `move_oper_simpCtx` is the `Simp.Context` for the reordering internal to `move_oper`.
To support a new binary operation, extend the list in this definition, so that it contains
enough lemmas to allow `simp` to close a generic permutation goal for the new binary operation.
-/
def moveOperSimpCtx : MetaM Simp.Context := do
  let simpNames := Elab.Tactic.simpOnlyBuiltins ++ [
    ``add_comm, ``add_assoc, ``add_left_comm,  -- for `HAdd.hAdd`
    ``mul_comm, ``mul_assoc, ``mul_left_comm,  -- for `HMul.hMul`
    ``and_comm, ``and_assoc, ``and_left_comm,  -- for `and`
    ``or_comm,  ``or_assoc,  ``or_left_comm,   -- for `or`
    ``max_comm, ``max_assoc, ``max_left_comm,  -- for `max`
    ``min_comm, ``min_assoc, ``min_left_comm   -- for `min`
    ]
  let simpThms ← simpNames.foldlM (·.addConst ·) ({} : SimpTheorems)
  Simp.mkContext {} (simpTheorems := #[simpThms])

/-- `reorderAndSimp mv op instr` takes as input an `MVarId`  `mv`, the name `op` of a binary
operation and a list of "instructions" `instr` that it passes to `permuteExpr`.

* It creates a version `permuted_mv` of `mv` with subexpressions representing `op`-sums reordered
  following `instructions`.
* It produces 2 temporary goals by applying `Eq.mpr` and unifying the resulting meta-variable with
  `permuted_mv`: `[⊢ mv = permuted_mv, ⊢ permuted_mv]`.
* It tries to solve the goal `mv = permuted_mv` by a simple-minded `simp` call, using the
  `op`-analogues of `add_comm, add_assoc, add_left_comm`.
-/
def reorderAndSimp (mv : MVarId) (instr : List (Expr × Bool)) :
    MetaM (List MVarId) := mv.withContext do
  let permExpr ← permuteExpr op (← mv.getType'') instr
  -- generate the implication `permutedMv → mv = permutedMv → mv`
  let eqmpr ← mkAppM ``Eq.mpr #[← mkFreshExprMVar (← mkEq (← mv.getType) permExpr)]
  let twoGoals ← mv.apply eqmpr
  guard (twoGoals.length == 2) <|>
    throwError m!"There should only be 2 goals, instead of {twoGoals.length}"
  -- `permGoal` is the single goal `mv_permuted`, possibly more operations will be permuted later on
  let permGoal ← twoGoals.filterM fun v => return !(← v.isAssigned)
  match ← (simpGoal (permGoal[1]!) (← moveOperSimpCtx)) with
    | (some x, _) => throwError m!"'move_oper' could not solve {indentD x.2}"
    | (none, _) => return permGoal

/-- `unifyMovements` takes as input
* an array of `Expr × Bool × Syntax`, as in the output of `parseArrows`,
* the `Name` `op` of a binary operation,
* an `Expr`ession `tgt`.
It unifies each `Expr`ession appearing as a first factor of the array with the atoms
for the operation `op` in the expression `tgt`, returning
* the lists of pairs of a matched subexpression with the corresponding `Bool`ean;
* a pair of a list of error messages and the corresponding list of Syntax terms where the error
  should be thrown;
* an array of debugging messages.
-/
def unifyMovements (data : Array (Expr × Bool × Syntax)) (tgt : Expr) :
    MetaM (List (Expr × Bool) × (List MessageData × List Syntax) × Array MessageData) := do
  let ops ← getOps op tgt
  let atoms := (ops.map Prod.fst).flatten.toList.filter (!isBVar ·)
  -- `instr` are the unified user-provided terms, `neverMatched` are non-unified ones
  let (instr, neverMatched) ← pairUp data.toList atoms
  let dbgMsg := #[m!"Matching of input variables:\n\
    * pre-match:  {data.map (Prod.snd ∘ Prod.snd)}\n\
    * post-match: {instr}",
    m!"\nMaximum number of iterations: {ops.size}"]
  -- if there are `neverMatched` terms, return the parsed terms and the syntax
  let errMsg := neverMatched.map fun (t, a, stx) => (if a then m!"← {t}" else m!"{t}", stx)
  return (instr, errMsg.unzip, dbgMsg)

section parsing
open Elab Parser Tactic

/-- `parseArrows` parses an input of the form `[a, ← b, _ * (1 : ℤ)]`, consisting of a list of
terms, each optionally preceded by the arrow `←`.
It returns an array of triples consisting of
* the `Expr`ession corresponding to the parsed term,
* the `Bool`ean `true` if the arrow is present in front of the term,
* the underlying `Syntax` of the given term.

E.g. convert `[a, ← b, _ * (1 : ℤ)]` to
``[(a, false, `(a)), (b, true, `(b)), (_ * 1, false, `(_ * 1))]``.
-/
def parseArrows : TSyntax `Lean.Parser.Tactic.rwRuleSeq → TermElabM (Array (Expr × Bool × Syntax))
  | `(rwRuleSeq| [$rs,*]) => do
    rs.getElems.mapM fun rstx => do
      let r : Syntax := rstx
      return (← Term.elabTerm r[1]! none, ! r[0]!.isNone, rstx)
  | _ => failure

initialize registerTraceClass `Tactic.move_oper

/-- The tactic `move_add` rearranges summands of expressions.
Calling `move_add [a, ← b, ...]` matches `a, b,...` with summands in the main goal.
It then moves `a` to the far right and `b` to the far left of each addition in which they appear.
The side to which the summands are moved is determined by the presence or absence of the arrow `←`.

The inputs `a, b,...` can be any terms, also with underscores.
The tactic uses the first "new" summand that unifies with each one of the given inputs.

There is a multiplicative variant, called `move_mul`.

There is also a general tactic for a "binary associative commutative operation": `move_oper`.
In this case the syntax requires providing first a term whose head symbol is the operation.
E.g. `move_oper HAdd.hAdd [...]` is the same as `move_add`, while `move_oper Max.max [...]`
rearranges `max`s.
-/
elab (name := moveOperTac) "move_oper" id:ident rws:rwRuleSeq : tactic => withMainContext do
  -- parse the operation
  let op := id.getId
  -- parse the list of terms
  let (instr, (unmatched, stxs), dbgMsg) ← unifyMovements op (← parseArrows rws)
                                                              (← instantiateMVars (← getMainTarget))
  unless unmatched.length = 0 do
    let _ ← stxs.mapM (logErrorAt · "") -- underline all non-matching terms
    trace[Tactic.move_oper] dbgMsg.foldl (fun x y => (x.compose y).compose "\n\n---\n") ""
    throwErrorAt stxs[0]! m!"Errors:\nThe terms in '{unmatched}' were not matched to any atom"
  -- move around the operands
  replaceMainGoal (← reorderAndSimp op (← getMainGoal) instr)

@[inherit_doc moveOperTac]
elab "move_add" rws:rwRuleSeq : tactic => do
  let hadd := mkIdent ``HAdd.hAdd
  evalTactic (← `(tactic| move_oper $hadd $rws))

@[inherit_doc moveOperTac]
elab "move_mul" rws:rwRuleSeq : tactic => do
  let hmul := mkIdent ``HMul.hMul
  evalTactic (← `(tactic| move_oper $hmul $rws))

end parsing

end MoveAdd

end Mathlib
