/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
import Mathlib.Tactic.Linarith.Datatypes
import Mathlib.Tactic.Zify
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Control.Basic
import Mathlib.Util.AtomM

/-!
# Linarith preprocessing

This file contains methods used to preprocess inputs to `linarith`.

In particular, `linarith` works over comparisons of the form `t R 0`, where `R ∈ {<,≤,=}`.
It assumes that expressions in `t` have integer coefficients and that the type of `t` has
well-behaved subtraction.

## Implementation details

A `GlobalPreprocessor` is a function `List Expr → TacticM (List Expr)`. Users can add custom
preprocessing steps by adding them to the `LinarithConfig` object. `Linarith.defaultPreprocessors`
is the main list, and generally none of these should be skipped unless you know what you're doing.
-/

namespace Mathlib.Tactic.Linarith

/-! ### Preprocessing -/

open Lean
open Elab Tactic Meta
open Qq
open Std (TreeSet)

/-- Processor that recursively replaces `P ∧ Q` hypotheses with the pair `P` and `Q`. -/
partial def splitConjunctions : Preprocessor where
  description := "split conjunctions"
  transform := aux
where
  /-- Implementation of the `splitConjunctions` preprocessor. -/
  aux (proof : Expr) : MetaM (List Expr) := do
    match (← instantiateMVars (← inferType proof)).getAppFnArgs with
    | (``And, #[_, _]) =>
      pure ((← aux (← mkAppM ``And.left #[proof])) ++
        (← aux (← mkAppM ``And.right #[proof])))
    | _ => pure [proof]

/--
Removes any expressions that are not proofs of inequalities, equalities, or negations thereof.
-/
partial def filterComparisons : Preprocessor where
  description := "filter terms that are not proofs of comparisons"
  transform h := do
    let tp ← instantiateMVars (← inferType h)
    try
      let (b, rel, _) ← tp.ineqOrNotIneq?
      if b || rel != Ineq.eq then pure [h] else pure []
    catch _ => pure []

section removeNegations

/--
If `prf` is a proof of `¬ e`, where `e` is a comparison,
`flipNegatedComparison prf e` flips the comparison in `e` and returns a proof.
For example, if `prf : ¬ a < b`, ``flipNegatedComparison prf q(a < b)`` returns a proof of `a ≥ b`.
-/
def flipNegatedComparison (prf : Expr) (e : Expr) : MetaM (Option Expr) :=
  match e.getAppFnArgs with
  | (``LE.le, #[_, _, _, _]) => try? <| mkAppM ``lt_of_not_ge #[prf]
  | (``LT.lt, #[_, _, _, _]) => try? <| mkAppM ``le_of_not_gt #[prf]
  | _ => throwError "Not a comparison (flipNegatedComparison): {e}"

/--
Replaces proofs of negations of comparisons with proofs of the reversed comparisons.
For example, a proof of `¬ a < b` will become a proof of `a ≥ b`.
-/
def removeNegations : Preprocessor where
  description := "replace negations of comparisons"
  transform h := do
    let t : Q(Prop) ← whnfR (← inferType h)
    match t with
    | ~q(¬ $p) =>
      match ← flipNegatedComparison h (← whnfR p) with
      | some h' =>
        trace[linarith] "removing negation in {h}"
        return [h']
      | _ => return [h]
    | _ => return [h]

end removeNegations

section natToInt

open Zify

/--
`isNatProp tp` is true iff `tp` is an inequality or equality between natural numbers
or the negation thereof.
-/
partial def isNatProp (e : Expr) : MetaM Bool := succeeds <| do
  let (_, _, .const ``Nat [], _, _) ← e.ineqOrNotIneq? | failure

/-- If `e` is of the form `((n : ℕ) : C)`, `isNatCoe e` returns `⟨n, C⟩`. -/
def isNatCoe (e : Expr) : Option (Expr × Expr) :=
  match e.getAppFnArgs with
  | (``Nat.cast, #[target, _, n]) => some ⟨n, target⟩
  | _ => none

/--
`getNatComparisons e` returns a list of all subexpressions of `e` of the form `((t : ℕ) : C)`.
-/
partial def getNatComparisons (e : Expr) : List (Expr × Expr) :=
  match isNatCoe e with
  | some x => [x]
  | none => match e.getAppFnArgs with
    | (``HAdd.hAdd, #[_, _, _, _, a, b]) => getNatComparisons a ++ getNatComparisons b
    | (``HMul.hMul, #[_, _, _, _, a, b]) => getNatComparisons a ++ getNatComparisons b
    | (``HSub.hSub, #[_, _, _, _, a, b]) => getNatComparisons a ++ getNatComparisons b
    | (``Neg.neg, #[_, _, a]) => getNatComparisons a
    | _ => []

/-- If `e : ℕ`, returns a proof of `0 ≤ (e : C)`. -/
def mk_natCast_nonneg_prf (p : Expr × Expr) : MetaM (Option Expr) :=
  match p with
  | ⟨e, target⟩ => try commitIfNoEx (mkAppM ``natCast_nonneg #[target, e])
    catch e => do
      trace[linarith] "Got exception when using cast {e.toMessageData}"
      return none

/-- Ordering on `Expr`. -/
@[deprecated
  "Use `Expr.lt` and `Expr.equal` or `Expr.eqv` directly. \
  If you need to order expressions, consider ordering them by order seen, with AtomM."
  (since := "2025-08-31")]
def Expr.Ord : Ord Expr :=
⟨fun a b => if Expr.lt a b then .lt else if a.equal b then .eq else .gt⟩

/--
If `h` is an equality or inequality between natural numbers,
`natToInt` lifts this inequality to the integers.
It also adds the facts that the integers involved are nonnegative.
To avoid adding the same nonnegativity facts many times, it is a global preprocessor.
-/
def natToInt : GlobalBranchingPreprocessor where
  description := "move nats to ints"
  transform g l := do
    let l ← l.mapM fun h => do
      let t ← whnfR (← instantiateMVars (← inferType h))
      if ← isNatProp t then
        let (some (h', t'), _) ← Term.TermElabM.run' (run_for g (zifyProof none h t))
          | throwError "zifyProof failed on {h}"
        if ← succeeds t'.ineqOrNotIneq? then
          pure h'
        else
          -- `zifyProof` turned our comparison into something that wasn't a comparison
          -- probably replacing `n = n` with `True`, because of
          -- https://github.com/leanprover-community/mathlib4/issues/741
          -- so we just keep the original hypothesis.
          pure h
      else
        pure h
    withNewMCtxDepth <| AtomM.run .reducible <| do
    let nonnegs ← l.foldlM (init := ∅) fun (es : TreeSet (Nat × Nat) lexOrd.compare) h => do
      try
        let (_, _, a, b) ← (← inferType h).ineq?
        let getIndices (p : Expr × Expr) : AtomM (ℕ × ℕ) := do
          return ((← AtomM.addAtom p.1).1, (← AtomM.addAtom p.2).1)
        let indices_a ← (getNatComparisons a).mapM getIndices
        let indices_b ← (getNatComparisons b).mapM getIndices
        pure <| (es.insertMany indices_a).insertMany indices_b
      catch _ => pure es
    let atoms : Array Expr := (← get).atoms
    let nonneg_pfs : List Expr ← nonnegs.toList.filterMapM fun p => do
      mk_natCast_nonneg_prf (atoms[p.1]!, atoms[p.2]!)
    pure [(g, nonneg_pfs ++ l)]

end natToInt

section strengthenStrictInt

/--
If `pf` is a proof of a strict inequality `(a : ℤ) < b`,
`mkNonstrictIntProof pf` returns a proof of `a + 1 ≤ b`,
and similarly if `pf` proves a negated weak inequality.
-/
def mkNonstrictIntProof (pf : Expr) : MetaM (Option Expr) := do
  match ← (← inferType pf).ineqOrNotIneq? with
  | (true, Ineq.lt, .const ``Int [], a, b) =>
    return mkApp (← mkAppM ``Iff.mpr #[← mkAppOptM ``Int.add_one_le_iff #[a, b]]) pf
  | (false, Ineq.le, .const ``Int [], a, b) =>
    return mkApp (← mkAppM ``Iff.mpr #[← mkAppOptM ``Int.add_one_le_iff #[b, a]])
      (← mkAppM ``lt_of_not_ge #[pf])
  | _ => return none

/-- `strengthenStrictInt h` turns a proof `h` of a strict integer inequality `t1 < t2`
into a proof of `t1 ≤ t2 + 1`. -/
def strengthenStrictInt : Preprocessor where
  description := "strengthen strict inequalities over int"
  transform h := return [(← mkNonstrictIntProof h).getD h]

end strengthenStrictInt

section compWithZero

/--
`rearrangeComparison e` takes a proof `e` of an equality, inequality, or negation thereof,
and turns it into a proof of a comparison `_ R 0`, where `R ∈ {=, ≤, <}`.
-/
partial def rearrangeComparison (e : Expr) : MetaM (Option Expr) := do
  match ← (← inferType e).ineq? with
  | (Ineq.le, _) => try? <| mkAppM ``Linarith.sub_nonpos_of_le #[e]
  | (Ineq.lt, _) => try? <| mkAppM ``Linarith.sub_neg_of_lt #[e]
  | (Ineq.eq, _) => try? <| mkAppM ``sub_eq_zero_of_eq #[e]

/--
`compWithZero h` takes a proof `h` of an equality, inequality, or negation thereof,
and turns it into a proof of a comparison `_ R 0`, where `R ∈ {=, ≤, <}`.
-/
def compWithZero : Preprocessor where
  description := "make comparisons with zero"
  transform e := return (← rearrangeComparison e).toList

end compWithZero

section cancelDenoms

theorem without_one_mul {M : Type*} [MulOneClass M] {a b : M} (h : 1 * a = b) : a = b := by
  rwa [one_mul] at h

/--
`normalizeDenominatorsLHS h lhs` assumes that `h` is a proof of `lhs R 0`.
It creates a proof of `lhs' R 0`, where all numeric division in `lhs` has been cancelled.
-/
def normalizeDenominatorsLHS (h lhs : Expr) : MetaM Expr := do
  let mut (v, lhs') ← CancelDenoms.derive lhs
  if v = 1 then
    -- `lhs'` has a `1 *` out front, but `mkSingleCompZeroOf` has a special case
    -- where it does not produce `1 *`. We strip it off here:
    lhs' ← mkAppM ``without_one_mul #[lhs']
  let (_, h'') ← mkSingleCompZeroOf v h
  try
    h''.rewriteType lhs'
  catch e =>
    dbg_trace
      s!"Error in Linarith.normalizeDenominatorsLHS: {← e.toMessageData.toString}"
    throw e

/--
`cancelDenoms pf` assumes `pf` is a proof of `t R 0`. If `t` contains the division symbol `/`,
it tries to scale `t` to cancel out division by numerals.
-/
def cancelDenoms : Preprocessor where
  description := "cancel denominators"
  transform := fun pf => (do
      let (_, lhs) ← parseCompAndExpr (← inferType pf)
      guard <| lhs.containsConst <| fun n =>
        n = ``HDiv.hDiv || n = ``Div.div || n = ``Inv.inv || n == ``OfScientific.ofScientific
      pure [← normalizeDenominatorsLHS pf lhs])
    <|> return [pf]
end cancelDenoms

section nlinarith
/--
`findSquares s e` collects all terms of the form `a ^ 2` and `a * a` that appear in `e`
and adds them to the set `s`.
A pair `(i, true)` is added to `s` when `atoms[i]^2` appears in `e`,
and `(i, false)` is added to `s` when `atoms[i]*atoms[i]` appears in `e`. -/
partial def findSquares (s : TreeSet (Nat × Bool) lexOrd.compare) (e : Expr) :
    AtomM (TreeSet (Nat × Bool) lexOrd.compare) :=
  -- Completely traversing the expression is non-ideal,
  -- as we can descend into expressions that could not possibly be seen by `linarith`.
  -- As a result we visit expressions with bvars, which then cause panics.
  -- Ideally this preprocessor would be reimplemented so it only visits things that could be atoms.
  -- In the meantime we just bail out if we ever encounter loose bvars.
  if e.hasLooseBVars then return s else
  match e.getAppFnArgs with
  | (``HPow.hPow, #[_, _, _, _, a, b]) => match b.numeral? with
    | some 2 => do
      let s ← findSquares s a
      let (ai, _) ← AtomM.addAtom a
      return (s.insert (ai, true))
    | _ => e.foldlM findSquares s
  | (``HMul.hMul, #[_, _, _, _, a, b]) => do
    let (ai, _) ← AtomM.addAtom a
    let (bi, _) ← AtomM.addAtom b
    if ai = bi then do
      let s ← findSquares s a
      return (s.insert (ai, false))
    else
      e.foldlM findSquares s
  | _ => e.foldlM findSquares s

/-- Get proofs of `-x^2 ≤ 0` and `-(x*x) ≤ 0`, when those terms appear in `ls` -/
private def nlinarithGetSquareProofs (ls : List Expr) : MetaM (List Expr) :=
  withTraceNode `linarith (return m!"{exceptEmoji ·} finding squares") do
  -- find the squares in `AtomM` to ensure deterministic behavior
  let s ← AtomM.run .reducible do
    let si ← ls.foldrM (fun h s' => do findSquares s' (← instantiateMVars (← inferType h))) ∅
    si.toList.mapM fun (i, is_sq) => return ((← get).atoms[i]!, is_sq)
  let new_es ← s.filterMapM fun (e, is_sq) =>
    observing? <| mkAppM (if is_sq then ``sq_nonneg else ``mul_self_nonneg) #[e]
  let new_es ← compWithZero.globalize.transform new_es
  trace[linarith] "found:{indentD <| toMessageData s}"
  linarithTraceProofs "so we added proofs" new_es
  return new_es

/--
Get proofs for products of inequalities from `ls`.

Note that the length of the resulting list is proportional to `ls.length^2`, which can make a large
amount of work for the linarith oracle.
-/
private def nlinarithGetProductsProofs (ls : List Expr) : MetaM (List Expr) :=
  withTraceNode `linarith (return m!"{exceptEmoji ·} adding product terms") do
  let with_comps ← ls.mapM (fun e => do
    let tp ← inferType e
    try
      let ⟨ine, _⟩ ← parseCompAndExpr tp
      pure (ine, e)
    catch _ => pure (Ineq.lt, e))
  let products ← with_comps.mapDiagM fun (⟨posa, a⟩ : Ineq × Expr) ⟨posb, b⟩ =>
    try
      (some <$> match posa, posb with
        | Ineq.eq, _ => mkAppM ``zero_mul_eq #[a, b]
        | _, Ineq.eq => mkAppM ``mul_zero_eq #[a, b]
        | Ineq.lt, Ineq.lt => mkAppM ``mul_pos_of_neg_of_neg #[a, b]
        | Ineq.lt, Ineq.le => do
            let a ← mkAppM ``le_of_lt #[a]
            mkAppM ``mul_nonneg_of_nonpos_of_nonpos #[a, b]
        | Ineq.le, Ineq.lt => do
            let b ← mkAppM ``le_of_lt #[b]
            mkAppM ``mul_nonneg_of_nonpos_of_nonpos #[a, b]
        | Ineq.le, Ineq.le => mkAppM ``mul_nonneg_of_nonpos_of_nonpos #[a, b])
    catch _ => pure none
  compWithZero.globalize.transform products.reduceOption

/--
`nlinarithExtras` is the preprocessor corresponding to the `nlinarith` tactic.

* For every term `t` such that `t^2` or `t*t` appears in the input, adds a proof of `t^2 ≥ 0`
  or `t*t ≥ 0`.
* For every pair of comparisons `t1 R1 0` and `t2 R2 0`, adds a proof of `t1*t2 R 0`.

This preprocessor is typically run last, after all inputs have been canonized.
-/
def nlinarithExtras : GlobalPreprocessor where
  description := "nonlinear arithmetic extras"
  transform ls := do
    let new_es ← nlinarithGetSquareProofs ls
    let products ← nlinarithGetProductsProofs (new_es ++ ls)
    return (new_es ++ ls ++ products)

end nlinarith

section removeNe
/--
`removeNe_aux` case splits on any proof `h : a ≠ b` in the input,
turning it into `a < b ∨ a > b`.
This produces `2^n` branches when there are `n` such hypotheses in the input.
-/
partial def removeNe_aux : MVarId → List Expr → MetaM (List Branch) := fun g hs => do
  let some (e, α, a, b) ← hs.findSomeM? (fun e : Expr => do
    let some (α, a, b) := (← instantiateMVars (← inferType e)).ne?' | return none
    return some (e, α, a, b)) | return [(g, hs)]
  let [ng1, ng2] ← g.apply (← mkAppOptM ``Or.elim #[none, none, ← g.getType,
      ← mkAppOptM ``lt_or_gt_of_ne #[α, none, a, b, e]]) | failure
  let do_goal : MVarId → MetaM (List Branch) := fun g => do
    let (f, h) ← g.intro1
    h.withContext do
      let ls ← removeNe_aux h <| hs.removeAll [e]
      return ls.map (fun b : Branch => (b.1, (.fvar f)::b.2))
  return ((← do_goal ng1) ++ (← do_goal ng2))

/--
`removeNe` case splits on any proof `h : a ≠ b` in the input, turning it into `a < b ∨ a > b`,
by calling `linarith.removeNe_aux`.
This produces `2^n` branches when there are `n` such hypotheses in the input.
-/
def removeNe : GlobalBranchingPreprocessor where
  description := "case split on ≠"
  transform := removeNe_aux
end removeNe


/--
The default list of preprocessors, in the order they should typically run.
-/
def defaultPreprocessors : List GlobalBranchingPreprocessor :=
  [filterComparisons, removeNegations, natToInt, strengthenStrictInt,
    compWithZero, cancelDenoms]

/--
`preprocess pps l` takes a list `l` of proofs of propositions.
It maps each preprocessor `pp ∈ pps` over this list.
The preprocessors are run sequentially: each receives the output of the previous one.
Note that a preprocessor may produce multiple or no expressions from each input expression,
so the size of the list may change.
-/
def preprocess (pps : List GlobalBranchingPreprocessor) (g : MVarId) (l : List Expr) :
    MetaM (List Branch) := do
  withTraceNode `linarith (fun e => return m!"{exceptEmoji e} Running preprocessors") <|
    g.withContext <|
      pps.foldlM (init := [(g, l)]) fun ls pp => do
        return (← ls.mapM fun (g, l) => do pp.process g l).flatten

end Mathlib.Tactic.Linarith
