/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
import Mathlib.Tactic.Linarith.Datatypes
import Mathlib.Tactic.Zify
import Mathlib.Tactic.CancelDenoms
import Mathlib.Lean.Exception
import Std.Data.RBMap.Basic
import Mathlib.Data.HashMap

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

set_option autoImplicit true

namespace Linarith

/-! ### Preprocessing -/

open Lean Elab Tactic Meta
open Qq

/-- Processor that recursively replaces `P ∧ Q` hypotheses with the pair `P` and `Q`. -/
partial def splitConjunctions : Preprocessor where
  name := "split conjunctions"
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
  name := "filter terms that are not proofs of comparisons"
  transform h := do
    let tp ← whnfR (← instantiateMVars (← inferType h))
    if (← isProp tp) && (← aux tp) then pure [h]
    else pure []
where
  /-- Implementation of the `filterComparisons` preprocessor. -/
  aux (e : Expr) : MetaM Bool := do
  match e.getAppFnArgs with
  | (``Eq, _) | (``LE.le, _) | (``LT.lt, _) => pure true
  | (``Not, #[e]) => match (← whnfR e).getAppFnArgs with
    | (``LE.le, _) | (``LT.lt, _) => pure true
    | _ => pure false
  | _ => pure false

section removeNegations

/--
If `prf` is a proof of `¬ e`, where `e` is a comparison,
`flipNegatedComparison prf e` flips the comparison in `e` and returns a proof.
For example, if `prf : ¬ a < b`, ``flipNegatedComparison prf q(a < b)`` returns a proof of `a ≥ b`.
-/
def flipNegatedComparison (prf : Expr) (e : Expr) : MetaM Expr :=
  match e.getAppFnArgs with
  | (``LE.le, #[_, _, _, _]) => mkAppM ``lt_of_not_ge #[prf]
  | (``LT.lt, #[_, _, _, _]) => mkAppM ``le_of_not_gt #[prf]
  | _ => throwError "Not a comparison (flipNegatedComparison): {e}"

/--
Replaces proofs of negations of comparisons with proofs of the reversed comparisons.
For example, a proof of `¬ a < b` will become a proof of `a ≥ b`.
-/
def removeNegations : Preprocessor where
  name := "replace negations of comparisons"
  transform h := do
    let t : Q(Prop) ← whnfR (← inferType h)
    match t with
    | ~q(¬ $p) =>
      trace[linarith] "removing negation in {h}"
      return [← flipNegatedComparison h (← whnfR p)]
    | _        => return [h]

end removeNegations

section natToInt

open Mathlib.Tactic.Zify

/--
`isNatProp tp` is true iff `tp` is an inequality or equality between natural numbers
or the negation thereof.
-/
partial def isNatProp (e : Expr) : Bool :=
  match e.getAppFnArgs with
  | (``Eq, #[.const ``Nat [], _, _]) => true
  | (``LE.le, #[.const ``Nat [], _, _, _]) => true
  | (``LT.lt, #[.const ``Nat [], _, _, _]) => true
  | (``GE.ge, #[.const ``Nat [], _, _, _]) => true
  | (``GT.gt, #[.const ``Nat [], _, _, _]) => true
  | (``Not, #[e]) => isNatProp e
  | _ => false

/-- If `e` is of the form `((n : ℕ) : ℤ)`, `isNatIntCoe e` returns `n : ℕ`. -/
def isNatIntCoe (e : Expr) : Option Expr :=
  match e.getAppFnArgs with
  | (``Nat.cast, #[.const ``Int [], _, n]) => some n
  | _ => none

/--
`getNatComparisons e` returns a list of all subexpressions of `e` of the form `((t : ℕ) : ℤ)`.
-/
partial def getNatComparisons (e : Expr) : List Expr :=
  match isNatIntCoe e with
  | some n => [n]
  | none => match e.getAppFnArgs with
    | (``HAdd.hAdd, #[_, _, _, _, a, b]) => getNatComparisons a ++ getNatComparisons b
    | (``HMul.hMul, #[_, _, _, _, a, b]) => getNatComparisons a ++ getNatComparisons b
    | _ => []

/-- If `e : ℕ`, returns a proof of `0 ≤ (e : ℤ)`. -/
def mk_coe_nat_nonneg_prf (e : Expr) : MetaM Expr :=
  mkAppM ``Int.coe_nat_nonneg #[e]

open Std

/-- Ordering on `Expr`. -/
-- We only define this so we can use `RBSet Expr`. Perhaps `HashSet` would be more appropriate?
def Expr.compare (a b : Expr) : Ordering :=
  if Expr.lt a b then .lt else if a.equal b then .eq else .gt

/--
If `h` is an equality or inequality between natural numbers,
`natToInt` lifts this inequality to the integers.
It also adds the facts that the integers involved are nonnegative.
To avoid adding the same nonnegativity facts many times, it is a global preprocessor.
 -/
def natToInt : GlobalBranchingPreprocessor where
  name := "move nats to ints"
  transform g l := do
    let l ← l.mapM $ fun h => do
      let t ← whnfR (← instantiateMVars (← inferType h))
      if isNatProp t then
        let (some (h', t'), _) ← Term.TermElabM.run' (run_for g (zifyProof none h t))
          | throwError "zifyProof failed on {h}"
        if ← filterComparisons.aux t' then
          pure h'
        else
          -- `zifyProof` turned our comparison into something that wasn't a comparison
          -- probably replacing `n = n` with `True`, because of
          -- https://github.com/leanprover-community/mathlib4/issues/741
          -- so we just keep the original hypothesis.
          pure h
      else
        pure h
    let nonnegs ← l.foldlM (init := ∅) fun (es : RBSet Expr Expr.compare) h => do
      try
        let (a, b) ← getRelSides (← inferType h)
        pure <| (es.insertList (getNatComparisons a)).insertList (getNatComparisons b)
      catch _ => pure es
    pure [(g, ((← nonnegs.toList.mapM mk_coe_nat_nonneg_prf) ++ l : List Expr))]

end natToInt

section strengthenStrictInt

/--
`isStrictIntComparison tp` is true iff `tp` is a strict inequality between integers
or the negation of a weak inequality between integers.
-/
def isStrictIntComparison (e : Expr) : Bool :=
  match e.getAppFnArgs with
  | (``LT.lt, #[.const ``Int [], _, _, _]) => true
  | (``GT.gt, #[.const ``Int [], _, _, _]) => true
  | (``Not, #[e]) => match e.getAppFnArgs with
    | (``LE.le, #[.const ``Int [], _, _, _]) => true
    | (``GE.ge, #[.const ``Int [], _, _, _]) => true
    | _ => false
  | _ => false

/--
If `pf` is a proof of a strict inequality `(a : ℤ) < b`,
`mkNonstrictIntProof pf` returns a proof of `a + 1 ≤ b`,
and similarly if `pf` proves a negated weak inequality.
-/
def mkNonstrictIntProof (pf : Expr) : MetaM Expr := do
  match (← inferType pf).getAppFnArgs with
  | (``LT.lt, #[_, _, a, b]) =>
    return mkApp (← mkAppM ``Iff.mpr #[← mkAppOptM ``Int.add_one_le_iff #[a, b]]) pf
  | (``GT.gt, #[_, _, a, b]) =>
    return mkApp (← mkAppM ``Iff.mpr #[← mkAppOptM ``Int.add_one_le_iff #[b, a]]) pf
  | (``Not, #[P]) => match P.getAppFnArgs with
    | (``LE.le, #[_, _, a, b]) =>
      return mkApp (← mkAppM ``Iff.mpr #[← mkAppOptM ``Int.add_one_le_iff #[b, a]])
        (← mkAppM ``lt_of_not_ge #[pf])
    | (``GE.ge, #[_, _, a, b]) =>
      return mkApp (← mkAppM ``Iff.mpr #[← mkAppOptM ``Int.add_one_le_iff #[a, b]])
        (← mkAppM ``lt_of_not_ge #[pf])
    | _ => throwError "mkNonstrictIntProof failed: proof is not an inequality"
  | _ => throwError "mkNonstrictIntProof failed: proof is not an inequality"


/-- `strengthenStrictInt h` turns a proof `h` of a strict integer inequality `t1 < t2`
into a proof of `t1 ≤ t2 + 1`. -/
def strengthenStrictInt : Preprocessor where
  name := "strengthen strict inequalities over int"
  transform h := do
    if isStrictIntComparison (← inferType h) then
      return [← mkNonstrictIntProof h]
    else
      return [h]

end strengthenStrictInt

section compWithZero

/--
`rearrangeComparison e` takes a proof `e` of an equality, inequality, or negation thereof,
and turns it into a proof of a comparison `_ R 0`, where `R ∈ {=, ≤, <}`.
 -/
partial def rearrangeComparison (e : Expr) : MetaM Expr := do
  aux e (← instantiateMVars (← inferType e))
where
  /-- Implementation of `rearrangeComparison`, after type inference. -/
  aux (proof e : Expr) : MetaM Expr :=
    match e.getAppFnArgs with
    | (``LE.le, #[_, _, a, b]) => match a.getAppFnArgs, b.getAppFnArgs with
      | _, (``OfNat.ofNat, #[_, .lit (.natVal 0), _]) => return proof
      | (``OfNat.ofNat, #[_, .lit (.natVal 0), _]), _ => mkAppM ``neg_nonpos_of_nonneg #[proof]
      | _, _                                          => mkAppM ``sub_nonpos_of_le #[proof]
    | (``LT.lt, #[_, _, a, b]) => match a.getAppFnArgs, b.getAppFnArgs with
      | _, (``OfNat.ofNat, #[_, .lit (.natVal 0), _]) => return proof
      | (``OfNat.ofNat, #[_, .lit (.natVal 0), _]), _ => mkAppM ``neg_neg_of_pos #[proof]
      | _, _                                          => mkAppM ``sub_neg_of_lt #[proof]
    | (``Eq, #[_, a, b]) => match a.getAppFnArgs, b.getAppFnArgs with
      | _, (``OfNat.ofNat, #[_, .lit (.natVal 0), _]) => return proof
      | (``OfNat.ofNat, #[_, .lit (.natVal 0), _]), _ => mkAppM ``Eq.symm #[proof]
      | _, _                                          => mkAppM ``sub_eq_zero_of_eq #[proof]
    | (``GT.gt, #[_, _, a, b]) => match a.getAppFnArgs, b.getAppFnArgs with
      | _, (``OfNat.ofNat, #[_, .lit (.natVal 0), _]) => mkAppM ``neg_neg_of_pos #[proof]
      | (``OfNat.ofNat, #[_, .lit (.natVal 0), _]), _ => mkAppM ``lt_zero_of_zero_gt #[proof]
      | _, _                                          => mkAppM ``sub_neg_of_lt #[proof]
    | (``GE.ge, #[_, _, a, b]) => match a.getAppFnArgs, b.getAppFnArgs with
      | _, (``OfNat.ofNat, #[_, .lit (.natVal 0), _]) => mkAppM ``neg_nonpos_of_nonneg #[proof]
      | (``OfNat.ofNat, #[_, .lit (.natVal 0), _]), _ => mkAppM ``le_zero_of_zero_ge #[proof]
      | _, _                                          => mkAppM ``sub_nonpos_of_le #[proof]
    | (``Not, #[a]) => do
      let nproof ← flipNegatedComparison proof a
      aux nproof (← inferType nproof)
    | a => throwError "couldn't rearrange comparison {a}"

/--
`compWithZero h` takes a proof `h` of an equality, inequality, or negation thereof,
and turns it into a proof of a comparison `_ R 0`, where `R ∈ {=, ≤, <}`.
 -/
def compWithZero : Preprocessor where
  name := "make comparisons with zero"
  transform e := try
    pure [← rearrangeComparison e]
  catch e =>
    if ← e.isFailedToSynthesize then
      pure []
    else
      throw e

end compWithZero

section cancelDenoms

theorem without_one_mul [MulOneClass M] {a b : M} (h : 1 * a = b) : a = b := by rwa [one_mul] at h
                                                                                -- 🎉 no goals

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
  name := "cancel denominators"
  transform := fun pf => (do
      let (_, lhs) ← parseCompAndExpr (← inferType pf)
      guard $ lhs.containsConst (fun n => n = ``HDiv.hDiv || n = ``Div.div)
      pure [← normalizeDenominatorsLHS pf lhs])
    <|> return [pf]
end cancelDenoms

section nlinarith
/--
`findSquares s e` collects all terms of the form `a ^ 2` and `a * a` that appear in `e`
and adds them to the set `s`.
A pair `(a, true)` is added to `s` when `a^2` appears in `e`,
and `(a, false)` is added to `s` when `a*a` appears in `e`.  -/
partial def findSquares (s : HashSet (Expr × Bool)) (e : Expr) : MetaM (HashSet (Expr × Bool)) :=
  match e.getAppFnArgs with
  | (``HPow.hPow, #[_, _, _, _, a, b]) => match b.numeral? with
    | some 2 => do
      let s ← findSquares s a
      return (s.insert (a, true))
    | _ => e.foldlM findSquares s
  | (``HMul.hMul, #[_, _, _, _, a, b]) => if a.equal b then do
      let s ← findSquares s a
      return (s.insert (a, false))
    else
      e.foldlM findSquares s
  | _ => e.foldlM findSquares s

/--
`nlinarithExtras` is the preprocessor corresponding to the `nlinarith` tactic.

* For every term `t` such that `t^2` or `t*t` appears in the input, adds a proof of `t^2 ≥ 0`
  or `t*t ≥ 0`.
* For every pair of comparisons `t1 R1 0` and `t2 R2 0`, adds a proof of `t1*t2 R 0`.

This preprocessor is typically run last, after all inputs have been canonized.
-/
def nlinarithExtras : GlobalPreprocessor where
  name := "nonlinear arithmetic extras"
  transform ls := do
    let s ← ls.foldrM (fun h s' => do findSquares s' (← instantiateMVars (← inferType h)))
      HashSet.empty
    let new_es ← s.foldM (fun new_es (⟨e, is_sq⟩ : Expr × Bool) =>
      ((do
        let p ← mkAppM (if is_sq then ``sq_nonneg else ``mul_self_nonneg) #[e]
        pure $ p::new_es) <|> pure new_es)) ([] : List Expr)
    let new_es ← compWithZero.globalize.transform new_es
    trace[linarith] "nlinarith preprocessing found squares"
    trace[linarith] "{s.toList}"
    linarithTraceProofs "so we added proofs" new_es
    let with_comps ← (new_es ++ ls).mapM (fun e => do
      let tp ← inferType e
      try
        let ⟨ine, _⟩ ← parseCompAndExpr tp
        pure (ine, e)
      catch _ => pure (Ineq.lt, e))
    let products ← with_comps.mapDiagM $ fun (⟨posa, a⟩ : Ineq × Expr) ⟨posb, b⟩ =>
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
    let products ← compWithZero.globalize.transform products.reduceOption
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
    let some (α, a, b) := (← inferType e).ne? | return none
    return some (e, α, a, b)) | return [(g, hs)]
  let [ng1, ng2] ← g.apply (← mkAppOptM ``Or.elim #[none, none, ← g.getType,
      ← mkAppOptM ``lt_or_gt_of_ne #[α, none, a, b, e]]) | failure
  let do_goal : MVarId → MetaM (List Branch) := fun g => do
    let (f, h) ← g.intro1
    h.withContext do
      let ls ← removeNe_aux h $ hs.removeAll [e]
      return ls.map (fun b : Branch => (b.1, (.fvar f)::b.2))
  return ((← do_goal ng1) ++ (← do_goal ng2))

/--
`removeNe` case splits on any proof `h : a ≠ b` in the input, turning it into `a < b ∨ a > b`,
by calling `linarith.removeNe_aux`.
This produces `2^n` branches when there are `n` such hypotheses in the input.
-/
def removeNe : GlobalBranchingPreprocessor where
  name := "removeNe"
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
    MetaM (List Branch) :=
  pps.foldlM (fun ls pp => return (← ls.mapM fun (g, l) => do pp.process g l).join) [(g, l)]

end Linarith
