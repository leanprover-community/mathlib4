/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
module

public meta import Mathlib.Control.Basic
public meta import Mathlib.Lean.Meta.Tactic.Rewrite
public meta import Mathlib.Tactic.Linarith.Datatypes
public meta import Mathlib.Util.AtomM
public import Mathlib.Tactic.CancelDenoms.Core
public import Mathlib.Tactic.Linarith.Datatypes
public import Mathlib.Tactic.Zify

/-!
# Linarith preprocessing

This file contains methods used to preprocess inputs to `linarith`.

In particular, `linarith` works over comparisons of the form `t R 0`, where `R ∈ {<,≤,=}`.
It assumes that expressions in `t` have integer coefficients and that the type of `t` has
well-behaved subtraction.

## Implementation details

A `GlobalPreprocessor` is a function `List TaggedProof → MetaM (List TaggedProof)`, where a
`TaggedProof` is a proof term paired with the indices of the hypotheses it was derived from.
Users can add custom
preprocessing steps by adding them to the `LinarithConfig` object. `Linarith.defaultPreprocessors`
is the main list, and generally none of these should be skipped unless you know what you're doing.

Preprocessors must propagate provenance, since the oracle's certificate indexes the preprocessed
facts rather than the user's hypotheses and `linarith?` has to report the latter. See
`Linarith.Origin`.
-/

public meta section

namespace Mathlib.Tactic.Linarith

/-! ### Preprocessing -/

open Lean
open Elab Tactic Meta
open Qq
open Std (TreeSet TreeMap)

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
Negations are pushed into inequalities when possible.
-/
partial def filterComparisons : Preprocessor where
  description := "filter terms that are not proofs of comparisons"
  transform h := do
    let tp ← instantiateMVars (← inferType h)
    try
      match tp.not? with
      | some p => match (← p.ineq?).1 with
        | .le => return [← mkAppM ``lt_of_not_ge #[h]]
        | .lt => return [← mkAppM ``le_of_not_gt #[h]]
        | .eq => return []
      | none =>
        _ ← tp.ineq?
        return [h]
    catch _ =>
      return []

section natToInt

open Zify

/--
`isNatProp tp` is true iff `tp` is an inequality or equality between natural numbers
or the negation thereof.
-/
partial def isNatProp (e : Expr) : MetaM Bool := succeeds do
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
def mkNatCastNonnegProof? (p : Expr × Expr) : MetaM (Option Expr) :=
  match p with
  | ⟨e, target⟩ => try commitIfNoEx (mkAppM ``natCast_nonneg #[target, e])
    catch e => do
      trace[linarith] "Got exception when using cast {e.toMessageData}"
      return none

@[deprecated (since := "2026-05-27")] alias mk_natCast_nonneg_prf := mkNatCastNonnegProof?

/--
If `h` is an equality or inequality between natural numbers,
`natToInt` lifts this inequality to the integers.
It also adds the facts that the integers involved are nonnegative.
To avoid adding the same nonnegativity facts many times, it is a global preprocessor.

Lifting a hypothesis preserves its origin; the nonnegativity facts are tagged with the origins of
every hypothesis the cast was found in. See `Linarith.Origin`.
-/
def natToInt : GlobalBranchingPreprocessor where
  description := "move nats to ints"
  transform g l := do
    let l : List TaggedProof ← l.mapM fun ⟨h, o⟩ => do
      let t ← whnfR (← instantiateMVars (← inferType h))
      unless ← isNatProp t do return ⟨h, o⟩
      let (some (h', t'), _) ← Term.TermElabM.run' (run_for g (zifyProof none h t))
        | throwError "zifyProof failed on {h}"
      if ← succeeds t'.ineqOrNotIneq? then
        pure ⟨h', o⟩
      else
        -- `zifyProof` turned our comparison into something that wasn't a comparison
        -- probably replacing `n = n` with `True`, because of
        -- https://github.com/leanprover-community/mathlib4/issues/741
        -- so we just keep the original hypothesis.
        pure ⟨h, o⟩
    withNewMCtxDepth <| AtomM.run .reducible do
    -- Keyed by atom indices, so the nonnegativity facts are generated in a deterministic order.
    let nonnegs ← l.foldlM (init := (∅ : TreeMap (Nat × Nat) (Expr × Expr × Origin) lexOrd.compare))
      fun es ⟨h, o⟩ => do
        try
          let (_, _, a, b) ← (← inferType h).ineq?
          (getNatComparisons a ++ getNatComparisons b).foldlM (init := es) fun es c => do
            -- Store the canonical form of the atoms, i.e. the first occurrence encountered.
            let (i₁, c₁) ← AtomM.addAtom c.1
            let (i₂, c₂) ← AtomM.addAtom c.2
            return es.alter (i₁, i₂) fun p? => some (c₁, c₂, ((p?.map (·.2.2)).getD []).union o)
        catch _ => pure es
    let nonnegProofs : List TaggedProof ← nonnegs.values.filterMapM fun (e, target, o) => do
      return (← mkNatCastNonnegProof? (e, target)).map (⟨·, o⟩)
    pure [(g, nonnegProofs ++ l)]

end natToInt

section strengthenStrictInt

/--
If `pf` is a proof of a strict inequality `(a : ℤ) < b`,
`mkNonstrictIntProof pf` returns a proof of `a + 1 ≤ b`,
and similarly if `pf` proves a negated weak inequality.
-/
def mkNonstrictIntProof? (pf : Expr) : MetaM (Option Expr) := do
  match ← (← inferType pf).ineqOrNotIneq? with
  | (true, Ineq.lt, .const ``Int [], a, b) =>
    return mkApp (← mkAppM ``Iff.mpr #[← mkAppOptM ``Int.add_one_le_iff #[a, b]]) pf
  | (false, Ineq.le, .const ``Int [], a, b) =>
    return mkApp (← mkAppM ``Iff.mpr #[← mkAppOptM ``Int.add_one_le_iff #[b, a]])
      (← mkAppM ``lt_of_not_ge #[pf])
  | _ => return none

@[deprecated (since := "2026-05-27")] alias mkNonstrictIntProof := mkNonstrictIntProof?

/-- `strengthenStrictInt h` turns a proof `h` of a strict integer inequality `t1 < t2`
into a proof of `t1 ≤ t2 + 1`. -/
def strengthenStrictInt : Preprocessor where
  description := "strengthen strict inequalities over int"
  transform h := return [(← mkNonstrictIntProof? h).getD h]

end strengthenStrictInt

section compWithZero

/--
`rearrangeComparison e` takes a proof `e` of an equality, inequality, or negation thereof,
and turns it into a proof of a comparison `_ R 0`, where `R ∈ {=, ≤, <}`.
-/
partial def rearrangeComparison? (e : Expr) : MetaM (Option Expr) := do
  match ← (← inferType e).ineq? with
  | (Ineq.le, _) => try? <| mkAppM ``Linarith.sub_nonpos_of_le #[e]
  | (Ineq.lt, _) => try? <| mkAppM ``Linarith.sub_neg_of_lt #[e]
  | (Ineq.eq, _) => try? <| mkAppM ``sub_eq_zero_of_eq #[e]

@[deprecated (since := "2026-05-27")] alias rearrangeComparison := rearrangeComparison?

/--
`compWithZero h` takes a proof `h` of an equality, inequality, or negation thereof,
and turns it into a proof of a comparison `_ R 0`, where `R ∈ {=, ≤, <}`.
-/
def compWithZero : Preprocessor where
  description := "make comparisons with zero"
  transform e := return (← rearrangeComparison? e).toList

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

/--
Get proofs of `-x^2 ≤ 0` and `-(x*x) ≤ 0`, when those terms appear in `ls`.

Each proof is tagged with the origins of the hypotheses the square was found in, as with the
nonnegativity facts added by `natToInt`. See `Linarith.Origin`.
-/
private def nlinarithGetSquareProofs (ls : List TaggedProof) : MetaM (List TaggedProof) :=
  withTraceNode `linarith (fun _ => return m!" finding squares") do
  -- find the squares in `AtomM` to ensure deterministic behavior
  let s ← AtomM.run .reducible do
    let m ← ls.foldrM (init := (∅ : TreeMap (Nat × Bool) Origin lexOrd.compare))
      fun ⟨h, o⟩ m => do
        let si ← findSquares ∅ (← instantiateMVars (← inferType h))
        return si.foldl (fun m k => m.alter k fun o? => some ((o?.getD []).union o)) m
    let atoms := (← get).atoms
    return m.toList.map fun ((i, is_sq), o) => (atoms[i]!, is_sq, o)
  let new_es : List TaggedProof ← s.filterMapM fun (e, is_sq, o) => do
    return (← observing? <|
      mkAppM (if is_sq then ``sq_nonneg else ``mul_self_nonneg) #[e]).map (⟨·, o⟩)
  let new_es ← compWithZero.globalize.transform new_es
  trace[linarith] "found:{indentD <| toMessageData (s.map fun (e, is_sq, _) => (e, is_sq))}"
  linarithTraceProofs "so we added proofs" (new_es.map (·.proof))
  return new_es

/--
Get proofs for products of inequalities from `ls`. Each product is attributed to the union of the
origins of its two factors.

Note that the length of the resulting list is proportional to `ls.length^2`, which can make a large
amount of work for the linarith oracle.
-/
private def nlinarithGetProductsProofs (ls : List TaggedProof) : MetaM (List TaggedProof) :=
  withTraceNode `linarith (fun _ => return m!" adding product terms") do
  let with_comps ← ls.mapM (fun ⟨e, o⟩ => do
    try
      let ⟨ine, _⟩ ← parseCompAndExpr (← inferType e)
      pure (ine, e, o)
    catch _ => pure (Ineq.lt, e, o))
  let products : List (Option TaggedProof) ← with_comps.mapDiagM
    fun (⟨posa, a, oa⟩ : Ineq × Expr × Origin) ⟨posb, b, ob⟩ =>
      try
        let pf ← match posa, posb with
          | Ineq.eq, _ => mkAppM ``zero_mul_eq #[a, b]
          | _, Ineq.eq => mkAppM ``mul_zero_eq #[a, b]
          | Ineq.lt, Ineq.lt => mkAppM ``mul_pos_of_neg_of_neg #[a, b]
          | Ineq.lt, Ineq.le =>
              mkAppM ``mul_nonneg_of_nonpos_of_nonpos #[← mkAppM ``le_of_lt #[a], b]
          | Ineq.le, Ineq.lt =>
              mkAppM ``mul_nonneg_of_nonpos_of_nonpos #[a, ← mkAppM ``le_of_lt #[b]]
          | Ineq.le, Ineq.le => mkAppM ``mul_nonneg_of_nonpos_of_nonpos #[a, b]
        pure (some ⟨pf, oa.union ob⟩)
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
`removeNeAux` case splits on any proof `h : a ≠ b` in the input, turning it into `a < b ∨ a > b`,
provided the type has a `LinearOrder` instance. This produces `2^n` branches when there are `n` such
hypotheses in the input.

The hypothesis introduced in each branch inherits the origin of the `≠` hypothesis it came from.
-/
partial def removeNeAux : MVarId → List TaggedProof → MetaM (List Branch) := fun g hs => do
  let some (⟨e, o⟩, α, a, b) ← hs.findSomeM? (fun f : TaggedProof => do
    let some (α, a, b) := (← instantiateMVars (← inferType f.proof)).ne?' | return none
    unless (← synthInstance? (← mkAppM ``LinearOrder #[α])).isSome do return none
    return some (f, α, a, b)) | return [(g, hs)]
  let [ng1, ng2] ← g.apply (← mkAppOptM ``Or.elim #[none, none, ← g.getType,
      ← mkAppOptM ``lt_or_gt_of_ne #[α, none, a, b, e]]) | failure
  let do_goal : MVarId → MetaM (List Branch) := fun g => do
    let (f, h) ← g.intro1
    h.withContext do
      let ls ← removeNeAux h <| hs.filter (·.proof != e)
      return ls.map fun b : Branch => (b.1, (⟨.fvar f, o⟩ : TaggedProof) :: b.2)
  return ((← do_goal ng1) ++ (← do_goal ng2))

@[deprecated (since := "2026-06-06")] alias removeNe_aux := removeNeAux

/--
`removeNe` case splits on any proof `h : a ≠ b` in the input, turning it into `a < b ∨ a > b`,
by calling `linarith.removeNeAux`, provided the type has a `LinearOrder` instance.
This produces `2^n` branches when there are `n` such hypotheses in the input.
-/
def removeNe : GlobalBranchingPreprocessor where
  description := "case split on ≠"
  transform := removeNeAux
end removeNe

/-- Definition overridden in `Mathlib.Tactic.Linarith.NNRealPreprocessor`. -/
initialize nnrealToRealTransform : IO.Ref (List TaggedProof → MetaM (List TaggedProof)) ←
  IO.mkRef pure

/--
If `h` is an equality or inequality between NNReals, `nnrealToReal` lifts this inequality to the
Reals. It also adds the facts that the reals involved are nonnegative. To avoid adding the same
nonnegativity facts many times, it is a global preprocessor. This preprocessor does nothing unless
`Mathlib.Tactic.Linarith.NNRealPreprocessor` is imported.

The override must preserve origins itself rather than being lifted with `Linarith.untagged`, since
the default here is the identity. -/
def nnrealToReal : GlobalPreprocessor where
  description := "move nnreals to reals"
  transform l := do (← nnrealToRealTransform.get) l

/--
The default list of preprocessors, in the order they should typically run.
-/
def defaultPreprocessors : List GlobalBranchingPreprocessor :=
  [filterComparisons, nnrealToReal, natToInt, strengthenStrictInt,
    compWithZero, cancelDenoms]

/--
`preprocess pps l` takes a list `l` of facts: proofs of propositions, each tagged with the
hypotheses it was derived from.
It maps each preprocessor `pp ∈ pps` over this list.
The preprocessors are run sequentially: each receives the output of the previous one.
Note that a preprocessor may produce multiple or no expressions from each input expression,
so the size of the list may change.
-/
def preprocess (pps : List GlobalBranchingPreprocessor) (g : MVarId) (l : List TaggedProof) :
    MetaM (List Branch) := do
  withTraceNode `linarith (fun _ => return m!"Running preprocessors") <|
    g.withContext <|
      pps.foldlM (init := [(g, l)]) fun ls pp => do
        return (← ls.mapM fun (g, l) => do pp.process g l).flatten

end Mathlib.Tactic.Linarith
