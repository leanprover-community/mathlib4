/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.GroupTheory.Perm.Hex.Generated
public meta import Mathlib.GroupTheory.Perm.Hex.Generated
public import HexPermGroup.Tactic
public meta import HexPermGroup.Tactic

/-!
# The `perm_group` tactic

Prove membership, non-membership, cardinality and full-generation goals about
`Subgroup.closure` of permutations of `Fin n`. Generators may be set literals,
coerced Finset literals or predicates of the form `{p | p ∈ [g₁, …, gₖ]}`;
definitions of the subgroup and generating set are unfolded. The degree and
claimed cardinality must be numerals, and permutations must be closed terms.
Imported definitions must expose their bodies; modules supplying generators
for evaluation must also be meta imported.

The tactic uses HexPermGroup for certificate production, checking and proof replay.
The `#perm_group_certificate` command prints certificate proofs for explicit set and
Finset literals of permutations.
-/

public section

namespace Mathlib.Tactic.PermGroup

open Lean Elab Meta Hex Hex.PermGroup
open _root_.Lean.Elab.Tactic _root_.Hex.PermGroup.Tactic

/-- Extract elements and an unfolded literal, recording Finset coercions so
normalization can avoid evaluating permutation equality. -/
private meta partial def elements? (s : Expr) (fuel : Nat := 32) :
    MetaM (Option (List Expr × Bool × Expr)) := do
  let s ← instantiateMVars s
  if s.isAppOfArity ``List.cons 3 then
    let some (rest, finset, _) ← elements? (s.getArg! 2) fuel | return none
    return some (s.getArg! 1 :: rest, finset, s)
  if s.isAppOfArity ``List.nil 1 then
    return some ([], false, s)
  if s.isAppOfArity ``Insert.insert 5 then
    let some (rest, finset, _) ← elements? (s.getArg! 4) fuel | return none
    return some (s.getArg! 3 :: rest, finset, s)
  if s.isAppOfArity ``Singleton.singleton 4 then
    return some ([s.getArg! 3], false, s)
  if s.isAppOfArity ``EmptyCollection.emptyCollection 2 then
    return some ([], false, s)
  if s.isAppOfArity ``SetLike.coe 4 then
    -- `↑t` for a `Finset` literal `t`
    unless (← whnfR (← inferType (s.getArg! 3))).isAppOfArity ``Finset 1 do return none
    let some (elements, _, literal) ← elements? (s.getArg! 3) fuel | return none
    return some (elements, true, mkAppN s.getAppFn (s.getAppArgs.set! 3 literal))
  let pred := if s.isAppOfArity ``Set.ofPred 2 then
      s.getArg! 1 else s
  if let .lam _ _ body _ := pred then
    if body.isAppOfArity ``Membership.mem 5 && body.getArg! 4 == .bvar 0 &&
        !(body.getArg! 3).hasLooseBVars then
      unless (← whnfR (← inferType (body.getArg! 3))).isAppOfArity ``List 1 do return none
      let list := body.getArg! 3
      let some (elements, _, literal) ← elements? list fuel | return none
      return some (elements, false, s.replace fun e => if e == list then some literal else none)
  if fuel = 0 then return none
  let s' ← whnfR s
  if s' != s then return ← elements? s' (fuel - 1)
  -- A generating set given by a definition, such as `def gens : Set _ := {a, b}`.
  let some s' ← unfoldDefinition? s | return none
  elements? s' (fuel - 1)

/-- The degree `n` of a type `Equiv.Perm (Fin n)`, as a numeral. -/
private meta def permDegree (ty : Expr) : MetaM Nat := do
  let some equiv ← whnfUntil (← instantiateMVars ty) ``Equiv
    | throwError "perm_group: expected permutations of `Fin n`, got{indentExpr ty}"
  let some fin ← whnfUntil (equiv.getArg! 0) ``Fin
    | throwError "perm_group: expected permutations of `Fin n`, got{indentExpr ty}"
  let some n ← evalNat (fin.getArg! 0) |>.run
    | throwError "perm_group: the degree must be a numeral, got{indentExpr (fin.getArg! 0)}"
  return n

/-- The subgroup `H` when the type `T` is `↥H`, that is `{x // x ∈ H}`. -/
private meta def coeSortArg? (T : Expr) : MetaM (Option Expr) := do
  let T ← whnfR (← instantiateMVars T)
  unless T.isAppOfArity ``Subtype 2 do return none
  let .lam _ _ body _ := T.getArg! 1 | return none
  unless body.isAppOfArity ``Membership.mem 5 do return none
  let H := body.getArg! 3
  if H.hasLooseBVars then return none
  return some H

/-- One normalized presentation, including the equality to the original set. -/
private meta structure Presentation where
  degree : Nat
  finset : Bool
  elements : List Expr
  list : Expr
  /-- A proof that the original generating set equals membership in `list`. -/
  equality : Expr

/-- Normalize once, producing a proof that the original set equals list membership. -/
private meta def presentation (s : Expr) : TermElabM Presentation := do
  let ty ← inferType s
  let s ← if ty.isAppOfArity ``Finset 1 then mkAppM ``SetLike.coe #[s] else pure s
  let some (elements, finset, literal) ← elements? s
    | throwError "perm_group: the generating set must be a set literal or a coerced Finset \
        literal{indentExpr s}"
  let ty ← inferType s
  let .forallE _ permTy (.sort .zero) _ ← whnfD ty
    | throwError "perm_group: unexpected set type{indentExpr ty}"
  let degree ← permDegree permTy
  let list ← mkListLit permTy elements
  let canonical ← withLocalDeclD `x permTy fun x => do
    mkAppOptM ``Set.ofPred #[permTy,
      ← mkLambdaFVars #[x] (← mkAppM ``Membership.mem #[list, x])]
  let proof ← mkFreshExprMVar (← mkEq literal canonical)
  let rem ← Term.withoutErrToSorry <| Tactic.run proof.mvarId! do
    evalTactic (← `(tactic| simp only [List.not_mem_nil, Set.ofPred_false,
      List.setOfPred_mem_cons, insert_empty_eq,
      Finset.coe_empty, Finset.coe_singleton, Finset.coe_insert]))
  unless rem.isEmpty do
    throwError "perm_group: could not identify the generating set with a list\
      {indentExpr (← rem.head!.getType)}"
  let equality ← mkExpectedTypeHint (← instantiateMVars proof) (← mkEq s canonical)
  return { degree, finset, elements, list, equality }

/-- The shape of a supported goal. -/
private meta inductive GoalKind where
  | card (N : Expr)
  | mem (g : Expr)
  | notMem (g : Expr)
  | top

/-- Match a supported goal and unfold its subgroup to a closure. The returned
goal is definitionally equal to the original and exposes the generating set. -/
private meta def readGoal? (goal : Expr) : MetaM (Option (Expr × GoalKind × Expr)) := do
  let goal ← instantiateMVars goal
  let some (H, kind) ← (show MetaM (Option (Expr × GoalKind)) from do
    if goal.isAppOfArity ``Eq 3 then
      let lhs := goal.getArg! 1
      let rhs := goal.getArg! 2
      if lhs.isAppOfArity ``Nat.card 1 then
        let some H ← coeSortArg? (lhs.getArg! 0) | return none
        return some (H, .card rhs)
      if rhs.isAppOfArity ``Top.top 2 then return some (lhs, .top)
    if goal.isAppOfArity ``Membership.mem 5 then
      return some (goal.getArg! 3, .mem (goal.getArg! 4))
    if goal.isAppOfArity ``Not 1 && (goal.getArg! 0).isAppOfArity ``Membership.mem 5 then
      let m := goal.getArg! 0
      return some (m.getArg! 3, .notMem (m.getArg! 4))
    return none) | return none
  let some closure ← whnfUntil H ``Subgroup.closure | return none
  let target := goal.replace fun e => if e == H then some closure else none
  return some (closure.getArg! 2, kind, target)

/-- The elements of a set-literal syntax `{a, b, …}`, possibly under a type
ascription. -/
private meta partial def setLitStx (stx : Syntax) : Option (Array Syntax) :=
  if stx.getKind == ``Lean.Parser.Term.typeAscription then setLitStx stx[1]
  else if stx.getKind == ``Lean.Parser.Term.paren then setLitStx stx[1]
  else if stx.getKind == `coeNotation then setLitStx stx[1]
  else if stx.getNumArgs == 3 && stx[0].isToken "{" && stx[2].isToken "}" then
    some stx[1].getSepArgs
  else none

/-- Supply only a round-trip equality; Hex owns the optimized packing proof. -/
private meta def input (n : Nat) (e : Expr) : MetaM Input := do
  let term ← mkAppOptM ``Perm.ofEquiv #[mkNatLit n, e]
  let canonical? ← (← whnfUntil e ``Perm.toEquiv).mapM fun converted => do
    let canonical := converted.getArg! 1
    return (canonical, ← mkAppM ``Perm.ofEquiv_toEquiv #[canonical])
  return { term, canonical? }

/-- Translate Mathlib's goal, run the shared computational tactic and transport
its conclusion through the correspondence theorems. -/
@[perm_group_extension] public meta def extension : Extension where
  prove? cfg target := do
    let some (s, kind, t) ← readGoal? target | return none
    let p ← presentation s
    let request ← match kind with
      | .card rhs => do
        let some N ← (evalNat rhs).run
          | throwError "perm_group: the claimed order must be a numeral{indentExpr rhs}"
        pure (Goal.card N)
      | .top => pure Goal.all
      | .mem g => pure (.mem (← input p.degree g))
      | .notMem g => pure (.notMem (← input p.degree g))
    let prepared ← prepare cfg p.degree (← p.elements.mapM fun e => input p.degree e)
    let core ← replay prepared request
    let pf ← match kind with
      | .card _ => mkAppOptM ``card_of_hasOrder #[mkNatLit p.degree, p.list, none, core]
      | .top => mkAppOptM ``eq_top_of_all #[mkNatLit p.degree, p.list, core]
      | .mem g => mkAppOptM ``mem_of_generated #[mkNatLit p.degree, p.list, g, core]
      | .notMem g => mkAppOptM ``not_mem_of_neg #[mkNatLit p.degree, p.list, g, core]
    let predicate := mkLambda `generators .default (← inferType s) (← kabstract t s)
    let goalEq ← mkCongrArg predicate p.equality
    return some (← mkAppM ``Eq.mpr #[goalEq, pf])
  certificate? name s sStx := do
    let some elemStx := setLitStx sStx | return none
    let p ← presentation s
    let prepared ← prepare {} p.degree (← p.elements.mapM fun e => input p.degree e)
    let n := p.degree
    let rawSrc := ((sStx.updateTrailing "".toRawSubstring).reprint.getD "").trimAscii.toString
    let sSrc := s!"({rawSrc} : _root_.Set (_root_.Equiv.Perm (_root_.Fin {n})))"
    let elemSrc := elemStx.toList.map fun e =>
      ((e.updateTrailing "".toRawSubstring).reprint.getD "").trimAscii.toString
    let gsSrc := "[" ++ ", ".intercalate elemSrc ++ "]"
    let arraySrc := s!"(({gsSrc} : _root_.List (_root_.Equiv.Perm (_root_.Fin {n})))" ++
      ".map _root_.Hex.Perm.ofEquiv).toArray"
    let out ← render name prepared
      (elemSrc.map fun g => s!"_root_.Hex.Perm.ofEquiv ({g} : _root_.Equiv.Perm (_root_.Fin {n}))")
      arraySrc
    let lemmas := ["_root_.List.setOfPred_mem_cons", "_root_.List.not_mem_nil",
      "_root_.Set.ofPred_false", "_root_.LawfulSingleton.insert_empty_eq"]
    let lemmas := if p.finset then
      lemmas ++ (match p.elements.length with
        | 1 => ["_root_.Finset.coe_singleton"]
        | _ => ["_root_.Finset.coe_insert", "_root_.Finset.coe_singleton"])
      else lemmas
    return some (out ++ "\nopen Hex.PermGroup in\n" ++
      s!"theorem {name}_card : _root_.Nat.card (_root_.Subgroup.closure {sSrc}) = " ++
      s!"{prepared.order} := by\n" ++
      s!"  rw [show {sSrc} = _root_.Set.ofPred (· ∈ {gsSrc}) by\n" ++
      s!"    symm; simp only [{", ".intercalate lemmas}]]\n" ++
      s!"  exact _root_.Hex.PermGroup.card_of_hasOrder {name}_hasOrder\n")

end Mathlib.Tactic.PermGroup
