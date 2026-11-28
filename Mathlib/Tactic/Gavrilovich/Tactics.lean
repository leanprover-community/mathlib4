/-
Copyright (c) 2026 Robert Maxton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Maxton
-/
module

public import Lean.Elab.Tactic.ElabTerm
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Gavrilovich.Elab.Basic
public import Mathlib.Util.AddRelatedDecl

/-!
# Tactics for Gavrilovich diagram spaces

* `gav_decide` is `decide`, but accepts goals containing universe metavariables, such as goals
  about diagrams inside the body of a universe-polymorphic definition.
* `gav_monotone` proves that a map between spaces is monotone (i.e. continuous), naming two points
  witnessing it if it isn't; `Space.hom f` is the morphism given by such a function `f`.
* `pt_cases` splits on the points of a space, on the morphisms between two spaces, or on the cases
  of a specialization `x ⤳ y`.
* `simp` puts points in their canonical form `Space.mk k _` (`Space.reducePt`, `Space.reduceMk`,
  `Space.reducePtsMk`) and evaluates `⊓`, `⊔` at points of two-point spaces. `@[simp_pt]` and
  `simp_pt%` restate lemmas with points `Space.pt n _` in canonical form.
-/

public meta section

namespace Mathlib.Tactic.Gavrilovich
open _root_.Gavrilovich
open Lean Elab Term Meta


/-- `gav_decide` is `decide`, except that it accepts goals containing universe metavariables.
Diagrams are universe polymorphic, so inside the body of a definition involving them, goals
usually contain the definition's universe as a metavariable, and `decide` refuses those. Universe
levels can't change whether a decidable proposition holds, so this is safe. -/
elab (name := gavDecide) "gav_decide" : tactic =>
  Tactic.closeMainGoalUsing `gav_decide fun type _ => do
    let type ← instantiateMVars type
    if type.hasExprMVar then
      throwError "gav_decide: the goal contains metavariables{indentExpr type}"
    let inst ← synthInstance (mkApp (mkConst ``Decidable) type)
    let r ← withAtLeastTransparency .default <|
      whnf (mkApp2 (mkConst ``Decidable.decide) type inst)
    unless r.isConstOf ``true do
      throwError "gav_decide failed to prove the proposition{indentExpr type}"
    return mkApp3 (mkConst ``of_decide_eq_true) type inst
      (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``true))

/-! ### Continuity of maps between spaces -/

/-- If `t` is the carrier of `Space L E`, its universe, label type, `L` and `E`. -/
def spaceOf? (t : Expr) : Option (Level × Expr × Expr × Expr) := do
  let t := t.consumeMData
  let s ← if t.isAppOfArity ``TopCat.carrier 1 then some t.appArg!
    else if let .proj ``TopCat 0 s := t then some s else none
  let .const ``Space [u] := s.getAppFn | none
  guard (s.getAppNumArgs == 3)
  return (u, s.getArg! 0, s.getArg! 1, s.getArg! 2)

/-- The value of a closed natural number, computed by `whnf`: a numeral, or anything that
reduces to one or to `Nat.zero`/`Nat.succ`, such as `Zero.zero` or `1 - 1`. -/
partial def natVal? (k : Expr) : MetaM (Option Nat) := withAtLeastTransparency .default do
  let k ← whnf k
  if let some n := k.rawNatLit? <|> k.nat? then return n
  if k.isConstOf ``Nat.zero then return some 0
  if k.isAppOfArity ``Nat.succ 1 then return (← natVal? k.appArg!).map (· + 1)
  return none

/-- The index of a point of a `Space`, computed by `whnf`. -/
def ptIdx? (x : Expr) : MetaM (Option Nat) := withAtLeastTransparency .default do
  let x ← whnf x
  unless x.isAppOfArity ``Pts.mk 4 do return none
  let i ← whnf x.appArg!
  unless i.isAppOfArity ``Fin.mk 3 do return none
  natVal? (i.getArg! 1)

/-- A literal point: `Space.mk k _`, or the constructor `⟨⟨k, _⟩⟩` that `grind` unfolds it to
(and, unlike `simp`, before running its simprocs). Its universes, the `α`, `L` and `E` of its space,
and its index. -/
def ptLit? (x : Expr) : MetaM (Option (List Level × Expr × Expr × Expr × Nat)) := do
  unless (x.isAppOfArity ``Space.mk 5 || x.isAppOfArity ``Pts.mk 4) && !x.hasLooseBVars do
    return none
  let .const _ us := x.getAppFn | return none
  -- not `(x.getArg! 3).nat?`: `grind` writes the index as `↑⟨k, _⟩`, for example
  let some n ← ptIdx? x | return none
  return (us, x.getArg! 0, x.getArg! 1, x.getArg! 2, n)

/-- For a goal `Monotone f`, with `f` a map between `Space`s that isn't monotone, a message naming
two points witnessing that. -/
def monotoneCounterexample? (goal : Expr) : MetaM (Option MessageData) := do
  let goal ← instantiateMVars goal
  unless goal.isAppOfArity ``Monotone 5 do return none
  let f := goal.getArg! 4
  let some (u, α, L, E) := spaceOf? (goal.getArg! 0) | return none
  let some (_, _, L', _) := spaceOf? (goal.getArg! 1) | return none
  let some (_, pts) := L.listLit? | return none
  let len := mkApp2 (mkConst ``List.length [0]) (mkApp (mkConst ``List [0]) α) L
  let point (i : Nat) : MetaM Expr := do
    let isLt ← mkDecideProof (← mkLt (mkNatLit i) len)
    return mkApp4 (mkConst ``Pts.mk [u]) α L E (mkApp3 (mkConst ``Fin.mk) len (mkNatLit i) isLt)
  let holds (p : Expr) : MetaM Bool := withAtLeastTransparency .default do
    return (← whnf (← mkDecide p)).isConstOf ``true
  let name (L : Expr) (i : Nat) : String :=
    match decodePoints L with
    | some names => "=".intercalate (names[i]?.getD [])
    | none => s!"#{i}"
  for i in [0:pts.length] do
    for j in [0:pts.length] do
      if i == j then continue
      let x ← point i; let y ← point j
      unless ← holds (← mkAppM ``LE.le #[x, y]) do continue
      let fx := mkApp f x; let fy := mkApp f y
      if ← holds (← mkAppM ``LE.le #[fx, fy]) then continue
      let (some k, some l) := (← ptIdx? fx, ← ptIdx? fy) | return none
      -- `x ≤ y` is the arrow `y → x`
      return m!"not continuous: {name L j} → {name L i} in the source, but no \
        {name L' l} → {name L' k} in the target"
  return none

/-- `gav_monotone` proves `Monotone f` for a map `f` between `Space`s (i.e. that `f` is
continuous) by `gav_decide`. If `f` isn't monotone, it names two points witnessing that. -/
elab (name := gavMonotone) "gav_monotone" : tactic => Tactic.withMainContext do
  let goal ← Tactic.getMainTarget
  try Tactic.evalTactic (← `(tactic| (unfold Monotone; gav_decide)))
  catch e =>
    if let some msg ← monotoneCounterexample? goal then throwError msg
    throw e

/-! ### Points in canonical form

The canonical form of a point is `Space.mk k _`, with `k` a numeral, which unfolds (reducibly)
to the constructor that pattern matching is about. So the equation lemmas of definitions by
pattern matching apply to it. `pt(n)` elaborates to it (outside patterns), `fin_cases` produces
it, `simp` rewrites `Space.pt n h` to it (`Space.reducePt`), and it is printed as `pt(n)`. -/

/-- The point `Space.mk k h` of `@Space.{us} α L E`, in canonical form. -/
def mkCanonicalPt (us : List Level) (α L E : Expr) (k : Nat) : MetaM Expr := do
  -- a fresh proof, whose type is syntactically `k < L.length`, so that it unifies with the
  -- proofs in lemmas about `Space.mk k h` at reducible transparency
  let len := mkApp2 (mkConst ``List.length [0]) (mkApp (mkConst ``List [0]) α) L
  let h ← mkDecideProof (← mkLt (mkNatLit k) len)
  return mkApp5 (mkConst ``Space.mk us) α L E (mkNatLit k) h

/-- The canonical form `Space.mk k h` of `Space.pt n h`, with `k` a numeral. -/
def canonicalPt? (e : Expr) : MetaM (Option Expr) := do
  unless e.isAppOfArity ``Space.pt 6 && !e.hasLooseBVars do return none
  let some k ← ptIdx? e | return none
  let .const _ us := e.getAppFn | return none
  mkCanonicalPt us (e.getArg! 0) (e.getArg! 1) (e.getArg! 2) k

/-- `simp` rewrites `Space.pt n h` to the canonical form `Space.mk k h`, with `k` a numeral. -/
dsimproc [simp, seval] _root_.Gavrilovich.Space.reducePt (Space.pt _ _) := fun e => do
  match ← canonicalPt? e with
  | some e => return .done e
  | none => return .continue

/-- `simp` rewrites `Space.mk k h`, where `k` isn't a numeral but evaluates to one (e.g. a raw
literal, `Zero.zero` or `1 - 1`), to the canonical form `Space.mk n h'`, with `n` a numeral. -/
dsimproc [simp, seval] _root_.Gavrilovich.Space.reduceMk (Space.mk _ _) := fun e => do
  unless e.isAppOfArity ``Space.mk 5 && !e.hasLooseBVars do return .continue
  let k := e.getArg! 3
  if k.nat?.isSome then return .continue
  let some n ← natVal? k | return .continue
  let .const _ us := e.getAppFn | return .continue
  return .done (← mkCanonicalPt us (e.getArg! 0) (e.getArg! 1) (e.getArg! 2) n)

/-- `simp` rewrites the constructor `⟨⟨k, _⟩⟩ : Pts L E` to the canonical form `Space.mk k _`. The
match elaborator produces the constructor: in `match h : x with | pt(o) => …`, say, `h` is
`x = ⟨⟨k, _⟩⟩`, since patterns are unfolded to constructors. This runs before `simp` visits the
index, which `Fin.isValue` would otherwise rewrite to `(k : Fin _)`. Not in `seval`: `grind`
unfolds `Space.mk` to the constructor anyway. -/
dsimproc ↓ [simp] _root_.Gavrilovich.Space.reducePtsMk (Pts.mk _) := fun e => do
  -- the discrimination tree also matches `Space.mk`, which unfolds to the constructor
  unless e.isAppOfArity ``Pts.mk 4 do return .continue
  let some (us, α, L, E, n) ← ptLit? e | return .continue
  let some (_, pts) := L.listLit? | return .continue
  unless n < pts.length do return .continue
  return .done (← mkCanonicalPt us α L E n)

/-- `a ⊓ b` and `a ⊔ b` for points `a`, `b` of a two-point space with one edge (with the
instances `Space.instMinCarrier`, `Space.instMaxCarrier`): `min` and `max` in the order, i.e. of
the indices of `a` and `b`, up to the direction of the edge. The result is in canonical form. -/
def boolOpPt : Simp.DSimproc := fun e => do
  let some (inst, a, b, isAnd) := match_expr e with
    | Min.min _ inst a b => some (inst, a, b, true)
    | Max.max _ inst a b => some (inst, a, b, false)
    | _ => none
    | return .continue
  unless inst.isAppOf ``Space.instMinCarrier || inst.isAppOf ``Space.instMaxCarrier do
    return .continue
  let some (us, α, L, E, n) ← ptLit? a | return .continue
  let some (_, _, _, _, m) ← ptLit? b | return .continue
  -- the edge `(i, j)` puts `j` below `i`
  let some (_, [edge]) := E.listLit? | return .continue
  let some k := match_expr edge with
    | Prod.mk _ _ i j => match i.nat?, j.nat? with
      | some 1, some 0 => some (if isAnd then min n m else max n m)
      | some 0, some 1 => some (if isAnd then max n m else min n m)
      | _, _ => none
    | _ => none
    | return .continue
  return .done (← mkCanonicalPt us α L E k)

/-- `simp` evaluates `a ⊓ b` at points of a two-point space with one edge (`boolOpPt`). -/
dsimproc [simp, seval] _root_.Gavrilovich.Space.reduceInfPt
    (@Min.min (Space [_, _] [_]) _ (Space.mk _ _) (Space.mk _ _)) := boolOpPt

/-- `simp` evaluates `a ⊔ b` at points of a two-point space with one edge (`boolOpPt`). -/
dsimproc [simp, seval] _root_.Gavrilovich.Space.reduceSupPt
    (@Max.max (Space [_, _] [_]) _ (Space.mk _ _) (Space.mk _ _)) := boolOpPt

/-- Rewrite every `Space.pt n h` in `e` to its canonical form, wrapped in `no_index` if
`noIndex`. -/
def canonicalizePts (e : Expr) (noIndex := false) : MetaM Expr :=
  Meta.transform e (post := fun e => do
    match ← canonicalPt? e with
    | some e => return .done (if noIndex then DiscrTree.mkNoindexAnnotation e else e)
    | none => return .continue)

/-- Canonicalize the points in the statement `type` of a `simp` lemma. On the left-hand side, they
are also wrapped in `no_index`: points are matched by unification rather than by the
discrimination tree, which is sensitive to how the index `k` is written (`fin_cases` writes it as
a raw literal, for example). -/
def canonicalizeSimpLemma (type : Expr) : MetaM Expr :=
  forallTelescope type fun xs body => do
    let body ← match body.getAppFn, body.getAppArgs with
      | .const ``Eq us, #[α, l, r] =>
        pure <| mkApp3 (.const ``Eq us) α (← canonicalizePts l true) (← canonicalizePts r)
      | .const ``Iff _, #[l, r] =>
        pure <| mkIff (← canonicalizePts l true) (← canonicalizePts r)
      | _, _ => canonicalizePts body
    mkForallFVars xs body

/-- `@[simp_pt]` makes a lemma stated with points `Space.pt n _` a `simp` lemma. On `foo`, it adds
the lemma `foo_mk`, which is `foo` restated with every `Space.pt n _` in its canonical form
`Space.mk k _`, and makes that a `simp` lemma.

This is needed because `simp` rewrites `Space.pt n _` to its canonical form (`Space.reducePt`)
before trying lemmas, so a `@[simp]` lemma whose left-hand side mentions `Space.pt n _` would never
fire. The notation `pt(o)` already elaborates to the canonical form (outside patterns), so lemmas
stated with it don't need this; a lemma without `Space.pt` is an error: it can just be
`@[simp]`.

As with `@[reassoc]`, `@[simp_pt (attr := foo)]` also applies `foo` to both lemmas. -/
syntax (name := simpPt) "simp_pt" optAttrArg : attr

initialize registerBuiltinAttribute {
  name := `simpPt
  descr := "make a lemma stated with points `pt(o)` a `simp` lemma"
  applicationTime := .afterCompilation
  add := fun src ref kind => match ref with
  | `(attr| simp_pt $optAttr) => MetaM.run' do
    if kind != AttributeKind.global then
      throwError "`simp_pt` can only be used as a global attribute"
    let tgt := src.appendAfter "_mk"
    addRelatedDecl src tgt ref optAttr fun value levels => do
      let type ← inferType value
      let type' ← canonicalizeSimpLemma type
      if type' == type then
        throwError "`simp_pt` made no progress on{indentExpr type}\nUse `@[simp]` instead."
      return (← mkExpectedTypeHint value type', levels)
    addSimpTheorem simpExtension tgt (post := true) (inv := false) kind (prio := eval_prio default)
  | _ => throwUnsupportedSyntax }

/-- `simp_pt% t`, for a proof `t`, is `t` with its statement restated as `@[simp_pt]` restates a
lemma: with every `Space.pt n _` in canonical form. So
`simp [simp_pt% foo]` uses `foo` as `simp [foo_mk]` would if `foo` were `@[simp_pt]`, instead of
```
have := foo
simp at this
simp [this]
```
As with `simp [foo]`, the arguments of a constant `foo` stay universally quantified. -/
syntax (name := simpPtPercent) "simp_pt% " term : term

@[term_elab simpPtPercent, inherit_doc simpPtPercent]
def elabSimpPtPercent : TermElab := fun stx _ => do
  let t := stx[1]
  let e ← match ← if t.isIdent then resolveId? t (withInfo := true) else pure none with
    | some e => pure e
    | none => elabTerm t none
  unless ← isProof e do throwError "`simp_pt%` expects a proof, but{indentExpr e}\nis not one"
  let type ← instantiateMVars (← inferType e)
  let type' ← canonicalizeSimpLemma type
  if type' == type then throwError "`simp_pt%` made no progress on{indentExpr type}"
  mkExpectedTypeHint e type'

/-- Whether the decidable proposition `p` holds, if `decide p` evaluates. -/
def decideProp? (p : Expr) : MetaM (Option Bool) := withAtLeastTransparency .default do
  let some d ← observing? (mkDecide p) | return none
  let d ← whnf d
  return if d.isConstOf ``true then some true else if d.isConstOf ``false then some false else none

/-- Case analysis on `h : x ≤ y` or `h : x ⤳ y`: split on each of `x` and `y` that is a local
variable (with `fin_cases`), then close the goals in which `h` is false, and clear `h` from the
others. Returns `none` if `h` isn't of this form. -/
def relCases (g : MVarId) (h : FVarId) : MetaM (Option (List MVarId)) := g.withContext do
  let type ← instantiateMVars (← h.getType)
  let some (x, y) := match_expr type with
    | LE.le _ _ x y => some (x, y)
    | Specializes _ _ x y => some (x, y)
    | _ => none
    | return none
  let vars := #[x, y].filter (·.isFVar) |>.map (·.fvarId!)
  -- revert everything, then reintroduce it one variable at a time, splitting on `x` and `y` (the
  -- variables' ids don't survive `fin_cases`)
  let (reverted, g) ← g.revert (vars.push h)
  -- `h` depends on `x` and `y`, so it is reintroduced after them, and its id then survives
  let mut gs : List (MVarId × Option FVarId) := [(g, none)]
  for v in reverted do
    gs ← gs.flatMapM fun (g, h') => do
      let (v', g) ← g.intro1P
      if vars.contains v then return (← Lean.Elab.Tactic.finCasesAt g v').map (·, h')
      return [(g, if v == h then some v' else h')]
  gs.filterMapM fun (g, h) => g.withContext do
    let some h := h | return some g
    let p ← instantiateMVars (← h.getType)
    match ← decideProp? p with
    | some false =>
      g.assign (← mkAbsurd (← g.getType) (.fvar h) (← mkDecideProof (mkNot p)))
      return none
    | some true => return some ((← observing? (g.clear h)).getD g)
    | none => return some g

/-- Clean up after `fin_cases`: beta-reduce, and rewrite `toUpperSet ⟨⟨k, h⟩⟩` to the canonical
form `Space.mk k h` (`Space.toUpperSet_eq`). This doesn't reduce projections (other than
`Fin.val`), which would unfold the carrier `↑(Space L E)` everywhere. -/
def cleanupCases (g : MVarId) : MetaM MVarId := g.withContext do
  let thms ← ({} : SimpTheorems).addConst `Gavrilovich.Space.toUpperSet_eq
  let ctx ← Simp.mkContext (config := { proj := false })
    (simpTheorems := #[← thms.addConst ``Fin.val_mk])
  let mut g := g
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    let (t', _) ← dsimp t ctx
    if t != t' then g ← g.replaceLocalDeclDefEq d.fvarId t'
  let t ← instantiateMVars (← g.getType)
  let (t', _) ← dsimp t ctx
  if t != t' then g ← g.replaceTargetDefEq t'
  return g

/-- `pt_cases x` splits into one goal per point of the space of `x` (or per element of `l`, for a
hypothesis `x ∈ l`), like `fin_cases`, and cleans up so that the points are the constructors
printed as `pt(…)`. On a morphism `f : Space L E ⟶ Space L' E'`, it splits into one goal per
morphism, each a diagram morphism printed as `(⌜…⌟ ⇢ ⌜…⌟)`.

On a hypothesis `h : x ≤ y` or `h : x ⤳ y`, it splits on the points `x` and `y`, and keeps only
the cases in which `h` holds (clearing `h`). So `intro x y h; pt_cases h` leaves one goal for each
specialization `x ⤳ y` of the space, including the trivial ones `x ⤳ x`. -/
syntax (name := ptCases) "pt_cases " term,+ : tactic

@[tactic ptCases, inherit_doc ptCases] def evalPtCases : Tactic.Tactic
  | `(tactic| pt_cases $hs,*) => Tactic.focus do
    for h in hs.getElems do
      Tactic.allGoals <| Tactic.withMainContext do
        let e ← Tactic.elabTerm h none
        if let .fvar v := e then
          if let some gs ← relCases (← Tactic.getMainGoal) v then
            Tactic.replaceMainGoal gs
            return
        Tactic.evalTactic (← `(tactic| fin_cases $h:term))
    Tactic.allGoals <| Tactic.liftMetaTactic1 (some <$> cleanupCases ·)
  | _ => throwUnsupportedSyntax

end Mathlib.Tactic.Gavrilovich

end

/-! ### Maps between spaces -/

@[expose] public section

universe u

namespace Gavrilovich.Space
variable {α β : Type} {L : List (List α)} {L' : List (List β)} {E E' : List (ℕ × ℕ)}

/-- The morphism of spaces given by a function between their points, which is continuous because
it is monotone, which `gav_monotone` checks by default. For example,
`Space.hom fun | pt(a) => pt(o) | pt(b) => pt(c)`. -/
abbrev hom (f : Space.{u} L E → Space.{u} L' E')
    (h : Monotone f := by gav_monotone) : Space L E ⟶ Space L' E' :=
  CategoryTheory.ConcreteCategory.ofHom ⟨f, Topology.IsUpperSet.monotone_iff_continuous.1 h⟩

lemma hom_apply (f : Space.{u} L E → Space.{u} L' E') (h : Monotone f) (x : Space L E) :
    hom f h x = f x := rfl

@[simp] lemma toUpperSet_eq (x : Pts.{u} L E) :
    @Eq (Space.{u} L E) (Topology.WithUpperSet.toUpperSet x) (mk x.idx.val x.idx.isLt) := rfl

/-- `ContinuousMap.coe_mk`, applied. `grind` unfolds reducible definitions, such as `Space.hom` and
`Space.homOfTable`, to `ConcreteCategory.ofHom ⟨f, _⟩`; with this and
`ConcreteCategory.hom_ofHom`, it evaluates them at points. -/
@[grind =] lemma coe_mk_apply {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y)
    (h : Continuous f) (x : X) : (⟨f, h⟩ : C(X, Y)) x = f x := rfl

attribute [grind =] _root_.CategoryTheory.ConcreteCategory.hom_ofHom

end Gavrilovich.Space
