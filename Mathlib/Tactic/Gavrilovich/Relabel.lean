/-
Copyright (c) 2026 Robert Maxton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Maxton
-/
module

public import Mathlib.Topology.Gavrilovich.Relabel

/-!
# Relabelling finite spaces: tactics, elaborators and simprocs

The implementation of `gav_relabel`, `gav_relabel_of`, `gav_arrow_iso`, `relabel[…]`,
`relabelIso[…]` and `relabelHomeo[…]`, and the simprocs that normalize relabellings and evaluate
morphisms given by tables. See `Mathlib.Topology.Gavrilovich.Relabel` for the definitions.
-/

/-! ### Finding isomorphisms -/

public meta section

namespace Mathlib.Tactic.Gavrilovich
open _root_.Gavrilovich
open Lean Meta Elab Term _root_.CategoryTheory

/-- The points (each a list of names) of a literal `L`. -/
def pointNames? (L : Expr) : Option (List (List Expr)) := do
  (← L.listLit?).2.mapM fun l => return (← l.listLit?).2

/-- All isomorphisms (as tables of indices) from `Space L E` to `Space L' E'` that send the `i`-th
point to `fixed[i]` (where that is given), those that keep the most names first. -/
def relabellings (L E L' E' : Expr) (fixed : Array (Option Nat) := #[]) (limit := 5040) :
    MetaM (Array (Array Nat)) := do
  let (L, E, L', E') := (← instantiateMVars L, ← instantiateMVars E, ← instantiateMVars L',
    ← instantiateMVars E')
  let (some P, some P') := (pointNames? L, pointNames? L') |
    throwError "the points of the spaces aren't literal lists{indentExpr L}\nand{indentExpr L'}"
  let (some E, some E') := (decodeEdges E, decodeEdges E') |
    throwError "the edges of the spaces aren't literal lists{indentExpr E}\nand{indentExpr E'}"
  return (relabellingsCore P P' E E' fixed limit).map (·.1)

/-- The canonical relabelling from `Space L E` to `Space L' E'`, which `gav_relabel` finds. -/
def canonicalRelabelling? (L E L' E' : Expr) (fixed : Array (Option Nat) := #[]) :
    MetaM (Option (Array Nat)) := do
  return (← observing? (relabellings L E L' E' fixed)).bind (·[0]?)

/-- The string that a `gavName` stands for. -/
def gavNameString (n : TSyntax ``gavName) : String :=
  match n.raw[0] with
  | .ident _ _ x _ => x.toString (escape := false)
  | s => s.isStrLit?.getD ((s.isLit? numLitKind).getD "")

/-- The index of the point named `n` in a literal list of points `L`. -/
def pointIdx? (L : Expr) (n : String) : Option Nat := do
  (← pointNames? L).findIdx? (·.contains (mkStrLit n))

/-- Apply `e` to `n` proofs by `decide` of the propositions that its type asks for, checking that
they hold. `err i` describes the `i`-th of them, for the error message if it doesn't. -/
def mkAppDecide (e : Expr) (n : Nat) (err : Nat → MessageData) : MetaM Expr := do
  let mut e := e
  for i in [0:n] do
    let .forallE _ p _ _ ← whnf (← inferType e) |
      throwError "mkAppDecide: not a function{indentExpr e}"
    unless (← decideProp? p) == some true do throwError (err i)
    e := mkApp e (← mkDecideProof p)
  return e

/-- The relabelling `⟨σ, σ⁻¹, …⟩ : Space.Relabelling L E L' E'`, with all conditions proved by
`decide`. -/
def mkRelabelling (α β L E L' E' : Expr) (σ : Array Nat) : MetaM Expr := do
  let mut inv := Array.replicate σ.size 0
  for h : i in [0:σ.size] do inv := inv.set! σ[i] i
  mkAppDecide (mkAppN (mkConst ``Space.Relabelling.mk) #[α, β, L, E, L', E', toExpr σ.toList,
    toExpr inv.toList]) 6 fun _ => m!"invalid relabelling {σ}"

/-- Given the space `Space L E` and a renaming `rs` of all of its points (`fwd`), or of all of the
points of a space onto those of `Space L E` (`!fwd`), assign the other space,
`Space (α := γ) L' E'` (in canonical form, as a diagram would elaborate to).

With `isPartial`, `rs` (if nonempty) needn't rename every point. If it only uses the names of
`Space L E`, the other space is `Space L E` itself (so that, e.g., `relabel[o₁ ↦ o₂]` is an
automorphism of `⌜o₁ → c ← o₂⌟`); otherwise the points not mentioned keep their names. -/
def completeSpace (rs : Array (TSyntax ``gavRenaming)) (L E γ L' E' : Expr) (fwd : Bool)
    (isPartial : Bool := false) : MetaM Unit := do
  let (some P, some Es) := (decodePoints L, decodeEdges E) | throwError
    "gav_relabel: the spaces aren't known yet; use a type ascription, e.g. \
      `(Space.relabel : ⌜o → c⌟ ⟶ ⌜T → F⌟)`"
  let side := if fwd then "target" else "source"
  let mut names : Array (Option String) := .replicate P.length none
  for r in rs do
    let `(gavRenaming| $x:gavName ↦ $y:gavName) := r | throwUnsupportedSyntax
    let (x, y) := (gavNameString x, gavNameString y)
    let (x, y) := if fwd then (x, y) else (y, x)
    let some i := P.findIdx? (·.contains x) |
      throwErrorAt r "gav_relabel: no point named '{x}' in\
        {indentExpr (mkApp3 (mkConst ``Space [0]) (mkConst ``String) L E)}"
    if let some (some y') := names[i]? then
      if y' != y then throwErrorAt r "gav_relabel: '{x}' is already sent elsewhere"
    names := names.set! i (some y)
  let isPartial := isPartial && !rs.isEmpty && names.any (·.isNone)
  if isPartial && names.all (·.all fun y => P.any (·.contains y)) then
    unless ← isDefEq γ (mkConst ``String) <&&> isDefEq L' L <&&> isDefEq E' E do
      throwError "gav_relabel: the {side} space doesn't match the renaming"
    return
  if !isPartial then
    if let some i := names.findIdx? (·.isNone) then
      throwError "gav_relabel: the {side} space isn't known, so the name of every point in it \
        must be given, but '{"=".intercalate P[i]!}' is missing (or use a type ascription)"
  let names' := (names.zip P.toArray).map fun (y?, ns) => y?.map ([·]) |>.getD ns
  if names'.toList.flatten.eraseDups.length != names'.toList.flatten.length then
    throwError "gav_relabel: the names {if isPartial then "of" else "given for"} the {side} space \
      {if isPartial then "(the points not mentioned keep their names) " else ""}aren't distinct; \
      give the name of every point in it, or use a type ascription"
  let c := canonOf names' Es.toArray
  unless ← isDefEq γ (mkConst ``String) <&&> isDefEq L' (toExpr c.L) <&&>
      isDefEq E' (toExpr c.E) do
    throwError "gav_relabel: the {side} space doesn't match the renaming"

/-- The relabelling of type `goal` (`Space.Relabelling L E L' E'`) asked for by the renaming
`rs`. If one of the spaces isn't known yet and `rs` renames all of the points of the other (or
with `isPartial`, any of them), the unknown one is assigned first (see `completeSpace`). -/
def relabellingFor (goal : Expr) (rs : Array (TSyntax ``gavRenaming)) (isPartial := false) :
    MetaM Expr := do
  -- a renaming of all points determines the other space
  let goal ← whnfR (← instantiateMVars goal)
  let known (e : Expr) := !e.hasExprMVar
  match_expr goal with
  | Space.Relabelling α β L E L' E' =>
    if known L && known E && !(known L' && known E') then
      completeSpace rs L E β L' E' true isPartial
    else if known L' && known E' && !(known L && known E) then
      completeSpace rs L' E' α L E false isPartial
  | _ => pure ()
  let goal ← whnfR (← instantiateMVars goal)
  let_expr Space.Relabelling α β L E L' E' := goal |
    throwError "gav_relabel: the goal isn't of the form `Space.Relabelling L E L' E'`"
  if goal.hasExprMVar then
    throwError "gav_relabel: the spaces aren't known yet, in{indentExpr goal}\nUse a type \
      ascription, e.g. `(Space.relabel : ⌜o → c⌟ ⟶ ⌜T → F⌟)`."
  let A := mkApp3 (mkConst ``Space [0]) α L E
  let B := mkApp3 (mkConst ``Space [0]) β L' E'
  let some (_, P) := L.listLit? |
    throwError "gav_relabel: the points of{indentExpr A}\naren't a literal list"
  -- the images that were asked for
  let mut fixed : Array (Option Nat) := .replicate P.length none
  for r in rs do
    let `(gavRenaming| $x:gavName ↦ $y:gavName) := r | throwUnsupportedSyntax
    let (x, y) := (gavNameString x, gavNameString y)
    let some i := pointIdx? L x |
      throwErrorAt r "gav_relabel: no point named '{x}' in{indentExpr A}"
    let some j := pointIdx? L' y |
      throwErrorAt r "gav_relabel: no point named '{y}' in{indentExpr B}"
    if let some (some j') := fixed[i]? then
      if j' != j then throwErrorAt r "gav_relabel: '{x}' is already sent elsewhere"
    fixed := fixed.set! i (some j)
  let some σ ← canonicalRelabelling? L E L' E' fixed |
    if rs.isEmpty then
      throwError "gav_relabel: the spaces{indentExpr A}\nand{indentExpr B}\naren't isomorphic"
    else
      throwError "gav_relabel: no isomorphism from{indentExpr A}\nto{indentExpr B}\nsends \
        {", ".intercalate (rs.toList.map fun r => toString r.raw.prettyPrint)}"
  mkRelabelling α β L E L' E' σ

@[tactic Gavrilovich.gavRelabel, inherit_doc gavRelabel]
def evalGavRelabel : Tactic.Tactic := fun stx => do
  -- the goal can already have been assigned by unification, e.g. with a local instance
  if (← Tactic.getUnsolvedGoals).isEmpty then return
  Tactic.withMainContext do
  let rs : Array (TSyntax ``gavRenaming) := match stx with
    | `(tactic| gav_relabel [$rs,*]) => rs.getElems
    | _ => #[]
  -- nothing more can be learned about the spaces by waiting, so a partial renaming is fine
  Tactic.closeMainGoal `gav_relabel
    (← relabellingFor (← Tactic.getMainTarget) rs (isPartial := true))

/-- The table of indices of a map `f` between the points of spaces, if it evaluates at points.
(`f` can be a function, or a morphism.) -/
def homTable? (f : Expr) (u : Level) (α L E : Expr) (n : Nat) :
    TermElabM (Option (Array Nat)) := do
  let len := mkApp2 (mkConst ``List.length [0]) (mkApp (mkConst ``List [0]) α) L
  let f ← exprToSyntax f
  let mut tbl := #[]
  for i in [0:n] do
    let h ← mkDecideProof (← mkLt (mkNatLit i) len)
    let x ← exprToSyntax (mkApp5 (mkConst ``Space.mk [u]) α L E (mkNatLit i) h)
    let some fx ← observing? (withSynthesize (elabTerm (← `($f $x)) none)) | return none
    let some k ← ptIdx? fx | return none
    tbl := tbl.push k
  return tbl

@[tactic Gavrilovich.gavRelabelOf, inherit_doc gavRelabelOf]
def evalGavRelabelOf : Tactic.Tactic := fun _ => do
  if (← Tactic.getUnsolvedGoals).isEmpty then return
  Tactic.withMainContext do
  let goal ← whnfR (← instantiateMVars (← Tactic.getMainTarget))
  let_expr Space.RelabellingOf α β L L' E E' f := goal |
    throwError "gav_relabel_of: the goal isn't of the form `Space.RelabellingOf f`"
  let .const _ us@(u :: _) := goal.getAppFn |
    throwError "gav_relabel_of: unexpected universe levels"
  let name (L : Expr) (i : Nat) : String :=
    match decodePoints L with
    | some names => "=".intercalate (names[i]?.getD [])
    | none => s!"#{i}"
  let (some (_, P), some (_, P')) := (L.listLit?, L'.listLit?) |
    throwError "gav_relabel_of: the points of the spaces aren't literal lists"
  let some t ← homTable? f u α L E P.length |
    throwError "gav_relabel_of: can't evaluate{indentExpr f}\nat the points of its domain"
  let mut pre : Array (Option Nat) := .replicate P'.length none
  for h : i in [0:t.size] do
    if let some j := pre[t[i]]! then
      throwError "gav_relabel_of: not injective: {name L j} and {name L i} both map to \
        {name L' t[i]}"
    pre := pre.set! t[i] (some i)
  if let some k := pre.findIdx? (·.isNone) then
    throwError "gav_relabel_of: not surjective: nothing maps to {name L' k}"
  let inv := pre.toList.map (·.get!)
  let σ ← mkAppDecide (mkAppN (mkConst ``Space.Relabelling.mk) #[α, β, L, E, L', E',
      toExpr t.toList, toExpr inv]) 6 fun
    | 2 => m!"gav_relabel_of:{indentExpr f}\nisn't continuous"
    | 3 => m!"gav_relabel_of: the inverse of{indentExpr f}\nisn't continuous"
    | _ => m!"gav_relabel_of: failed to check{indentExpr f}"
  Tactic.closeMainGoal `gav_relabel_of <| ← mkAppDecide
    (mkAppN (mkConst ``Space.RelabellingOf.mk us) #[α, β, L, L', E, E', f, σ]) 1
    fun _ => m!"gav_relabel_of: failed to check{indentExpr f}"

@[tactic Gavrilovich.gavArrowIso, inherit_doc gavArrowIso]
def evalGavArrowIso : Tactic.Tactic := fun _ => do
  if (← Tactic.getUnsolvedGoals).isEmpty then return
  Tactic.withMainContext do
  let goal ← whnfR (← instantiateMVars (← Tactic.getMainTarget))
  let_expr Iso _ _ X Y := goal |
    throwError "gav_arrow_iso: the goal isn't of the form `Arrow.mk f ≅ Arrow.mk f'`"
  let_expr Arrow.mk _ _ A B f := (← instantiateMVars X) |
    throwError "gav_arrow_iso: {X} isn't of the form `Arrow.mk f`"
  let_expr Arrow.mk _ _ A' B' f' := (← instantiateMVars Y) |
    throwError "gav_arrow_iso: {Y} isn't of the form `Arrow.mk f`"
  if f.hasExprMVar || f'.hasExprMVar then
    throwError "gav_arrow_iso: both morphisms must be known, but the goal is{indentExpr goal}"
  -- the candidate isomorphisms of each side (as `relabelIso` lacking its relabelling), or `none`
  -- for the identity
  let side (X X' : Expr) : TermElabM (Option (Expr × Array (Array Nat))) := do
    match ← spaceObj? X, ← spaceObj? X' with
    | some (u, α, L, E), some (_, β, L', E') =>
      let σs ← relabellings L E L' E'
      if σs.isEmpty then throwError "gav_arrow_iso: {X} and {X'} aren't isomorphic"
      return some (mkAppN (mkConst ``Space.relabelIso [u]) #[α, β, L, L', E, E'], σs)
    | _, _ =>
      unless ← isDefEq X X' do
        throwError "gav_arrow_iso: {X} and {X'} aren't isomorphic spaces, nor the same object"
      return none
  let (l, r) := (← side A A', ← side B B')
  -- choose isomorphisms that commute with `f` and `f'`, when that can be checked here
  let tables (A B f : Expr) : TermElabM (Option (Array Nat)) := do
    let (some (u, α, L, E), some _) := (← spaceObj? A, ← spaceObj? B) | return none
    let some (_, P) := L.listLit? | return none
    homTable? f u α L E P.length
  let (σ, τ) ← match l, r with
    | some (_, σs), some (_, τs) =>
      match ← tables A B f, ← tables A' B' f' with
      | some t, some t' =>
        let some (σ, τ) := σs.findSome? fun σ => τs.findSome? fun τ =>
            if (List.range σ.size).all fun i => τ[t[i]!]! == t'[σ[i]!]! then some (σ, τ) else none
          | throwError "gav_arrow_iso: no isomorphisms of the sides commute with the morphisms"
        pure (some σ, some τ)
      | _, _ => pure (some σs[0]!, some τs[0]!)
    | _, _ => pure (l.map (·.2[0]!), r.map (·.2[0]!))
  let iso (side : Option (Expr × Array (Array Nat))) (σ : Option (Array Nat)) :
      TermElabM Term := do
    match side, σ with
    | some (e, _), some σ =>
      let_expr Space.relabelIso α β L L' E E' := e | throwError "gav_arrow_iso: unexpected {e}"
      exprToSyntax (mkApp e (← mkRelabelling α β L E L' E' σ))
    | _, _ => `(Iso.refl _)
  Tactic.evalTactic (← `(tactic| exact Arrow.isoMk' $(← exprToSyntax f) $(← exprToSyntax f')
    $(← iso l σ) $(← iso r τ) (by first | gav_decide | cat_disch)))

/-! ### Normalizing relabellings -/

/-- Evaluate a list of natural numbers. -/
partial def evalNatList? (e : Expr) : MetaM (Option (List Nat)) := do
  let e ← whnfD (← instantiateMVars e)
  match_expr e with
  | List.nil _ => return some []
  | List.cons _ a l =>
    let a ← whnfD a
    let some n := a.rawNatLit? <|> a.nat? | return none
    return (← evalNatList? l).map (n :: ·)
  | _ => return none

/-- The arguments of a relabelling morphism `Space.relabel σ`, and its table of indices. -/
def relabelTable? (e : Expr) (c : Name := ``Space.relabel) :
    MetaM (Option (Array Expr × List Nat)) := do
  unless e.isAppOfArity c 7 do return none
  let args := e.getAppArgs
  let some (_, P') := args[3]!.listLit? | return none
  let some t ← evalNatList? (← mkAppM ``Space.Relabelling.fwd #[args[6]!]) | return none
  return (args, t.map (· % P'.length))

/-- `simp` normalizes `Space.relabel σ` to `𝟙 _` if it is the identity of a space, and otherwise
to `Space.relabel` of a literal relabelling (which is printed as plain `Space.relabel` if it is the
canonical one). -/
simproc [simp, seval] _root_.Gavrilovich.Space.reduceRelabel (Space.relabel _) := fun e => do
  let some (args, t) ← relabelTable? e | return .continue
  let #[α, β, L, L', E, E', σ] := args | return .continue
  let .const _ us := e.getAppFn | return .continue
  if α == β && L == L' && E == E' && t == List.range t.length then
    let rhs ← mkAppM ``CategoryStruct.id #[mkApp3 (mkConst ``Space us) α L E]
    return .done { expr := rhs, proof? := ← mkDecideProof (← mkEq e rhs) }
  if σ.isAppOf ``Space.Relabelling.mk then return .continue
  let rhs := mkAppN e.getAppFn #[α, β, L, L', E, E', ← mkRelabelling α β L E L' E' t.toArray]
  return .done { expr := rhs, proof? := ← mkDecideProof (← mkEq e rhs) }

/-- A morphism between spaces given by a table, `Space.relabel σ` or `Space.homOfTable tbl _ _`:
its first six arguments `α β L L' E E'`, whether it is a relabelling, and its table. -/
def tableHom? (e : Expr) : MetaM (Option (Array Expr × Bool × List Nat)) := do
  if let some (args, t) ← relabelTable? e then return (args, true, t)
  unless e.isAppOfArity ``Space.homOfTable 9 do return none
  let args := e.getAppArgs
  let some (_, P') := args[3]!.listLit? | return none
  let some t ← evalNatList? args[6]! | return none
  return (args, false, t.map (· % P'.length))

/-- The morphism `Space L E ⟶ Space L' E'` given by the table `ρ`: `𝟙 _` if it is the identity of
a space, and otherwise `Space.relabel` (with a literal relabelling) if `rel`, and
`Space.homOfTable ρ _ _` if not. -/
def mkTableHom (us : List Level) (α β L L' E E' : Expr) (rel : Bool) (ρ : Array Nat) :
    MetaM Expr := do
  if α == β && L == L' && E == E' && ρ == Array.range ρ.size then
    return ← mkAppM ``CategoryStruct.id #[mkApp3 (mkConst ``Space us) α L E]
  if rel then
    return mkAppN (mkConst ``Space.relabel us) #[α, β, L, L', E, E',
      ← mkRelabelling α β L E L' E' ρ]
  mkAppDecide (mkAppN (mkConst ``Space.homOfTable us)
    #[α, β, L, L', E, E', toExpr ρ.toList]) 2 fun _ => m!"invalid table {ρ}"

/-- The composite `f ≫ g` of two morphisms given by tables, as one: `𝟙 _` if it is the identity of
a space, `Space.relabel ρ` if both are relabellings, and otherwise `Space.homOfTable ρ _ _`. -/
def composeTableHoms? (f g : Expr) : MetaM (Option Expr) := do
  let (some (a, rf, t₁), some (b, rg, t₂)) := (← tableHom? f, ← tableHom? g) | return none
  let .const _ us := f.getAppFn | return none
  let ρ := t₁.toArray.map fun i => t₂.getD i 0
  some <$> mkTableHom us a[0]! b[1]! a[2]! b[3]! a[4]! b[5]! (rf && rg) ρ

/-- Compose `f ≫ g`, or `f ≫ g ≫ h`, where `f` and `g` are given by tables. -/
def reduceTableComp (e : Expr) : MetaM Simp.Step := do
  let_expr CategoryStruct.comp _ _ _ _ _ f g := e | return .continue
  if let some r ← composeTableHoms? f g then
    return .visit { expr := r, proof? := ← mkDecideProof (← mkEq e r) }
  let_expr CategoryStruct.comp _ _ _ _ _ g₁ h := g | return .continue
  let some r ← composeTableHoms? f g₁ | return .continue
  let pf ← mkDecideProof (← mkEq (← mkAppM ``CategoryStruct.comp #[f, g₁]) r)
  let pf ← mkEqTrans (← mkEqSymm (← mkAppM ``Category.assoc #[f, g₁, h]))
    (← mkAppM ``eq_whisker #[pf, h])
  return .visit { expr := ← mkAppM ``CategoryStruct.comp #[r, h], proof? := pf }

/-- `simp` composes relabellings, and diagram morphisms (`Space.homOfTable`), into one:
`relabel σ ≫ relabel τ` becomes `relabel ρ`, `relabel σ ≫ (⌜x  y⌟ ⇢ ⌜x → y⌟)` becomes a single
diagram morphism, and so on (also as `f ≫ g ≫ h`, with `h` arbitrary). Composites that are
identities become `𝟙 _`. -/
simproc [simp, seval] _root_.Gavrilovich.Space.reduceRelabelComp
    ((Space.relabel _) ≫ _) := fun e => reduceTableComp e

/-- `simp` composes diagram morphisms (`Space.homOfTable`) with relabellings and with each other, as
`Space.reduceRelabelComp`. This runs before `simp` visits the morphisms, which it would otherwise
unfold. -/
simproc ↓ [simp, seval] _root_.Gavrilovich.Space.reduceHomOfTableComp
    ((Space.homOfTable _ _ _) ≫ _) :=
  fun e => reduceTableComp e

/-- A morphism of `TopCat` applied to a point, `⇑(ConcreteCategory.hom f) x` (or with
`TopCat.Hom.hom f`): `f` and `x`. -/
def homApp? (e : Expr) : Option (Expr × Expr) := do
  guard <| e.isAppOfArity ``DFunLike.coe 6
  let F := e.getArg! 4
  guard <| F.isAppOfArity ``TopCat.Hom.hom 3 ||
    F.isAppOfArity ``ConcreteCategory.hom 9 && (F.getArg! 0).isConstOf ``TopCat
  return (F.appArg!, e.appArg!)

/-- `Space.mapOfTable tbl h x`: its arguments `α β L L' E E'`, its universes, its table (taken
modulo `L'.length`), and `x`. -/
def mapOfTable? (e : Expr) : MetaM (Option (Array Expr × List Level × List Nat × Expr)) := do
  unless e.isAppOfArity ``Space.mapOfTable 9 do return none
  let .const _ us := e.getAppFn | return none
  let args := e.getAppArgs
  let some (_, P') := args[3]!.listLit? | return none
  let some t ← evalNatList? args[6]! | return none
  return (args.extract 0 6, us, t.map (· % P'.length), args[8]!)

/-- Evaluate `f x`, for `f` a morphism given by a table; see `Space.reduceTableApply`. -/
partial def evalTableApply (e : Expr) : SimpM Simp.Step := do
  let some (f, x) := homApp? e | return .continue
  let some (a, rel, t) ← tableHom? f | do
    -- `f` may become one, e.g. `g ≫ h` (which `simp` would otherwise unfold before composing)
    if f.isFVar || f.isMVar then return .continue
    let rf ← Simp.simp f
    let some pf := rf.proof? | return .continue
    if rf.expr.isAppOf ``CategoryStruct.id then
      return .visit { expr := x, proof? := ← mkAppM ``Space.apply_eq_self_of_eq_id #[pf, x] }
    if (← tableHom? rf.expr).isNone then return .continue
    let pf ← mkAppM ``Space.apply_eq_of_eq #[pf, x]
    let some (_, _, e') := (← instantiateMVars (← inferType pf)).eq? | return .continue
    let r₀ : Simp.Result := { expr := e', proof? := pf }
    match ← evalTableApply e' with
    | .done r | .visit r => return .done (← r₀.mkEqTrans r)
    | .continue (some r) => return .done (← r₀.mkEqTrans r)
    | .continue none => return .done r₀
  let .const _ us := f.getAppFn | return .continue
  let rx ← Simp.simp x
  let x := rx.expr
  let e₁ := mkApp e.appFn! x
  let r₁ : Simp.Result := { expr := e₁, proof? := ← rx.proof?.mapM (mkCongrArg e.appFn! ·) }
  -- at a point
  if let some (_, _, _, _, n) ← ptLit? x then
    let some (_, P') := a[3]!.listLit? | return .continue
    let m := t.getD n 0
    let len := mkApp2 (mkConst ``List.length [0]) (mkApp (mkConst ``List [0]) a[1]!) a[3]!
    let rhs := mkApp5 (mkConst ``Space.mk us) a[1]! a[3]! a[5]! (mkNatLit m)
      (← mkDecideProof (← mkLt (mkNatLit m) len))
    unless m < P'.length do return .continue
    let pf := mkExpectedPropHint (← mkEqRefl e₁) (← mkEq e₁ rhs)
    return .done (← r₁.mkEqTrans { expr := rhs, proof? := pf })
  -- at a point of a homeomorphism (`mapOfTable`): leave it to `Space.reduceMapOfTable`
  if x.isAppOfArity ``Space.mapOfTable 9 then
    let pos ← mkDecideProof (← mkLt (mkNatLit 0) (← mkAppM ``List.length #[a[3]!]))
    let rhs := mkAppN (mkConst ``Space.mapOfTable [us[0]!, us[0]!]) #[a[0]!, a[1]!, a[2]!, a[3]!,
      a[4]!, a[5]!, toExpr t, pos, x]
    let pf := mkExpectedPropHint (← mkEqRefl e₁) (← mkEq e₁ rhs)
    return .visit (← r₁.mkEqTrans { expr := rhs, proof? := pf })
  -- a constant map, e.g. to a single point
  let some (_, P) := a[2]!.listLit? | return .continue
  let some (_, P') := a[3]!.listLit? | return .continue
  if let some m := t[0]? then
    if (List.range P.length).all (t.getD · 0 == m) then
      let (tbl, h, mono) ← if rel then
          pure (← mkAppM ``Space.Relabelling.fwd #[a[6]!],
            ← mkAppM ``Space.Relabelling.pos' #[a[6]!], ← mkAppM ``Space.Relabelling.mono #[a[6]!])
        else pure (a[6]!, a[7]!, a[8]!)
      let len ← mkAppM ``List.length #[a[3]!]
      let hm ← mkDecideProof (← mkLt (mkNatLit m) len)
      let lem := mkAppN (mkConst ``Space.homOfTable_apply_eq_of_forall [us[0]!])
        (a.extract 0 6 ++ #[tbl, h, mono, mkNatLit m, hm])
      let pf := mkApp (← mkAppDecide lem 1 fun _ => m!"not constant") x
      let rhs := mkApp5 (mkConst ``Space.mk us) a[1]! a[3]! a[5]! (mkNatLit m) hm
      unless m < P'.length do return .continue
      let pf := mkExpectedPropHint pf (← mkEq e₁ rhs)
      return .done (← r₁.mkEqTrans { expr := rhs, proof? := pf })
  -- at `g y`
  if let some (g, y) := homApp? x then
    if let some h ← composeTableHoms? g f then
      let comp ← mkAppM ``CategoryStruct.comp #[g, f]
      let pf ← mkDecideProof (← mkEq comp h)
      let pf ← if h.isAppOf ``CategoryStruct.id then
          mkAppM ``Space.apply_apply_eq_self_of_comp_eq_id #[pf, y]
        else mkAppM ``Space.apply_apply_eq_of_comp_eq #[pf, y]
      let some (_, _, rhs) := (← instantiateMVars (← inferType pf)).eq? | return .continue
      return .done (← r₁.mkEqTrans { expr := rhs, proof? := pf })
  -- elsewhere: normalize `f`
  let f' ← mkTableHom us a[0]! a[1]! a[2]! a[3]! a[4]! a[5]! rel t.toArray
  if f'.isAppOf ``CategoryStruct.id then
    let pf ← mkAppM ``Space.apply_eq_self_of_eq_id #[← mkDecideProof (← mkEq f f'), x]
    return .done (← r₁.mkEqTrans { expr := x, proof? := pf })
  -- `f` is already normal. The result is `.done`, so that `simp` doesn't visit `f x` (which would
  -- make invisible progress, beta-reducing the type argument of `DFunLike.coe`), but first `simp`'s
  -- lemmas about `f x` are tried, such as `elementwise` lemmas `f (g y) = h y` for `g` not given
  -- by a table
  if !rel || (a[6]!.isAppOf ``Space.Relabelling.mk) then
    let r? ← match ← (← Simp.getMethods).post e₁ with
      | .done r | .visit r | .continue (some r) => pure (some r)
      | .continue none => pure none
    if let some r := r? then
      if r.expr != e₁ then return .visit (← r₁.mkEqTrans r)
    return .done r₁
  let pf ← mkAppM ``Space.apply_eq_of_eq #[← mkDecideProof (← mkEq f f'), x]
  let some (_, _, rhs) := (← instantiateMVars (← inferType pf)).eq? | return .continue
  return .done (← r₁.mkEqTrans { expr := rhs, proof? := pf })

/-- `simp` evaluates a morphism given by a table (`Space.relabel σ`, or a diagram morphism
`Space.homOfTable tbl _ _`) at a point `x`: after simplifying `x`, at `pt(o)` it gives the image
point; at `g y`, with `g` also given by a table, it gives `h y` with `h` the composite `g ≫ f` (as
`Space.reduceRelabelComp` would), or `y` if that is the identity; and otherwise it leaves `f x` as
it is (rather than unfolding `f`; see `Space.reduceTableHom`), with `f` normalized as by
`Space.reduceRelabel`. A morphism `f` that `simp` turns into one given by a table, such as a
composite `g ≫ h` of them, is treated likewise. -/
simproc ↓ [simp, seval] _root_.Gavrilovich.Space.reduceTableApply
    (DFunLike.coe _ _) := evalTableApply

/-- Stop `simp` at the continuous map underlying a morphism given by a table, `f.hom`. -/
def keepTableHom (e : Expr) : SimpM Simp.Step := do
  unless e.isAppOfArity ``TopCat.Hom.hom 3 || e.isAppOfArity ``ConcreteCategory.hom 9 do
    return .continue
  let f := e.appArg!
  unless f.isAppOf ``Space.relabel || f.isAppOf ``Space.homOfTable do return .continue
  let some _ ← tableHom? f | return .continue
  return .done { expr := e }

/-- `simp` leaves the continuous map underlying a morphism given by a table (`Space.relabel σ`,
or a diagram morphism `Space.homOfTable tbl _ _`) as it is, rather than unfolding it, so that
`Space.reduceTableApply` can evaluate it. -/
simproc ↓ [simp, seval] _root_.Gavrilovich.Space.reduceTableHom (TopCat.Hom.hom _) := keepTableHom

/-- `Space.reduceTableHom`, for `ConcreteCategory.hom`. -/
simproc ↓ [simp, seval] _root_.Gavrilovich.Space.reduceTableConcreteHom
    (ConcreteCategory.hom (C := TopCat) _) :=
  keepTableHom

/-- `simp` composes `Space.mapOfTable` (which `Space.relabelHomeo` evaluates to) with itself, and
with morphisms given by tables (as `Space.reduceTableApply` does for morphisms), and removes it
when it is the identity. -/
simproc [simp, seval] _root_.Gavrilovich.Space.reduceMapOfTable
    (Space.mapOfTable _ _ _) := fun e => do
  let some (a, us, t, x) ← mapOfTable? e | return .continue
  -- the inner map, as `mapOfTable`
  let inner? : Option (Array Expr × List Level × List Nat × Expr) ← do
    if let some r ← mapOfTable? x then pure (some r)
    else if let some (g, y) := homApp? x then
      let some (b, _, t') ← tableHom? g | pure none
      let .const _ vs := g.getAppFn | pure none
      pure (some (b.extract 0 6, [vs[0]!, vs[0]!], t', y))
    else pure none
  if let some (b, vs, t', y) := inner? then
    let ρ := t'.map fun i => t.getD i 0
    let pos (L : Expr) : MetaM Expr := do
      mkDecideProof (← mkLt (mkNatLit 0) (← mkAppM ``List.length #[L]))
    -- (`x` is `mapOfTable t' _ y` by definition, if it isn't already)
    let lem := mkAppN (mkConst ``Space.mapOfTable_mapOfTable [vs[0]!, us[0]!, us[1]!])
      #[b[0]!, b[1]!, b[2]!, b[3]!, b[4]!, b[5]!, a[1]!, a[3]!, a[5]!, toExpr t, toExpr t',
        toExpr ρ, ← pos a[3]!, ← pos b[3]!, ← pos a[3]!]
    let pf := mkApp (← mkAppDecide lem 1 fun _ => m!"invalid composite {ρ}") y
    let rhs := mkAppN (mkConst ``Space.mapOfTable [vs[0]!, us[1]!])
      #[b[0]!, a[1]!, b[2]!, a[3]!, b[4]!, a[5]!, toExpr ρ, ← pos a[3]!, y]
    let pf := mkExpectedPropHint pf (← mkEq e rhs)
    return .visit { expr := rhs, proof? := pf }
  -- the identity
  if a[0]! == a[1]! && a[2]! == a[3]! && a[4]! == a[5]! && us[0]! == us[1]! &&
      t == List.range t.length then
    let lem := mkAppN (mkConst ``Space.mapOfTable_eq_self [us[0]!])
      #[a[0]!, a[2]!, a[4]!, e.getArg! 6, e.getArg! 7]
    let pf := mkApp (← mkAppDecide lem 1 fun _ => m!"not the identity") x
    return .visit { expr := x, proof? := pf }
  return .continue

/-- The syntax `x` for the name of a point `n`, as in `pt(x)`. -/
def gavNameStx (n : String) : MetaM (TSyntax ``gavName) := do
  if !n.isEmpty && n.all Char.isDigit then `(gavName| $(Syntax.mkNumLit n):num)
  else if isIdentName (← getEnv) n then `(gavName| $(mkIdent (.mkSimple n)):ident)
  else `(gavName| $(Syntax.mkStrLit n):str)

open PrettyPrinter.Delaborator SubExpr in
/-- Print `Space.relabel σ` for a literal relabelling `σ` as plain `Space.relabel` if `σ` is the
canonical relabelling (the one that `gav_relabel` finds), and otherwise as `relabel[x ↦ o, …]`,
listing the image of every point (by its first name). Likewise for `Space.relabelIso` and
`Space.relabelHomeo`. -/
@[delab app.Gavrilovich.Space.relabel,
  delab app.Gavrilovich.Space.relabelIso,
  delab app.Gavrilovich.Space.relabelHomeo]
def delabRelabel : Delab := whenNotPPOption getPPExplicit do
  let e ← getExpr
  let .const c _ := e.getAppFn | failure
  let some (args, t) ← relabelTable? e c | failure
  guard (args[6]!.isAppOf ``Space.Relabelling.mk)
  if let some c ← canonicalRelabelling? args[2]! args[4]! args[3]! args[5]! then
    if c.toList == t then return ← withNaryFn delabConst
  guard (← ptNotationOpen)
  let (some P, some P') := (decodePoints args[2]!, decodePoints args[3]!) | failure
  let rs ← t.zipIdx.toArray.mapM fun (j, i) => do
    let (some (x :: _), some (y :: _)) := (P[i]?, P'[j]?) | failure
    `(gavRenaming| $(← gavNameStx x) ↦ $(← gavNameStx y))
  match c with
  | ``Space.relabelIso => `(relabelIso[$rs,*])
  | ``Space.relabelHomeo => `(relabelHomeo[$rs,*])
  | _ => `(relabel[$rs,*])

@[term_elab Gavrilovich.gavRelabelling, inherit_doc gavRelabelling]
def elabGavRelabelling : TermElab := fun stx expected? => do
  let `(gav_relabelling%[$rs,*]) := stx | throwUnsupportedSyntax
  let some goal := expected? | throwError "gav_relabelling%: the expected type must be known"
  let goal ← instantiateMVars goal
  let goal := if goal.isAppOfArity ``autoParam 2 then goal.getArg! 0 else goal
  let_expr Space.Relabelling _ _ L E L' E' := goal |
    throwError "gav_relabelling%: the expected type isn't of the form \
      `Space.Relabelling L E L' E'`{indentExpr goal}"
  let (knownA, knownB) := (!L.hasExprMVar && !E.hasExprMVar, !L'.hasExprMVar && !E'.hasExprMVar)
  if knownA && knownB then return ← relabellingFor goal rs.getElems
  -- a renaming of all of the points of one space determines the other
  if knownA || knownB then
    if let some r ← observing? (relabellingFor goal rs.getElems) then return r
  tryPostpone
  if knownA || knownB then relabellingFor goal rs.getElems (isPartial := true)
  else elabTerm (← `(by gav_relabel [$rs,*])) goal

macro_rules
  | `(relabel[$rs,*]) => `(Space.relabel (gav_relabelling%[$rs,*]))
  | `(relabelIso[$rs,*]) => `(Space.relabelIso (gav_relabelling%[$rs,*]))
  | `(relabelHomeo[$rs,*]) => `(Space.relabelHomeo (gav_relabelling%[$rs,*]))

end Mathlib.Tactic.Gavrilovich

end
