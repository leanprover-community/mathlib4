/-
Copyright (c) 2026 Robert Maxton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Maxton
-/
module

public import Lean.Elab.Term
public import Lean.PrettyPrinter.Delaborator.Basic
public import Mathlib.Tactic.Gavrilovich.Parser
public import Mathlib.Topology.Gavrilovich.Space

/-!
# Gavrilovich diagrams: finite spaces drawn as boxes

A finite topological space can be written inline as a one-box diagram, in the style of
Gavrilovich's papers on lifting properties: `⌜o → c⌟` is the Sierpiński space, as an object of
`TopCat`.
* A single box elaborates to a `Gavrilovich.Space`, an object of `TopCat`. Inside a box, `x → y`
  means that `y` is in the closure of `x`, i.e. `x ⤳ y`. `a=b` is a single point with two names.
  Drawings of the same space give syntactically equal terms, so for example `⌜o → c⌟ = ⌜c ← o⌟`
  holds by `rfl`.
* Spaces are printed as one-row diagrams, e.g. `⌜o → c⌟`, when their specialization order can be
  drawn that way (`oneRow`); every printed diagram is checked to elaborate back to the same term,
  and otherwise `Space L E` is printed. Set `pp.gavDiagrams` to `false` to always print `Space L E`.

The layout rules are documented in `Mathlib.Tactic.Gavrilovich.Grid`. Morphisms between boxes,
multi-row boxes, points `pt(o)` and more are in `Mathlib.Tactic.Gavrilovich.Elab.Full`; tactics
for diagram spaces are in `Mathlib.Tactic.Gavrilovich.Tactics`.
-/

public meta section

namespace Mathlib.Tactic.Gavrilovich
open _root_.Gavrilovich
open Lean Elab Term Meta


/-- A finite space (one box), a continuous map between two of them (two boxes joined by a
dashed connective), or the type of morphisms between a box and a term, drawn as a 2D diagram.
See `Mathlib.Tactic.Gavrilovich.Grid` for the layout rules. -/
syntax:max (name := gavDiagram) diagram : term

/-! ### Elaboration -/

/-- A synthetic syntax node spanning the byte range of `e`, to put an error message on. -/
def errStx (e : Err) : Syntax := .atom (.synthetic ⟨e.start⟩ ⟨e.stop⟩) ""

/-- Rethrow a positioned layout error in `TermElabM`. -/
def liftErr {α} : Except Err α → TermElabM α
  | .ok a => pure a
  | .error e => throwErrorAt (errStx e) e.msg

/-- The space denoted by a box, in the universe `u?` if given (for `D.{u}`). -/
def boxTerm (c : Canon) (u? : Option (TSyntax `level) := none) : TermElabM Term := do
  let t ← `(Space $(quote c.L) $(quote c.E))
  match u? with
  | some u => `(($t : TopCat.{$u}))
  | none => pure t

/-- The first atom of `stx`, whether or not it has a position (unlike `Syntax.getHead?`). -/
partial def firstAtom? : Syntax → Option Syntax
  | s@(.atom ..) => some s
  | .node _ _ args => args.findSome? firstAtom?
  | _ => none

/-- Decode a literal `List (List String)`. -/
def decodePoints (e : Expr) : Option (List (List String)) := do
  (← e.listLit?).2.mapM fun l => do
    (← l.listLit?).2.mapM fun | .lit (.strVal s) => some s | _ => none

/-- Decode a literal `List (ℕ × ℕ)`. -/
def decodeEdges (e : Expr) : Option (List (Nat × Nat)) := do
  (← e.listLit?).2.mapM fun p => do
    guard (p.isAppOfArity ``Prod.mk 4)
    let nat (e : Expr) := e.nat? <|> e.rawNatLit?
    return (← nat (p.getArg! 2), ← nat (p.getArg! 3))

/-- Ascriptions `(=…)` and holes `_` are only for the boxes of a morphism: elsewhere, they are an
error. -/
def checkNoAscriptions (bd : BoxD) : TermElabM Unit := do
  if let some l := bd.labels.find? (·.ascribed) then
    liftErr (.error (l.err "ascriptions `(=…)` are only for the boxes of a morphism, whose \
      points are matched by the names before them"))
  if let some l := bd.labels.find? (·.names.any isHoleName) then
    liftErr (.error (l.err "`_` is a point named by the expected type of a morphism, so it is \
      only for the boxes of a morphism"))

/-- Elaborate the diagram `stx`: currently, a single box (a space). -/
def elabDiagramBasic : TermElab := fun stx expected? => do
  let some (.atom (.original _ pos _ _) _) := firstAtom? stx | throwUnsupportedSyntax
  let text := (← getFileMap).source
  let blk ← liftErr (scanBlock text pos.byteIdx)
  let d ← liftErr blk.read
  unless d.colon.isNone && d.boxes.size == 1 && d.nodes.isEmpty && d.links.isEmpty do
    throwErrorAt stx "a diagram must currently be a single box (a space)"
  checkNoAscriptions d.boxes[0]!
  elabTerm (← boxTerm (canon d.boxes[0]!)) expected?

@[term_elab gavDiagram, inherit_doc gavDiagram]
def elabDiagram : TermElab := elabDiagramBasic

/-! ### Delaboration -/

/-- Print `Space L E` as a one-row Gavrilovich diagram, and `Space.pt "o"` as `pt(o)`, when
possible. -/
register_option pp.gavDiagrams : Bool := {
  defValue := true
  descr := "(pretty printer) print `Space L E` as a one-row Gavrilovich diagram, and \
    `Space.pt \"o\"` as `pt(o)`, when possible"
}

/-- Lay out the space with points `L` and specialization closure `E` on one row, if possible:
that is, if the Hasse diagram of its specialization order (with equivalent points merged) is a
disjoint union of paths. Point `i` is drawn as `label i`. -/
def oneRow (L : List (List String)) (E : List (Nat × Nat))
    (label : Nat → String := fun i => "=".intercalate L[i]!) : Option String := do
  let n := L.length
  let le (i j : Nat) : Bool := i == j || E.contains (i, j)
  -- the least point equivalent to each point represents its class
  let rep : Array Nat := (Array.range n).map fun i => ((List.range n).find? fun j =>
    le i j && le j i).getD i
  let reps := (List.range n).filter fun i => rep[i]! == i
  let lt (a b : Nat) : Bool := a != b && le a b
  let covers := reps.flatMap fun a =>
    (reps.filter fun b => lt a b && !reps.any fun k => lt a k && lt k b).map (a, ·)
  let nbrs (a : Nat) : List Nat :=
    covers.filterMap fun (x, y) => if x == a then some y else if y == a then some x else none
  guard (reps.all fun a => (nbrs a).length ≤ 2)
  -- walk each path from its least endpoint
  let mut seen : List Nat := []
  let mut paths : List (List Nat) := []
  for a in reps do
    if seen.contains a || (nbrs a).length == 2 then continue
    let mut path := [a]
    for _ in [0:n] do
      match (nbrs path.head!).filter (!path.contains ·) with
      | [b] => path := b :: path
      | _ => break
    path := path.reverse
    -- prefer the first arrow to point right
    if path.length ≥ 2 && !lt path[0]! path[1]! && lt path.getLast! path[path.length - 2]! then
      path := path.reverse
    seen := seen ++ path
    paths := paths ++ [path]
  -- anything unseen lies on a cycle
  guard (reps.all seen.contains)
  let cls (a : Nat) := " ↔ ".intercalate <| ((List.range n).filter (rep[·]! == a)).map label
  let draw (path : List Nat) : String := Id.run do
    let mut out := cls path[0]!
    for (a, b) in path.zip path.tail do
      out := out ++ (if lt a b then " → " else " ← ") ++ cls b
    return out
  return "⌜" ++ "  ".intercalate (paths.map draw) ++ "⌟"

/-- Does the diagram `text` (one box) elaborate to `Space L E`? -/
def roundTrips (text : String) (L : List (List String)) (E : List (Nat × Nat)) : Bool :=
  match scanBlock text 0 >>= Block.read with
  | .ok d => d.boxes.size == 1 && d.links.isEmpty && d.nodes.isEmpty &&
      (canon d.boxes[0]!).L == L && (canon d.boxes[0]!).E == E
  | .error _ => false

open PrettyPrinter.Delaborator SubExpr in
/-- Print `Space L E` as a one-row diagram, when there is one that elaborates back to it. -/
@[delab app.Gavrilovich.Space]
def delabSpace : Delab := whenPPOption (pp.gavDiagrams.get ·) <| whenNotPPOption getPPExplicit do
  let e ← getExpr
  guard (e.getAppNumArgs == 3)
  let some L := decodePoints (e.getArg! 1) | failure
  let some E := decodeEdges (e.getArg! 2) | failure
  let some text := oneRow L E | failure
  guard (roundTrips text L E)
  return ⟨.node .none ``gavDiagram #[.atom .none text]⟩

open PrettyPrinter.Delaborator SubExpr in
/-- Print the type of points `↑(Space L E)` as the diagram of `Space L E`, without the `↑` (as a
type, the diagram elaborates back to `↑(Space L E)`). -/
@[delab app.TopCat.carrier]
def delabSpaceCarrier : Delab := do
  let e ← getExpr
  guard (e.getAppNumArgs == 1 && e.appArg!.isAppOfArity ``Space 3)
  let stx ← withAppArg delab
  guard (stx.raw.isOfKind ``gavDiagram)
  return stx

end Mathlib.Tactic.Gavrilovich

end
