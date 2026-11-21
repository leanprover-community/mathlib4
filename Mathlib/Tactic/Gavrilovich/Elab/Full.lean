/-
Copyright (c) 2026 Robert Maxton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Maxton
-/
module

public meta import Mathlib.Control.Traversable.Basic
public import Mathlib.Tactic.Gavrilovich.Tactics
public import Mathlib.Topology.Gavrilovich.Model

/-!
# Gavrilovich diagrams: morphisms, multi-row boxes, points, models

Finite topological spaces, and continuous maps between them, can be written inline as diagrams,
in the style of Gavrilovich's papers on lifting properties:
```
def q :=
    ⌜a   b⌝      ⌜ a=b ⌝
      ↘ ↙    ⇢      ↓
    ⌞  c  ⌟      ⌞  c  ⌟
```
* A single box elaborates to a `Gavrilovich.Space`, an object of `TopCat`. Inside
  a box, `x → y` means that `y` is in the closure of `x`, i.e. `x ⤳ y`. `a=b` is a single point
  with two names. Drawings of the same space give syntactically equal terms, so for example
  `⌜o → c⌟ = ⌜c ← o⌟` holds by `rfl`.
* Two boxes joined by a dashed connective `⇢ ⇠ ⇣ ⇡` elaborate to a morphism in `TopCat`. Points
  are matched by name (a point with several names, `a=b`, goes where any of its names is found),
  and continuity is checked (with a readable error) and proved by `decide`.
* Following Gavrilovich, the target box can be labelled by the names of the source points: the
  names in a box need not be the names of its space. A label can end with an *ascription*
  `(=…)` giving its point's names in the space, while the names before it only match it with the
  points of the other box. So
  ```
  def toSierpinski : ⌜a  b⌟ ⟶ ⌜o → c⌟ := ⌜a  b⌟ ⇢ ⌜a(=o) → b(=c)⌟
  ```
  maps `a` to `o` and `b` to `c`, as does `⌜x(=a)  y(=b)⌟ ⇢ ⌜x(=o) → y(=c)⌟`. A name can be the
  name of one point and match another, as in the swap `⌜a  b⌟ ⇢ ⌜b(=a)  a(=b)⌟`, and `_` matches
  nothing, as in `⌜a⌟ ⇢ ⌜a(=b) → _(=a)⌟` (where the name `a` would otherwise be taken twice).
* If the expected type of a morphism is `X ⟶ Y` for spaces `X`, `Y` with the same shapes as the
  boxes but different names, the morphism is relabelled to it, so ascriptions are only needed
  where the shapes leave a choice:
  ```
  def toSierpinski' : ⌜a  b⌟ ⟶ ⌜o → c⌟ := ⌜a  b⌟ ⇢ ⌜a → b⌟
  ```
  The relabelling of each box keeps as many names as possible. Without ascriptions, all names
  choose it as well as they can (so `⌜a  b⌟ ⇢ ⌜b=x  a=y⌟ : _ ⟶ ⌜x  y⌟` maps `b` to `x`). Once
  any point of the morphism has an ascription, the plain names in the target box only match
  points of the source box, whatever their names in the target space, so only ascriptions choose
  its relabelling: in `⌜o₀ → c₀ ← o₁ → c₁ ← o₂⌟ ⇢ ⌜o₀ → c₀ ← o₁(=o₂) → c₁=o₂⌟` of type
  `_ ⟶ ⌜o₁ → c₁ ← o₂ → c₂⌟`, the last point is `c₂`. If that leaves a choice that changes the
  map, it is an error, and ascribed names must be the names of their points in the expected
  spaces. (Plain names are names in the space only in a box that keeps its own names, because the
  type doesn't say which space it is.) A bare `_` is a point that matches nothing and is
  named only by the expected type, so a box can have several, as in
  `⌜a⌟ ⇢ ⌜_ → a ← _⌟ : _ ⟶ ⌜o₁ → c ← o₂⌟`.
* A box joined by a dashed connective to an ordinary term `X : TopCat` elaborates to the *type*
  of morphisms between them, `Space L E ⟶ X` or `X ⟶ Space L E`:
  ```
  let f :
      ⌜a   b⌝
        ↘ ↙    ⇢ X
      ⌞  c  ⌟      := ...
  ```
  Inside a block, a term extends along its row up to two consecutive spaces. After the last box
  of a block (in particular, for one-row boxes), `⇢` is an infix notation for `⟶` that requires
  one side to be a diagram: `⌜a b⌟ ⇢ X` and `X ⇢ ⌜a b⌟`.
* `D.{u}`, right after the last `⌟` of a diagram `D`, puts its spaces in the universe `u`:
  `⌜o → c⌟.{u}` is `(⌜o → c⌟ : TopCat.{u})`, and `(⌜a b⌟ ⇢ ⌜x y⌟.{u})` is a morphism of
  `TopCat.{u}`. It is never printed.
* `pt(o)` is the point named `o` (scoped to `Mathlib.Tactic.Gavrilovich`), in its canonical form
  `Space.mk k _`, so that lemmas stated with it can be `@[simp]` lemmas. It also works as a
  pattern, so maps out of a space can be written `fun | pt(o) => x | pt(c) => y`. For names of
  other types, there is `pt[n]`, e.g. `pt[("a", 1)]`.
* `Space.hom f` is the morphism given by a function `f` between the points of two spaces, with
  continuity checked automatically, e.g. `Space.hom fun | pt(a) => pt(o) | pt(b) => pt(c)`.
* `gav_decide` is `decide`, but accepts goals containing universe metavariables, such as goals
  about diagrams inside the body of a universe-polymorphic definition.

Spaces are printed as diagrams: on one row if their specialization order can be drawn that way,
e.g. `⌜o → c⌟`, and otherwise as a multi-row box (found by a small search, with each class of
equivalent points on the row of its height), which starts on a new line so that its corners stay
aligned. Diagram morphisms are printed as `(⌜…⌟ ⇢ ⌜…⌟)` in Gavrilovich's convention, with the
names of the target ascribed where they differ, as in `(⌜a  b⌟ ⇢ ⌜a(=o) → b(=c)⌟)`. Every printed
diagram is checked to elaborate back to the same term; when there is none, `Space L E` and
`Space.homOfTable tbl _ _` are printed instead. Set `pp.gavDiagrams` to `false` to always print
those.

The layout rules are documented in `Mathlib.Tactic.Gavrilovich.Grid`. This file extends the
elaborator and delaborators of `Mathlib.Tactic.Gavrilovich.Elab.Basic`, which handle one-box,
one-row diagrams.

Labels are part of the type, so `f ≫ g` typechecks exactly when the labels line up, and
relabelling is an explicit isomorphism (`Space.relabel`, in
`Mathlib.Tactic.Gavrilovich.Relabel`), or
done when elaborating a morphism, as above. (Treating `=` gluing specially in targets was
rejected, because then a box elaborated as a target would have a different type from the same box
written alone; ascriptions `(=…)` are explicit, and an error in a box alone.)

## TODO

* Squares and lifting problems: four boxes with four connectives in a square should elaborate to
  a `CommSq`, and a diagonal (a new dashed glyph) to `CommSq.HasLift`.
* Maps from a box into a term `X`, as morphism terms rather than types (`a ↦ x` beside the
  connective? a side table?).
* Editor support: give each label synthetic `SourceInfo` covering its byte range and add term info
  (for hover and go-to-definition). Check `diagram.formatter` on a multi-line atom.
* Audit the glyph allowlists against common editor fonts, dropping anything not exactly one
  column wide.
-/

public meta section

namespace Mathlib.Tactic.Gavrilovich
open _root_.Gavrilovich
open Lean Elab Term Meta


/-- `D.{u}`, for a diagram `D`, puts its spaces in the universe `u`: `⌜o → c⌟.{u}` is
`(⌜o → c⌟ : TopCat.{u})`, and likewise for morphisms and types of morphisms. There is no space
before `.{`, which follows the last `⌟` of the diagram. -/
@[term_parser] def gavDiagramUniv : Lean.Parser.TrailingParser := trailing_parser
  Lean.Parser.checkStackTop (·.isOfKind ``gavDiagram) "expected preceding diagram" >>
  Lean.Parser.checkNoWsBefore "no space before '.{'" >> ".{" >> Lean.Parser.levelParser >> "}"

/-- `A ⇢ X`, where `A` or `X` is a diagram, is the type `A ⟶ X` of morphisms. (Inside a diagram,
`⇢` is a connective; this is the notation for the same arrow after the last box of a diagram.) -/
syntax:10 (name := gavHom) term:11 " ⇢ " term:10 : term

macro_rules (kind := gavHom)
  | `($a ⇢ $b) => do
    let isDiagram (t : Term) := t.raw.isOfKind ``gavDiagram || t.raw.isOfKind ``gavDiagramUniv
    unless isDiagram a || isDiagram b do
      Macro.throwError "`⇢` is only for Gavrilovich diagrams; use `⟶` for morphisms in general"
    `($a ⟶ $b)

end Mathlib.Tactic.Gavrilovich

namespace Gavrilovich
/-- `pt(o)` is the point named `o` of a diagram space. Names that aren't identifiers can be given
as numerals, `pt(0)`, or as strings, `pt("a*")`. This notation is scoped to
`Mathlib.Tactic.Gavrilovich`.

As a term, `pt(o)` elaborates to the canonical form `Space.mk k _` of the point, where `k` is its
index (`gav_pt_lt%`), so that lemmas stated with `pt(o)` can be `@[simp]` lemmas. This needs the
space to be known, possibly only later in elaboration.

`pt(o)` can also be used as a pattern, e.g. `fun | pt(o) => x | pt(c) => y`, where it is
`Space.pt "o" _`, which unfolds to the constructor with index `L.findIdx ("o" ∈ ·)`: patterns can't
wait for the space to be known.

Since a macro can't tell whether it is expanding a pattern, `pt(o)` expands to a choice node with
both alternatives, each of which fails to elaborate in the other mode. -/
scoped syntax (name := gavPt) "pt(" (ident <|> num <|> str) ")" : term
end Gavrilovich

namespace Mathlib.Tactic.Gavrilovich
open _root_.Gavrilovich
open Lean Elab Term Meta

end Mathlib.Tactic.Gavrilovich

namespace Gavrilovich
/-- `pt[n]` is the point named `n` of a space whose names have any type, e.g. `pt[("a", 1)]`. Like
`pt(o)`, it can be used as a pattern, and it is scoped to `Mathlib.Tactic.Gavrilovich`. -/
scoped syntax (name := gavPtTerm) "pt[" term "]" : term
end Gavrilovich

namespace Mathlib.Tactic.Gavrilovich
open _root_.Gavrilovich
open Lean Elab Term Meta

/-- `gav_pt_mem n` proves the side condition of `Space.pt n`, that the space has a point named
`n`, by `decide`, with a readable error if it doesn't. -/
syntax (name := gavPtMem) "gav_pt_mem " term:max : tactic

/-- `gav_pt_lt% n`, as the proof `h` in `Space.mk _ h : Space L E` (outside patterns), assigns the
index of the point named `n` to the placeholder `_`, once `L` is known, and proves `h` by
`decide`. In a pattern it fails, which selects the other alternative of `pt(n)`. -/
syntax (name := gavPtLt) "gav_pt_lt% " term:max : term

/-- `gav_pt_pat% n` is `by gav_pt_mem n` in a pattern, and fails elsewhere, which selects the
other alternative of `pt(n)`. -/
syntax (name := gavPtPat) "gav_pt_pat% " term:max : term

/-- `gav_pt_model% n`, at a type `X` (other than a diagram space) with a `Model`, is the point of
`X` named `n`, as listed in `Model.pts` (e.g. `True` for `pt(T) : Prop`). It fails at any other
expected type (without postponing), and in patterns, which selects another alternative of
`pt(n)`. -/
syntax (name := gavPtModel) "gav_pt_model% " term:max : term

/-- The expansion of `pt(n)` and `pt[n]`: a choice between the pattern `Space.pt n _`, the term
`Space.mk _ _` (a point of a diagram space), and a point of a model (`gav_pt_model%`), of which
exactly one elaborates. (The last is inaccessible only so that it is a valid pattern, to be
rejected when elaborated; outside patterns, `simp` ignores the annotation.) -/
def ptChoice (n : Term) : MacroM Term := do
  let pat ← `(Space.pt $n .(gav_pt_pat% $n))
  let term ← `(Space.mk _ .(gav_pt_lt% $n))
  let model ← `(.(gav_pt_model% $n))
  return ⟨mkNode choiceKind #[pat, term, model]⟩

macro_rules (kind := Gavrilovich.gavPtTerm)
  | `(pt[$n]) => ptChoice n

macro_rules (kind := Gavrilovich.gavPt)
  | `(pt($x:ident)) => ptChoice (Syntax.mkStrLit (x.getId.toString (escape := false)))
  | `(pt($n:num)) => ptChoice (Syntax.mkStrLit ((n.raw.isLit? numLitKind).getD ""))
  | `(pt($s:str)) => ptChoice s

/-! ### Elaboration -/

/-- The display name of the `i`-th canonical point, e.g. `a=b`. -/
def ptName (c : Canon) (i : Nat) : String := "=".intercalate (c.L[i]!.map displayName)

/-- Does the box with canonical form `c` have a hole `_`? -/
def Canon.hasHole (c : Canon) : Bool := c.L.any (·.any isHoleName)

/-- The error for a hole `_` in the box `bd` that the expected type doesn't name. -/
def holeErr {α} (bd : BoxD) : TermElabM α := do
  let some l := bd.labels.find? (·.names.any isHoleName) | throwError "internal: no hole"
  throwErrorAt (errStx (l.err "")) "can't tell the name of this point `_` in its space: give \
    the morphism a type that says which space this box is, or name it, as in `_(=o)`"

/-- The text that a diagram was read from: the file itself, when the diagram's syntax comes from
it, and otherwise (e.g. for syntax made by a quotation) the text of the diagram's atom, which is
`virtual`. -/
structure DiagramSource where
  /-- The text. -/
  text : String
  /-- Byte offset of the diagram's first `⌜` in `text`. -/
  start : Nat
  /-- Is `text` made up, so that its positions are not positions in the file? -/
  virtual : Bool

/-- The text of a diagram whose syntax doesn't come from the file: its atom, with its first row
indented as in the source, so that its corners line up. That indentation is lost, so it is taken
to be that of the leftmost `⌞`, which lines up with the first `⌜` (unless the first box has a
single row). -/
def virtualSource (text : String) : DiagramSource :=
  let rows := (text.splitOn "\n").drop 1
  let cols := rows.filterMap fun row =>
    (row.toList.findIdx? fun ch => cornerKind? ch == some 2)
  let col0 := cols.foldl min (cols.headD 0)
  { text := String.ofList (List.replicate col0 ' ') ++ text, start := col0, virtual := true }


/-- Give every node of `stx` the source info `info`. -/
partial def setInfoDeep (info : SourceInfo) : Syntax → Syntax
  | .node _ k args => .node info k (args.map (setInfoDeep info))
  | .atom _ v => .atom info v
  | .ident _ r n p => .ident info r n p
  | s => s

/-- Parse the text of a node as a term. The parser runs on the file itself, so that positions in
the term (for error messages, hovers, …) are right. (For a virtual source, the term gets the
position of the diagram instead.) -/
def parseNode (src : DiagramSource) (n : Node) : TermElabM Term := do
  let input := String.Pos.Raw.extract src.text 0 ⟨n.stop⟩
  let env ← getEnv
  let ictx := Parser.mkInputContext input (← getFileName) (normalizeLineEndings := false)
  let pmctx : Parser.ParserModuleContext :=
    { env, options := ← getOptions, currNamespace := ← getCurrNamespace,
      openDecls := ← getOpenDecls }
  let s := (Parser.categoryParser `term 0).fn.run ictx pmctx (Parser.getTokenTable env)
    { Parser.mkParserState input with pos := ⟨n.start⟩ }
  if let some (pos, _, err) := s.allErrors[0]? then
    throwErrorAt (errStx ⟨pos.byteIdx, n.stop, ""⟩) (toString err)
  unless s.pos.byteIdx == n.stop do
    throwErrorAt (errStx ⟨s.pos.byteIdx, n.stop, ""⟩) "expected a single term"
  if src.virtual then return ⟨setInfoDeep (SourceInfo.fromRef (← getRef)) s.stxStack.back⟩
  return ⟨s.stxStack.back⟩

/-! ### Relabelling -/

/-- The order of a space with `n` points and edges `E` (the reflexive-transitive closure of `E`),
as a matrix. -/
def leMatrix (n : Nat) (E : List (Nat × Nat)) : Array (Array Bool) := Id.run do
  let mut m := Array.ofFn (n := n) fun i => Array.ofFn (n := n) fun j =>
    i.val == j.val || E.contains (i.val, j.val)
  for k in [0:n] do
    for i in [0:n] do
      if (m[i]!)[k]! then
        for j in [0:n] do
          if (m[k]!)[j]! then m := m.modify i (·.set! j true)
  return m

/-- Extend the partial isomorphism `σ` (the images of the first `σ.size` points) between the orders
`le` and `le'` in all possible ways, trying the candidates `pref i` for the image of point `i` in
order, and add the results to `acc` (up to `limit` of them). -/
partial def extendIsos (le le' : Array (Array Bool)) (pref : Nat → List Nat) (limit : Nat)
    (σ : Array Nat) (acc : Array (Array Nat)) : Array (Array Nat) :=
  let i := σ.size
  if acc.size ≥ limit then acc
  else if i == le.size then acc.push σ
  else (pref i).foldl (init := acc) fun acc j =>
    if σ.contains j then acc
    else if (List.range i).all fun k =>
        (le[k]!)[i]! == (le'[σ[k]!]!)[j]! && (le[i]!)[k]! == (le'[j]!)[σ[k]!]! then
      extendIsos le le' pref limit (σ.push j) acc
    else acc

/-- All isomorphisms (as tables of indices) from the space with points `P` and edges `E` to the
space with points `P'` and edges `E'` that send the `i`-th point to `fixed[i]` (where that is
given), each with its score: the number of points whose image shares a name with it. They are
sorted by score, highest first, and otherwise in order (of the tables). -/
def relabellingsCore {α : Type} [BEq α] (P P' : List (List α)) (E E' : List (Nat × Nat))
    (fixed : Array (Option Nat) := #[]) (limit := 5040) : Array (Array Nat × Nat) :=
  let n := P.length
  if P'.length != n then #[] else
  let shares (i j : Nat) : Bool := P[i]!.any (P'[j]!.contains ·)
  let pref (i : Nat) : List Nat :=
    if let some (some j) := fixed[i]? then [j] else
    let same := (List.range n).filter (shares i)
    same ++ (List.range n).filter (!same.contains ·)
  let score (σ : Array Nat) : Nat := (List.range n).countP fun i => shares i σ[i]!
  let σs := extendIsos (leMatrix n E) (leMatrix n E') pref limit #[] #[]
  (σs.zipIdx.qsort fun (σ, i) (τ, j) =>
    score σ > score τ || (score σ == score τ && i < j)).map fun (σ, _) => (σ, score σ)

/-- The decomposition `(u, α, L, E)` of a space `Space.{u} L E`, unfolding definitions (such as
`def Sierpinski := ⌜o → c⌟`) to get there. -/
partial def spaceObj? (X : Expr) : MetaM (Option (Level × Expr × Expr × Expr)) := do
  let X := (← instantiateMVars X).consumeMData
  if let .const ``Space [u] := X.getAppFn then
    return if X.getAppNumArgs == 3 then some (u, X.getArg! 0, X.getArg! 1, X.getArg! 2) else none
  let some X ← unfoldDefinition? X | return none
  spaceObj? X

/-- The table of the morphism `src ⇢ tgt` (from canonical source indices to canonical target
indices), matching points by name: a point goes to the target point that has its names (those of
its names that the target has, that is). Names in ascriptions `(=…)` don't count: they are the
names of points in their spaces. Checks that this is a continuous function. -/
def morphismTable (src tgt : BoxD) : TermElabM (Canon × Canon × Array Nat) := do
  let cs := canon src; let ct := canon tgt
  let matchT := canonMatchNames tgt ct
  let mut tbl := Array.replicate cs.L.length 0
  for h : li in [0:src.labels.size] do
    let l := src.labels[li]
    let mut img : Option Nat := none
    for n in l.matchNames do
      let some k := matchT.findIdx? (·.contains n) | continue
      if let some k' := img then
        if k' != k then
          liftErr (.error (l.err s!"the names of '{l.text}' land on different target points \
            ('{ptName ct k'}' and '{ptName ct k}'), so this isn't a function"))
      img := some k
    let some k := img | liftErr (.error (l.err <| match l.matchNames with
      | [] => s!"'{l.text}' has no name to find its image in the target box by"
      | [n] => s!"no point named '{n}' in the target box"
      | _ => s!"none of the names of '{l.text}' are in the target box"))
    tbl := tbl.set! cs.perm[li]! k
  -- continuity, checked here so the error is readable; the kernel re-checks via `decide`
  for (i, j) in cs.E do
    let fi := tbl[i]!; let fj := tbl[j]!
    unless fi == fj || ct.E.contains (fi, fj) do
      liftErr (.error (src.box.err s!"not continuous: {ptName cs i} → {ptName cs j} in the \
        source, but no {ptName ct fi} → {ptName ct fj} in the target"))
  return (cs, ct, tbl)

/-- The morphism `Space.homOfTable tbl _ _ : A ⟶ B`. -/
def homOfTableStx (tbl : Array Nat) (A B : Term) : TermElabM Term :=
  -- the side conditions are proved by `decide` in term mode, rather than by `by decide` blocks:
  -- those are elaborated last, and if the morphism is unified with another first (say, in
  -- instance synthesis), they find their goals already assigned
  `((Space.homOfTable $(quote tbl.toList) (of_decide_eq_true (Eq.refl true))
    (of_decide_eq_true (Eq.refl true)) : $A ⟶ $B))

/-- An instance `Model X L E`, with the arguments of `Model`. -/
structure ModelInfo where
  /-- The universe of `X`. -/
  u : Level
  /-- The type that is modelled. -/
  X : Expr
  /-- Its topology. -/
  top : Expr
  /-- The type of names. -/
  α : Expr
  /-- The points of the diagram space. -/
  L : Expr
  /-- The edges of the diagram space. -/
  E : Expr
  /-- The instance. -/
  inst : Expr

/-- The arguments `X top α L E inst` shared by the fields of `Model`. -/
def ModelInfo.args (m : ModelInfo) : Array Expr := #[m.X, m.top, m.α, m.L, m.E, m.inst]

/-- The diagram space `Space L E` of a model. -/
def ModelInfo.space (m : ModelInfo) : Expr := mkApp3 (mkConst ``Space [m.u]) m.α m.L m.E

/-- `Model.pts` of a model. -/
def ModelInfo.pts (m : ModelInfo) : Expr := mkAppN (mkConst ``Model.pts [m.u]) m.args

/-- The model of the type `X`, if it has one (and isn't a diagram space, which is its own model:
callers handle those directly). -/
def modelOf? (X : Expr) : MetaM (Option ModelInfo) := do
  let X ← instantiateMVars X
  if X.hasExprMVar || X.hasLooseBVars then return none
  let .sort (.succ u) ← whnfR (← inferType X) | return none
  let some top ← synthInstance? (mkApp (mkConst ``TopologicalSpace [u]) X) | return none
  let α ← mkFreshExprMVar (mkSort Level.one)
  let L ← mkFreshExprMVar (mkApp (mkConst ``List [0]) (mkApp (mkConst ``List [0]) α))
  let nat := Lean.mkConst ``Nat
  let E ← mkFreshExprMVar
    (mkApp (mkConst ``List [0]) (mkApp2 (mkConst ``Prod [0, 0]) nat nat))
  let some inst ← (try synthInstance? (mkAppN (mkConst ``Model [u]) #[X, top, α, L, E])
    catch _ => pure none) | return none
  if inst.isAppOf ``Model.instSpace then return none
  return some ⟨u, X, top, ← instantiateMVars α, ← instantiateMVars L, ← instantiateMVars E, inst⟩

/-- The model of the carrier `↑Z` of `Z : TopCat`, if it has one: of `↑Z` as written (for an
instance on, say, `↑(forget TopCat).coreprObj`), or else of `↑Z` reduced (so that it is `X` for
`Z = of X`). The reduced form alone isn't enough: `whnfR` can stop at a projection `Z'.1`, which
instance search doesn't match against `↑Z'`. -/
def topCatModel? (Z : Expr) : MetaM (Option ModelInfo) := do
  let .const ``TopCat [u] ← whnfR (← inferType Z) | return none
  let X := mkApp (mkConst ``TopCat.carrier [u]) Z
  if let some m ← modelOf? X then return m
  let X' ← whnfR X
  if X' == X then return none
  modelOf? X'

/-- If `expected` is `X ⟶ Y`, for spaces `X`, `Y` of the shapes of the boxes of the morphism
`src ⇢ tgt` (with table `tbl`) but with different names, the morphism relabelled to that type.
A side `X` (or `Y`) that isn't a diagram space but has a `Model` is relabelled to its diagram
space, and the morphism conjugated by `Model.iso ↑X` (or `Model.iso ↑Y`). -/
def relabelledMorphism? (src tgt : BoxD) (cs ct : Canon) (tbl : Array Nat)
    (expected? : Option Expr) (u? : Option (TSyntax `level) := none) :
    TermElabM (Option Term) := do
  let some expected := expected? | return none
  let_expr Quiver.Hom _ _ X Y := (← instantiateMVars expected).consumeMData | return none
  -- each side of the expected type: a known space to relabel the box to, or else the box itself
  -- (and, for a model, the object itself, to conjugate by)
  let side (Z : Expr) (b : BoxD) (c : Canon) :
      TermElabM (List (List String) × List (Nat × Nat) × Term × Option Term × Bool) := do
    if !Z.hasExprMVar then
      if let some (_, _, LZ, EZ) ← spaceObj? Z then
        if let (some P, some E) := (decodePoints LZ, decodeEdges EZ) then
          return (P, E, ← exprToSyntax Z, none, false)
      else if let some m ← topCatModel? Z then
        if let (some P, some E) := (decodePoints m.L, decodeEdges m.E) then
          return (P, E, ← exprToSyntax m.space, some (← exprToSyntax m.X), false)
    -- holes `_` are named only by relabelling
    if c.hasHole then holeErr b
    liftErr (checkOwnNames b)
    return (c.L, c.E, ← boxTerm c u?, none, true)
  -- once any point of the morphism has an ascription, the plain names in the target box only match
  -- it with the source box, so then only its ascriptions choose how it is relabelled
  let formal := (src.labels ++ tgt.labels).any (·.ascribed)
  let (PX, EX, Xs, mX, _) ← side X src cs
  let (PY, EY, Ys, mY, keptY) ← side Y tgt ct
  if !formal && mX.isNone && mY.isNone && PX == cs.L && EX == cs.E && PY == ct.L && EY == ct.E then
    return none
  let Ls := cs.L
  -- (unless the target box keeps its own names)
  let Lt := if formal && !keptY then canonAscribedNames tgt ct else ct.L
  -- the best relabellings of each box
  let best (b : BoxD) (c : Canon) (L : List (List String)) (P : List (List String))
      (E : List (Nat × Nat)) (Z : Expr) : TermElabM (Array (Array Nat)) := do
    let σs := relabellingsCore L P c.E E (limit := 1000)
    let some (_, top) := σs[0]? |
      throwErrorAt (errStx (b.box.err "")) "this box doesn't have the shape of{indentExpr Z}\n\
        so the morphism can't be relabelled to have type{indentExpr expected}"
    return (σs.filter (·.2 == top)).map (·.1)
  let σs ← best src cs Ls PX EX X
  let τs ← best tgt ct Lt PY EY Y
  -- the names of an ascription `(=…)` must be its point's names in the expected space (a label
  -- without one is relabelled to whatever names its point gets)
  let checkNames (b : BoxD) (c : Canon) (P : List (List String)) (σ : Array Nat) (Z : Expr) :
      TermElabM Unit := do
    let real := P.flatten
    for h : li in [0:b.labels.size] do
      let l := b.labels[li]
      let Pj := P[σ[c.perm[li]!]!]!
      let err (msg : MessageData) : TermElabM Unit := throwErrorAt (errStx (l.err "")) msg
      if l.ascribed then
        if let some n := l.names.find? (!Pj.contains ·) then
          if real.contains n then
            err m!"this box is relabelled to{indentExpr Z}\nwhich has a point named '{n}', but \
              this point goes to its point '{"=".intercalate Pj}'"
          else
            err m!"'{n}' is not the name of a point in{indentExpr Z}"
  -- the relabelled tables
  let relabel (σ τ : Array Nat) : Array Nat := Id.run do
    let mut out := Array.replicate σ.size 0
    for h : i in [0:σ.size] do out := out.set! σ[i] (τ[tbl[i]!]!)
    return out
  let t := relabel σs[0]! τs[0]!
  for σ in σs do
    for τ in τs do
      unless relabel σ τ == t do
        -- suggest names to glue on, for the boxes whose relabelling isn't determined
        let glue (box : String) (c : Canon) (L P : List (List String)) (σs : Array (Array Nat)) :
            List String :=
          if σs.size == 1 then [] else
          let σ := σs[0]!
          let gs := (List.range σ.size).filterMap fun i =>
            if L[i]!.any (P[σ[i]!]!.contains ·) then none
            else some s!"{ptName c i}(={P[σ[i]!]!.head!})"
          [s!"{", ".intercalate gs} in the {box} box"]
        throwErrorAt (errStx (src.box.err "")) "this morphism can be relabelled to have type\
          {indentExpr expected}\nin more than one way, giving different maps. Choose one by \
          ascribing names in that type to points, e.g. \
          {"; ".intercalate (glue "source" cs Ls PX σs ++ glue "target" ct Lt PY τs)}"
  checkNames src cs PX σs[0]! X
  checkNames tgt ct PY τs[0]! Y
  let mut f ← homOfTableStx t Xs Ys
  if let some Zx := mX then f ← `(CategoryTheory.CategoryStruct.comp (Model.iso $Zx).hom $f)
  if let some Zy := mY then f ← `(CategoryTheory.CategoryStruct.comp $f (Model.iso $Zy).inv)
  return some f

/-- The type that the part `d` of a diagram (after the `:` of a type ascription) stands for: a box
(a space), a term, or two of them joined by a connective (the type of morphisms between them). -/
def diagramTypeStx (src : DiagramSource) (stx : Syntax) (d : Diagram)
    (u? : Option (TSyntax `level) := none) : TermElabM Term := do
  let obj : Obj → TermElabM Term
    | .box i => do checkNoAscriptions d.boxes[i]!; boxTerm (canon d.boxes[i]!) u?
    | .node i => parseNode src d.nodes[i]!
  match d.boxes.size + d.nodes.size, d.links.toList with
  | 1, [] => obj (if d.boxes.size == 1 then .box 0 else .node 0)
  | 2, [l] =>
    unless l.homType do
      liftErr (.error (l.cell.err "this connective is a morphism; for the type of morphisms \
        after the `:` of a type ascription, use `⟶` (or `──→`)"))
    `($(← obj l.src) ⟶ $(← obj l.tgt))
  | _, _ => throwErrorAt stx "the type in a diagram (after `:`) must currently be one box (a \
      space) or term, or two of them joined by `⟶` (a type of morphisms)"

/-- Elaborate the part `d` of the diagram `stx` (before the `:` of a type ascription, if any), with
its spaces in the universe `u?` if given. -/
def elabDiagramTerm (src : DiagramSource) (stx : Syntax) (d : Diagram) (expected? : Option Expr)
    (u? : Option (TSyntax `level) := none) : TermElabM Expr := do
  let box (i : Nat) := do checkNoAscriptions d.boxes[i]!; boxTerm (canon d.boxes[i]!) u?
  let t ← match d.boxes.size, d.nodes.size, d.links.toList with
    | 1, 0, [] => box 0
    | 2, 0, [l] => match l.src, l.tgt with
      | .box i, .box j =>
        if l.homType then do `($(← box i) ⟶ $(← box j)) else do
        let (src, tgt) := (d.boxes[i]!, d.boxes[j]!)
        let (cs, ct, tbl) ← morphismTable src tgt
        -- the morphism is relabelled to its expected type, so wait for that if it isn't known
        -- yet: as for a side of `=` (which `binop%` elaborates without an expected type), or for
        -- `d ≫ f` (whose target `f` fixes)
        let expected? ← expected?.mapM fun e => return (← instantiateMVars e).consumeMData
        let known := match expected? with
          | none => false
          | some e => match_expr e with
            | Quiver.Hom _ _ X Y => !X.hasExprMVar && !Y.hasExprMVar
            | _ => !e.hasExprMVar
        unless known do
          -- while waiting, say that this is a morphism of `TopCat`, e.g. so that `(d ≫ d') x`
          -- can find the coercion to functions
          let inTopCat := match expected? with
            | some e => match_expr e with
              | Quiver.Hom C _ _ _ => C.isConstOf ``TopCat
              | _ => false
            | none => false
          if !inTopCat && (← read).mayPostpone then
            let ty ← match u? with
              | some u => `((_ : TopCat.{$u}) ⟶ (_ : TopCat.{$u}))
              | none => `((_ : TopCat) ⟶ (_ : TopCat))
            return ← elabTerm (← `(($(⟨stx⟩) : $ty))) expected?
          tryPostpone
        match ← relabelledMorphism? src tgt cs ct tbl expected? u? with
        | some t => pure t
        | none =>
          if cs.hasHole then holeErr src
          if ct.hasHole then holeErr tgt
          liftErr (checkOwnNames src); liftErr (checkOwnNames tgt)
          homOfTableStx tbl (← boxTerm cs u?) (← boxTerm ct u?)
      | _, _ => unreachable!
    | 1, 1, [l] => match l.src, l.tgt with
      | .box i, .node j => do `($(← box i) ⟶ $(← parseNode src d.nodes[j]!))
      | .node i, .box j => do `($(← parseNode src d.nodes[i]!) ⟶ $(← box j))
      | _, _ => unreachable!
    | _, _, _ => throwErrorAt stx "a diagram must currently be one box (a space), two boxes \
        joined by a dashed connective (a morphism), or a box and a term joined by a dashed \
        connective (a type of morphisms)"
  elabTerm t expected?

/-- Elaborate the diagram `stx`, with its spaces in the universe `u?` if given (for `D.{u}`). -/
def elabDiagramWith (u? : Option (TSyntax `level)) : TermElab := fun stx expected? => do
  let src : DiagramSource ← match firstAtom? stx with
    | some (.atom (.original _ pos _ _) _) =>
      pure { text := (← getFileMap).source, start := pos.byteIdx, virtual := false }
    | some (.atom _ text) => pure (virtualSource text)
    | _ => throwError "diagram has no text"
  let go : TermElabM Expr := do
    let blk ← liftErr (scanBlock src.text src.start)
    let d ← liftErr blk.read
    let some (_, col) := d.colon | elabDiagramTerm src stx d expected? u?
    -- `(d : T)`, written as one block
    let ty ← elabType (← diagramTypeStx src stx (d.side false col) u?)
    Term.ensureHasType ty (← elabDiagramTerm src stx (d.side true col) ty u?)
  unless src.virtual do return ← go
  -- positions in a virtual source aren't positions in the file, so report errors at the diagram
  tryCatch go fun
    | .error _ msg => throwErrorAt stx msg
    | ex => throw ex

@[term_elab gavDiagram, inherit_doc gavDiagram]
def elabDiagramFull : TermElab := elabDiagramWith none

@[term_elab gavDiagramUniv, inherit_doc gavDiagramUniv]
def elabDiagramUniv : TermElab := fun stx expected? =>
  elabDiagramWith (some ⟨stx[2]⟩) stx[0] expected?

/-- Print multi-row diagrams with box-drawing glyphs (`┌ ┐ └ ┘`, `╲ ╱ │`, `╌╌→`), which are one
column wide in more fonts than `⌜ ⌝ ⌞ ⌟`, `↘ ↙` and `⇢` (notably in Consolas, VS Code's default
font on Windows), so that the diagrams stay aligned. -/
register_option pp.gavDiagrams.boxDrawing : Bool := {
  defValue := false
  descr := "(pretty printer) print multi-row Gavrilovich diagrams with box-drawing glyphs \
    (`┌ ┐ └ ┘`, `╲ ╱ │`, `╌╌→`), which stay aligned in more fonts"
}

/-- The name `n` of a point `pt(n)`, as written: a string literal without its quotes. -/
def ptNameStx (n : Syntax) : String := n.isStrLit?.getD (toString n.prettyPrint)

/-- The error for `pt(n)` (with `n` the syntax of the name) in the space with points `L`. -/
def noPointMsg (n : Syntax) (L? : Option Expr) : MessageData :=
  let n := ptNameStx n
  match L? >>= decodePoints with
  | some L => m!"no point named '{n}' in this space (its points are \
      {", ".intercalate (L.map ("=".intercalate ·))})"
  | none => m!"no point named '{n}' in this space"

@[tactic gavPtMem, inherit_doc gavPtMem]
def evalGavPtMem : Tactic.Tactic := fun stx => do
  try Tactic.evalTactic (← `(tactic| decide))
  catch _ =>
    -- the goal is `List.findIdx _ L < List.length L`
    let tgt ← instantiateMVars (← Tactic.getMainTarget)
    throwError noPointMsg stx[1] (tgt.getAppArgs.back?.map (·.appArg!))

/-! ### Laying out multi-row boxes -/

/-- A partial drawing of the inside of a multi-row box, in (row, column) coordinates. -/
structure Sketch where
  /-- The non-blank cells. -/
  cells : Array ((Int × Int) × Char) := #[]
  /-- The cells of label characters, with the class of points they belong to. -/
  owner : Array ((Int × Int) × Nat) := #[]
  /-- Blank cells that rays pass through, which must stay blank. -/
  reserved : Array (Int × Int) := #[]
  /-- The row and column of each class that has been placed. -/
  pos : Array (Option (Int × Int))

namespace Sketch

/-- The character at `p`. -/
def charAt (s : Sketch) (p : Int × Int) : Char :=
  ((s.cells.find? (·.1 == p)).map (·.2)).getD ' '

/-- The class whose label has a character at `p`. -/
def ownerAt (s : Sketch) (p : Int × Int) : Option Nat :=
  (s.owner.find? (·.1 == p)).map (·.2)

/-- Is `p` blank, and not needed blank by a ray? -/
def free (s : Sketch) (p : Int × Int) : Bool := s.charAt p == ' ' && !s.reserved.contains p

/-- Place class `i`, drawn as `text`, at row `r` and column `x`, if there is room: its cells must
be free, with two blanks on either side. -/
def place (s : Sketch) (i : Nat) (text : String) (r x : Int) : Option Sketch := do
  let cs := text.toList
  let w : Int := cs.length
  for j in [0:cs.length] do guard (s.free (r, x + j))
  for d in [1, 2] do
    guard (s.charAt (r, x - d) == ' ' && s.charAt (r, x + w - 1 + d) == ' ')
  let mut s := { s with pos := s.pos.set! i (some (r, x)) }
  for h : j in [0:cs.length] do
    let p := (r, x + j)
    s := { s with cells := s.cells.push (p, cs[j]) }
    if labelChar cs[j] then s := { s with owner := s.owner.push (p, i) }
  return s

/-- Draw an arrow from class `a` down to class `b` (placed on a lower row): `↓`, `↘` or `↙`, on a
straight line from a character of `a`'s label down to a character of `b`'s label, through blanks.
If `spaced`, the arrow must not be next to another arrow. -/
def route (s : Sketch) (spaced : Bool) (a b : Nat) : Option Sketch := do
  let some (ra, _) := s.pos[a]! | none
  let some (rb, _) := s.pos[b]! | none
  let d := rb - ra
  let starts := (s.owner.filter (·.2 == a)).map (·.1)
  for t in [1:d.toNat] do
    for (_, c) in starts do
      for (dc, glyph) in [((0 : Int), '↓'), (1, '↘'), (-1, '↙')] do
        let cell (k : Int) : Int × Int := (ra + k, c + dc * k)
        -- the line must end on `b`, and be blank in between
        unless s.ownerAt (cell d) == some b do continue
        let between := (List.range (d.toNat - 1)).map fun k => cell (k + 1)
        unless between.all (s.charAt · == ' ') do continue
        let arrow := cell t
        unless s.free arrow do continue
        let (r, col) := arrow
        if spaced && (s.charAt (r, col - 1) != ' ' || s.charAt (r, col + 1) != ' ') then continue
        return { s with cells := s.cells.push (arrow, glyph),
                        reserved := s.reserved ++ (between.filter (· != arrow)).toArray }
  none

end Sketch

/-- Search for a drawing: place the classes in `order` one by one (each on row `rows[i]`, drawn as
`texts[i]`), each followed by the arrows to it from its predecessors `preds[i]`, backtracking over
the columns of the classes. Each step uses up some `fuel`. -/
partial def sketchSearch (texts : Array String) (rows : Array Int) (preds : Array (List Nat))
    (spaced : Bool) : List Nat → Sketch → StateM Nat (Option Sketch)
  | [], s => return some s
  | i :: rest, s => do
    let w : Int := texts[i]!.length
    let r := rows[i]!
    -- the end of the row so far
    let rowEnd : Option Int := s.pos.foldl (init := none) fun m p? => match p? with
      | some (r', x') =>
        let e := x' + ((s.cells.filter fun ((r'', _), _) => r'' == r').foldl
          (fun m ((_, c), _) => max m (c - x' + 1)) 0)
        if r' == r then some (max (m.getD e) e) else m
      | none => m
    let candidates : List Int := match preds[i]! with
      | [] => match rowEnd with
        | none => [0]
        | some e => (List.range 4).map fun d => e + 2 + d
      | ps => Id.run do
        -- columns from which an arrow from each predecessor can reach a label this wide
        let mut lo : Int := -1000; let mut hi : Int := 1000
        let mut centre : Int := 0
        for p in ps do
          let some (rp, xp) := s.pos[p]! | continue
          let wp : Int := texts[p]!.length
          let d := r - rp
          lo := max lo (xp - d - w + 1); hi := min hi (xp + wp - 1 + d)
          centre := centre + 2 * xp + wp
        let mid := centre / ps.length
        if lo > hi then return []
        return ((List.range (hi - lo + 1).toNat).map fun k => lo + k).mergeSort fun x y =>
          (2 * x + w - mid).natAbs ≤ (2 * y + w - mid).natAbs
    for x in candidates do
      if (← get) == 0 then return none
      modify (· - 1)
      let some s := s.place i texts[i]! r x | continue
      let some s := preds[i]!.foldlM (fun s p => s.route spaced p i) s | continue
      if let some s ← sketchSearch texts rows preds spaced rest s then return some s
    return none

/-- Lay out the space with points `L` and specialization closure `E` as a multi-row box: each class
of equivalent points (drawn `a ↔ b`) goes on the row of its height in the Hasse diagram, with
arrows down to the classes that cover it. The drawing is checked to elaborate back to
`Space L E`. Point `i` is drawn as `label i`. -/
def multiRow (L : List (List String)) (E : List (Nat × Nat))
    (label : Nat → String := fun i => "=".intercalate L[i]!) (fuel := 2000) : Option String := do
  let n := L.length
  let le (i j : Nat) : Bool := i == j || E.contains (i, j)
  let rep : Array Nat := (Array.range n).map fun i => ((List.range n).find? fun j =>
    le i j && le j i).getD i
  let reps := (List.range n).filter fun i => rep[i]! == i
  let lt (a b : Nat) : Bool := !(le b a) && le a b
  let covers (a b : Nat) : Bool := lt a b && !reps.any fun k => lt a k && lt k b
  -- classes, indexed by position in `reps`
  let m := reps.length
  let texts : Array String := reps.toArray.map fun a =>
    " ↔ ".intercalate (((List.range n).filter (rep[·]! == a)).map label)
  let preds : Array (List Nat) := (Array.range m).map fun j =>
    (List.range m).filter fun i => covers reps[i]! reps[j]!
  -- height: the length of the longest chain of covers below
  let mut height : Array Nat := Array.replicate m 0
  for _ in [0:m] do
    for j in [0:m] do
      for i in preds[j]! do
        height := height.set! j (max height[j]! (height[i]! + 1))
  let top := height.foldl max 0
  guard (top ≥ 1)
  let order := (List.range m).mergeSort fun i j =>
    height[i]! < height[j]! || (height[i]! == height[j]! && i ≤ j)
  -- the rows of labels are `gap` apart: `gap = 2` (one row of arrows between) if possible, and
  -- otherwise more, which gives diagonal arrows more room; for each, first with arrows spaced apart
  let tries := [(2 : Int), 3, 4].flatMap fun gap => [(true, gap), (false, gap)]
  let some (gap, sk) := tries.findSome? fun (spaced, gap) =>
      let rows : Array Int := height.map fun h => gap * Int.ofNat h
      let init : Sketch := { pos := Array.replicate m none }
      ((sketchSearch texts rows preds spaced order init).run' fuel).map (gap, ·) | none
  -- render
  let cols := sk.cells.map (·.1.2)
  let c0 := cols.foldl min 0; let c1 := cols.foldl max 0
  let lastRow : Int := gap * top
  let lines := (List.range (lastRow.toNat + 1)).map fun r => Id.run do
    let mut line := ""
    for c in [0:(c1 - c0 + 1).toNat] do line := line.push (sk.charAt (r, c0 + c))
    let (l, rgt) := if r == 0 then ('⌜', '⌝') else if r == lastRow.toNat then ('⌞', '⌟')
      else (' ', ' ')
    return ((String.singleton l ++ line).push rgt).trimAsciiEnd.copy
  let text := "\n".intercalate lines
  guard (roundTrips text L E)
  return text

/-- The box-drawing glyphs for a multi-row box drawn by `multiRow`, whose arrows all point down the
page (or are `↔`, which stays). -/
def toBoxDrawing (text : String) : String :=
  text.map fun
    | '⌜' => '┌' | '⌝' => '┐' | '⌞' => '└' | '⌟' => '┘'
    | '↘' => '╲' | '↙' => '╱' | '↓' => '│'
    | c => c

/-- Lay out `Space L E` as a box: on one row if possible, and otherwise on several (with
box-drawing glyphs if `boxDrawing`), with point `i` drawn as `label i`. -/
def layoutBox (L : List (List String)) (E : List (Nat × Nat)) (boxDrawing := false)
    (label : Nat → String := fun i => "=".intercalate L[i]!) : Option String :=
  oneRow L E label <|> (multiRow L E label).map fun t => if boxDrawing then toBoxDrawing t else t

/-- Put two boxes side by side, joined by `⇢` (or `╌╌→`, if `boxDrawing` and a box has several
rows). -/
def joinBoxes (s t : String) (boxDrawing := false) : String :=
  let (as, bs) := (s.splitOn "\n", t.splitOn "\n")
  let wa := as.foldl (fun w a => max w a.length) 0
  let k := (min as.length bs.length - 1) / 2
  let n := max as.length bs.length
  let (arrow, blank) := if boxDrawing && n > 1 then (" ╌╌→ ", "     ") else (" ⇢ ", "   ")
  "\n".intercalate <| (List.range n).map fun r =>
    let a := as.getD r ""
    let a := a.pushn ' ' (wa - a.length)
    let conn := if r == k then arrow else blank
    match bs[r]? with
    | some b => (a ++ conn ++ b).trimAsciiEnd.copy
    | none => a.trimAsciiEnd.copy

open PrettyPrinter.Delaborator SubExpr in
/-- Print `Space L E` as a multi-row box, when it can't be drawn on one row (`delabSpace`) and
there is a drawing that elaborates back to it. -/
@[delab app.Gavrilovich.Space]
def delabSpaceMultiRow : Delab :=
  whenPPOption (pp.gavDiagrams.get ·) <| whenNotPPOption getPPExplicit do
  let e ← getExpr
  guard (e.getAppNumArgs == 3)
  let some L := decodePoints (e.getArg! 1) | failure
  let some E := decodeEdges (e.getArg! 2) | failure
  -- one-row boxes are printed by `delabSpace`
  guard (oneRow L E).isNone
  let some text := layoutBox L E (pp.gavDiagrams.boxDrawing.get (← getOptions)) | failure
  guard (roundTrips text L E)
  return ⟨.node .none ``gavDiagram #[.atom .none text]⟩

/-- Decode a literal `List ℕ`. -/
def decodeNats (e : Expr) : Option (List Nat) := do
  (← e.listLit?).2.mapM fun n => n.nat? <|> n.rawNatLit?

open PrettyPrinter.Delaborator SubExpr in
/-- Print `Space.homOfTable tbl _ _ : Space L E ⟶ Space L' E'` as a diagram `(⌜…⌟ ⇢ ⌜…⌟)`
(with multi-row boxes if necessary), in Gavrilovich's convention: a target point whose own names
don't match exactly the source points that go to it is labelled by their names, with its own names
ascribed. So `a ↦ o, b ↦ c` is printed `(⌜a  b⌟ ⇢ ⌜a(=o) → b(=c)⌟)`, and the swap of `⌜a  b⌟` is
printed `(⌜a  b⌟ ⇢ ⌜b(=a)  a(=b)⌟)`. A target point that nothing goes to is labelled `_(=o)` if
its names are names in the source. Once there is an ascription, plain names in the target box only
match points, so more points get ascriptions where that is needed to fix the map, as in
`(⌜a  b⌟ ⇢ ⌜a(=a)  b  _(=c)⌟)`. -/
@[delab app.Gavrilovich.Space.homOfTable]
def delabHomOfTable : Delab :=
  whenPPOption (pp.gavDiagrams.get ·) <| whenNotPPOption getPPExplicit do
  let e ← getExpr
  guard (e.getAppNumArgs == 9)
  let args := e.getAppArgs
  let (some L, some L', some E, some E', some tbl) := (decodePoints args[2]!,
    decodePoints args[3]!, decodeEdges args[4]!, decodeEdges args[5]!, decodeNats args[6]!) |
    failure
  guard (tbl.length == L.length && !L'.isEmpty)
  let tbl := tbl.map (· % L'.length)
  -- the names of the source points that go to each target point
  let pre (k : Nat) : List String :=
    ((List.range L.length).filter (tbl[·]! == k)).flatMap (L[·]!) |>.mergeSort strLe
  -- do the target point's own names match exactly the source points that go to it?
  let ownMatch (k : Nat) : Bool := (List.range L.length).all fun i =>
    (tbl[i]! == k) == L[i]!.any L'[k]!.contains
  -- the target points to ascribe names to: those whose names don't match. Once there is one, the
  -- other plain names in the target box only match points, so (as when elaborating) only the
  -- ascriptions choose how it is relabelled to the target space; ascribe more points until that
  -- leaves no choice that changes the map
  let mut asc := Array.ofFn (n := L'.length) fun k => !ownMatch k
  while asc.any id do
    let Lt := (List.range L'.length).map fun k => if asc[k]! then L'[k]! else []
    let τs := relabellingsCore Lt L' E' E' (limit := 1000)
    let some (_, top) := τs[0]? | failure
    let moved := (τs.filter (·.2 == top)).toList.flatMap fun (τ, _) =>
      tbl.filter fun k => τ[k]! != k
    let some k := moved.head? | break
    asc := asc.set! k true
  let label (k : Nat) : String :=
    let own := "=".intercalate L'[k]!
    if !asc[k]! then own else
    match pre k with
    | [] => s!"_(={own})"
    | ns => s!"{"=".intercalate ns}(={own})"
  let bd := pp.gavDiagrams.boxDrawing.get (← getOptions)
  let (some s, some t) := (layoutBox L E bd, layoutBox L' E' bd label) | failure
  let text := joinBoxes s t bd
  -- check that the text reads back
  let .ok d := scanBlock text 0 >>= Block.read | failure
  guard (d.boxes.size == 2 && d.links.size == 1 && d.nodes.isEmpty)
  let some l := d.links[0]? | failure
  let (Obj.box i, Obj.box j) := (l.src, l.tgt) | failure
  let (cs, cd) := (canon d.boxes[i]!, canon d.boxes[j]!)
  guard (cs.L == L && cs.E == E && cd.L == L' && cd.E == E')
  let matchT := canonMatchNames d.boxes[j]! cd
  for i in [0:L.length] do
    let ks := (List.range L'.length).filter fun k => L[i]!.any (matchT[k]!.contains ·)
    guard (ks == [tbl[i]!])
  let stx : Term := ⟨.node .none ``gavDiagram #[.atom .none text]⟩
  `(($stx))

/-- Does the name `n` parse back as the identifier `n`? -/
def isIdentName (env : Environment) (n : String) : Bool :=
  match Parser.runParserCategory env `term n with
  | .ok stx => stx.isIdent && stx.getId == .mkSimple n
  | .error _ => false

/-- Is the scoped `pt(…)` notation available? -/
def ptNotationOpen : MetaM Bool := do
  let ns := `Gavrilovich
  return ns.isPrefixOf (← getCurrNamespace) ||
    (← getOpenDecls).any fun | .simple ns' _ => ns' == ns | _ => false

/-- `pt(n)` for a string name `n`. -/
def ptStx (n : String) : MetaM Term := do
  if !n.isEmpty && n.all Char.isDigit then `(pt($(Syntax.mkNumLit n)))
  else if isIdentName (← getEnv) n then `(pt($(mkIdent (.mkSimple n))))
  else `(pt($(Syntax.mkStrLit n)))

open PrettyPrinter.Delaborator SubExpr in
/-- Print `Space.pt "o"` as `pt(o)`, and `Space.pt n` for other names as `pt[n]`, when the scoped
notation is available. -/
@[delab app.Gavrilovich.Space.pt]
def delabPt : Delab := whenPPOption (pp.gavDiagrams.get ·) <| whenNotPPOption getPPExplicit do
  let e ← getExpr
  guard (e.getAppNumArgs == 6)
  guard (← ptNotationOpen)
  let .lit (.strVal n) := e.getArg! 4 | `(pt[$(← withNaryArg 4 delab)])
  ptStx n

@[term_elab gavPtPat, inherit_doc gavPtPat]
def elabGavPtPat : TermElab := fun stx expectedType? => do
  unless (← read).inPattern do throwError "`gav_pt_pat%` is only for patterns"
  elabTerm (← `(by gav_pt_mem $(⟨stx[1]⟩))) expectedType?

@[term_elab gavPtLt, inherit_doc gavPtLt]
def elabGavPtLt : TermElab := fun stx expectedType? => do
  if (← read).inPattern then throwError "`gav_pt_lt%` is not for patterns"
  let some ty := expectedType? | throwError "`gav_pt_lt%` needs an expected type"
  let ty ← instantiateMVars ty
  let_expr LT.lt _ _ k len := ty.consumeMData
    | throwError "`gav_pt_lt%`: expected a goal `k < L.length`, not{indentExpr ty}"
  let_expr List.length α L := len
    | throwError "`gav_pt_lt%`: expected a goal `k < L.length`, not{indentExpr ty}"
  let L ← instantiateMVars L
  if L.hasExprMVar then
    tryPostpone
    throwError "can't tell which space the point '{ptNameStx stx[1]}' is in; \
      use a type ascription, e.g. `(pt(o) : ⌜o → c⌟)`"
  let_expr List β := α | throwError "`gav_pt_lt%`: the points aren't lists of names"
  -- the index as `Space.pt` computes it, evaluated (synthesizing only what this creates: the
  -- enclosing term may have pending instances that aren't determined yet)
  let idx ← withSynthesize do
    let n ← elabTermEnsuringType stx[1] β
    elabTerm (← `(List.findIdx (fun x => decide ($(← exprToSyntax n) ∈ x))
      $(← exprToSyntax L))) (mkConst ``Nat)
  let some i ← natVal? (← instantiateMVars idx)
    | throwError "can't compute the index of the point '{ptNameStx stx[1]}'"
  let some (_, pts) := L.listLit? | throwError "the points of this space aren't a literal list"
  let ok := i < pts.length
  -- for a missing name, log the error rather than throwing it, so that this alternative of
  -- `pt(n)` is still the one selected, and its error the one reported
  unless ok do logError (noPointMsg stx[1] L)
  let k ← instantiateMVars k
  let iE := mkNatLit (if ok then i else 0)
  if let .mvar m := k then m.assign iE  -- `_` is synthetic opaque under `refine`
  else unless ← isDefEq k iE do throwError "`gav_pt_lt%`: the index is already{indentExpr k}"
  let ty ← instantiateMVars ty.consumeMData
  if ok then mkDecideProof ty else mkSorry ty (synthetic := true)

/-- The point named `n` (syntax) of the model `m`: its entry in `Model.pts` if that is a literal
list, and otherwise `Model.homeo.symm (Space.mk k _)`. -/
def modelPt (m : ModelInfo) (n : Syntax) : TermElabM Expr := do
  let idx ← withSynthesize do
    let n ← elabTermEnsuringType n m.α
    elabTerm (← `(List.findIdx (fun x => decide ($(← exprToSyntax n) ∈ x))
      $(← exprToSyntax m.L))) (mkConst ``Nat)
  let some i ← natVal? (← instantiateMVars idx)
    | throwError "can't compute the index of the point '{ptNameStx n}'"
  let some (_, pts) := m.L.listLit? | throwError "the points of this space aren't a literal list"
  -- for a missing name, log the error rather than throwing it, so that this alternative of `pt(n)`
  -- is still the one selected, and its error the one reported (as for `gav_pt_lt%`)
  unless i < pts.length do
    logError (noPointMsg n m.L)
    return ← mkSorry m.X (synthetic := true)
  if let some ps ← Space.listElems? m.pts then
    if let some x := ps[i]? then return x
  let len := mkApp2 (mkConst ``List.length [0]) (mkApp (mkConst ``List [0]) m.α) m.L
  let h ← mkDecideProof (← mkLt (mkNatLit i) len)
  let pt := mkApp5 (mkConst ``Space.mk [m.u]) m.α m.L m.E (mkNatLit i) h
  mkAppM ``DFunLike.coe #[← mkAppM ``Homeomorph.symm #[mkAppN (mkConst ``Model.homeo [m.u]) m.args],
    pt]

@[term_elab gavPtModel, inherit_doc gavPtModel]
def elabGavPtModel : TermElab := fun stx expectedType? => do
  if (← read).inPattern then throwError "`gav_pt_model%` is not for patterns"
  let some ty := expectedType? | throwError "`gav_pt_model%` needs an expected type"
  let ty ← instantiateMVars ty
  if ty.hasExprMVar || (spaceOf? (← whnfR ty)).isSome then
    throwError "`gav_pt_model%`: not a model type{indentExpr ty}"
  let some m ← modelOf? ty | throwError "`gav_pt_model%`: no `Model` instance for{indentExpr ty}"
  modelPt m stx[1]

open PrettyPrinter.Delaborator SubExpr in
/-- Print a point `Space.mk k _` or `⟨⟨k, _⟩⟩` of a space with a literal list of points as
`pt(n)` (or `pt[n]`), where `n` is the first name of the `k`-th point. -/
@[delab app.Gavrilovich.Pts.mk,
  delab app.Gavrilovich.Space.mk]
def delabPtsMk : Delab := whenPPOption (pp.gavDiagrams.get ·) <| whenNotPPOption getPPExplicit do
  let e ← getExpr
  guard (e.isAppOfArity ``Pts.mk 4 || e.isAppOfArity ``Space.mk 5)
  guard (← ptNotationOpen)
  let some k ← ptIdx? e | failure
  let some (_, pts) := (e.getArg! 1).listLit? | failure
  let some (_, n :: _) := pts[k]? >>= (·.listLit?) | failure
  match n with
  | .lit (.strVal n) => ptStx n
  | n => `(pt[$(← PrettyPrinter.delab n)])

/-! ### Models -/

/-- The model of an application `Model.homeo …` (with all of its arguments). -/
def modelOfHomeo? (h : Expr) : Option ModelInfo := do
  guard (h.isAppOfArity ``Model.homeo 6)
  let .const _ [u] := h.getAppFn | none
  let a := h.getAppArgs
  return ⟨u, a[0]!, a[1]!, a[2]!, a[3]!, a[4]!, a[5]!⟩

/-- Evaluate `Model.homeo x`, for `x` one of the listed points `Model.pts` of the model, to the
point `Space.mk k _` of the diagram space. -/
def evalModelApply : Simp.Simproc := fun e => do
  let_expr DFunLike.coe _ _ _ _ f x := e | return .continue
  if x.hasLooseBVars then return .continue
  let some m := modelOfHomeo? f | return .continue
  let some ps ← Space.listElems? m.pts | return .continue
  let x ← instantiateMVars x
  let some k ← ps.toArray.findIdxM? (withReducible <| isDefEq · x) | return .continue
  let len ← mkAppM ``List.length #[m.pts]
  let hk ← mkDecideProof (← mkLt (mkNatLit k) len)
  let pf := mkAppN (mkConst ``Model.homeo_eq_of_getElem_eq [m.u])
    (m.args ++ #[mkNatLit k, hk, x, ← mkEqRefl x])
  return .done { expr := ← mkCanonicalPt [m.u] m.α m.L m.E k, proof? := pf }

/-- `simp` evaluates `Model.homeo x` at the listed points `x` of a model (e.g. `True : Prop`).
(`Model.homeo.symm` at points `pt(…)` is `Model.homeo_symm_mk`, followed by `Model.reducePts`.) -/
simproc [simp, seval] _root_.Gavrilovich.Model.reduceApply (DFunLike.coe _ _) := evalModelApply

/-- `simp` rewrites `(f ∘ g) x` to `f (g x)`, as `Function.comp_apply` does, but also when `x` has
the domain type of `g` only up to unfolding: a pair `(x, y)` is a point of `A ⊗ B` in `TopCat`, but
its type `↑A × ↑B` is `↑(A ⊗ B)` only up to unfolding `⊗`, so `simp` can't instantiate
`Function.comp_apply` with it. (`simp` turns `(f ≫ g) p` into such a composition.) -/
dsimproc [simp, seval] _root_.Gavrilovich.Model.reduceCompApply (Function.comp _ _ _) := fun e => do
  let_expr Function.comp _ _ _ f g x := e | return .continue
  return .visit (mkApp f (mkApp g x))

/-- `simp` rewrites `Model.pts[k]`, for a numeral `k`, to the `k`-th listed point of the model (as
`Model.reducePts` and `List.getElem_cons_succ` would, except that these can't rewrite a point whose
type is the type of the model only up to unfolding, such as a pair `(x, y)` in `↑(A ⊗ B)`). -/
dsimproc ↓ [simp, seval] _root_.Gavrilovich.Model.reducePtsGetElem
    ((@Model.pts _ _ _ _ _ _)[_]) := fun e => do
  let_expr GetElem.getElem _ _ _ _ _ xs i _ := e | return .continue
  unless xs.isAppOfArity ``Model.pts 6 && !xs.hasLooseBVars do return .continue
  let some k ← natVal? i | return .continue
  let some ps ← Space.listElems? xs | return .continue
  let some p := ps[k]? | return .continue
  return .done p

/-- `simp` unfolds `Model.pts` to its literal list of points, if it is one. A point whose type is
the type `X` of the model only up to unfolding (such as a pair `(x, y)`, for `X = ↑(A ⊗ B)`) is
given as `@id X p`, so that the list is type-correct at reducible transparency, which `simp` needs
to rewrite it. -/
dsimproc [simp, seval] _root_.Gavrilovich.Model.reducePts (@Model.pts _ _ _ _ _ _) := fun e => do
  unless e.isAppOfArity ``Model.pts 6 && !e.hasLooseBVars do return .continue
  let .const _ [u] := e.getAppFn | return .continue
  let some ps ← Space.listElems? e | return .continue
  let X := e.getArg! 0
  let ps ← ps.mapM fun p => do
    if ← withReducible (isDefEq (← inferType p) X) then return p
    return mkApp2 (mkConst ``id [mkLevelSucc u]) X p
  return .done (← mkListLit X ps)

/-- `∀ x : X, p x`, for `X` with a model (whose points `Model.pts` are a literal list), is the
conjunction of `p x` over the listed points. -/
simproc_decl _root_.Gavrilovich.Model.forallPts (∀ _ : _, _) := fun e => do
  let .forallE n X body bi := e | return .continue
  let some m ← modelOf? X | return .continue
  let some ps ← Space.listElems? m.pts | return .continue
  let rhs := ps.foldr (fun x acc => mkApp2 (mkConst ``And) (body.instantiate1 x) acc)
    (mkConst ``True)
  let pf ← mkPropExt (mkAppN (mkConst ``Model.forall_iff_foldr [m.u])
    (m.args.push (.lam n X body bi)))
  return .visit { expr := rhs, proof? := pf }

/-- `∃ x : X, p x`, for `X` with a model (whose points `Model.pts` are a literal list), is the
disjunction of `p x` over the listed points. -/
simproc_decl _root_.Gavrilovich.Model.existsPts (∃ _ : _, _) := fun e => do
  let_expr Exists X p := e | return .continue
  let some m ← modelOf? X | return .continue
  let some ps ← Space.listElems? m.pts | return .continue
  let rhs := ps.foldr (fun x acc => mkApp2 (mkConst ``Or) (p.beta #[x]) acc) (mkConst ``False)
  let pf ← mkPropExt (mkAppN (mkConst ``Model.exists_iff_foldr [m.u]) (m.args.push p))
  return .visit { expr := rhs, proof? := pf }

end Mathlib.Tactic.Gavrilovich

end
