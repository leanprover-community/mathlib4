/-
Copyright (c) 2026 Robert Maxton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Maxton
-/
module

public meta import Mathlib.Tactic.Simps.Basic
public meta import Mathlib.Tactic.Translate.ToDual

/-!
# `simps!!`: `simps` with generalized projections

`@[simps!!]` does everything `@[simps!]` does, and also generates lemmas for *generalized
projections*: arbitrary functions out of the type of the definition, registered with
`@[simps_proj]`. For example, after
```
attribute [simps_proj] PullbackCone.fst PullbackCone.snd
initialize_simps_projections!! PullbackCone (π → fst snd)
```
a definition `@[simps!!] def c : PullbackCone f g := PullbackCone.mk a b w` gets the lemmas
`c_pt : c.pt = W`, `c_fst : c.fst = a` and `c_snd : c.snd = b`, instead of `c_pt` and `c_π_app`.

A generalized projection need not be a function out of a structure: after
```
attribute [simps_proj comp (attr := reassoc (attr := simp))] pullback.fst
```
every morphism `h` into a pullback gets a lemma for `h ≫ pullback.fst f g`, wherever it appears:
as the definition itself, or as a field of it, like the `hom` of an isomorphism.

## Generalized projections

A generalized projection is a function `p : ∀ params (x : S) extras, R`. The `params` are found by
unifying `S` with the type of the definition (or of the field) at hand, and the `extras` become
arguments of the generated lemma. Generalized projections are looked up by the type `S`, up to
reducible unfolding, so a projection registered for `PullbackCone f g` also applies to a
definition of type `Cone (cospan f g)`.

`@[simps_proj]` on a declaration `p` registers:
* `p` itself, by default. Its *self argument* `x` is the last argument whose type depends
  (transitively) on all the arguments before it, unless the option `(self := x)` says otherwise.
* with `comp`, for a morphism `p : ∀ args, A ⟶ B`: `fun (h : W ⟶ A) ↦ h ≫ p args`. Here `S` is
  `W ⟶ A`, the `params` are the arguments that `A` depends on, and the `extras` are the other
  arguments of `p`. This is how `pullback.fst` is registered.
* with `precomp`, for a morphism `p : ∀ args, A ⟶ B`: `fun (h : B ⟶ W) ↦ p args ≫ h`, keyed on
  `B ⟶ W`. This is how `pushout.inl` is registered, and also `pullback.lift`, whose `extras` are
  then the two morphisms and the proof that they form a cone.

A declaration can only be registered once (and an η-rule too).

For a term `t` of type `S` with value `v`, the generated lemma is `p params t extras = rhs`, and
`rhs` is computed from `p params v extras`:
1. definitions applied to structure instances (`PullbackCone.fst ⟨W, π⟩`, say) are unfolded, as
   are class projections applied to them (`⇑(Equiv.mk f g l r) x`), and then projections of
   structure instances, `match`es on constructors and β-redexes are reduced. This is what makes
   generalized projections that are compositions of genuine projections (with arguments) work.
2. the result is simplified by `simp`, with the lemmas given by `(rules := ...)` (and their
   `_assoc` versions, if they exist) added to the simp set. This is what makes generalized
   projections that are characterized by lemmas, like `pullback.lift_fst`, work.

Before that, `simps!!` tries the same with `v` replaced by the body of the definition *as
written*, not unfolded to a constructor application, so that `simp` can use the lemmas about the
definitions it is made of: for `e := pullbackSymmetry f g`, `e.hom ≫ pullback.fst g f` is computed
from `(pullbackSymmetry f g).hom ≫ pullback.fst g f`, which simplifies to `pullback.snd f g` by a
lemma about `pullbackSymmetry`. This result is used if it no longer contains the head of the body
(`pullbackSymmetry`).

`simps!!` then recurses into the result, as `simps` does with the fields of a structure: both
into the genuine projections of its type, if it is a structure, and into the generalized
projections that apply to it.

Options of `@[simps_proj]`:
* `comp`, `precomp`: see above. The name of a `precomp` projection is added *before* the last
  component of the lemma name: the lemma for `pullback.lift a b w ≫ e.hom` is `e_lift_hom`.
* `(name := n)`: the name used for this projection in generated lemma names. The default is the
  last component of the name of the declaration.
* `(self := x)`: the self argument is the argument named `x`, or the `x`-th argument if `x` is a
  number. This is needed when an extra argument also depends on all the arguments before it, as
  `i` does in `RelCWComplex.openCell [RelCWComplex C D] (n : ℕ) (i : cell C n)`.
* `(rules := l₁, …)`: lemmas to simplify with when computing right-hand sides.
* `(attr := …)`: attributes to add to the lemmas generated for this projection.
* `as_prefix`: the name of the projection is added at the start of the lemma name.
* `noRecurse`: don't recurse into the result. The right-hand side is instead expanded by an
  η-rule of its type, if one is registered (see below). Such projections only apply to the
  declaration and its genuine projections, not to the results of other generalized projections:
  `pullback.lift a b w ≫ (e.hom ≫ pullback.fst _ _)` would follow from the lemma for
  `e.hom ≫ pullback.fst _ _`.
* `nonDefault`: only generate lemmas for this projection if it is asked for explicitly.

## Replacing genuine projections

`initialize_simps_projections!! N (p → q₁ … qₙ)` declares that the generalized projections
`N.q₁`, …, `N.qₙ` replace the genuine projection `p` of a structure: when one of them applies,
`simps!!` generates no lemmas for `p`. For instance, `PullbackCone.fst` and `PullbackCone.snd`
replace `Cone.π`, and `PullbackCone.IsLimit.lift` replaces `IsLimit.lift`:
```
initialize_simps_projections!! PullbackCone (π → fst snd)
initialize_simps_projections!! PullbackCone.IsLimit (lift → lift)
```

## η-rules

An η-rule is a theorem `∀ params (x : T), x = c (p₁ x) … (pₙ x)`, registered with
`@[simps_eta]`, that expresses a term of `T` by its generalized projections. After a `noRecurse`
generalized projection, the lemma is stated as `p t extras = c rhs₁ … rhsₙ` instead, where the
`rhsᵢ` are computed by `simp` from `pᵢ (p t extras)`, using the lemmas generated so far. This is
how `simps!!` states the universal property of a limit `L` in terms of a limit `R`, for an
isomorphism `e : L ≅ R`:
`pullback.lift a b w ≫ e.hom = R.lift (…) (…)`.

## `to_dual`

* `@[to_dual (attr := simps_proj opts)]` registers both the declaration and its dual: for the
  dual, `comp` and `precomp` are exchanged, and the `rules` are replaced by their duals. So
  `@[to_dual (attr := simps_proj comp)]` on `pullback.fst` registers `pushout.inl` with
  `precomp`.
* `@[to_dual (attr := simps_eta)]` registers both η-rules.
* `initialize_simps_projections!!` also declares the dual replacements, when the generalized
  projections and the projection `p` have `to_dual` translations: after
  `initialize_simps_projections!! PullbackCone (π → fst snd)`, `PushoutCocone.inl` and
  `PushoutCocone.inr` replace `Cocone.ι`.
* `@[to_dual (attr := simps!!)]` generates the lemmas of the declaration and of its dual, and
  adds the translations between them. Their `reassoc` versions get `to_dual none`, as with
  `@[to_dual (attr := reassoc)]`.

## Overlapping registrations

Generalized projections and η-rules are found by matching types up to reducible unfolding, so a
registration for `W ⟶ equalizer f g` also applies to `W ⟶ kernel f`, which unfolds to
`W ⟶ equalizer f 0`. When several generalized projections with the same name apply, only the most
specific ones are used (those whose discrimination tree keys have the fewest `*`s), and so is the
most specific η-rule: once kernels have their own registrations, morphisms into kernels get
lemmas about `kernel.ι` and `kernel.lift` only.

## Limitations

* Only fully applied lemmas are generated (`-fullyApplied` is ignored for generalized
  projections).
* `comp` and `precomp` are for morphisms in a category (`CategoryTheory.CategoryStruct.comp`).
* Generalized projections that are definitions applied to structure instances are unfolded to
  compute right-hand sides, so their bodies must be exposed (e.g. be `abbrev`s or `@[expose]`) to
  be unfolded in other modules.
-/

public meta section

open Lean Meta Elab Term

namespace Lean.Parser.Attr

/-- `(name := n)` option of `@[simps_proj]`. -/
syntax simpsProjName := atomic(" (" &"name" " := ") ident ")"
/-- `(rules := l₁, …)` option of `@[simps_proj]`. -/
syntax simpsProjRules := atomic(" (" &"rules" " := ") ident,+ ")"
/-- `(attr := …)` option of `@[simps_proj]`. -/
syntax simpsProjAttrs := atomic(" (" &"attr" " := ") Parser.Term.attrInstance,* ")"
/-- `(self := x)` option of `@[simps_proj]`: `x` is the name of an argument, or its position
(starting at `1`). -/
syntax simpsProjSelf := atomic(" (" &"self" " := ") (ident <|> num) ")"
/-- Flags of `@[simps_proj]`. -/
syntax simpsProjFlag :=
  &" comp" <|> &" precomp" <|> &" as_prefix" <|> &" noRecurse" <|> &" nonDefault"
/-- An option of `@[simps_proj]`. See `Mathlib.Tactic.Simps.Generalized` for their meanings. -/
syntax simpsProjOpt :=
  simpsProjName <|> simpsProjSelf <|> simpsProjRules <|> simpsProjAttrs <|> simpsProjFlag

/-- `@[simps_proj]` registers a function `p : ∀ params (x : S) extras, R` as a generalized
projection for `simps!!`: every definition (or field of a definition) of type `S` tagged
`@[simps!!]` gets a lemma `p params t extras = rhs`.

`@[simps_proj comp]` on a morphism `p : ∀ args, A ⟶ B` registers `fun h ↦ h ≫ p args` as a
generalized projection of morphisms `h : W ⟶ A`, and `@[simps_proj precomp]` registers
`fun h ↦ p args ≫ h` for morphisms `h : B ⟶ W`.

See the module documentation of `Mathlib.Tactic.Simps.Generalized` for details and options. -/
syntax (name := simpsProj) "simps_proj" (simpsProjOpt)* : attr

/-- `@[simps_eta]` registers a theorem `∀ params (x : T), x = c (p₁ x) … (pₙ x)` as an η-rule for
`simps!!`, which uses it to state the lemmas of `noRecurse` generalized projections whose result
has type `T`. See the module documentation of `Mathlib.Tactic.Simps.Generalized`. -/
syntax (name := simpsEta) "simps_eta" : attr

/-- `@[simps!!]` is `@[simps!]` with generalized projections, registered with `@[simps_proj]`.
See the module documentation of `Mathlib.Tactic.Simps.Generalized`. It takes the same arguments
as `@[simps]`; projection names may also be the names of generalized projections. -/
syntax (name := simpsGen) "simps!!" "?"? simpsArgsRest : attr

@[inherit_doc simpsGen] macro "simps!!?" rest:simpsArgsRest : attr => `(attr| simps!! ? $rest)

end Lean.Parser.Attr

namespace Lean.Parser.Command

/-- `(p → q₁ … qₙ)`: the generalized projections `qᵢ` replace the projection `p`. -/
syntax simpsGenReplace := " (" ident " → " ident+ ")"

/-- `initialize_simps_projections!! N (p → q₁ … qₙ)` declares that `simps!!` doesn't generate
lemmas for the (genuine) projection `p` of a structure when one of the generalized projections
`N.qᵢ` (registered with `@[simps_proj]`) applies. For instance,
```
initialize_simps_projections!! PullbackCone (π → fst snd)
```
gives definitions of pullback cones lemmas about `PullbackCone.fst` and `PullbackCone.snd`
instead of `Cone.π`.

If the `qᵢ` and `p` have `to_dual` translations, the same is declared for those. -/
syntax (name := initializeSimpsProjectionsGen)
  "initialize_simps_projections!!" ident (simpsGenReplace)* : command

end Lean.Parser.Command

namespace Simps.Gen

open Mathlib.Tactic

/-- Where the name of a generalized projection goes in the name of a generated lemma. -/
inductive NamePos where
  /-- At the end (the default). -/
  | suffix
  /-- At the start. -/
  | «prefix»
  /-- Before the last component. -/
  | precomp
  deriving Inhabited, BEq, Repr

/-- How a registered declaration `p` gives a generalized projection. -/
inductive ProjKind where
  /-- `p` itself is the generalized projection. -/
  | direct
  /-- `p` is a morphism, and the generalized projection is `fun h ↦ h ≫ p`. -/
  | comp
  /-- `p` is a morphism, and the generalized projection is `fun h ↦ p ≫ h`. -/
  | precomp
  deriving Inhabited, BEq, Repr

/-- The kind of the `to_dual` translation of a generalized projection. -/
def ProjKind.dual : ProjKind → ProjKind
  | .direct => .direct
  | .comp => .precomp
  | .precomp => .comp

/-- A generalized projection, registered with `@[simps_proj]`. -/
structure GenProj where
  /-- The registered declaration. -/
  declName : Name
  /-- The name of the projection, used in the names of generated lemmas. -/
  name : String
  /-- How `declName` gives the generalized projection. -/
  kind : ProjKind := .direct
  /-- The universe parameters of `type` and `value` (those of `declName`). -/
  levelParams : List Name
  /-- The type of the generalized projection, `∀ params (x : S) extras, R`. -/
  type : Expr
  /-- The generalized projection: `declName` itself, or a composition with it. -/
  value : Expr
  /-- The index of the self argument in `type`. -/
  selfIdx : Nat
  /-- The discrimination tree keys of the type of the self argument. -/
  keys : Array DiscrTree.Key
  /-- Where the name goes in generated lemma names. -/
  pos : NamePos := .suffix
  /-- Extra lemmas to simplify with when computing right-hand sides. -/
  rules : Array Name := #[]
  /-- Extra attributes for the generated lemmas (`attrInstance` syntax). -/
  attrs : Array Syntax := #[]
  /-- Whether to recurse into the result. -/
  recurse : Bool := true
  /-- Whether lemmas are generated for this projection by default. -/
  isDefault : Bool := true
  /-- The options of the `@[simps_proj]` attribute, to recognize its application by `to_dual` to
  the dual declaration. -/
  opts : Array Syntax := #[]
  deriving Inhabited

instance : BEq GenProj := ⟨(·.declName == ·.declName)⟩

/-- An η-rule, registered with `@[simps_eta]`. -/
structure EtaRule where
  /-- The registered theorem. -/
  declName : Name
  /-- The index of the self argument (the left-hand side of the equation). -/
  selfIdx : Nat
  /-- The discrimination tree keys of the type of the self argument. -/
  keys : Array DiscrTree.Key
  deriving Inhabited

instance : BEq EtaRule := ⟨(·.declName == ·.declName)⟩

/-- The generalized projections, keyed by the type of their self argument, and by the name of
the registered declaration. -/
initialize projExt : SimpleScopedEnvExtension GenProj (DiscrTree GenProj × NameMap GenProj) ←
  registerSimpleScopedEnvExtension {
    initial := ({}, {})
    addEntry := fun (d, m) e => (d.insertKeyValue e.keys e, m.insert e.declName e) }

/-- The η-rules, keyed by the type of their self argument, and the set of their names. -/
initialize etaExt : SimpleScopedEnvExtension EtaRule (DiscrTree EtaRule × NameSet) ←
  registerSimpleScopedEnvExtension {
    initial := ({}, {})
    addEntry := fun (d, s) e => (d.insertKeyValue e.keys e, s.insert e.declName) }

/-- For each generalized projection (by the name of its declaration), the genuine projections
that `simps!!` doesn't generate lemmas for when it applies, declared with
`initialize_simps_projections!!`. -/
initialize hideExt : SimpleScopedEnvExtension (Name × Name) (NameMap (Array Name)) ←
  registerSimpleScopedEnvExtension {
    initial := {}
    addEntry := fun m (g, p) =>
      let ps := m.getD g #[]
      if ps.contains p then m else m.insert g (ps.push p) }

initialize registerTraceClass `simps.gen

/-! ### Registration -/

/-- The free variables `e` depends on: those occurring in it, and (recursively) in their types. -/
partial def depClosure (e : Expr) : MetaM FVarIdSet := do
  let rec go (todo : List FVarId) (acc : FVarIdSet) : MetaM FVarIdSet := do
    match todo with
    | [] => return acc
    | x :: todo =>
      if acc.contains x then go todo acc else
      let ty ← instantiateMVars (← x.getType)
      go ((collectFVars {} ty).fvarIds.toList ++ todo) (acc.insert x)
  go (collectFVars {} (← instantiateMVars e)).fvarIds.toList {}

/-- The index of the self argument of a generalized projection of type `type`: the last argument
whose type depends on all the arguments before it. -/
def findSelfIdx (type : Expr) : MetaM Nat :=
  forallTelescope type fun xs _ => do
    let mut best := none
    for h : i in [:xs.size] do
      let deps ← depClosure (← inferType xs[i])
      if (xs.extract 0 i).all (deps.contains ·.fvarId!) then best := some i
    let some i := best | throwError "no self argument found in{indentExpr type}"
    return i

/-- The discrimination tree keys for the type of the `selfIdx`-th argument of `type`. -/
def selfKeys (type : Expr) (selfIdx : Nat) : MetaM (Array DiscrTree.Key) := do
  let (xs, _, _) ← forallMetaBoundedTelescope type (selfIdx + 1)
  let some x := xs[selfIdx]? | throwError "not enough arguments in{indentExpr type}"
  withReducible <| DiscrTree.mkPath (← instantiateMVars (← inferType x))

/-- The first atom of `stx`. -/
partial def firstAtom : Syntax → String
  | .atom _ v => v
  | .node _ _ args => (args.map firstAtom).find? (· != "") |>.getD ""
  | _ => ""

/-- The `to_dual` translation of the declaration `n`, if there is one. -/
def dualName? (n : Name) : CoreM (Option Name) :=
  return Translate.findTranslationName? (← getEnv) ToDual.data n

/-- The type and the value of the generalized projection given by the declaration `decl`,
of kind `.comp` or `.precomp`, and the index of its self argument.

For `p : ∀ args, A ⟶ B` and `.comp`, this is `fun params {W} (h : W ⟶ A) extras ↦ h ≫ p args`,
where `params` are the arguments that `A` depends on and `extras` are the others. -/
def mkCompProj (decl : Name) (kind : ProjKind) : MetaM (Expr × Expr × Nat) := do
  let info ← getConstInfo decl
  let lvls := info.levelParams.map Level.param
  forallTelescope info.type fun xs body => do
    let body ← whnfR body
    let .const `Quiver.Hom us := body.getAppFn | throwError "`simps_proj`: with `comp` or \
      `precomp`, {.ofConstName decl} must be a morphism, but its type is{indentExpr body}"
    let #[obj, q, a, b] := body.getAppArgs |
      throwError "`simps_proj`: unexpected type{indentExpr body}"
    -- the arguments that the type of the self argument depends on (apart from `W`)
    let deps ← depClosure (mkApp3 body.getAppFn obj q (if kind == .comp then a else b))
    let params := xs.filter (deps.contains ·.fvarId!)
    let extras := xs.filter (!deps.contains ·.fvarId!)
    withLocalDecl `W .implicit obj fun w => do
    let selfTy := mkAppN (.const `Quiver.Hom us) <|
      if kind == .comp then #[obj, q, w, a] else #[obj, q, b, w]
    withLocalDeclD `h selfTy fun h => do
    let p := mkAppN (.const decl lvls) xs
    let val ← mkAppM `CategoryTheory.CategoryStruct.comp <|
      if kind == .comp then #[h, p] else #[p, h]
    let binders := params ++ #[w, h] ++ extras
    return (← mkForallFVars binders (← inferType val), ← mkLambdaFVars binders val,
      params.size + 1)

/-- The type and the value of the generalized projection given by the declaration `decl` itself,
with self argument the `selfIdx`-th one, and the index of its self argument.

This is `decl`, unless some arguments before the self argument don't occur in its type (like `W`
in `BinaryFan.IsLimit.lift {W : C} {s : BinaryFan X Y} (h : IsLimit s) (f : W ⟶ X) …`): those
are moved after the self argument, as they can't be found by unifying its type. -/
def mkDirectProj (decl : Name) (selfIdx : Nat) : MetaM (Expr × Expr × Nat) := do
  let info ← getConstInfo decl
  let c := Expr.const decl (info.levelParams.map .param)
  forallTelescope info.type fun xs _ => do
    let some self := xs[selfIdx]? | throwError "`simps_proj`: not enough arguments"
    let deps ← depClosure (← inferType self)
    let params := (xs.extract 0 selfIdx).filter (deps.contains ·.fvarId!)
    if params.size == selfIdx then return (info.type, c, selfIdx)
    let extras := xs.filter fun x => x != self && !params.contains x
    let binders := params.push self ++ extras
    let val := mkAppN c xs
    return (← mkForallFVars binders (← inferType val), ← mkLambdaFVars binders val, params.size)

open Lean.Parser.Attr in
/-- The generalized projection registered by `@[simps_proj opts]` on `decl`. If `dual`, this is
the application of the attribute to the `to_dual` translation of a declaration registered with
the same options: then `comp` and `precomp` are exchanged, and the `rules` are translated. -/
def mkGenProj (decl : Name) (opts : Array Syntax) (dual : Option Name) : MetaM GenProj := do
  let info ← getConstInfo decl
  unless info.hasValue (allowOpaque := false) && !info.isTheorem do
    throwError "`simps_proj`: {.ofConstName decl} must be a definition"
  let mut name := decl.lastComponentAsString
  let mut kind := ProjKind.direct
  let mut asPrefix := false
  let mut self? : Option Syntax := none
  let mut rules := #[]
  let mut attrs := #[]
  let mut recurse := true
  let mut isDefault := true
  for opt in opts do
    let opt := opt[0]
    match opt with
    | `(simpsProjName| (name := $n:ident)) => name := n.getId.toString
    | `(simpsProjRules| (rules := $ns:ident,*)) =>
      rules := rules ++ (← ns.getElems.mapM fun n => realizeGlobalConstNoOverloadWithInfo n)
    | `(simpsProjAttrs| (attr := $as:attrInstance,*)) => attrs := attrs ++ as.getElems.map (·.raw)
    | _ =>
      if opt.getKind == ``simpsProjSelf then
        self? := opt.getArgs.find? fun a => a.isIdent || a.isNatLit?.isSome
      else match (firstAtom opt).trimAscii.toString with
        | "comp" => kind := .comp
        | "precomp" => kind := .precomp
        | "as_prefix" => asPrefix := true
        | "noRecurse" => recurse := false
        | "nonDefault" => isDefault := false
        | _ => throwErrorAt opt "unknown `simps_proj` option"
  if dual.isSome then
    kind := kind.dual
    rules ← rules.mapM fun r => do
      let some r' ← dualName? r | throwError "`simps_proj`: the rule {.ofConstName r} has no \
        `to_dual` translation. Register {.ofConstName decl} separately."
      pure r'
  let (type, value, selfIdx) ← match kind with
    | .direct =>
      let selfIdx ← match self? with
        | none => findSelfIdx info.type
        | some x => forallTelescope info.type fun xs _ => do
          if let some n := x.isNatLit? then
            unless 0 < n && n ≤ xs.size do
              throwErrorAt x "`simps_proj`: {.ofConstName decl} has {xs.size} arguments"
            return n - 1
          let some i ← xs.findIdxM? fun x' => return (← x'.fvarId!.getUserName) == x.getId |
            throwErrorAt x "`simps_proj`: {.ofConstName decl} has no argument {x.getId}"
          return i
      mkDirectProj decl selfIdx
    | _ =>
      if let some x := self? then
        throwErrorAt x "`simps_proj`: `self` can't be used with `comp` or `precomp`"
      mkCompProj decl kind
  let keys ← selfKeys type selfIdx
  let pos := if asPrefix then .prefix else if kind == .precomp then .precomp else .suffix
  return {
    declName := decl
    levelParams := info.levelParams
    name := name
    kind := kind
    type := type
    value := value
    selfIdx := selfIdx
    keys := keys
    pos := pos
    rules := rules
    attrs := attrs
    recurse := recurse
    isDefault := isDefault
    opts := opts }

initialize registerBuiltinAttribute {
  name := `simpsProj
  descr := "register a generalized projection for `simps!!`"
  applicationTime := .afterCompilation
  add := fun decl stx kind => do
    let opts := stx[1].getArgs
    let projs := (projExt.getState (← getEnv)).2
    if projs.contains decl then
      throwError "`simps_proj`: {.ofConstName decl} is already registered"
    -- `@[to_dual (attr := simps_proj opts)]` applies `simps_proj opts` to both declarations: the
    -- second application is to the dual of a declaration registered with the same options
    let dual ← do
      let some src ← dualName? decl | pure none
      let some g := projs.find? src | pure none
      let sameOpts := g.opts.size == opts.size && (g.opts.zip opts).all fun (a, b) => a.structEq b
      pure <| if sameOpts then some src else none
    let g ← MetaM.run' <| mkGenProj decl opts dual
    trace[simps.gen] "registering {decl} as a generalized projection {g.name} \
      (to_dual translation of: {dual}), keyed on {g.keys}"
    projExt.add g kind }

/-- The structure that the self argument of `g` is an instance of. -/
def selfStructure (g : GenProj) : MetaM Name := do
  let (xs, _, _) ← forallMetaBoundedTelescope
    (g.type.instantiateLevelParams g.levelParams (g.levelParams.map fun _ => Level.zero))
    (g.selfIdx + 1)
  let some x := xs[g.selfIdx]? | throwError "not enough arguments in{indentExpr g.type}"
  let tgt ← whnfD (← inferType x)
  let some str := tgt.getAppFn.constName? | throwError "{.ofConstName g.declName} is not a \
    generalized projection of a structure"
  unless isStructure (← getEnv) str do throwError "{.ofConstName g.declName} is not a \
    generalized projection of a structure"
  return str

/-- The names of the projections of the structure `str` that `simps` uses: its fields, and its
custom projections. -/
def projNames (str : Name) : CoreM (Array Name) := do
  let env ← getEnv
  let custom := (Simps.structureExt.find? env str).elim #[] (·.2.map (·.name))
  return getStructureFields env str ++ custom

open Lean.Parser.Command Command in
elab_rules : command
  | `(initialize_simps_projections!! $ns:ident $[$groups:simpsGenReplace]*) => liftTermElabM do
    for group in groups do
      let `(simpsGenReplace| ($p:ident → $qs:ident*)) := group | throwUnsupportedSyntax
      for q in qs do
        let decl ← try realizeGlobalConstNoOverloadWithInfo (mkIdentFrom q (ns.getId ++ q.getId))
          catch _ => realizeGlobalConstNoOverloadWithInfo q
        let some g := (projExt.getState (← getEnv)).2.find? decl | throwErrorAt q
          "{.ofConstName decl} is not a generalized projection (registered with `@[simps_proj]`)"
        let str ← withRef q <| selfStructure g
        unless (← projNames str).contains p.getId do
          throwErrorAt p "{p.getId} is not a projection of the structure {.ofConstName str}"
        hideExt.add (decl, p.getId)
        -- the `to_dual` translation
        let some decl' ← dualName? decl | continue
        let some pDecl' ← dualName? (str ++ p.getId) | continue
        trace[simps.gen] "{decl'} replaces {pDecl'}"
        hideExt.add (decl', .mkSimple pDecl'.lastComponentAsString)

initialize registerBuiltinAttribute {
  name := `simpsEta
  descr := "register an η-rule for `simps!!`"
  add := fun decl _ kind => do
    if (etaExt.getState (← getEnv)).2.contains decl then
      throwError "`simps_eta`: {.ofConstName decl} is already registered"
    let info ← getConstInfo decl
    let (selfIdx, keys) ← MetaM.run' <| forallTelescope info.type fun xs concl => do
      let some (_, lhs, _) := concl.eq? |
        throwError "`simps_eta`: {.ofConstName decl} must be an equation `x = …`"
      let some selfIdx := xs.idxOf? lhs |
        throwError "`simps_eta`: the left-hand side of {.ofConstName decl} must be a variable"
      return (selfIdx, ← selfKeys info.type selfIdx)
    etaExt.add { declName := decl, selfIdx, keys } kind }

/-! ### Computing right-hand sides -/

/-- Whether `e` is an application of a structure constructor. -/
def isStructCtorApp (e : Expr) : MetaM Bool := do
  let .const c _ := e.getAppFn | return false
  let env ← getEnv
  let some (.ctorInfo ci) := env.find? c | return false
  return isStructure env ci.induct

/-- Whether `normalize` may unfold applications of `c`. -/
def canUnfold (c : Name) : MetaM Bool := do
  let some (.defnInfo _) := (← getEnv).find? c | return false
  if (← isProjectionFn c) || (← isInstance c) || (← isMatcher c) then return false
  return true

/-- Reduces `t` if it is a projection (or projection function) applied to a structure instance. -/
def reduceProjOfCtor? (t : Expr) : MetaM (Option Expr) := do
  match t with
  | .proj _ i s =>
    unless ← isStructCtorApp s do return none
    let some (.ctorInfo ci) := (← getEnv).find? s.getAppFn.constName! | return none
    return s.getAppArgs[ci.numParams + i]?
  | _ =>
    let .const c _ := t.getAppFn | return none
    let some info ← getProjectionFnInfo? c | return none
    let args := t.getAppArgs
    let some s := args[info.numParams]? | return none
    unless ← isStructCtorApp s do return none
    let some field := s.getAppArgs[info.numParams + info.i]? | return none
    return some <| mkAppN field (args.extract (info.numParams + 1)) |>.headBeta

/-- Unfolds the definitions that are applied to structure instances, and then reduces projections
of structure instances, `match`es on constructors and β-redexes, repeatedly. Projections of
structure instances are also reduced in implicit and instance arguments (including types), which
`dsimp` doesn't visit, so that the result is not stuck on mismatched types. -/
def normalize (e : Expr) : MetaM Expr := do
  let ctx ← Simp.mkContext {} (simpTheorems := #[]) (congrTheorems := ← getSimpCongrTheorems)
  let mut e := e
  for _ in [:16] do
    let e' ← Meta.transform e (pre := fun t => do
      let .const c _ := t.getAppFn | return .continue
      unless ← t.getAppArgs.anyM isStructCtorApp do return .continue
      -- a class projection, like the coercion `⇑(Equiv.mk f g l r) x`: unfold the instance
      if let some t' ← unfoldProjInst? t then
        trace[simps.gen] "unfolding the instance of {c}"
        return .visit t'
      unless ← canUnfold c do return .continue
      let some t' ← unfoldDefinition? t | return .continue
      trace[simps.gen] "unfolding {c}"
      return .visit t'.headBeta)
      (post := fun t => do
        let some t' ← reduceProjOfCtor? t | return .done t
        return .visit t')
    let (e', _) ← Meta.dsimp e' ctx
    if e' == e then return e
    e := e'
  return e

/-- The simp context of `simps!!`: the default simp set, together with `rules` and their `_assoc`
versions (if they exist). -/
def simpCtx (rules : Array Name) : MetaM Simp.Context := do
  let mut thms ← getSimpTheorems
  let env ← getEnv
  for r in rules do
    thms ← thms.addConst r
    let r' := r.appendAfter "_assoc"
    if env.contains r' then thms ← thms.addConst r'
  Simp.mkContext {} (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)

/-- Simplifies `e` with `simpCtx rules`. Returns the result and a proof that `e` equals it, or
`none` if it is definitionally equal to `e`.

Unlike `simps!`, this doesn't call `dsimp` first: `dsimp` rewrites implicit arguments, but not
instance arguments, which can leave terms like `@DFunLike.coe (α ≃ β') (EquivLike.toFunLike …β…)`
on which `simp` lemmas no longer unify. -/
def simpRhs (e : Expr) (rules : Array Name) : MetaM (Expr × Option Expr) := do
  let ctx ← simpCtx rules
  let simprocs := #[← Simp.getSimprocs]
  let (r, _) ← Meta.simp e ctx simprocs
  return (r.expr, r.proof?)

/-- Instantiates the generalized projection `g` for a self argument of type `tgt`: returns
`g.value` applied to its parameters (a function of the self argument and the extra arguments), or
`none` if `g` doesn't apply. -/
def instGenProj (g : GenProj) (tgt : Expr) : MetaM (Option Expr) := do
  let lvls ← g.levelParams.mapM fun _ => mkFreshLevelMVar
  let (xs, bis, _) ← forallMetaBoundedTelescope (g.type.instantiateLevelParams g.levelParams lvls)
    (g.selfIdx + 1)
  let some x := xs[g.selfIdx]? | return none
  unless ← isDefEq (← inferType x) tgt do return none
  let params := xs.pop
  for p in params, bi in bis do
    if bi.isInstImplicit && !(← p.mvarId!.isAssigned) then
      let .some inst ← trySynthInstance (← inferType p) | return none
      unless ← isDefEq p inst do return none
  let params ← params.mapM instantiateMVars
  if params.any (·.hasMVar) then return none
  let lvls ← lvls.mapM instantiateLevelMVars
  return (g.value.instantiateLevelParams g.levelParams lvls).beta params

/-- How specific the discrimination tree keys `keys` are: the number of keys that aren't `*`. -/
def specificity (keys : Array DiscrTree.Key) : Nat :=
  keys.foldl (fun n k => if k matches .star then n else n + 1) 0

/-- The generalized projections that apply to terms of type `tgt`, each with the result of
`instGenProj`.

Of the generalized projections with the same name, only the most specific ones are used: for
instance, a projection registered for `W ⟶ kernel f` takes precedence over one registered for
`W ⟶ equalizer f g`, which `kernel f` unfolds to. -/
def genProjsFor (tgt : Expr) : MetaM (Array (GenProj × Expr)) := do
  let cands ← withReducible <| (projExt.getState (← getEnv)).1.getMatch tgt
  let gens ← cands.filterMapM fun g => do
    let some f ← instGenProj g tgt | return none
    return some (g, f)
  return gens.filter fun (g, _) =>
    gens.all fun (g', _) => g'.name != g.name || specificity g'.keys ≤ specificity g.keys

/-- Applies an η-rule for the type of `x`, if there is one, the most specific one if there are
several: returns `x'` and a proof of `x = x'`. -/
def applyEta? (x : Expr) : MetaM (Option (Expr × Expr)) := do
  let tgt ← inferType x
  let rules ← withReducible <| (etaExt.getState (← getEnv)).1.getMatch tgt
  -- the most specific rule first (e.g. the one for `kernel f` rather than `equalizer f g`)
  for rule in rules.qsort (specificity ·.keys > specificity ·.keys) do
    let info ← getConstInfo rule.declName
    let lvls ← mkFreshLevelMVarsFor info
    let (xs, bis, concl) ← forallMetaTelescope (info.instantiateTypeLevelParams lvls)
    let some self := xs[rule.selfIdx]? | continue
    unless ← isDefEq self x do continue
    for p in xs, bi in bis do
      if bi.isInstImplicit && !(← p.mvarId!.isAssigned) then
        if let .some inst ← trySynthInstance (← inferType p) then
          discard <| isDefEq p inst
    let prf ← instantiateMVars (mkAppN (.const rule.declName lvls) xs)
    let concl ← instantiateMVars concl
    if prf.hasMVar then continue
    let some (_, _, rhs) := concl.eq? | continue
    return some (rhs, prf)
  return none

/-! ### Generating the lemmas -/

/-- The name of a generated lemma, as a list of components joined by `_`. -/
structure LemmaName where
  /-- The namespace of the lemma. -/
  parent : Name
  /-- The components of the last part of the name. -/
  components : List String

/-- The name of the lemma. -/
def LemmaName.toName (n : LemmaName) : Name :=
  .str n.parent <| match n.components with
    | [] => ""
    | [x] => s!"{x}_def"
    | e => "_".intercalate e

/-- Adds the projection name `s` to `n`, at position `pos`. -/
def LemmaName.update (n : LemmaName) (s : String) (pos : NamePos) : LemmaName :=
  { n with components := match pos, n.components.getLast? with
    | .suffix, _ | .precomp, none => n.components ++ [s]
    | .prefix, _ => s :: n.components
    | .precomp, some l => n.components.dropLast ++ [s, l] }

/-- A variant of `String.dropPrefix?` that doesn't consider `toFoo` to be a prefix of `toFoo_1`. -/
def dropPrefixIfNotNumber? (s pre : String) : Option String := do
  let ret ← s.dropPrefix? pre
  if ret.toString.toList.head?.elim false Char.isDigit then none else some ret.toString

/-- The state shared by the recursive calls of `addLemmas`. -/
structure Ctx where
  /-- The syntax of the attribute. -/
  ref : Syntax
  /-- The universe parameters of the declaration. -/
  univs : List Name
  /-- The configuration. -/
  cfg : Simps.Config
  /-- The head constant of the body of the declaration, if it is a definition (not a
  constructor). -/
  rootHead? : Option Name

/-- Adds the lemma `lhs = rhs` (with proof `prf`, or `rfl` if `none`), universally quantified
over `args`, under the name `nm`. -/
def addLemma (c : Ctx) (ref : Syntax) (nm : Name) (lhs rhs : Expr) (prf? : Option Expr)
    (args : Array Expr) (attrs : Array Syntax) : MetaM Unit :=
  withOptions (fun opts => backward.defeqAttrib.useBackward.set opts true) do
  let type ← inferType lhs
  let lvl ← getLevel type
  let prf := prf?.getD (mkApp2 (.const ``Eq.refl [lvl]) type lhs)
  let declType ← instantiateMVars <| ← mkForallFVars args (mkApp3 (.const ``Eq [lvl]) type lhs rhs)
  let declValue ← instantiateMVars <| ← mkLambdaFVars args prf
  if declType.hasMVar || declValue.hasMVar then
    throwError "`simps!!` failed to generate {nm}: the statement{indentExpr declType}\n\
      contains metavariables"
  if (← getEnv).contains nm then
    throwError "`simps!!` tried to add lemma{indentD m!"{.ofConstName nm} : {declType}"}\n\
      to the environment, but it already exists."
  Mathlib.Tactic.warnIfImplicitIllTyped ref nm declType
  prependError "Failed to add projection lemma {nm}:" do
    addDecl <| .thmDecl { name := nm, levelParams := c.univs, type := declType, value := declValue }
  trace[simps] "Adding `{.ofConstName nm}` :{indentExpr declType}"
  inferDefEqAttr nm
  addDeclarationRangesFromSyntax nm (← getRef) ref
  addTermInfo' ref (← mkConstWithLevelParams nm) (isBinder := true) |>.run'
  if c.cfg.isSimp then
    addSimpTheorem simpExtension nm true false .global <| eval_prio default
  TermElabM.run' do
    Term.applyAttributes nm c.cfg.attrs
    Term.applyAttributes nm (← elabAttrs attrs)

/-- The maximal nesting of generalized projections. -/
def maxDepth : Nat := 8

/-- A node of the tree of projections explored by `addLemmas`: the equation `lhs = rhs`, where
both sides have type `type` and contain the variables `args`. -/
structure Node where
  /-- The name of the lemma for this node. -/
  nm : LemmaName
  /-- The type of both sides. -/
  type : Expr
  /-- The left-hand side: (generalized) projections applied to the declaration. -/
  lhs : Expr
  /-- The right-hand side, computed from the body of the declaration, unfolded to constructor
  applications as needed. -/
  rhs : Expr
  /-- The same (generalized) projections applied to the body of the declaration, without
  unfolding it. Simplifying this often gives better results, by using the lemmas about the
  definitions the body is made of. -/
  folded : Expr
  /-- The variables in `lhs` and `rhs`. -/
  args : Array Expr
  /-- Whether this is the declaration itself, for which (generalized) projections must exist. -/
  mustBeStr : Bool := false
  /-- The projections asked for, as in `Simps.addProjections`. -/
  todo : List (String × Syntax)
  /-- The remaining indices of a custom composite projection. -/
  toApply : List Nat := []
  /-- The extra lemmas to simplify the right-hand side with. -/
  rules : Array Name := #[]
  /-- Whether `rhs` and `folded` are a generalized projection applied to a value, to be
  normalized. -/
  pending : Bool := false
  /-- Whether we got here through a `noRecurse` generalized projection. -/
  eta : Bool := false
  /-- Whether we got here through a generalized projection. -/
  viaGen : Bool := false
  /-- The number of generalized projections applied. -/
  depth : Nat := 0
  /-- The extra attributes for the lemma (those of the last generalized projection). -/
  attrs : Array Syntax := #[]

/-- The right-hand side of a lemma, with its proof (`none` for `rfl`): the simp normal form of
`folded`, if it no longer contains the head of the body of the declaration, and that of `rhs`
otherwise. -/
def finalRhs (c : Ctx) (rules : Array Name) (rhs folded : Expr) : MetaM (Expr × Option Expr) := do
  if !c.cfg.simpRhs then return (rhs, none)
  if let some h := c.rootHead? then
    let (r, prf?) ← simpRhs folded rules
    if !r.containsConst (· == h) then return (r, prf?)
    trace[simps.gen] "the folded right-hand side simplifies to{indentExpr r}\nwhich contains {h}"
  simpRhs rhs rules

/-- Derives the lemmas for the node `n`, by applying projections and generalized projections to
both sides, recursively. This follows `Simps.addProjections`. -/
partial def addLemmas (c : Ctx) (n : Node) : MetaM (Array Name) := do
  let cfg := c.cfg
  withTransparency cfg.typeMd <| forallTelescopeReducing n.type fun typeArgs tgt ↦ withDefault do
  let tgtWhnf ← whnfD tgt
  let nm := n.nm
  let newArgs := n.args ++ typeArgs
  let lhsAp := n.lhs.instantiateLambdasOrApps typeArgs
  let mut rhsAp := n.rhs.instantiateLambdasOrApps typeArgs
  let mut foldedAp := n.folded.instantiateLambdasOrApps typeArgs
  if n.pending then
    rhsAp ← normalize rhsAp
    foldedAp ← normalize foldedAp
  trace[simps.gen] "{nm.toName}, before simplification: {lhsAp} = {rhsAp}"
  let todo := n.todo
  let todoNext := todo.filter (·.1 ≠ "")
  let stx? := todo.find? (·.1 == "") |>.map (·.2)
  let stxProj := stx?.getD c.ref[0]
  let leaf (rhsAp : Expr) : MetaM (Array Name) := do
    let (rhs, prf?) ← do
      if n.eta then
        if let some (e, pe) ← applyEta? lhsAp then
          let (r, pr?) ← simpRhs e n.rules
          pure (r, some <| ← match pr? with
            | some pr => mkEqTrans pe pr
            | none => pure pe)
        else finalRhs c n.rules rhsAp foldedAp
      else finalRhs c n.rules rhsAp foldedAp
    addLemma c stxProj nm.toName lhsAp rhs prf? newArgs n.attrs
    return #[nm.toName]
  -- the generalized projections
  let gens ← if n.toApply.isEmpty && !n.eta && n.depth < maxDepth then genProjsFor tgt
    else pure #[]
  let gens := gens.filter fun (g, _) => !(todo.isEmpty && !g.isDefault) &&
    -- projections that don't recurse state a universal property of the object itself, which
    -- after a generalized projection would be redundant
    (g.recurse || !n.viaGen) &&
    (todo.isEmpty || todoNext.any fun (x, _) => (dropPrefixIfNotNumber? x (g.name ++ "_")).isSome)
  let hideMap := hideExt.getState (← getEnv)
  let hides := gens.flatMap fun (g, _) => hideMap.getD g.declName #[]
  -- the genuine projections
  let str := tgtWhnf.getAppFn.constName?.getD .anonymous
  let env ← getEnv
  let isStr := (getStructureInfo? env str).isSome && !n.eta &&
    !(todo.isEmpty && str ∈ cfg.notRecursive && !n.mustBeStr && n.toApply.isEmpty)
  let rhsEta ← Simps.headStructureEtaReduce rhsAp
  let rhsWhnf? ← if isStr then do
      let rhsWhnf ← withTransparency cfg.rhsMd <| whnf rhsEta
      if rhsWhnf.getAppFn.isConstOf (getStructureCtor env str).name then pure (some rhsWhnf)
      else pure none
    else pure none
  let projInfo ← match rhsWhnf? with
    | some rhsWhnf => Simps.getProjectionExprs c.ref tgtWhnf rhsWhnf cfg
    | none => pure #[]
  -- in the middle of a custom composite projection
  if let idx :: rest := n.toApply then
    let some ⟨newRhs, _⟩ := projInfo[idx]? |
      throwError "Invalid simp lemma {nm.toName}.\nThe given definition is not a constructor \
        application:{indentExpr rhsAp}"
    return ← addLemmas c { n with
      type := ← inferType newRhs, lhs := lhsAp, rhs := newRhs, folded := foldedAp, args := newArgs,
      mustBeStr := false, toApply := rest, pending := false }
  let projInfo := projInfo.filter fun (_, p) => !hides.contains p.name
  if projInfo.isEmpty && gens.isEmpty then
    if n.mustBeStr then
      throwError "Invalid `simps!!` attribute: neither projections nor generalized projections \
        apply to{indentExpr tgt}"
    if let some (x, _) := todoNext.head? then
      throwError "Invalid simp lemma {nm.toName}_{x.dropEnd 1}.\nNo projection or generalized \
        projection applies to{indentExpr tgt}"
    return ← leaf rhsEta
  let addThis := stx?.isSome
  let mut nms := #[]
  if addThis then nms := nms ++ (← leaf rhsEta)
  if todo.length == 1 && addThis then return nms
  -- check that every element of `todo` starts with a projection
  let names := projInfo.map (·.2.name.lastComponentAsString) ++ gens.map (·.1.name)
  if let some (x, _) := todoNext.find? fun (x, _) => names.all
      fun n => (dropPrefixIfNotNumber? x (n ++ "_")).isNone then
    throwError "Invalid simp lemma {nm.toName}_{x.dropEnd 1}. There is no projection or \
      generalized projection {x.dropEnd 1} for{indentExpr tgt}\nThe known ones are:\
      {indentD <| toMessageData names}"
  let newTodo (n : String) := todoNext.filterMap fun (x, stx) =>
    (dropPrefixIfNotNumber? x (n ++ "_")).map (·, stx)
  for ⟨newRhs, proj, projExpr, projNrs, isDefault, isPrefix⟩ in projInfo do
    let p := proj.lastComponentAsString
    if !(isDefault && todoNext.isEmpty) && (newTodo p).isEmpty then continue
    let newLhs := projExpr.instantiateLambdasOrApps #[lhsAp]
    -- the type of the left-hand side is the one written by the user, which is the one that
    -- generalized projections are keyed on (unlike the type of the value)
    nms := nms ++ (← addLemmas c { n with
      nm := nm.update p (if isPrefix then .prefix else .suffix), type := ← inferType newLhs,
      lhs := newLhs, rhs := newRhs, folded := projExpr.instantiateLambdasOrApps #[foldedAp],
      args := newArgs, mustBeStr := false, todo := newTodo p, toApply := projNrs,
      pending := false, eta := false, attrs := #[] })
  -- recursive generalized projections first, so that the lemmas they generate can be used by
  -- the others
  let gens := gens.filter (·.1.recurse) ++ gens.filter (!·.1.recurse)
  for (g, f) in gens do
    let newLhs := f.beta #[lhsAp]
    let newType ← inferType newLhs
    if ← isProp newType then continue
    nms := nms ++ (← addLemmas c {
      nm := nm.update g.name g.pos, type := newType, lhs := newLhs,
      rhs := f.beta #[rhsWhnf?.getD rhsAp], folded := f.beta #[foldedAp], args := newArgs,
      todo := newTodo g.name, rules := n.rules ++ g.rules, pending := true, eta := !g.recurse,
      viaGen := true, depth := n.depth + 1, attrs := g.attrs })
  return nms

/-- `simps!!` applied to the declaration `declName`. -/
def simpsGenTac (ref : Syntax) (declName : Name) (cfg : Simps.Config)
    (todo : List (String × Syntax)) (trc : Bool) : AttrM (Array Name) :=
  withOptions (fun o => if trc then o.set `trace.simps true else o) do
  let env ← withoutExporting getEnv
  let some d := env.find? declName | throwError "Declaration {declName} doesn't exist."
  let lhs : Expr := .const d.name <| d.levelParams.map .param
  let todo := todo.eraseDups.map fun (proj, stx) => (proj ++ "_", stx)
  let nm : LemmaName :=
    { parent := declName.getPrefix
      components :=
        if let some n := cfg.nameStem then
          if n == "" then [] else [n]
        else
          let s := declName.lastComponentAsString
          if (← isInstance declName) ∧ s.startsWith "inst" then [] else [s] }
  let body := d.value! (allowOpaque := true)
  let rootHead? := match body.getLambdaBody.getAppFn with
    | .const h _ => if (env.find? h matches some (.ctorInfo _)) then none else some h
    | _ => none
  withoutExporting <| MetaM.run' <| addLemmas { ref, univs := d.levelParams, cfg, rootHead? }
    { nm, type := d.type, lhs, rhs := body, folded := body, args := #[], mustBeStr := true, todo }

/-- The implementation of the `simps!!` attribute: returns the generated lemmas. -/
def simpsGenImpl (decl : Name) (stx : Syntax) : AttrM (Array Name) := do
  match stx with
  | `(attr| simps!! $[?%$trc]? $c:simpsConfig $[$ids]*) =>
    let cfg ← Simps.elabSimpsConfig c
    let cfg := { cfg with rhsMd := .default, simpRhs := true }
    let ids := ids.map fun x => (x.getId.eraseMacroScopes.lastComponentAsString, x.raw)
    simpsGenTac stx decl cfg ids.toList trc.isSome
  | _ => throwUnsupportedSyntax

initialize registerBuiltinAttribute {
  name := `simpsGen
  descr := "`simps!` with generalized projections"
  applicationTime := .afterCompilation
  add := fun decl stx _ => discard <| simpsGenImpl decl stx }

/-- The lemmas generated by `to_dual (attr := simps!!)` for the declarations it was applied to
first (`simps!!` is applied to a declaration first, and then to its dual). -/
initialize toDualLemmasRef : IO.Ref (NameMap (Array Name)) ← IO.mkRef {}

/- With `@[to_dual (attr := simps!!)]`, the lemmas generated for the declaration and for its dual
are translations of each other.

Their `reassoc` versions (added by the attributes of generalized projections) aren't: as `reassoc`
does for lemmas with a `to_dual` translation, we tag them `to_dual none`. This needs the
translations of the lemmas themselves, so we add those here, when `simps!!` is applied to the
dual declaration, rather than leaving them to `to_dual`. -/
initialize registerGeneratingAttr `simpsGen fun decl stx _ => do
  let lemmas ← simpsGenImpl decl stx
  let some src ← dualName? decl | return lemmas
  let some srcLemmas := (← toDualLemmasRef.get).find? src |
    toDualLemmasRef.modify (·.insert decl lemmas)
    return lemmas
  toDualLemmasRef.modify (·.erase src)
  Translate.insertTranslationsChecked ToDual.data srcLemmas lemmas { ref := stx }
  for nm in srcLemmas ++ lemmas do
    let nmAssoc := nm.appendAfter "_assoc"
    if (← getEnv).contains nmAssoc then
      liftCommandElabM <| Command.elabCommand <| ←
        `(command| attribute [to_dual none] $(mkIdent nmAssoc))
  return lemmas

end Simps.Gen
