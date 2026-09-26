/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Tactic.CategoryTheory.HomTransform

/-!
# The `map` attribute

Adding `@[map]` to a lemma named `H` of shape `∀ .., f = g`, where `f` and `g` are morphisms
in some category `C`, creates a new lemma named `H_map` of the form
`∀ .. {D} (F : C ⥤ D), F.map f = F.map g` and then applies
`simp only [Functor.map_comp, Functor.map_id]`.

The generated lemma orders morphism universes before object universes, with source universes
before target universes in each group. Source parameters retain their names and relative order
within each group. A parameter used for both objects and morphisms goes in the morphism group;
parameters unrelated to category universes come last.

There is also a term elaborator `map_of% t` for use within proofs.
-/

public meta section

open Lean Meta Elab Tactic Qq
open CategoryTheory

namespace Mathlib.Tactic.CategoryTheory.Map

open TheoremTransform

/-- `simp only` with `Functor.map_comp` and `Functor.map_id` on a single expression
(used on each side via `simpEq`). -/
def mapCompSimp (e : Expr) : MetaM Simp.Result :=
  simpOnlyNames [``Functor.map_comp, ``Functor.map_id] e (config := { decide := false })

/-- Build and normalize a mapping proof at the given target-category universes. -/
def mapHomProof (p : Proof) (uLev vLev : Level) (attrName : Name := `map) :
    Term.TermElabM (Except MessageData Proof) := do
  match ← matchHomEquality p attrName with
  | .error reason => return .error reason
  | .ok ⟨u, v, C, instC, _X, _Y, f, g⟩ => do
    let e : Q($f = $g) := p.value
    let type : Q(Prop) := q(∀ {D : Type uLev} [_instD : Category.{vLev} D] (F : $C ⥤ D),
      F.map $f = F.map $g)
    let value : Q($type) := q(fun {D : Type uLev} [_instD : Category.{vLev} D]
      (F : $C ⥤ D) => F.congr_map $e)
    return .ok (← normalizeHomProof instC ⟨type, value⟩ mapCompSimp)

/-- Build the functor `map` lemma for `e : f = g` with target category levels `uLev`, `vLev`. -/
def mapExprHom (type : Q(Prop)) (e : Q($type)) (uLev vLev : Level)
    (attrName : Name := `map) : Term.TermElabM Expr := do
  match ← mapHomProof ⟨type, e⟩ uLev vLev attrName with
  | .ok p => p.toExpr
  | .error reason => throwError reason

/-- Map beneath the source telescope. After its original binders, the result has exactly three
binders: an implicit target category, its instance, and an explicit functor. `instantiateMap`
exposes those parameters as structured data for specialization clients. -/
def mapProof (p : Proof) (attrName : Name := `map) :
    Term.TermElabM (Except MessageData Proof) := do
  let uLev ← mkFreshLevelMVar
  let vLev ← mkFreshLevelMVar
  underForall p (mapHomProof · uLev vLev attrName)

/-- Produce a mapping proof without emitting a declaration. Target universes remain metavariables
until declaration finalization or surrounding term elaboration determines them. -/
def mapExpr (pf : Expr) (attrName : Name := `map) : Term.TermElabM Expr := do
  match ← mapProof (← Proof.ofExpr pf) attrName with
  | .ok p => p.toExpr
  | .error reason => throwError reason

/-- A mapping proof applied to metavariables, with source parameters kept separate from the
new functor. Its target category and instance are determined by specializing `functor`. -/
structure MapApplication where
  /-- Metavariables instantiating the original source telescope. -/
  sourceArgs : Array Expr
  /-- Original binder information, in the same order as `sourceArgs`. -/
  sourceInfos : Array BinderInfo
  /-- Functor metavariable; unify its type with the template's type before assigning it. -/
  functor : Expr
  /-- Mapping proof applied to its source and target parameters. -/
  value : Expr

/-- Instantiate the three appended binders specified by `mapProof`'s contract. This isolates the
mapping telescope's layout from parameter-specialization clients. No named map lemma is needed. -/
def instantiateMap (p : Proof) (attrName : Name := `map) :
    Term.TermElabM (Except MessageData MapApplication) := do
  match ← mapProof p attrName with
  | .error reason => return .error reason
  | .ok mapped => do
    let (args, infos, _) ← forallMetaTelescopeReducing mapped.type
    let sourceSize := args.size - 3
    return .ok { sourceArgs := args.extract 0 sourceSize
                 sourceInfos := infos.extract 0 sourceSize
                 functor := args.back!
                 value := mkAppN mapped.value args }

/-- Collect the universe parameters used for morphisms and objects in category-theoretic types.
Traversing the levels also handles expressions such as `max u v` and `u + 1`.
Reduce under binders to expose abbreviated instance types, and follow parent projections to
recognize structures inheriting from `Quiver`, such as `Groupoid`. -/
private partial def collectCategoryUniverses (type : Expr) :
    StateRefT (CollectLevelParams.State × CollectLevelParams.State) MetaM Unit := do
  forallTelescopeReducing type (whnfType := true) fun xs body => do
    for x in xs do
      collectCategoryUniverses (← inferType x)
    body.forEach fun e => do
      let (homLevels, objLevels) := match e with
        | .const ``Category [v, u] | .const ``CategoryStruct [v, u]
        | .const ``Quiver [v, u] | .const ``Quiver.Hom [v, u] => ([v], [u])
        | .const ``CategoryTheory.Functor [vC, vD, uC, uD] => ([vC, vD], [uC, uD])
        | _ => ([], [])
      modify fun (hom, obj) =>
        (CollectLevelParams.visitLevels homLevels hom, CollectLevelParams.visitLevels objLevels obj)
    let .const name _ := body.getAppFn | return
    let some path := getPathToBaseStructure? (← getEnv) ``Quiver name | return
    unless path.isEmpty do
      withLocalDeclD `inst body fun inst => do
        let quiver ← path.foldlM (fun inst proj => do
          let args := (← whnf (← inferType inst)).getAppArgs
          mkAppOptM proj (args.map some |>.push (some inst))) inst
        collectCategoryUniverses (← inferType quiver)

/-- Order universe parameters by their roles in the generated declaration's type.
Shared parameters belong to the morphism group; unrelated parameters are placed last.
Within each group, retain source order and put new target parameters after source parameters. -/
def orderMapUniverses (type : Expr) (source target : List Name) : MetaM (List Name) := do
  let (_, (hom, obj)) ← (collectCategoryUniverses type).run ({}, {})
  let (hom, obj) := (hom.params, obj.params)
  let isHom := hom.contains
  let isObj := fun n => obj.contains n && !isHom n
  return source.filter isHom ++ target.filter isHom ++
    source.filter isObj ++ target.filter isObj ++
    (source ++ target).filter (fun n => !isHom n && !isObj n)

/--
Adding `@[map]` to a lemma named `H` of shape `∀ .., f = g`, where `f` and `g` are morphisms
in some category `C`, creates a new lemma named `H_map` of the form
`∀ .. {D} (F : C ⥤ D), F.map f = F.map g` and then applies
`simp only [Functor.map_comp, Functor.map_id]`.

Use `@[map (attr := simp)]` to mark both the original lemma and `H_map` as `simp` lemmas, and
`@[map (attr := reassoc)]` to generate reassociated versions of both the original lemma and the
`_map` lemma (`@[reassoc (attr := map)]` generates `_map` versions of both the original and the
reassociated lemma, but this is of course less general than `@[map (attr := reassoc)]`). All four
lemmas can be registered as `simp` lemmas with `@[map (attr := reassoc (attr := simp))]`.
-/
syntax (name := mapStx) "map" optAttrArg : attr

/-- Finalize category universes using the established morphism-before-object ordering. -/
def finalizeMap (p : Proof) (levels : List Name) : Term.TermElabM (Expr × List Name) := do
  let (value, allLevels) ← generalize p levels
  let ordered ← orderMapUniverses (← inferType value) levels (allLevels.drop levels.length)
  return (value, ordered)

initialize TheoremTransform.register `map {
  suffix := "_map"
  apply := fun request p => do
    unless request.args.isEmpty do throwError "`map` takes no transformation arguments"
    mapProof p
  finalize := finalizeMap }

private def mapImpl (src : Name) (ref : Syntax) (kind : AttributeKind) : AttrM Name :=
  match ref with
  | `(attr| map $optAttr) => MetaM.run' do
    unless kind == .global do throwError "`map` can only be used as a global attribute"
    TheoremTransform.addDecl { transformation := `map } src ref optAttr
  | _ => throwUnsupportedSyntax

initialize
  registerGeneratingAttr `mapStx ((#[·]) <$> mapImpl · · ·)
  registerBuiltinAttribute {
    name := `mapStx
    descr := ""
    applicationTime := .afterCompilation
    add := fun src ref kind => discard <| mapImpl src ref kind }

/--
`map_of% t`, where `t` is an equality `f = g` between morphisms (possibly under `∀` binders),
produces the corresponding statement with a functor applied and
`simp only [Functor.map_comp, Functor.map_id]` on each side.
-/
elab "map_of% " t:term : term => do
  TheoremTransform.elabTerm { transformation := `map } t

end Mathlib.Tactic.CategoryTheory.Map
