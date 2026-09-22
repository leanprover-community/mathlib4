/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Tactic.CategoryTheory.Op
public import Mathlib.Tactic.CategoryTheory.SpecializeMap

/-!
# A pilot bundle of categorical lemmas

`@[cat_lemmas]` proposes a small, fixed profile: an optional `op` stage, followed by a mapping
stage. Each stage retains its input branches. On a morphism equality named `H`, the default family
is `H`, `H_op`, `H_map`, `H_op_map`, in that order. Transformations are not iterated, and importing
another registration does not silently enlarge the profile. In particular, `H_op_map` maps an
equality in the opposite category; it is not the opposite of a mapped equality.

The mapping stage also accepts explicitly named functor templates as sibling alternatives:
```
@[cat_lemmas (specialize := [left := MonoidalCategory.tensorLeft,
                           right := MonoidalCategory.tensorRight])]
```
This adds `_left` and `_right` paths, without specializing a generic `_map` lemma or another
specialization. A request may override its suffix, as in `left := F (suffix := "_tensorLeft")`.
Repeated identical requests are ignored; distinct paths with the same target name are errors.
Template order is the written order, after generic `map`.

`(skip := [op, map, left])` removes the selected branches, including their descendants.
Skipping `map` does not disable specializations. Default transformations skip non-morphism
equalities. A requested specialization must apply to at least one retained input branch; it may
skip incompatible branches (for example, an opposite category incompatible with its template).
Malformed templates and implementation errors are always reported.

Simp registration is opt-in: `(simp)` marks the source and family. `(noSimp := [op, left])`
suppresses this registration along every path containing a selected step, including descendants.
It does not remove existing attributes. Normalization uses each transformation's own simp set,
independently of these options. Arbitrary source attributes are not copied.

`cat_lemmas?` generates the same family and reports names and attributes applied by this invocation.
The report uses the generation results, without rerunning the transformations.

Reassociation is deliberately left to its existing interface in this pilot. For example,
`attribute [reassoc] H_map` appends a general postcomposition morphism in the target category;
mapping `H_assoc` instead quantifies over a postcomposition morphism in the source category.
The existing nested attributes retain their order and their source/result propagation semantics.
-/

public meta section

open Lean Meta Elab Term
open Mathlib.Tactic.TheoremTransform

namespace Mathlib.Tactic.CategoryTheory.CatLemmas

/-- A profile step, with a user-facing selector and the complete transformation request. -/
structure Step where
  selector : Name
  request : Request
  required : Bool := false
  deriving BEq, Inhabited

/-- A generated declaration and its actual ordered path, including specialization arguments. -/
structure Generated where
  name : Name
  path : Array Step
  attributes : Array Name := #[]

/-- Options for the finite pilot profile. -/
structure Config where
  simp : Bool := false
  skip : Array Name := #[]
  noSimp : Array Name := #[]
  specializations : Array Step := #[]

/-- Run an explicitly ordered list of stages. Alternatives in one stage act on the same inputs,
never on each other's outputs. The registry supplies operations, not scheduling decisions. -/
def generate (src : Name) (ref : Syntax) (stages : Array (Array Step)) (cfg : Config) :
    MetaM (Array Generated) := do
  let attrs ← `(optAttrArg|)
  let mut results : Array Generated := #[⟨src, #[], #[]⟩]
  let mut claimed : NameMap (Array Step) := ({} : NameMap (Array Step)).insert src #[]
  for stage in stages do
    let inputs := results
    let mut seen : Array Step := #[]
    for step in stage do
      if cfg.skip.contains step.selector || seen.contains step then continue
      seen := seen.push step
      let mut applied := false
      let mut reason : MessageData := m!"no applicable input branch"
      for input in inputs do
        let path := input.path.push step
        let tgt ← step.request.targetName input.name
        if let some previous := claimed.find? tgt then
          if previous == path then continue
          throwError "distinct transformation paths generate the same name \
            '{privateToUserName tgt}'"
        claimed := claimed.insert tgt path
        match ← TheoremTransform.addDecl? step.request input.name ref attrs with
        | .error why => reason := why
        | .ok name =>
          applied := true
          results := results.push ⟨name, path, #[]⟩
      if step.required && !applied then
        throwError "request '{step.selector}' has no applicable branch:\n{reason}"
  if cfg.simp then
    let attrs ← TermElabM.run' <| elabOptAttrArg (← `(optAttrArg| (attr := simp)))
    results ← results.mapM fun result => do
      if result.path.any (fun step => cfg.noSimp.contains step.selector) then return result
      TermElabM.run' <| applyAttributes result.name attrs
      return { result with attributes := #[`simp] }
  return results

/-- A named functor-template request in the mapping stage. -/
syntax specialization := ident " := " ident (" (" &"suffix" " := " str ")")?

/-- The pilot's options may be written in any order. -/
declare_syntax_cat bundleOption

/-- Opt in to simp registration for the source and family. -/
syntax (name := bundleSimp) " (" &"simp" ")" : bundleOption
/-- Omit the selected transformations and their descendants. -/
syntax (name := bundleSkip) " (" &"skip" " := " "[" ident,* "]" ")" : bundleOption
/-- Suppress bundle simp registration along the selected paths. -/
syntax (name := bundleNoSimp) " (" &"noSimp" " := " "[" ident,* "]" ")" : bundleOption
/-- Add explicitly named functor templates as alternatives in the mapping stage. -/
syntax (name := bundleSpecialize)
  " (" &"specialize" " := " "[" specialization,* "]" ")" : bundleOption

private def elabConfig (options : Array (TSyntax `bundleOption)) : TermElabM Config := do
  let mut cfg : Config := {}
  for option in options do
    match option with
    | `(bundleOption| (simp)) => cfg := { cfg with simp := true }
    | `(bundleOption| (skip := [$names:ident,*])) =>
      cfg := { cfg with skip := cfg.skip ++ names.getElems.map (·.getId) }
    | `(bundleOption| (noSimp := [$names:ident,*])) =>
      cfg := { cfg with noSimp := cfg.noSimp ++ names.getElems.map (·.getId) }
    | `(bundleOption| (specialize := [$requests:specialization,*])) =>
      for request in requests.getElems do
        let `(specialization| $selector:ident := $F:ident $[(suffix := $suffix:str)]?) := request |
          throwUnsupportedSyntax
        let selector := selector.getId
        if selector == `map || selector == `op then
          throwError "'{selector}' is reserved for a default transformation"
        let F ← resolveGlobalConstNoOverload F
        let request : Request := {
          transformation := `specialize_map
          args := #[F]
          suffix? := some (suffix.map (·.getString) |>.getD ("_" ++ selector.toString)) }
        cfg := { cfg with specializations := cfg.specializations.push ⟨selector, request, true⟩ }
    | _ => throwUnsupportedSyntax
  let selectors := #[`op, `map] ++ cfg.specializations.map (·.selector)
  for selector in cfg.skip ++ cfg.noSimp do
    unless selectors.contains selector do throwError "unknown bundle selector '{selector}'"
  return cfg

/-- Generate a finite family of opposite and mapped lemmas; simp registration is opt-in. -/
syntax (name := catLemmas) "cat_lemmas" bundleOption* : attr

/-- Generate the family and report its names and the attributes applied by the bundle. -/
syntax (name := catLemmasDiagnostic) "cat_lemmas?" bundleOption* : attr

private def catLemmasImpl (src : Name) (ref : Syntax) (kind : AttributeKind) : AttrM (Array Name) :=
  MetaM.run' do
    unless kind == .global do throwAttrMustBeGlobal `cat_lemmas kind
    let (diagnostic, options) ← match ref with
      | `(attr| cat_lemmas $options:bundleOption*) => pure (false, options)
      | `(attr| cat_lemmas? $options:bundleOption*) => pure (true, options)
      | _ => throwUnsupportedSyntax
    let cfg ← TermElabM.run' <| elabConfig options
    let op : Step := ⟨`op, { transformation := `op }, false⟩
    let map : Step := ⟨`map, { transformation := `map }, false⟩
    let results ← generate src ref #[#[op], #[map] ++ cfg.specializations] cfg
    if diagnostic then
      let lines := results.toList.map fun result =>
        m!"{MessageData.ofConstName result.name}\
          {if result.attributes.isEmpty then "" else " [simp]"}"
      logInfo m!"Lemma family (attributes applied by cat_lemmas):\n\
        {MessageData.joinSep lines "\n"}"
    return results.extract 1 results.size |>.map (·.name)

initialize
  for name in [`catLemmas, `catLemmasDiagnostic] do
    registerGeneratingAttr name catLemmasImpl
    registerBuiltinAttribute {
      name := name
      descr := "generate a finite family of categorical lemmas"
      applicationTime := .afterCompilation
      add := fun src ref kind => discard <| catLemmasImpl src ref kind }

end Mathlib.Tactic.CategoryTheory.CatLemmas
