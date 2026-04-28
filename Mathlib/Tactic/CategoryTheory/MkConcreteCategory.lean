/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.Tactic.ToAdditive

/-!
# The `mk_concrete_category` command

`mk_concrete_category C FC id comp` generates the standard initial boilerplate for a concrete
category whose morphisms are modeled by a bundled function type `FC`.

It creates a wrapper morphism structure `Hom`, a `Category` instance, a `ConcreteCategory`
instance, the public constructor `ofHom`, the projection abbreviation `Hom.hom`, and the basic
`dsimp`/round-trip lemmas.
-/

open Lean Elab Command
open CategoryTheory

namespace Mathlib.Tactic.CategoryTheory

/--
`mk_concrete_category C FC id comp` generates the standard boilerplate for a concrete category on
`C` whose underlying bundled hom type is `FC : C → C → Type*`, with identities given by `id` and
composition given by `comp`.

The command is intended to be used in the namespace of `C`. It creates declarations named `Hom`,
`Hom.hom`, `ofHom`, `hom_id`, `hom_comp`, `hom_ofHom`, and `ofHom_hom`.
-/
syntax (name := mkConcreteCategory) declModifiers "mk_concrete_category " term:max ppSpace
  term:max ppSpace term:max ppSpace term:max : command

/-- Variant of `mk_concrete_category` with a custom generated `ofHom` signature. -/
syntax (name := mkConcreteCategoryWithOfHom) declModifiers "mk_concrete_category " term:max ppSpace
  term:max ppSpace term:max ppSpace term:max ppSpace "with_of_hom"
  (ppSpace bracketedBinder)* ppSpace "hom_type " term:max ppSpace "from " term:max ppSpace
  "to " term:max : command

/-- Variant of `mk_concrete_category` generating multiplicative and additive categories together. -/
syntax (name := mkConcreteCategoryWithAdditive) declModifiers
  "mk_concrete_category " term:max ppSpace term:max ppSpace term:max ppSpace term:max ppSpace
  "to_additive " term:max ppSpace term:max ppSpace term:max ppSpace term:max : command

/-- Variant of `mk_concrete_category` combining the custom `ofHom` and additive forms. -/
syntax (name := mkConcreteCategoryWithOfHomAndAdditive) (priority := high) declModifiers
  "mk_concrete_category " term:max ppSpace term:max ppSpace term:max ppSpace term:max ppSpace
  "with_of_hom" (ppSpace bracketedBinder)* ppSpace "hom_type " term:max ppSpace
  "from " term:max ppSpace "to " term:max ppSpace
  "to_additive " term:max ppSpace term:max ppSpace term:max ppSpace term:max ppSpace
  "with_of_hom" (ppSpace bracketedBinder)* ppSpace "hom_type " term:max ppSpace
  "from " term:max ppSpace "to " term:max : command

/-- Whether a syntax tree contains a `to_additive` attribute. -/
private meta partial def hasToAdditiveAttr (stx : Syntax) : Bool :=
  match stx with
  | .ident _ _ n _ => n == `to_additive
  | .atom _ val => val == "to_additive"
  | .node _ k args => k == ``Mathlib.Tactic.ToAdditive.to_additive || args.any hasToAdditiveAttr
  | _ => false

/-- The first identifier occurring in a syntax tree. -/
private meta partial def firstIdent? (stx : Syntax) : Option Name :=
  if stx.isIdent then some stx.getId else
    match stx with
    | .node _ _ args => args.findSome? firstIdent?
    | _ => none

/-- The explicit target of a `@[to_additive Target]` attribute, if present. -/
private meta partial def toAdditiveTarget? (stx : Syntax) : Option Name :=
  if stx.isOfKind ``Mathlib.Tactic.ToAdditive.to_additive then
    firstIdent? stx
  else
    match stx with
    | .node _ _ args => args.findSome? toAdditiveTarget?
    | _ => none

/-- If a term is just an application to placeholder dots, return the applied function.

This lets the command recover from common inputs such as `LinearMap.id ·` and
`LinearMap.comp · ·`, where the dots are intended as a mnemonic for the arguments supplied by the
command rather than as Lean's usual placeholder abstraction.
-/
private meta partial def stripPlaceholderApplication (stx : Syntax) : TSyntax `term :=
  let stx :=
    if stx.isOfKind ``Lean.Parser.Term.paren then
      stripPlaceholderApplication stx[1]
    else if stx.isOfKind ``Lean.Parser.Term.app then
      let args := stx[1].getArgs
      if args.all (·.isOfKind ``Lean.Parser.Term.cdot) then
        ⟨stx[0]⟩
      else
        ⟨stx⟩
    else
      ⟨stx⟩
  stx

/-- Elaborator for the `mk_concrete_category ... to_additive ...` form. -/
@[command_elab mkConcreteCategoryWithAdditive]
public meta def elabMkConcreteCategoryWithAdditive : CommandElab := fun stx => do
  let `($_mods:declModifiers mk_concrete_category $cat $FC $idTerm $compTerm to_additive
      $addCat $addFC $addIdTerm $addCompTerm) := stx
    | throwUnsupportedSyntax
  let catNs ←
    if cat.raw.isIdent then pure <| mkIdent cat.raw.getId
    else throwErrorAt cat "category must be an identifier in the `to_additive` form"
  let addCatNs ←
    if addCat.raw.isIdent then pure <| mkIdent addCat.raw.getId
    else throwErrorAt addCat "additive category must be an identifier"
  elabCommand <| ← set_option hygiene false in `(command| namespace $addCatNs:ident)
  elabCommand <| ← set_option hygiene false in
    `(command| mk_concrete_category $addCat $addFC $addIdTerm $addCompTerm)
  elabCommand <| ← set_option hygiene false in `(command| end $addCatNs:ident)
  elabCommand <| ← set_option hygiene false in `(command| namespace $catNs:ident)
  elabCommand <| ← set_option hygiene false in
    `(command| mk_concrete_category $cat $FC $idTerm $compTerm)
  elabCommand <| ← set_option hygiene false in `(command| end $catNs:ident)

/-- Data for a custom generated `ofHom` declaration: binders, source hom type, source
object, and target object. -/
private abbrev CustomOfHomData :=
  TSyntaxArray `Lean.Parser.Term.bracketedBinder × TSyntax `term × TSyntax `term × TSyntax `term

/-- Core implementation of `mk_concrete_category`. -/
private meta def elabMkConcreteCategoryCore (mods : Syntax) (cat FC idTerm compTerm : TSyntax `term)
    (customOfHom? : Option CustomOfHomData) : CommandElabM Unit := do
  let useToAdditive := hasToAdditiveAttr mods
  let addHom? := toAdditiveTarget? mods |>.map fun n => mkCIdent (n ++ `Hom)
  let idBase : TSyntax `term := stripPlaceholderApplication idTerm
  let compBase : TSyntax `term := stripPlaceholderApplication compTerm
  let idWasStripped := idBase.raw != idTerm.raw
  let compWasStripped := compBase.raw != compTerm.raw
  let idDef : TSyntax `term ←
    if idWasStripped then
      `(term| by first | exact ($(idBase)) X | exact $(idBase))
    else
      `(term| ($(idBase)) X)
  let compDef : TSyntax `term ←
    if compWasStripped then
      `(term| ($(compBase)) g.hom' f.hom')
    else
      `(term| ($(compBase)) f.hom' g.hom')
  let homCompRhs : TSyntax `term ←
    if compWasStripped then
      `(term| ($(compBase)) g.hom f.hom)
    else
      `(term| ($(compBase)) f.hom g.hom)

  if useToAdditive then
    match addHom? with
    | some addHom =>
        elabCommand <| ← set_option hygiene false in `(command|
          set_option backward.privateInPublic true in
          /-- The type of morphisms in this concrete category. -/
          @[to_additive $addHom:ident, ext]
          structure Hom (X Y : $cat) where
            private mk ::
            /-- The underlying bundled morphism. -/
            hom' : (($FC : $cat → $cat → Type _)) X Y)
    | none =>
        elabCommand <| ← set_option hygiene false in `(command|
          set_option backward.privateInPublic true in
          /-- The type of morphisms in this concrete category. -/
          @[to_additive, ext]
          structure Hom (X Y : $cat) where
            private mk ::
            /-- The underlying bundled morphism. -/
            hom' : (($FC : $cat → $cat → Type _)) X Y)
  else
    elabCommand <| ← set_option hygiene false in `(command|
      set_option backward.privateInPublic true in
      /-- The type of morphisms in this concrete category. -/
      @[ext]
      structure Hom (X Y : $cat) where
        private mk ::
        /-- The underlying bundled morphism. -/
        hom' : (($FC : $cat → $cat → Type _)) X Y)

  if useToAdditive then
    elabCommand <| ← set_option hygiene false in `(command|
      set_option backward.privateInPublic true in
      set_option backward.privateInPublic.warn false in
      @[to_additive]
      instance instCategory : CategoryTheory.Category $cat where
        Hom X Y := Hom (X := X) (Y := Y)
        id X := Hom.mk (X := X) (Y := X) $idDef
        comp {X Y Z} f g := Hom.mk (X := X) (Y := Z) $compDef)
  else
    elabCommand <| ← set_option hygiene false in `(command|
      set_option backward.privateInPublic true in
      set_option backward.privateInPublic.warn false in
      instance instCategory : CategoryTheory.Category $cat where
        Hom X Y := Hom (X := X) (Y := Y)
        id X := Hom.mk (X := X) (Y := X) $idDef
        comp {X Y Z} f g := Hom.mk (X := X) (Y := Z) $compDef)

  if useToAdditive then
    elabCommand <| ← set_option hygiene false in `(command|
      set_option backward.privateInPublic true in
      set_option backward.privateInPublic.warn false in
      @[to_additive]
      instance instConcreteCategory :
          CategoryTheory.ConcreteCategory $cat (($FC : $cat → $cat → Type _)) where
        hom := fun f => Hom.hom' f
        ofHom := fun {X Y} f => Hom.mk (X := X) (Y := Y) f
        id_apply := by intros; rfl
        comp_apply := by intros; rfl)
  else
    elabCommand <| ← set_option hygiene false in `(command|
      set_option backward.privateInPublic true in
      set_option backward.privateInPublic.warn false in
      instance instConcreteCategory :
          CategoryTheory.ConcreteCategory $cat (($FC : $cat → $cat → Type _)) where
        hom := fun f => Hom.hom' f
        ofHom := fun {X Y} f => Hom.mk (X := X) (Y := Y) f
        id_apply := by intros; rfl
        comp_apply := by intros; rfl)

  if useToAdditive then
    elabCommand <| ← set_option hygiene false in `(command|
      /-- Turn a categorical morphism back into its underlying bundled morphism. -/
      @[to_additive]
      abbrev Hom.hom {X Y : $cat} (f : Hom (X := X) (Y := Y)) :=
        CategoryTheory.ConcreteCategory.hom (C := $cat) f)
  else
    elabCommand <| ← set_option hygiene false in `(command|
      /-- Turn a categorical morphism back into its underlying bundled morphism. -/
      abbrev Hom.hom {X Y : $cat} (f : Hom (X := X) (Y := Y)) :=
        CategoryTheory.ConcreteCategory.hom (C := $cat) f)

  match customOfHom? with
  | some (binders, homTy, source, target) =>
      if useToAdditive then
        elabCommand <| ← set_option hygiene false in `(command|
          /-- Typecheck a bundled morphism as a morphism in this concrete category. -/
          @[to_additive]
          abbrev ofHom $binders:bracketedBinder*
              (f : ($homTy)) : $source ⟶ $target :=
            CategoryTheory.ConcreteCategory.ofHom (C := $cat) f)
      else
        elabCommand <| ← set_option hygiene false in `(command|
          /-- Typecheck a bundled morphism as a morphism in this concrete category. -/
          abbrev ofHom $binders:bracketedBinder*
              (f : ($homTy)) : $source ⟶ $target :=
            CategoryTheory.ConcreteCategory.ofHom (C := $cat) f)
  | none =>
      if useToAdditive then
        elabCommand <| ← set_option hygiene false in `(command|
          /-- Typecheck a bundled morphism as a morphism in this concrete category. -/
          @[to_additive]
          abbrev ofHom {X Y : $cat} (f : (($FC : $cat → $cat → Type _)) X Y) : X ⟶ Y :=
            CategoryTheory.ConcreteCategory.ofHom (C := $cat) f)
      else
        elabCommand <| ← set_option hygiene false in `(command|
          /-- Typecheck a bundled morphism as a morphism in this concrete category. -/
          abbrev ofHom {X Y : $cat} (f : (($FC : $cat → $cat → Type _)) X Y) : X ⟶ Y :=
            CategoryTheory.ConcreteCategory.ofHom (C := $cat) f)

  if useToAdditive then
    elabCommand <| ← set_option hygiene false in `(command|
      /-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
      @[to_additive]
      def Hom.Simps.hom (X Y : $cat) (f : Hom (X := X) (Y := Y)) :
          (($FC : $cat → $cat → Type _)) X Y :=
        f.hom')
  else
    elabCommand <| ← set_option hygiene false in `(command|
      /-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
      def Hom.Simps.hom (X Y : $cat) (f : Hom (X := X) (Y := Y)) :
          (($FC : $cat → $cat → Type _)) X Y :=
        f.hom')

  elabCommand <| ← set_option hygiene false in `(command|
    initialize_simps_projections Hom (hom' → hom))
  match addHom? with
  | some addHom =>
      elabCommand <| ← set_option hygiene false in `(command|
        initialize_simps_projections $addHom:ident (hom' → hom))
  | none => pure ()

  if useToAdditive then
    elabCommand <| ← set_option hygiene false in `(command|
      @[to_additive (attr := simp), simp]
      lemma hom_id {X : $cat} : (𝟙 X : X ⟶ X).hom = $idDef :=
        rfl)
  else
    elabCommand <| ← set_option hygiene false in `(command|
      @[simp]
      lemma hom_id {X : $cat} : (𝟙 X : X ⟶ X).hom = $idDef :=
        rfl)

  if useToAdditive then
    elabCommand <| ← set_option hygiene false in `(command|
      @[to_additive (attr := simp), simp]
      lemma hom_comp {X Y Z : $cat} (f : X ⟶ Y) (g : Y ⟶ Z) :
          (f ≫ g).hom = $homCompRhs :=
        rfl)
  else
    elabCommand <| ← set_option hygiene false in `(command|
      @[simp]
      lemma hom_comp {X Y Z : $cat} (f : X ⟶ Y) (g : Y ⟶ Z) :
          (f ≫ g).hom = $homCompRhs :=
        rfl)

  if useToAdditive then
    elabCommand <| ← set_option hygiene false in `(command|
      @[to_additive (attr := simp), simp]
      lemma hom_ofHom {X Y : $cat} (f : (($FC : $cat → $cat → Type _)) X Y) :
          (CategoryTheory.ConcreteCategory.ofHom (C := $cat) f).hom = f :=
        rfl)
  else
    elabCommand <| ← set_option hygiene false in `(command|
      @[simp]
      lemma hom_ofHom {X Y : $cat} (f : (($FC : $cat → $cat → Type _)) X Y) :
          (CategoryTheory.ConcreteCategory.ofHom (C := $cat) f).hom = f :=
        rfl)

  if useToAdditive then
    elabCommand <| ← set_option hygiene false in `(command|
      @[to_additive (attr := simp), simp]
      lemma ofHom_hom {X Y : $cat} (f : X ⟶ Y) :
          CategoryTheory.ConcreteCategory.ofHom (C := $cat) f.hom = f :=
        rfl)
  else
    elabCommand <| ← set_option hygiene false in `(command|
      @[simp]
      lemma ofHom_hom {X Y : $cat} (f : X ⟶ Y) :
          CategoryTheory.ConcreteCategory.ofHom (C := $cat) f.hom = f :=
        rfl)

/-- Elaborator for `mk_concrete_category`. -/
@[command_elab mkConcreteCategory]
public meta def elabMkConcreteCategory : CommandElab := fun stx => do
  let `($mods:declModifiers mk_concrete_category $cat $FC $idTerm $compTerm) := stx
    | throwUnsupportedSyntax
  elabMkConcreteCategoryCore mods cat FC idTerm compTerm none

/-- Elaborator for the `mk_concrete_category ... with_of_hom ...` form. -/
@[command_elab mkConcreteCategoryWithOfHom]
public meta def elabMkConcreteCategoryWithOfHom : CommandElab := fun stx => do
  let `($mods:declModifiers mk_concrete_category $cat $FC $idTerm $compTerm with_of_hom
      $binders:bracketedBinder* hom_type $homTy from $source to $target) := stx
    | throwUnsupportedSyntax
  elabMkConcreteCategoryCore mods cat FC idTerm compTerm (some (binders, homTy, source, target))

/-- Elaborator for the `mk_concrete_category ... with_of_hom ... to_additive ...` form. -/
@[command_elab mkConcreteCategoryWithOfHomAndAdditive]
public meta def elabMkConcreteCategoryWithOfHomAndAdditive : CommandElab := fun stx => do
  let `($_mods:declModifiers mk_concrete_category $cat $FC $idTerm $compTerm with_of_hom
      $binders:bracketedBinder* hom_type $homTy from $source to $target to_additive
      $addCat $addFC $addIdTerm $addCompTerm with_of_hom $addBinders:bracketedBinder*
      hom_type $addHomTy from $addSource to $addTarget) := stx
    | throwUnsupportedSyntax
  let catNs ←
    if cat.raw.isIdent then pure <| mkIdent cat.raw.getId
    else throwErrorAt cat "category must be an identifier in the `to_additive` form"
  let addCatNs ←
    if addCat.raw.isIdent then pure <| mkIdent addCat.raw.getId
    else throwErrorAt addCat "additive category must be an identifier"
  elabCommand <| ← set_option hygiene false in `(command| namespace $addCatNs:ident)
  elabMkConcreteCategoryCore Syntax.missing addCat addFC addIdTerm addCompTerm
    (some (addBinders, addHomTy, addSource, addTarget))
  elabCommand <| ← set_option hygiene false in `(command| end $addCatNs:ident)
  elabCommand <| ← set_option hygiene false in `(command| namespace $catNs:ident)
  elabMkConcreteCategoryCore Syntax.missing cat FC idTerm compTerm
    (some (binders, homTy, source, target))
  elabCommand <| ← set_option hygiene false in `(command| end $catNs:ident)

end Mathlib.Tactic.CategoryTheory
