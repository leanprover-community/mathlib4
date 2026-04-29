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
category whose morphisms are modeled by a bundled function type `FC`. The identity term is applied
to an object, and the composition term is applied to the underlying morphism of the second
categorical morphism and then to the underlying morphism of the first.

The command is intended to be run in the namespace of the category it is defining. It creates a
wrapper morphism structure `Hom`, with private field `Hom.hom'`, and uses it as the
categorical morphism type. It then creates:

* `instCategory`, the `Category` instance with `id X = id X` and
  `comp f g = comp g.hom' f.hom'`;
* `instConcreteCategory`, the `ConcreteCategory C FC` instance;
* `Hom.hom`, an abbreviation for the `ConcreteCategory.hom` projection;
* `Hom.Simps.hom`, so `simps` uses the public concrete morphism projection;
* `ofHom`, a public abbreviation for `ConcreteCategory.ofHom`;
* simp lemmas `hom_id`, `hom_comp`, `hom_ofHom`, and `ofHom_hom`.

For example, the plain command

```lean
mk_concrete_category TestCat Fun Fun.id (Fun.comp · ·)
```

where `Fun.comp : Y.Fun Z → X.Fun Y → X.Fun Z`, generates an API where
`Hom.hom : X.Hom Y → X.Fun Y`, `ofHom : X.Fun Y → (X ⟶ Y)`,
`hom_id : Hom.hom (𝟙 X) = Fun.id X`, and
`hom_comp : Hom.hom (f ≫ g) = Fun.comp (Hom.hom g) (Hom.hom f)`.

For bundled categories whose public constructor should take unbundled objects, `with_of_hom`
customizes only the generated `ofHom` signature. The underlying `ConcreteCategory.ofHom` lemma still
uses bundled objects.

```lean
mk_concrete_category (ModuleTestCat R) (· →ₗ[R] ·)
  (fun _ => LinearMap.id) (LinearMap.comp · ·)
  with_of_hom {X Y : Type v} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
  hom_type (X →ₗ[R] Y) from (of R X) to (of R Y)
```

Here `ofHom` has type `(X →ₗ[R] Y) → (of R X ⟶ of R Y)`, while `hom_comp` states
`Hom.hom (f ≫ g) = LinearMap.comp (Hom.hom g) (Hom.hom f)`.

The identity and composition terms are ordinary Lean terms. Because categorical composition
`f ≫ g` is implemented as `comp g.hom' f.hom'`, the supplied `comp` should take the target-side
morphism first and the source-side morphism second. Placeholder abstractions such as
`LinearMap.comp · ·` keep Lean's usual argument order, which is exactly the order used by the
command.

The explicit `to_additive` forms are for pairs of categories where the multiplicative and additive
versions should be generated at the same time. They take the multiplicative category data and the
corresponding additive category data in one command. The elaborator first enters the additive
namespace and generates the additive concrete category, then enters the multiplicative namespace and
generates the multiplicative one. This is useful for commands such as the test case generating both
`MultiplicativeTestCat` with homs `X →* Y` and `AdditiveTestCat` with homs `X →+ Y`, including their
matching `ofHom`, `hom_id`, and `hom_comp` declarations.
-/

open Lean Elab Command
open CategoryTheory

namespace Mathlib.Tactic.CategoryTheory

/-!
The parser exposes four surface forms: the basic command, the same command with a custom `ofHom`
signature, a form that supplies multiplicative and additive category data together, and a combined
form with both `with_of_hom` and explicit additive data.
-/

/--
`mk_concrete_category C FC id comp` generates the standard boilerplate for a concrete category on
`C` whose underlying bundled hom type is `FC : C → C → Type*`, with identities given by `id X`
and composition given by `comp g.hom' f.hom'` for categorical morphisms `f : X ⟶ Y` and
`g : Y ⟶ Z`.

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

/-!
These helpers inspect raw syntax rather than elaborated terms. This command has to notice ordinary
command modifiers such as `@[to_additive]` before Lean elaborates them.
-/

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

/-!
The explicit `to_additive` forms generate declarations by entering the target namespaces and
running the same core generator there. These helpers keep the namespace checks and open/close
commands in one place.
-/

/-- Turn a category term from a `to_additive` form into the namespace identifier to generate in. -/
private meta def categoryNamespaceIdent (cat : TSyntax `term) (message : String) :
    CommandElabM Ident := do
  if cat.raw.isIdent then
    pure <| mkIdent cat.raw.getId
  else
    throwErrorAt cat message

/-- Elaborate commands inside a namespace generated by a `to_additive` form. -/
private meta def elabInNamespace (ns : Ident) (body : CommandElabM Unit) : CommandElabM Unit := do
  elabCommand <| ← set_option hygiene false in `(command| namespace $ns:ident)
  body
  elabCommand <| ← set_option hygiene false in `(command| end $ns:ident)

/-- Register that a declaration generated on the multiplicative side has an existing additive
counterpart generated by the explicit `to_additive` form. -/
private meta def registerToAdditiveExisting (src tgt : Name) : CommandElabM Unit := do
  let srcIdent := mkIdent src
  let tgtIdent := mkIdent tgt
  elabCommand <| ← set_option hygiene false in
    `(command|
      set_option linter.translateGenerateName false in
      set_option linter.existingAttributeWarning false in
      attribute [to_additive existing $tgtIdent:ident] $srcIdent:ident)

/-- Register the standard declarations generated by `mk_concrete_category` with `to_additive`, so
later `@[to_additive]` declarations can translate references to them. -/
private meta def registerConcreteCategoryToAdditive (catNs addCatNs : Name) :
    CommandElabM Unit := do
  for suffix in [`Hom, `instCategory, `instConcreteCategory, `Hom.hom, `ofHom,
      `Hom.Simps.hom, `hom_id, `hom_comp, `hom_ofHom, `ofHom_hom] do
    registerToAdditiveExisting (catNs ++ suffix) (addCatNs ++ suffix)

/-!
For the explicit `to_additive` form without `with_of_hom`, generation is just two ordinary
`mk_concrete_category` commands: one in the additive namespace, then one in the multiplicative
namespace. The additive side is generated first so any later `to_additive` naming choices on the
multiplicative side can refer to existing additive declarations.
-/

/-- Elaborator for the `mk_concrete_category ... to_additive ...` form. -/
@[command_elab mkConcreteCategoryWithAdditive]
public meta def elabMkConcreteCategoryWithAdditive : CommandElab := fun stx => do
  let `($_mods:declModifiers mk_concrete_category $cat $FC $idTerm $compTerm to_additive
      $addCat $addFC $addIdTerm $addCompTerm) := stx
    | throwUnsupportedSyntax
  let catNs ← categoryNamespaceIdent cat "category must be an identifier in the `to_additive` form"
  let addCatNs ← categoryNamespaceIdent addCat "additive category must be an identifier"
  elabInNamespace addCatNs do
    elabCommand <| ← set_option hygiene false in
      `(command| mk_concrete_category $addCat $addFC $addIdTerm $addCompTerm)
  elabInNamespace catNs do
    elabCommand <| ← set_option hygiene false in
      `(command| mk_concrete_category $cat $FC $idTerm $compTerm)
  registerConcreteCategoryToAdditive catNs.getId addCatNs.getId

/-- Data for a custom generated `ofHom` declaration: binders, source hom type, source
object, and target object. -/
private abbrev CustomOfHomData :=
  TSyntaxArray `Lean.Parser.Term.bracketedBinder × TSyntax `term × TSyntax `term × TSyntax `term

/-!
The core generator emits the declarations shared by all forms: `Hom`, the category and concrete
category instances, projections and constructors, simps support, and the round-trip lemmas. Most
branches below differ only in attributes, so the generated syntax is kept explicit to make the
resulting declarations predictable.
-/

/-- Core implementation of `mk_concrete_category`. -/
private meta def elabMkConcreteCategoryCore (mods : Syntax) (cat FC idTerm compTerm : TSyntax `term)
    (customOfHom? : Option CustomOfHomData) : CommandElabM Unit := do
  let useToAdditive := hasToAdditiveAttr mods
  let addHom? := toAdditiveTarget? mods |>.map fun n => mkCIdent (n ++ `Hom)
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
            hom' : ($FC : $cat → $cat → Type _) X Y)
    | none =>
        elabCommand <| ← set_option hygiene false in `(command|
          set_option backward.privateInPublic true in
          /-- The type of morphisms in this concrete category. -/
          @[to_additive, ext]
          structure Hom (X Y : $cat) where
            private mk ::
            /-- The underlying bundled morphism. -/
            hom' : ($FC : $cat → $cat → Type _) X Y)
  else
    elabCommand <| ← set_option hygiene false in `(command|
      set_option backward.privateInPublic true in
      /-- The type of morphisms in this concrete category. -/
      @[ext]
      structure Hom (X Y : $cat) where
        private mk ::
        /-- The underlying bundled morphism. -/
        hom' : ($FC : $cat → $cat → Type _) X Y)

  if useToAdditive then
    elabCommand <| ← set_option hygiene false in `(command|
      set_option backward.privateInPublic true in
      set_option backward.privateInPublic.warn false in
      @[to_additive]
      instance instCategory : CategoryTheory.Category $cat where
        Hom X Y := Hom (X := X) (Y := Y)
        id X := Hom.mk (X := X) (Y := X) (($idTerm) X)
        comp {X Y Z} f g := Hom.mk (X := X) (Y := Z) (($compTerm) g.hom' f.hom'))
  else
    elabCommand <| ← set_option hygiene false in `(command|
      set_option backward.privateInPublic true in
      set_option backward.privateInPublic.warn false in
      instance instCategory : CategoryTheory.Category $cat where
        Hom X Y := Hom (X := X) (Y := Y)
        id X := Hom.mk (X := X) (Y := X) (($idTerm) X)
        comp {X Y Z} f g := Hom.mk (X := X) (Y := Z) (($compTerm) g.hom' f.hom'))

  if useToAdditive then
    elabCommand <| ← set_option hygiene false in `(command|
      set_option backward.privateInPublic true in
      set_option backward.privateInPublic.warn false in
      @[to_additive]
      instance instConcreteCategory :
          CategoryTheory.ConcreteCategory $cat ($FC : $cat → $cat → Type _) where
        hom := fun f => Hom.hom' f
        ofHom := fun {X Y} f => Hom.mk (X := X) (Y := Y) f
        id_apply := by intros; rfl
        comp_apply := by intros; rfl)
  else
    elabCommand <| ← set_option hygiene false in `(command|
      set_option backward.privateInPublic true in
      set_option backward.privateInPublic.warn false in
      instance instConcreteCategory :
          CategoryTheory.ConcreteCategory $cat ($FC : $cat → $cat → Type _) where
        hom := fun f => Hom.hom' f
        ofHom := fun {X Y} f => Hom.mk (X := X) (Y := Y) f
        id_apply := by intros; rfl
        comp_apply := by intros; rfl)


  if useToAdditive then
    elabCommand <| ← set_option hygiene false in `(command|
      /-- Turn a categorical morphism back into its underlying bundled morphism. -/
      @[to_additive]
      abbrev Hom.hom {X Y : $cat} (f : X ⟶ Y) :=
        CategoryTheory.ConcreteCategory.hom (C := $cat) f)
  else
    elabCommand <| ← set_option hygiene false in `(command|
      /-- Turn a categorical morphism back into its underlying bundled morphism. -/
      abbrev Hom.hom {X Y : $cat} (f : X ⟶ Y) :=
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
          abbrev ofHom {X Y : $cat} (f : ($FC : $cat → $cat → Type _) X Y) : X ⟶ Y :=
            CategoryTheory.ConcreteCategory.ofHom (C := $cat) f)
      else
        elabCommand <| ← set_option hygiene false in `(command|
          /-- Typecheck a bundled morphism as a morphism in this concrete category. -/
          abbrev ofHom {X Y : $cat} (f : ($FC : $cat → $cat → Type _) X Y) : X ⟶ Y :=
            CategoryTheory.ConcreteCategory.ofHom (C := $cat) f)


  if useToAdditive then
    elabCommand <| ← set_option hygiene false in `(command|
      /-- Use the public `Hom.hom` projection for `@[simps]` lemmas. -/
      @[to_additive]
      def Hom.Simps.hom : (X : $cat) → (Y : $cat) → Hom (X := X) (Y := Y) →
          ($FC : $cat → $cat → Type _) X Y :=
        fun _ _ f => Hom.hom f)
  else
    elabCommand <| ← set_option hygiene false in `(command|
      /-- Use the public `Hom.hom` projection for `@[simps]` lemmas. -/
      def Hom.Simps.hom : (X : $cat) → (Y : $cat) → Hom (X := X) (Y := Y) →
          ($FC : $cat → $cat → Type _) X Y :=
        fun _ _ f => Hom.hom f)

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
      lemma hom_id {X : $cat} : (𝟙 X : X ⟶ X).hom = dsimp'% (($idTerm) X) :=
        rfl)
  else
    elabCommand <| ← set_option hygiene false in `(command|
      @[simp]
      lemma hom_id {X : $cat} : (𝟙 X : X ⟶ X).hom = dsimp'% (($idTerm) X) :=
        rfl)

  if useToAdditive then
    elabCommand <| ← set_option hygiene false in `(command|
      @[to_additive (attr := simp), simp]
      lemma hom_comp {X Y Z : $cat} (f : X ⟶ Y) (g : Y ⟶ Z) :
          (f ≫ g).hom = (($compTerm) g.hom f.hom) :=
        rfl)
  else
    elabCommand <| ← set_option hygiene false in `(command|
      @[simp]
      lemma hom_comp {X Y Z : $cat} (f : X ⟶ Y) (g : Y ⟶ Z) :
          (f ≫ g).hom = (($compTerm) g.hom f.hom) :=
        rfl)

  if useToAdditive then
    elabCommand <| ← set_option hygiene false in `(command|
      @[to_additive (attr := simp), simp]
      lemma hom_ofHom {X Y : $cat} (f : ($FC : $cat → $cat → Type _) X Y) :
          (CategoryTheory.ConcreteCategory.ofHom (C := $cat) f).hom = f :=
        rfl)
  else
    elabCommand <| ← set_option hygiene false in `(command|
      @[simp]
      lemma hom_ofHom {X Y : $cat} (f : ($FC : $cat → $cat → Type _) X Y) :
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

/-!
The remaining elaborators parse their surface syntax and delegate to the core generator. The
combined `with_of_hom`/`to_additive` form calls the core generator directly for each namespace
because each side has its own custom `ofHom` binders and source/target terms.
-/

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
  let catNs ← categoryNamespaceIdent cat "category must be an identifier in the `to_additive` form"
  let addCatNs ← categoryNamespaceIdent addCat "additive category must be an identifier"
  elabInNamespace addCatNs do
    elabMkConcreteCategoryCore Syntax.missing addCat addFC addIdTerm addCompTerm
      (some (addBinders, addHomTy, addSource, addTarget))
  elabInNamespace catNs do
    elabMkConcreteCategoryCore Syntax.missing cat FC idTerm compTerm
      (some (binders, homTy, source, target))
  registerConcreteCategoryToAdditive catNs.getId addCatNs.getId

end Mathlib.Tactic.CategoryTheory
