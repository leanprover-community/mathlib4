/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.ConcreteCategory.Basic

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

private meta partial def containsCDot : Syntax → Bool
  | .node _ k args => k == ``Lean.Parser.Term.cdot || args.any containsCDot
  | _ => false

private meta partial def replaceCDots (repls : Array Syntax) : Syntax → StateT Nat MacroM Syntax
  | .node info k args => do
      if k == ``Lean.Parser.Term.cdot then
        let i ← get
        modify (· + 1)
        if h : i < repls.size then
          pure repls[i]
        else
          Macro.throwError "too many placeholders in hom-family argument"
      else
        return .node info k (← args.mapM (replaceCDots repls))
  | stx => pure stx

private meta def explicitHomFamilyLambda (cat FC : Term) : MacroM Term := do
  let X := mkIdentFrom FC.raw `X
  let Y := mkIdentFrom FC.raw `Y
  let body ← (replaceCDots #[X, Y] FC.raw).run' 0
  let bodyTerm : Term := ⟨body⟩
  `(fun $X:ident $Y:ident : ($cat:term) => ($bodyTerm:term))

private meta def homFamilyApp (FC X Y : Term) : MacroM Term := do
  if containsCDot FC.raw then
    return ⟨← (replaceCDots #[X.raw, Y.raw] FC.raw).run' 0⟩
  else
    `(($FC:term) $X $Y)

/--
`mk_concrete_category C FC id comp` generates the standard boilerplate for a concrete category on
`C` whose underlying bundled hom type is `FC : C → C → Type*`, with identities given by `id` and
composition given by `comp`.

The command is intended to be used in the namespace of `C`. It creates declarations named `Hom`,
`Hom.hom`, `ofHom`, `hom_id`, `hom_comp`, `hom_ofHom`, and `ofHom_hom`.
-/
syntax (name := mkConcreteCategory) "mk_concrete_category " term:max ppSpace term:max ppSpace
  term:max ppSpace term:max (ppSpace "without_hom_equiv")? : command

/-- Elaborator for `mk_concrete_category`. -/
@[command_elab mkConcreteCategory]
public meta def elabMkConcreteCategory : CommandElab := fun stx => do
  let `(mk_concrete_category $cat $FC $idTerm $compTerm $[without_hom_equiv]?) := stx
    | throwUnsupportedSyntax
  let genHomEquiv := stx[5].isNone
  let FCFam ←
    if containsCDot FC.raw then
      liftMacroM <| explicitHomFamilyLambda cat FC
    else
      pure FC
  let X : Term := mkIdent `X
  let Y : Term := mkIdent `Y
  let Z : Term := mkIdent `Z
  let FCXX ← liftMacroM <| homFamilyApp FC X X
  let FCXY ← liftMacroM <| homFamilyApp FC X Y
  let FCYZ ← liftMacroM <| homFamilyApp FC Y Z
  let FCXZ ← liftMacroM <| homFamilyApp FC X Z
  let idFam ← `(($idTerm:term : ∀ X : $cat, $FCFam X X))
  let compFam ← `(($compTerm:term : ∀ {X Y Z : $cat} (g : $FCFam Y Z) (f : $FCFam X Y),
    $FCFam X Z))

  -- Check the expected shape of the arguments before generating declarations, so errors are
  -- reported at the command invocation rather than inside the generated code.
  -- elabCommand <| ← set_option hygiene false in `(command|
  --   example : Sort _ := $cat)

  -- elabCommand <| ← set_option hygiene false in `(command|
  --   example : ∀ X Y : $cat, Sort _ := ($FCFam:term))

  -- elabCommand <| ← set_option hygiene false in `(command|
  --   example : ∀ X : $cat, ($FCFam:term) X X :=
  --     fun X => ($idFam:term) X)

  -- elabCommand <| ← set_option hygiene false in `(command|
  --   example : ∀ {X Y Z : $cat},
  --       ($FCFam:term) Y Z →
  --       ($FCFam:term) X Y →
  --       ($FCFam:term) X Z :=
  --     fun {X Y Z} g f => ($compFam:term) g f)

  elabCommand <| ← set_option hygiene false in `(command|
    set_option backward.privateInPublic true in
    /-- The type of morphisms in this concrete category. -/
    @[ext]
    structure Hom (X Y : $cat) where
      private mk ::
      /-- The underlying bundled morphism. -/
      hom' : $FCXY)

  elabCommand <| ← set_option hygiene false in `(command|
    set_option backward.privateInPublic true in
    set_option backward.privateInPublic.warn false in
    instance : CategoryTheory.Category $cat where
      Hom X Y := Hom X Y
      id X := ⟨($idFam:term) X⟩
      comp f g := ⟨($compFam:term) g.hom' f.hom'⟩)

  elabCommand <| ← set_option hygiene false in `(command|
    set_option backward.privateInPublic true in
    set_option backward.privateInPublic.warn false in
    instance : CategoryTheory.ConcreteCategory $cat $FCFam where
      hom := Hom.hom'
      ofHom := Hom.mk
      hom_ofHom := by intros; rfl
      ofHom_hom := by intros; rfl
      id_apply := by intros; rfl
      comp_apply := by intros; rfl)

  elabCommand <| ← set_option hygiene false in `(command|
    /-- Turn a categorical morphism back into its underlying bundled morphism. -/
    abbrev Hom.hom {X Y : $cat} (f : Hom X Y) : $FCXY :=
      CategoryTheory.ConcreteCategory.hom (C := $cat) (FC := $FCFam) f)

  elabCommand <| ← set_option hygiene false in `(command|
    /-- Typecheck a bundled morphism as a morphism in this concrete category. -/
    abbrev ofHom {X Y : $cat} (f : $FCXY) : X ⟶ Y :=
      CategoryTheory.ConcreteCategory.ofHom (C := $cat) (FC := $FCFam) f)

  elabCommand <| ← set_option hygiene false in `(command|
    /-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
    def Hom.Simps.hom (X Y : $cat) (f : Hom X Y) : $FCXY :=
      f.hom)

  elabCommand <| ← set_option hygiene false in `(command|
    initialize_simps_projections Hom (hom' → hom))

  elabCommand <| ← set_option hygiene false in `(command|
    @[simp]
    lemma hom_id {X : $cat} : (𝟙 X : X ⟶ X).hom = (($idFam) X) :=
      rfl)

  elabCommand <| ← set_option hygiene false in `(command|
    @[simp]
    lemma hom_comp {X Y Z : $cat} (f : X ⟶ Y) (g : Y ⟶ Z) :
        (f ≫ g).hom = dsimp% (($compFam) g.hom f.hom) :=
      rfl)

  elabCommand <| ← set_option hygiene false in `(command|
    @[simp]
    lemma hom_ofHom {X Y : $cat} (f : $FCXY) : (ofHom f).hom = f :=
      rfl)

  elabCommand <| ← set_option hygiene false in `(command|
    @[simp]
    lemma ofHom_hom {X Y : $cat} (f : X ⟶ Y) : ofHom f.hom = f :=
      rfl)

  if genHomEquiv then
    elabCommand <| ← set_option hygiene false in `(command|
      /-- `Hom.hom` bundled as an `Equiv`. -/
      def homEquiv {X Y : $cat} : (X ⟶ Y) ≃ $FCXY where
        toFun := Hom.hom
        invFun := ofHom
        left_inv _ := rfl
        right_inv _ := rfl)

    elabCommand <| ← set_option hygiene false in `(command|
      lemma hom_bijective {X Y : $cat} :
          Function.Bijective (Hom.hom : (X ⟶ Y) → $FCXY) :=
        homEquiv.bijective)

    elabCommand <| ← set_option hygiene false in `(command|
      lemma hom_injective {X Y : $cat} :
          Function.Injective (Hom.hom : (X ⟶ Y) → $FCXY) :=
        hom_bijective.injective)

    elabCommand <| ← set_option hygiene false in `(command|
      lemma hom_surjective {X Y : $cat} :
          Function.Surjective (Hom.hom : (X ⟶ Y) → $FCXY) :=
        hom_bijective.surjective)

end Mathlib.Tactic.CategoryTheory
