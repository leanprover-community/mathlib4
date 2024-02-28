/-
Copyright (c) 2024 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import ProofWidgets.Component.PenroseDiagram
import ProofWidgets.Presentation.Expr
import Mathlib.Tactic.CategoryTheory.Coherence


/-!
# String Diagrams

This file provides tactic/meta infrastructure for displaying string diagrams for morphisms
in monoidal categories in the infoview.

-/

namespace Mathlib.Tactic.Widget.StringDiagram

open Lean Meta Elab
open CategoryTheory
open Mathlib.Tactic.Coherence

/-- Expressions for atomic 1-morphisms. -/
structure Atom₁ : Type where
  /-- Extract a Lean expression from an `Atom₁` expression. -/
  e : Expr

/-- Expressions for 1-morphisms. -/
inductive Mor₁ : Type
  /-- `id` is the expression for `𝟙_ C`. -/
  | id : Mor₁
  /-- `comp X Y` is the expression for `X ⊗ Y` -/
  | comp : Mor₁ → Mor₁ → Mor₁
  /-- Construct the expression for an atomic 1-morphism. -/
  | of : Atom₁ → Mor₁
  deriving Inhabited

/-- Converts a 1-morphism into a list of its underlying expressions. -/
def Mor₁.toList : Mor₁ → List Expr
  | .id => []
  | .comp f g => f.toList ++ g.toList
  | .of f => [f.e]

/-- Returns `𝟙_ C` if the expression `e` is of the form `𝟙_ C`. -/
def isTensorUnit? (e : Expr) : MetaM (Option Expr) := do
  let v ← mkFreshLevelMVar
  let u ← mkFreshLevelMVar
  let C ← mkFreshExprMVar none
  let instC ← mkFreshExprMVar none
  let instMC ← mkFreshExprMVar none
  let unit := mkAppN (.const ``MonoidalCategoryStruct.tensorUnit [v, u]) #[C, instC, instMC]
  if ← isDefEq e unit then
    return ← instantiateMVars unit
  else
    return none

/-- Returns `(f, g)` if the expression `e` is of the form `f ⊗ g`. -/
def isTensorObj? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let v ← mkFreshLevelMVar
  let u ← mkFreshLevelMVar
  let C ← mkFreshExprMVar none
  let f ← mkFreshExprMVar C
  let g ← mkFreshExprMVar C
  let instC ← mkFreshExprMVar none
  let instMC ← mkFreshExprMVar none
  let fg := mkAppN (.const ``MonoidalCategoryStruct.tensorObj [v, u]) #[C, instC, instMC, f, g]
  if ← withDefault <| isDefEq e fg then
    return (← instantiateMVars f, ← instantiateMVars g)
  else
    return none

/-- Construct a `Mor₁` expression from a Lean expression. -/
partial def toMor₁ (e : Expr) : MetaM Mor₁ := do
  if let some _ ← isTensorUnit? e then
    return Mor₁.id
  else if let some (f, g) ← isTensorObj? e then
    return (← toMor₁ f).comp (← toMor₁ g)
  else
    return Mor₁.of ⟨e⟩

/-- Expressions for atomic structural 2-morphisms. -/
inductive StructuralAtom : Type
  /-- The expression for the associator `(α_ f g h).hom`. -/
  | associator (f g h : Mor₁) : StructuralAtom
  /-- The expression for the inverse of the associator `(α_ f g h).inv`. -/
  | associatorInv (f g h : Mor₁) : StructuralAtom
  /-- The expression for the left unitor `(λ_ f).hom`. -/
  | leftUnitor (f : Mor₁) : StructuralAtom
  /-- The expression for the inverse of the left unitor `(λ_ f).inv`. -/
  | leftUnitorInv (f : Mor₁) : StructuralAtom
  /-- The expression for the right unitor `(ρ_ f).hom`. -/
  | rightUnitor (f : Mor₁) : StructuralAtom
  /-- The expression for the inverse of the right unitor `(ρ_ f).inv`. -/
  | rightUnitorInv (f : Mor₁) : StructuralAtom
  deriving Inhabited

/-- Construct a `StructuralAtom` expression from a Lean expression. -/
def structuralAtom? (e : Expr) : MetaM (Option StructuralAtom) := do
  match e.getAppFnArgs with
  | (``Iso.hom, #[_, _, _, _, η]) =>
    match (← whnfR η).getAppFnArgs with
    | (``MonoidalCategoryStruct.associator, #[_, _, _, f, g, h]) =>
      return some <| .associator (← toMor₁ f) (← toMor₁ g) (← toMor₁ h)
    | (``MonoidalCategoryStruct.leftUnitor, #[_, _, _, f]) => return some <| .leftUnitor (← toMor₁ f)
    | (``MonoidalCategoryStruct.rightUnitor, #[_, _, _, f]) => return some <| .rightUnitor (← toMor₁ f)
    | _ => return none
  | (``Iso.inv, #[_, _, _, _, η]) =>
    match (← whnfR η).getAppFnArgs with
    | (``MonoidalCategoryStruct.associator, #[_, _, _, f, g, h]) =>
      return some <| .associatorInv (← toMor₁ f) (← toMor₁ g) (← toMor₁ h)
    | (``MonoidalCategoryStruct.leftUnitor, #[_, _, _, f]) => return some <| .leftUnitorInv (← toMor₁ f)
    | (``MonoidalCategoryStruct.rightUnitor, #[_, _, _, f]) => return some <| .rightUnitorInv (← toMor₁ f)
    | _ => return none
  | _ => return none

/-- Expressions for atomic non-structural 2-morphisms. -/
structure Atom where
  /-- Extract a Lean expression from an `Atom` expression. -/
  e : Expr
  deriving Inhabited

/-- Expressions of the form `η ▷ f₁ ▷ ... ▷ fₙ`. -/
inductive WhiskerRightExpr : Type
  /-- Construct the expression for an atomic 2-morphism. -/
  | of (η : Atom) : WhiskerRightExpr
  /-- Construct the expression for `η ▷ f`. -/
  | whisker (η : WhiskerRightExpr) (f : Atom₁) : WhiskerRightExpr
  deriving Inhabited

/-- Expressions of the form `f₁ ◁ ... ◁ fₙ ◁ η`. -/
inductive WhiskerLeftExpr : Type
  /-- Construct the expression for a right-whiskered 2-morphism. -/
  | of (η : WhiskerRightExpr) : WhiskerLeftExpr
  /-- Construct the expression for `f ◁ η`. -/
  | whisker (f : Atom₁) (η : WhiskerLeftExpr) : WhiskerLeftExpr
  deriving Inhabited

/-- Expressions for structural 2-morphisms. -/
inductive Structural : Type
  /-- Expressions for atomic structural 2-morphisms. -/
  | atom (η : StructuralAtom) : Structural
  /-- Expressions for the identity `𝟙 f`. -/
  | id (f : Mor₁) : Structural
  /-- Expressions for the composition `η ≫ θ`. -/
  | comp (α β : Structural) : Structural
  /-- Expressions for the left whiskering `f ◁ η`. -/
  | whiskerLeft (f : Mor₁) (η : Structural) : Structural
  /-- Expressions for the right whiskering `η ▷ f`. -/
  | whiskerRight (η : Structural) (f : Mor₁) : Structural
  /-- Expressions for `α` in the monoidal composition `η ⊗≫ θ := η ≫ α ≫ θ`. -/
  | monoidalCoherence (f g : Mor₁) (e : Expr) : Structural
  deriving Inhabited

/-- Normalized expressions for 2-morphisms. -/
inductive NormalExpr : Type
  /-- Construct the expression for a structural 2-morphism. -/
  | nil (α : Structural) : NormalExpr
  /-- Construct the normalized expression of 2-morphisms recursively. -/
  | cons (head_structural : Structural) (head : WhiskerLeftExpr) (tail : NormalExpr) : NormalExpr
  deriving Inhabited

/-- The domain of a morphism. -/
def src (η : Expr) : MetaM Mor₁ := do
  match (← inferType η).getAppFnArgs with
  | (``Quiver.Hom, #[_, _, f, _]) => toMor₁ f
  | _ => throwError "{η} is not a morphism"

/-- The codomain of a morphism. -/
def tar (η : Expr) : MetaM Mor₁ := do
  match (← inferType η).getAppFnArgs with
  | (``Quiver.Hom, #[_, _, _, g]) => toMor₁ g
  | _ => throwError "{η} is not a morphism"

/-- The domain of a 2-morphism. -/
def Atom.src (η : Atom) : MetaM Mor₁ := do StringDiagram.src η.e
/-- The codomain of a 2-morphism. -/
def Atom.tar (η : Atom) : MetaM Mor₁ := do StringDiagram.tar η.e

/-- The domain of a 2-morphism. -/
def WhiskerRightExpr.src : WhiskerRightExpr → MetaM Mor₁
  | WhiskerRightExpr.of η => η.src
  | WhiskerRightExpr.whisker η f => return (← WhiskerRightExpr.src η).comp (Mor₁.of f)

/-- The codomain of a 2-morphism. -/
def WhiskerRightExpr.tar : WhiskerRightExpr → MetaM Mor₁
  | WhiskerRightExpr.of η => η.tar
  | WhiskerRightExpr.whisker η f => return (← WhiskerRightExpr.tar η).comp (Mor₁.of f)

/-- The domain of a 2-morphism. -/
def WhiskerLeftExpr.src : WhiskerLeftExpr → MetaM Mor₁
  | WhiskerLeftExpr.of η => WhiskerRightExpr.src η
  | WhiskerLeftExpr.whisker f η => return (Mor₁.of f).comp (← WhiskerLeftExpr.src η)

/-- The codomain of a 2-morphism. -/
def WhiskerLeftExpr.tar : WhiskerLeftExpr → MetaM Mor₁
  | WhiskerLeftExpr.of η => WhiskerRightExpr.tar η
  | WhiskerLeftExpr.whisker f η => return (Mor₁.of f).comp (← WhiskerLeftExpr.tar η)

/-- The domain of a 2-morphism. -/
def StructuralAtom.src : StructuralAtom → Mor₁
  | .associator f g h => (f.comp g).comp h
  | .associatorInv f g h => f.comp (g.comp h)
  | .leftUnitor f => Mor₁.id.comp f
  | .leftUnitorInv f => f
  | .rightUnitor f => f.comp Mor₁.id
  | .rightUnitorInv f => f

/-- The codomain of a 2-morphism. -/
def StructuralAtom.tar : StructuralAtom → Mor₁
  | .associator f g h => f.comp (g.comp h)
  | .associatorInv f g h => (f.comp g).comp h
  | .leftUnitor f => f
  | .leftUnitorInv f => Mor₁.id.comp f
  | .rightUnitor f => f
  | .rightUnitorInv f => f.comp Mor₁.id

/-- The domain of a 2-morphism. -/
def Structural.src : Structural → Mor₁
  | .atom η => η.src
  | .id f => f
  | .comp α _ => α.src
  | .whiskerLeft f η => f.comp η.src
  | .whiskerRight η f => η.src.comp f
  | .monoidalCoherence f _ _ => f

/-- The codomain of a 2-morphism. -/
def Structural.tar : Structural → Mor₁
  | .atom η => η.tar
  | .id f => f
  | .comp _ β => β.tar
  | .whiskerLeft f η => f.comp η.tar
  | .whiskerRight η f => η.tar.comp f
  | .monoidalCoherence _ g _ => g

/-- The domain of a 2-morphism. -/
def NormalExpr.src : NormalExpr → Mor₁
  | NormalExpr.nil η => η.src
  | NormalExpr.cons α _ _ => α.src

/-- The codomain of a 2-morphism. -/
def NormalExpr.tar : NormalExpr → Mor₁
  | NormalExpr.nil η => η.tar
  | NormalExpr.cons _ _ ηs => ηs.tar

/-- The associator as a term of `normalExpr`. -/
def NormalExpr.associator (f g h : Mor₁) : NormalExpr :=
  .nil <| .atom <| .associator f g h

/-- The inverse of the associator as a term of `normalExpr`. -/
def NormalExpr.associatorInv (f g h : Mor₁) : NormalExpr :=
  .nil <| .atom <| .associatorInv f g h

/-- The left unitor as a term of `normalExpr`. -/
def NormalExpr.leftUnitor (f : Mor₁) : NormalExpr :=
  .nil <| .atom <| .leftUnitor f

/-- The inverse of the left unitor as a term of `normalExpr`. -/
def NormalExpr.leftUnitorInv (f : Mor₁) : NormalExpr :=
  .nil <| .atom <| .leftUnitorInv f

/-- The right unitor as a term of `normalExpr`. -/
def NormalExpr.rightUnitor (f : Mor₁) : NormalExpr :=
  .nil <| .atom <| .rightUnitor f

/-- The inverse of the right unitor as a term of `normalExpr`. -/
def NormalExpr.rightUnitorInv (f : Mor₁) : NormalExpr :=
  .nil <| .atom <| .rightUnitorInv f

/-- Return `η` for `η ▷ g₁ ▷ ... ▷ gₙ`. -/
def WhiskerRightExpr.atom : WhiskerRightExpr → Atom
  | WhiskerRightExpr.of η => η
  | WhiskerRightExpr.whisker η _ => η.atom

/-- Return `η` for `f₁ ◁ ... ◁ fₙ ◁ η ▷ g₁ ▷ ... ▷ gₙ`. -/
def WhiskerLeftExpr.atom : WhiskerLeftExpr → Atom
  | WhiskerLeftExpr.of η => η.atom
  | WhiskerLeftExpr.whisker _ η => η.atom

/-- Construct a `Structural` expression from a Lean expression for a structural 2-morphism. -/
partial def structural? (e : Expr) : MetaM Structural := do
  match (← whnfR e).getAppFnArgs with
  | (``CategoryStruct.comp, #[_, _, _, α, β]) =>
    return .comp (← structural? α) (← structural? β)
  | (``CategoryStruct.id, #[_, f]) => return .id (← toMor₁ f)
  | (``MonoidalCategoryStruct.whiskerLeft, #[f, η]) =>
    return .whiskerLeft (← toMor₁ f) (← structural? η)
  | (``MonoidalCategoryStruct.whiskerRight, #[η, f]) =>
    return .whiskerRight (← structural? η) (← toMor₁ f)
  | (``Mathlib.Tactic.Coherence.MonoidalCoherence.hom, #[_, _, f, g, _, _, inst]) =>
    return .monoidalCoherence (← toMor₁ f) (← toMor₁ g) inst
  | _ => match ← structuralAtom? e with
    | some η => return .atom η
    | none => throwError "not a structural 2-morphism"

/-- Construct a `NormalExpr` expression from a Lean expression for an atomic 2-morphism. -/
def NormalExpr.of (η : Expr) : MetaM NormalExpr := do
  return .cons (.id (← StringDiagram.src η)) (.of (.of ⟨η⟩)) (.nil  (.id (← StringDiagram.tar η)))

/-- If `e` is an expression of the form `η ⊗≫ θ := η ≫ α ≫ θ` in the monoidal category `C`,
return the expression for `α` .-/
def structuralOfMonoidalComp (C e : Expr) : MetaM Structural := do
  let v ← mkFreshLevelMVar
  let u ← mkFreshLevelMVar
  _ ← isDefEq (.sort (.succ v)) (← inferType (← inferType e))
  _ ← isDefEq (.sort (.succ u)) (← inferType C)
  let W ← mkFreshExprMVar none
  let X ← mkFreshExprMVar none
  let Y ← mkFreshExprMVar none
  let Z ← mkFreshExprMVar none
  let f ← mkFreshExprMVar none
  let g ← mkFreshExprMVar none
  let α₀ ← mkFreshExprMVar none
  let instC ← mkFreshExprMVar none
  let αg := mkAppN (.const ``CategoryStruct.comp [v, u]) #[C, instC, X, Y, Z, α₀, g]
  let fαg := mkAppN (.const ``CategoryStruct.comp [v, u]) #[C, instC, W, X, Z, f, αg]
  _ ← isDefEq e fαg
  structural? α₀

/-- Evaluate the expression `η ≫ θ` into a normalized form. -/
partial def evalComp : NormalExpr → NormalExpr → MetaM NormalExpr
  | .nil α, .cons β η ηs => do
    return (.cons (α.comp β) η ηs)
  | .nil α, .nil α' => do
    return .nil (α.comp α')
  | .cons α η ηs, θ => do
    let ι ← evalComp ηs θ
    return .cons α η ι

/-- Evaluate the expression `f ◁ η` into a normalized form. -/
partial def evalWhiskerLeftExpr : Mor₁ → NormalExpr → MetaM NormalExpr
  | f, .nil α => do
    return .nil (.whiskerLeft f α)
  | .of f, .cons α η ηs => do
    let η' := WhiskerLeftExpr.whisker f η
    let θ ← evalWhiskerLeftExpr (.of f) ηs
    return (.cons (.whiskerLeft (.of f) α) η' θ)
  | .comp f g, η => do
    let θ ← evalWhiskerLeftExpr g η
    let ι ← evalWhiskerLeftExpr f θ
    let h := η.src
    let h' := η.tar
    let ι' ← evalComp ι (NormalExpr.associatorInv f g h')
    let ι'' ← evalComp (NormalExpr.associator f g h) ι'
    return ι''
  | .id, η => do
    let f := η.src
    let g := η.tar
    let η' ← evalComp η (NormalExpr.leftUnitorInv g)
    let η'' ← evalComp (NormalExpr.leftUnitor f) η'
    return η''

/-- Evaluate the expression `η ▷ f` into a normalized form. -/
partial def evalWhiskerRightExpr : NormalExpr → Mor₁ → MetaM NormalExpr
  | .nil α, h => do
    return .nil (.whiskerRight α h)
  | .cons α (.of η) ηs, .of f => do
    let θ ← evalWhiskerRightExpr ηs (.of f)
    return (.cons (.whiskerRight α (.of f)) (.of (.whisker η f)) θ)
  | .cons α (.whisker f η) ηs, h => do
    let g ← η.src
    let g' ← η.tar
    let η₁ ← evalWhiskerRightExpr (.cons (.id g) η (.nil (.id g'))) h
    let η₂ ← evalWhiskerLeftExpr (.of f) η₁
    let ηs₁ ← evalWhiskerRightExpr ηs h
    let α' := .whiskerRight α h
    let ηs₂ ← evalComp (.associatorInv (.of f) g' h) ηs₁
    let η₃ ← evalComp η₂ ηs₂
    let η₄ ← evalComp (.associator (.of f) g h) η₃
    let η₅ ← evalComp (.nil α') η₄
    return η₅
  | η, .comp g h => do
    let η₁ ← evalWhiskerRightExpr η g
    let η₂ ← evalWhiskerRightExpr η₁ h
    let f := η.src
    let f' := η.tar
    let η₃ ← evalComp η₂ (.associator f' g h)
    let η₄ ← evalComp (.associatorInv f g h) η₃
    return η₄
  | η, .id => do
    let f := η.src
    let g := η.tar
    let η₁ ← evalComp η (.rightUnitorInv g)
    let η₂ ← evalComp (.rightUnitor f) η₁
    return η₂

/-- Evaluate the expression of a 2-morphism into a normalized form. -/
partial def eval (e : Expr) : MetaM NormalExpr := do
  if let .some e' ← structuralAtom? e then return .nil <| .atom e' else
    match e.getAppFnArgs with
    | (``CategoryStruct.id, #[_, _, f]) =>
      return .nil (.id (← toMor₁ f))
    | (``CategoryStruct.comp, #[_, _, _, _, _, η, θ]) =>
      let η_e ← eval η
      let θ_e ← eval θ
      let ηθ ← evalComp η_e θ_e
      return ηθ
    | (``MonoidalCategoryStruct.whiskerLeft, #[_, _, _, f, _, _, η]) =>
      evalWhiskerLeftExpr (← toMor₁ f) (← eval η)
    | (``MonoidalCategoryStruct.whiskerRight, #[_, _, _, _, _, η, h]) =>
      evalWhiskerRightExpr (← eval η) (← toMor₁ h)
    | (``monoidalComp, #[C, _, _, _, _, _, _, _, _, η, θ]) =>
      let η_e ← eval η
      let α₀' ← structuralOfMonoidalComp C e
      let α := NormalExpr.nil α₀'
      let θ_e ← eval θ
      let αθ ← evalComp α θ_e
      let ηαθ ← evalComp η_e αθ
      return ηαθ
    | (``MonoidalCategoryStruct.tensorHom, #[_, _, _, _f₁, g₁, f₂, _g₂, η, θ]) =>
      /- Evaluate `η ⊗ 𝟙 f` and `𝟙 f ⊗ θ` as whiskerings. -/
      match η.getAppFnArgs, θ.getAppFnArgs with
      | _, (``CategoryStruct.id, #[_, _, f]) =>
        evalWhiskerRightExpr (← eval η) (← toMor₁ f)
      | (``CategoryStruct.id, #[_, _, f]), _ =>
        evalWhiskerLeftExpr (← toMor₁ f) (← eval θ)
      /- Otherwise, expand `tensorHom` by using `tensorHom_def`. -/
      | _, _ =>
        let η' ← evalWhiskerRightExpr (← eval η) (← toMor₁ f₂)
        let θ' ← evalWhiskerLeftExpr (← toMor₁ g₁) (← eval θ)
        evalComp η' θ'
    | _ => NormalExpr.of e

/-- Convert a `NormalExpr` expression into a list of `WhiskerLeftExpr` expressions. -/
def NormalExpr.toList : NormalExpr → List WhiskerLeftExpr
  | NormalExpr.nil _ => []
  | NormalExpr.cons _ η ηs => η :: NormalExpr.toList ηs

/-- Return `[f₁, ..., fₙ]` for `f₁ ◁ ... ◁ fₙ ◁ η ▷ g₁ ▷ ... ▷ gₙ`. -/
def leftMor₁List (η : WhiskerLeftExpr) : List Expr :=
  match η with
  | WhiskerLeftExpr.of _ => []
  | WhiskerLeftExpr.whisker f η => f.e :: leftMor₁List η

/-- Return `[gₙ, ..., g₁]` for `η ▷ g₁ ▷ ... ▷ gₙ`. -/
def rightMor₁ListAux (η : WhiskerRightExpr) : List Expr :=
  match η with
  | WhiskerRightExpr.of _ => []
  | WhiskerRightExpr.whisker η f => f.e :: rightMor₁ListAux η

/-- Return `[gₙ, ..., g₁]` for `f₁ ◁ ... ◁ fₙ ◁ η ▷ g₁ ▷ ... ▷ gₙ`. -/
def rightMor₁ListReversed (η : WhiskerLeftExpr) : List Expr :=
  match η with
  | WhiskerLeftExpr.of η => rightMor₁ListAux η
  | WhiskerLeftExpr.whisker _ η => rightMor₁ListReversed η

/-- Return `[g₁, ..., gₙ]` for `f₁ ◁ ... ◁ fₙ ◁ η ▷ g₁ ▷ ... ▷ gₙ`. -/
def rightMor₁List (η : WhiskerLeftExpr) : List Expr :=
  (rightMor₁ListReversed η).reverse

/-- Returns domain 1-morphisms as a list of components.` -/
def srcLists (η : WhiskerLeftExpr) : MetaM (List Expr × List Expr × List Expr) := do
  return (leftMor₁List η, (← η.atom.src).toList, rightMor₁List η)

/-- Returns codomain 1-morphisms as a list of components.` -/
def tarLists (η : WhiskerLeftExpr) : MetaM (List Expr × List Expr × List Expr) := do
  return (leftMor₁List η, (← η.atom.tar).toList, rightMor₁List η)

/-- `pairs [a, b, c, d]` is `[(a, b), (b, c), (c, d)]`. -/
def pairs {α : Type} : List α → List (α × α)
  | [] => []
  | [_] => []
  | (x :: y :: ys) => (x, y) :: pairs (y :: ys)

/-- A type for Penrose variables. -/
structure PenroseVar : Type where
  /-- The identifier of the variable. -/
  ident : String
  /-- The indices of the variable. -/
  indices : List ℕ
  /-- The underlying expression of the variable. -/
  e : Expr
  deriving Inhabited

instance : BEq PenroseVar := ⟨fun x y => x.ident == y.ident && x.indices == y.indices⟩

instance : Hashable PenroseVar := ⟨fun v ↦ hash (v.ident, v.indices)⟩

instance : ToString PenroseVar :=
  ⟨fun v => v.ident ++ v.indices.foldl (fun s x => s ++ s!"_{x}") ""⟩

/-- Expressions to display as labels in a diagram. -/
abbrev ExprEmbeds := Array (String × Expr)

/-! ## Widget for general string diagrams -/

open ProofWidgets

/-- The state of a diagram builder. -/
structure DiagramState where
  /-- The Penrose substance program.
  Note that `embeds` are added lazily at the end. -/
  sub : String := ""
  /-- Components to display as labels in the diagram,
  mapped as name ↦ (type, html). -/
  embeds : HashMap String (String × Html) := .empty
  /-- The start point of a string. -/
  startPoint : HashMap PenroseVar PenroseVar := .empty
  /-- The end point of a string. -/
  endPoint : HashMap PenroseVar PenroseVar := .empty

/-- The monad for building a string diagram. -/
abbrev DiagramBuilderM := StateT DiagramState MetaM

open scoped Jsx in
/-- Build a string diagram from state. -/
def buildDiagram : DiagramBuilderM (Option Html) := do
  let st ← get
  if st.sub == "" && st.embeds.isEmpty then
    return none
  let mut sub := "AutoLabel All\n"
  let mut embedHtmls := #[]
  for (n, (tp, h)) in st.embeds.toArray do
    sub := sub ++ s!"{tp} {n}\n"
    embedHtmls := embedHtmls.push (n, h)
  sub := sub ++ st.sub
  return <PenroseDiagram
    embeds={embedHtmls}
    dsl={include_str ".."/".."/".."/"widget"/"src"/"penrose"/"monoidal.dsl"}
    sty={include_str ".."/".."/".."/"widget"/"src"/"penrose"/"monoidal.sty"}
    sub={sub} />

/-- Add a substance `nm` of Penrose type `tp`,
labelled by `h` to the substance program. -/
def addEmbed (nm : String) (tp : String) (h : Html) : DiagramBuilderM Unit := do
  modify fun st => { st with embeds := st.embeds.insert nm (tp, h )}

open scoped Jsx in
/-- Add the variable `v` with the type `tp` to the substance program. -/
def addPenroseVar (tp : String) (v : PenroseVar) : DiagramBuilderM Unit := do
  let h := <InteractiveCode fmt={← Widget.ppExprTagged v.e} />
  addEmbed (toString v) tp h

/-- Add instruction `i` to the substance program. -/
def addInstruction (i : String) : DiagramBuilderM Unit := do
  modify fun st => { st with sub := st.sub ++ s!"{i}\n" }

/-- Add constructor `tp v := nm (vs)` to the substance program. -/
def addConstructor (tp : String) (v : PenroseVar) (nm : String) (vs : List PenroseVar) :
    DiagramBuilderM Unit := do
  let vs' := ", ".intercalate (vs.map (fun v => toString v))
  addInstruction s!"{tp} {v} := {nm} ({vs'})"

/-- Run the program in the diagram builder monad. -/
def DiagramBuilderM.run {α : Type} (x : DiagramBuilderM α) : MetaM α :=
  x.run' {}

open scoped Jsx in
/-- Construct a string diagram from a Penrose `sub`stance program and expressions `embeds` to
display as labels in the diagram. -/
def mkStringDiag (e : Expr) : MetaM Html := do
  DiagramBuilderM.run do
    let l := (← eval e).toList
    /- Add 2-morphisms. -/
    for (i, x) in l.enumFrom 1 do
      let v : PenroseVar := ⟨"E", [i], x.atom.e⟩
      addPenroseVar "Atom" v
      let (L, C, R) ← srcLists x
      let C' := (← x.atom.tar).toList
      for (j, X) in L.enum do
        let v' : PenroseVar := ⟨"I_left", [i, j], X⟩
        addPenroseVar "Id" v'
        addInstruction s!"Left({v'}, {v})"
        let v_mor : PenroseVar := ⟨"f", [i, j], X⟩
        let v_mor' : PenroseVar := ⟨"f", [i + 1, j], X⟩
        modify fun st => { st with
          endPoint := st.endPoint.insert v_mor v'
          startPoint := st.startPoint.insert v_mor' v' }
      for (j, X) in R.enum do
        let v' : PenroseVar := ⟨"I_right", [i, j], X⟩
        addPenroseVar "Id" v'
        addInstruction s!"Left({v}, {v'})"
        let v_mor : PenroseVar := ⟨"f", [i, j + L.length + C.length], X⟩
        let v_mor' : PenroseVar := ⟨"f", [i + 1, j + L.length + C'.length], X⟩
        modify fun st => { st with
          endPoint := st.endPoint.insert v_mor v'
          startPoint := st.startPoint.insert v_mor' v' }
      for (j, X) in C.enum do
        let v_mor : PenroseVar := ⟨"f", [i, j + L.length], X⟩
        modify fun st => { st with endPoint := st.endPoint.insert v_mor v }
      for (j, X) in C'.enum do
        let v_mor' : PenroseVar := ⟨"f", [i + 1, j + L.length], X⟩
        modify fun st => { st with startPoint := st.startPoint.insert v_mor' v }
      /- Add constraints. -/
      for (j, (X, Y)) in (pairs L).enum do
        let v₁ : PenroseVar := ⟨"I_left", [i, j], X⟩
        let v₂ : PenroseVar := ⟨"I_left", [i, j + 1], Y⟩
        addInstruction s!"Left({v₁}, {v₂})"
      /- Add constraints. -/
      for (j, (X, Y)) in (pairs R).enum do
        let v₁ : PenroseVar := ⟨"I_right", [i, j], X⟩
        let v₂ : PenroseVar := ⟨"I_right", [i, j + 1], Y⟩
        addInstruction s!"Left({v₁}, {v₂})"
    /- Add constraints. -/
    for (i, (x, y)) in (pairs l).enumFrom 1 do
      let v₁ : PenroseVar := ⟨"E", [i], x.atom.e⟩
      let v₂ : PenroseVar := ⟨"E", [i + 1], y.atom.e⟩
      addInstruction s!"Above({v₁}, {v₂})"
    /- The top of the diagram. -/
    if let some x₀ := l.head? then
      let v₀ : PenroseVar := ⟨"E", [1], x₀.atom.e⟩
      let (L, C, R) ← srcLists x₀
      for (j, X) in (L ++ C ++ R).enum do
        let v' : PenroseVar := ⟨"I_left", [0, j], X⟩
        addPenroseVar "Id" v'
        addInstruction s!"Above({v'}, {v₀})"
        let v_mor : PenroseVar := ⟨"f", [1, j], X⟩
        modify fun st => { st with startPoint := st.startPoint.insert v_mor v' }
      for (j, (X, Y)) in (pairs (L ++ C ++ R)).enum do
        let v₁ : PenroseVar := ⟨"I_left", [0, j], X⟩
        let v₂ : PenroseVar := ⟨"I_left", [0, j + 1], Y⟩
        addInstruction s!"Left({v₁}, {v₂})"
    /- The bottom of the diagram. -/
    if let some xₙ := l.getLast? then
      let vₙ : PenroseVar := ⟨"E", [l.length], xₙ.atom.e⟩
      let (L, C', R) ← tarLists xₙ
      for (j, X) in (L ++ C' ++ R).enum do
        let v' : PenroseVar := ⟨"I_left", [l.length + 1, j], X⟩
        addPenroseVar "Id" v'
        addInstruction s!"Above({vₙ}, {v'})"
        let v_mor : PenroseVar := ⟨"f", [l.length + 1, j], X⟩
        modify fun st => { st with endPoint := st.endPoint.insert v_mor v' }
      for (j, (X, Y)) in (pairs (L ++ C' ++ R)).enum do
        let v₁ : PenroseVar := ⟨"I_left", [l.length + 1, j], X⟩
        let v₂ : PenroseVar := ⟨"I_left", [l.length + 1, j + 1], Y⟩
        addInstruction s!"Left({v₁}, {v₂})"
    /- Add 1-morphisms as strings. -/
    for (i, x) in l.enumFrom 1 do
      let (L, C, R) ← srcLists x
      for (j, X) in (L ++ C ++ R).enum do
        let v : PenroseVar := ⟨"f", [i, j], X⟩
        let st ← get
        if let .some vStart := st.startPoint.find? v then
          if let .some vEnd := st.endPoint.find? v then
            addConstructor "Mor1" v "MakeString" [vStart, vEnd]
    /- Add strings in the last row. -/
    if let some xₙ := l.getLast? then
      let (L, C', R) ← tarLists xₙ
      for (j, X) in (L ++ C' ++ R).enum do
        let v : PenroseVar := ⟨"f", [l.length + 1, j], X⟩
        let st ← get
        if let .some vStart := st.startPoint.find? v then
          if let .some vEnd := st.endPoint.find? v then
            addConstructor "Mor1" v "MakeString" [vStart, vEnd]
    match ← buildDiagram with
    | some html => return html
    | none => return <span>No 2-morphisms.</span>

/-- Given a 2-morphism, return a string diagram. Otherwise `none`. -/
def stringM? (e : Expr) : MetaM (Option Html) := do
  let e ← instantiateMVars e
  return some <| ← mkStringDiag e

/-- Given an equality between 2-morphisms, return a string diagram of the LHS. Otherwise `none`. -/
def stringLeftM? (e : Expr) : MetaM (Option Html) := do
  let e ← instantiateMVars e
  let some (_, lhs, _) := e.eq? | return none
  return some <| ← mkStringDiag lhs

/-- Given an equality between 2-morphisms, return a string diagram of the RHS. Otherwise `none`. -/
def stringRightM? (e : Expr) : MetaM (Option Html) := do
  let e ← instantiateMVars e
  let some (_, _, rhs) := e.eq? | return none
  return some <| ← mkStringDiag rhs

/-- The string diagram widget. -/
@[expr_presenter]
def stringPresenter : ExprPresenter where
  userName := "String diagram"
  layoutKind := .block
  present type := do
    if let some d ← stringM? type then
      return d
    throwError "Couldn't find a string diagram."

/-- The string diagram widget. -/
@[expr_presenter]
def stringPresenterLeft : ExprPresenter where
  userName := "String diagram of LHS"
  layoutKind := .block
  present type := do
    if let some d ← stringLeftM? type then
      return d
    throwError "Couldn't find a string diagram."

/-- The string diagram widget. -/
@[expr_presenter]
def stringPresenterRight : ExprPresenter where
  userName := "String diagram of RHS"
  layoutKind := .block
  present type := do
    if let some d ← stringRightM? type then
      return d
    throwError "Couldn't find a string diagram."

end Mathlib.Tactic.Widget.StringDiagram
