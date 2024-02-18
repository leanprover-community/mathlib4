/-
Copyright (c) 2024 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import ProofWidgets.Component.PenroseDiagram
import ProofWidgets.Presentation.Expr
import Mathlib.CategoryTheory.Monoidal.Category


/-!
# String Diagrams

This file provides tactic/meta infrastructure for displaying string diagrams for morphisms
in monoidal categories in the infoview.

-/

namespace Mathlib.Tactic.Widget.StringDiagram

open Lean Meta Elab
open CategoryTheory

/-- Expressions for atomic 1-morphisms. -/
structure Atom₁ : Type where
  /-- Extract a Lean expression from an `Atom₁` expression. -/
  e : Expr

/-- Expressions for 1-morphisms. -/
inductive Mor₁ : Type
  /-- Construct the expression for `𝟙_ C`. -/
  | id : Expr → Mor₁
  /-- Construct the expression for `X ⊗ Y` -/
  | comp : Mor₁ → Mor₁ → Mor₁
  /-- Construct the expression for an atomic 1-morphism. -/
  | of : Atom₁ → Mor₁
  deriving Inhabited

/-- Extract a Lean expression from a `Mor₁` expression. -/
def Mor₁.e : Mor₁ → MetaM Expr
  | .id C => do
    mkAppOptM ``MonoidalCategoryStruct.tensorUnit #[C]
  | .comp f g => do
    mkAppM ``MonoidalCategoryStruct.tensorObj #[← Mor₁.e f, ← Mor₁.e g]
  | .of f => return f.e

/-- Converts a 1-morphism into a list of its underlying expressions. -/
def Mor₁.toList : Mor₁ → List Expr
  | .id _ => []
  | .comp f g => f.toList ++ g.toList
  | .of f => [f.e]

/-- Construct a `Mor₁` expression from a Lean expression. -/
partial def toMor₁ (e : Expr) : Mor₁ :=
  match e.getAppFnArgs with
  | (``MonoidalCategoryStruct.tensorUnit, #[C, _, _]) => Mor₁.id C
  | (``MonoidalCategoryStruct.tensorObj, #[_, _, _, f, g]) => (toMor₁ f).comp (toMor₁ g)
  | _ => Mor₁.of ⟨e⟩

/-- Expressions for atomic structural 2-morphisms. -/
inductive StructuralAtom : Type
  /-- Construct the expression for the associator. -/
  | associator (f g h : Mor₁) : StructuralAtom
  /-- Construct the expression for the inverse of the associator. -/
  | associatorInv (f g h : Mor₁) : StructuralAtom
  /-- Construct the expression for the left unitor. -/
  | leftUnitor (f : Mor₁) : StructuralAtom
  /-- Construct the expression for the inverse of the left unitor. -/
  | leftUnitorInv (f : Mor₁) : StructuralAtom
  /-- Construct the expression for the right unitor. -/
  | rightUnitor (f : Mor₁) : StructuralAtom
  /-- Construct the expression for the inverse of the right unitor. -/
  | rightUnitorInv (f : Mor₁) : StructuralAtom
  deriving Inhabited

/-- Extract a Lean expression from a `StructuralAtom` expression. -/
def StructuralAtom.e : StructuralAtom → MetaM Expr
  | .associator f g h => do
    mkAppM ``Iso.hom #[← mkAppM ``MonoidalCategoryStruct.associator #[← f.e, ← g.e, ← h.e]]
  | .associatorInv f g h => do
    mkAppM ``Iso.inv #[← mkAppM ``MonoidalCategoryStruct.associator #[← f.e, ← g.e, ← h.e]]
  | .leftUnitor f => do mkAppM ``Iso.hom #[← mkAppM ``MonoidalCategoryStruct.leftUnitor #[← f.e]]
  | .leftUnitorInv f => do mkAppM ``Iso.inv #[← mkAppM ``MonoidalCategoryStruct.leftUnitor #[← f.e]]
  | .rightUnitor f => do mkAppM ``Iso.hom #[← mkAppM ``MonoidalCategoryStruct.rightUnitor #[← f.e]]
  | .rightUnitorInv f => do mkAppM ``Iso.inv #[← mkAppM ``MonoidalCategoryStruct.rightUnitor #[← f.e]]

/-- Construct a `StructuralAtom` expression from a Lean expression. -/
def structuralAtom? (e : Expr) : Option StructuralAtom := do
  match e.getAppFnArgs with
  | (``Iso.hom, #[_, _, _, _, η]) =>
    match η.getAppFnArgs with
    | (``MonoidalCategoryStruct.associator, #[_, _, _, f, g, h]) => return .associator (toMor₁ f) (toMor₁ g) (toMor₁ h)
    | (``MonoidalCategoryStruct.leftUnitor, #[_, _, _, f]) => return .leftUnitor (toMor₁ f)
    | (``MonoidalCategoryStruct.rightUnitor, #[_, _, _, f]) => return .rightUnitor (toMor₁ f)
    | _ => none
  | (``Iso.inv, #[_, _, _, _, η]) =>
    match η.getAppFnArgs with
    | (``MonoidalCategoryStruct.associator, #[_, _, _, f, g, h]) => return .associatorInv (toMor₁ f) (toMor₁ g) (toMor₁ h)
    | (``MonoidalCategoryStruct.leftUnitor, #[_, _, _, f]) => return .leftUnitorInv (toMor₁ f)
    | (``MonoidalCategoryStruct.rightUnitor, #[_, _, _, f]) => return .rightUnitorInv (toMor₁ f)
    | _ => none
  | _ => none

/-- Expressions for atomic (non-structural) 2-morphisms. -/
structure Atom where
  /-- Extract a Lean expression from an `Atom` expression. -/
  e : Expr

/-- Expressions for atomic 2-Morphisms. -/
inductive Core : Type
  /-- Construct the expression for a structural 2-morphism. -/
  | ofStructural : StructuralAtom → Core
  /-- Construct the expression for an atomic 2-morphism. -/
  | of : Atom → Core
  deriving Inhabited

/-- Extract a Lean expression from a `Core` expression. -/
def Core.e : Core → MetaM Expr
  | .ofStructural η => η.e
  | .of a => return a.e

/-- Expressions of the form `η ▷ f₁ ▷ ... ▷ fₙ`. -/
inductive WhiskerRightExpr : Type
  /-- Construct the expression for a core 2-morphism. -/
  | of (η : Core) : WhiskerRightExpr
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

/-- Normalized expressions for 2-morphisms. -/
inductive NormalExpr : Type
  /-- Construct the expression for `𝟙 f`. -/
  | id (f : Mor₁) : NormalExpr
  /-- Construct the normalized expression of 2-morphisms recursively. -/
  | cons (head : WhiskerLeftExpr) (tail : NormalExpr) : NormalExpr
  deriving Inhabited

/-- The domain of a morphism. -/
def src (η : Expr) : MetaM Mor₁ := do
  match (← inferType η).getAppFnArgs with
  | (``Quiver.Hom, #[_, _, f, _]) => return toMor₁ f
  | _ => throwError "{η} is not a morphism"

/-- The codomain of a morphism. -/
def tar (η : Expr) : MetaM Mor₁ := do
  match (← inferType η).getAppFnArgs with
  | (``Quiver.Hom, #[_, _, _, g]) => return toMor₁ g
  | _ => throwError "{η} is not a morphism"

/-- The domain of a 2-morphism. -/
def Core.src (η : Core) : MetaM Mor₁ := do StringDiagram.src (← η.e)
/-- The codomain of a 2-morphism. -/
def Core.tar (η : Core) : MetaM Mor₁ := do StringDiagram.tar (← η.e)

/-- Construct a normalized expression from an atomic 2-morphism. -/
def NormalExpr.mk (η : Core) : MetaM NormalExpr := do
  return .cons (.of (.of η)) (.id (← η.tar))

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
def NormalExpr.src : NormalExpr → MetaM Mor₁
  | NormalExpr.id f => return f
  | NormalExpr.cons η _ => η.src

/-- The codomain of a 2-morphism. -/
def NormalExpr.tar : NormalExpr → MetaM Mor₁
  | NormalExpr.id f => return f
  | NormalExpr.cons _ θ => θ.tar

/-- Evaluate the expression `η ≫ θ` into a normalized form. -/
def evalComp : NormalExpr → NormalExpr → NormalExpr
  | .id _, e => e
  | e, .id _ => e
  | .cons f g, e => .cons f (evalComp g e)

/-- The associator as a term of `normalExpr`. -/
def NormalExpr.associator (f g h : Mor₁) : MetaM NormalExpr := do
  NormalExpr.mk (.ofStructural <| .associator f g h)

/-- The inverse of the associator as a term of `normalExpr`. -/
def NormalExpr.associatorInv (f g h : Mor₁) : MetaM NormalExpr := do
  NormalExpr.mk (.ofStructural <| .associatorInv f g h)

/-- The left unitor as a term of `normalExpr`. -/
def NormalExpr.leftUnitor (f : Mor₁) : MetaM NormalExpr := do
  NormalExpr.mk (.ofStructural <| .leftUnitor f)

/-- The inverse of the left unitor as a term of `normalExpr`. -/
def NormalExpr.leftUnitorInv (f : Mor₁) : MetaM NormalExpr := do
  NormalExpr.mk (.ofStructural <| .leftUnitorInv f)

/-- The right unitor as a term of `normalExpr`. -/
def NormalExpr.rightUnitor (f : Mor₁) : MetaM NormalExpr := do
  NormalExpr.mk (.ofStructural <| .rightUnitor f)

/-- The inverse of the right unitor as a term of `normalExpr`. -/
def NormalExpr.rightUnitorInv (f : Mor₁) : MetaM NormalExpr := do
  NormalExpr.mk (.ofStructural <| .rightUnitorInv f)

/-- Evaluate the expression `f ◁ η` into a normalized form. -/
partial def evalWhiskerLeftExpr : Mor₁ → NormalExpr → MetaM NormalExpr
  | f, .id g => do
    return .id (f.comp g)
  | .of f, .cons η θ => do
    let η' := WhiskerLeftExpr.whisker f η
    let θ' ← evalWhiskerLeftExpr (.of f) θ
    return .cons η' θ'
  | .comp f g, η => do
    let η' ← evalWhiskerLeftExpr f (← evalWhiskerLeftExpr g η)
    let h ← η.src
    let h' ← η.tar
    return evalComp (← NormalExpr.associator f g h) (evalComp η' (← NormalExpr.associatorInv f g h'))
  | .id _, η => do
    let f ← η.src
    let g ← η.tar
    return evalComp (← NormalExpr.leftUnitor f) (evalComp η (← NormalExpr.leftUnitorInv g))

/-- Evaluate the expression `η ▷ f` into a normalized form. -/
partial def evalWhiskerRightExpr : NormalExpr → Mor₁ → MetaM NormalExpr
  | .id f, .of g => do
    return .id (f.comp (.of g))
  | .cons (.of η) θ, .of f => do
    let η' := WhiskerRightExpr.whisker η f
    let θ' ← evalWhiskerRightExpr θ (.of f)
    return .cons (.of η') θ'
  | .cons (.whisker f η) θ, .of h => do
    let g ← η.src
    let g' ← η.tar
    let η' ← evalWhiskerLeftExpr (.of f) (← evalWhiskerRightExpr (.cons η (.id g')) (.of h))
    let θ' ← evalWhiskerRightExpr θ (.of h)
    return evalComp (← NormalExpr.associator (.of f) g (.of h)) (evalComp η' (evalComp (← NormalExpr.associatorInv (.of f) g' (.of h)) θ'))
  | η, .comp g h => do
    let η' ← evalWhiskerRightExpr (← evalWhiskerRightExpr η g) h
    let f ← η.src
    let f' ← η.tar
    return evalComp (← NormalExpr.associatorInv f g h) (evalComp η' (← NormalExpr.associator f' g h))
  | η, .id _ => do
    let f ← η.src
    let g ← η.tar
    return evalComp (← NormalExpr.rightUnitor f) (evalComp η (← NormalExpr.rightUnitorInv g))

/-- Extract a Lean expression from a `WhiskerRightExpr` expression. -/
def WhiskerRightExpr.e : WhiskerRightExpr → MetaM Expr
  | WhiskerRightExpr.of η => η.e
  | WhiskerRightExpr.whisker η f => do
    mkAppM ``MonoidalCategoryStruct.whiskerRight #[← η.e, f.e]

/-- Extract a Lean expression from a `WhiskerLeftExpr` expression. -/
def WhiskerLeftExpr.e : WhiskerLeftExpr → MetaM Expr
  | WhiskerLeftExpr.of η => η.e
  | WhiskerLeftExpr.whisker f η => do
    mkAppM ``MonoidalCategoryStruct.whiskerLeft #[f.e, ← η.e]

/-- Extract a Lean expression from a `NormalExpr` expression. -/
def NormalExpr.e : NormalExpr → MetaM Expr
  | NormalExpr.id f => do mkAppM ``CategoryStruct.id #[← f.e]
  | NormalExpr.cons η (NormalExpr.id _) => η.e
  | NormalExpr.cons η θ => do mkAppM ``CategoryStruct.comp #[← η.e, ← θ.e]

/-- Convert a `NormalExpr` expression into a list of `WhiskerLeftExpr` expressions. -/
def NormalExpr.toList : NormalExpr → List WhiskerLeftExpr
  | NormalExpr.id _ => []
  | NormalExpr.cons η θ => η :: NormalExpr.toList θ

/-- Return `η` for `η ▷ g₁ ▷ ... ▷ gₙ`. -/
def WhiskerRightExpr.core : WhiskerRightExpr → Core
  | WhiskerRightExpr.of η => η
  | WhiskerRightExpr.whisker η _ => η.core

/-- Return `η` for `f₁ ◁ ... ◁ fₙ ◁ η ▷ g₁ ▷ ... ▷ gₙ`. -/
def WhiskerLeftExpr.core : WhiskerLeftExpr → Core
  | WhiskerLeftExpr.of η => η.core
  | WhiskerLeftExpr.whisker _ η => η.core

/-- Return `ture` if `η` is a structural 2-morphism. -/
def WhiskerLeftExpr.isStructural (η : WhiskerLeftExpr) : Bool :=
  match η.core with
  | .of _ => false
  | .ofStructural _ => true

/-- Interpret an `Expr` term as a `Core` term. -/
def toCore (e : Expr) : Core :=
  match structuralAtom? e with
  | some η => Core.ofStructural η
  | none => Core.of ⟨e⟩

/-- Construct a `NormalExpr` expression from a Lean expression for a core 2-morphism. -/
def NormalExpr.of (η : Expr) : MetaM NormalExpr := do
  return .cons (.of (.of (toCore η))) (.id <| ← StringDiagram.tar η)

/-- Evaluate the expression of a 2-morphism into a normalized form. -/
partial def eval (e : Expr) : MetaM NormalExpr := do
  match e.getAppFnArgs with
  | (``CategoryStruct.id, #[_, _, f]) => return NormalExpr.id (toMor₁ f)
  | (``CategoryStruct.comp, #[_, _, _, _, _, η, θ]) => return evalComp (← eval η) (← eval θ)
  | (``MonoidalCategoryStruct.whiskerLeft, #[_, _, _, f, _, _, η]) => evalWhiskerLeftExpr (toMor₁ f) (← eval η)
  | (``MonoidalCategoryStruct.whiskerRight, #[_, _, _, _, _, η, h]) => evalWhiskerRightExpr (← eval η) (toMor₁ h)
  | _ => NormalExpr.of e

/-- Remove structural 2-morphisms. -/
def removeStructural : List WhiskerLeftExpr → List WhiskerLeftExpr
  | [] => []
  | η :: ηs => match η.isStructural with
    | true => removeStructural ηs
    | false => η :: removeStructural ηs

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
  return (leftMor₁List η, (← η.core.src).toList, rightMor₁List η)

/-- Returns codomain 1-morphisms as a list of components.` -/
def tarLists (η : WhiskerLeftExpr) : MetaM (List Expr × List Expr × List Expr) := do
  return (leftMor₁List η, (← η.core.tar).toList, rightMor₁List η)

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
  deriving Inhabited, BEq, Hashable

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
    let l := removeStructural (← eval e).toList
    /- Add 2-morphisms. -/
    for (i, x) in l.enumFrom 1 do
      let v : PenroseVar := ⟨"E", [i], ← x.core.e⟩
      addPenroseVar "Core" v
      let (L, C, R) ← srcLists x
      let C' := (← x.core.tar).toList
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
      let v₁ : PenroseVar := ⟨"E", [i], ← x.core.e⟩
      let v₂ : PenroseVar := ⟨"E", [i + 1], ← y.core.e⟩
      addInstruction s!"Above({v₁}, {v₂})"
    /- The top of the diagram. -/
    if let some x₀ := l.head? then
      let v₀ : PenroseVar := ⟨"E", [1], ← x₀.core.e⟩
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
      let vₙ : PenroseVar := ⟨"E", [l.length], ← xₙ.core.e⟩
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
