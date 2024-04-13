import Mathlib.Tactic.Widget.StringDiagram
import ProofWidgets.Component.Panel.SelectionPanel
import ProofWidgets.Component.Panel.GoalTypePanel

/-! ## Example use of string diagram widgets -/

section MonoidalCategory

open ProofWidgets

open CategoryTheory
open scoped MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

lemma left_triangle {X Y : C} (η : 𝟙_ _ ⟶ X ⊗ Y) (ε : Y ⊗ X ⟶ 𝟙_ _) (w : False) :
    η ▷ X ≫ (α_ _ _ _).hom ≫ X ◁ ε = (λ_ _).hom ≫ (ρ_ _).inv := by
  with_panel_widgets [SelectionPanel]
    exact w.elim

lemma yang_baxter {V₁ V₂ V₃ : C} (R : ∀ V₁ V₂ : C, V₁ ⊗ V₂ ⟶ V₂ ⊗ V₁) (w : False) :
    R V₁ V₂ ▷ V₃ ≫ (α_ _ ..).hom ≫ _ ◁ R _ _ ≫ (α_ _ ..).inv ≫ R _ _ ▷ _ ≫ (α_ _ ..).hom =
    (α_ _ ..).hom ≫ V₁ ◁ R V₂ V₃ ≫ (α_ _ ..).inv ≫ R _ _ ▷ _ ≫ (α_ _ ..).hom ≫ _ ◁ R _ _ := by
  with_panel_widgets [GoalTypePanel]
    exact w.elim

lemma yang_baxter' {V₁ V₂ V₃ : C} (R : ∀ V₁ V₂ : C, V₁ ⊗ V₂ ⟶ V₂ ⊗ V₁) (w : False) :
    R V₁ V₂ ▷ V₃ ⊗≫ V₂ ◁ R V₁ V₃ ⊗≫ R V₂ V₃ ▷ V₁ ⊗≫ 𝟙 _ =
    𝟙 _ ⊗≫ V₁ ◁ R V₂ V₃ ⊗≫ R V₁ V₃ ▷ V₂ ⊗≫ V₃ ◁ R V₁ V₂ := by
  with_panel_widgets [GoalTypePanel]
    exact w.elim

lemma yang_baxter'' {V₁ V₂ V₃ : C} (R : ∀ V₁ V₂ : C, V₁ ⊗ V₂ ⟶ V₂ ⊗ V₁) (w : False) :
    (R V₁ V₂ ⊗ 𝟙 V₃) ≫ (α_ _ ..).hom ≫
      (𝟙 V₂ ⊗ R V₁ V₃) ≫ (α_ _ ..).inv ≫
        (R V₂ V₃ ⊗ 𝟙 V₁) ≫ (α_ _ ..).hom =
      (α_ _ ..).hom ≫ (𝟙 V₁ ⊗ R V₂ V₃) ≫
        (α_ _ ..).inv ≫ (R V₁ V₃ ⊗ 𝟙 V₂) ≫
          (α_ _ ..).hom ≫ (𝟙 V₃ ⊗ R V₁ V₂) := by
  with_panel_widgets [GoalTypePanel]
    exact w.elim

example {X Y : C} (f : X ⟶ Y) (g : X ⊗ X ⊗ Y ⟶ Y ⊗ X ⊗ Y) (w : False) : f ▷ (X ⊗ Y) = g := by
  with_panel_widgets [SelectionPanel]
    exact w.elim

example {X Y : C} (f : X ⟶ Y) (g : 𝟙_ C ⊗ X ⟶ 𝟙_ C ⊗ Y) (w : False) : 𝟙_ C ◁ f = g := by
  with_panel_widgets [SelectionPanel]
    exact w.elim

example {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : f ⊗ g = X₁ ◁ g ≫ f ▷ Y₂ := by
  with_panel_widgets [GoalTypePanel]
    rw [MonoidalCategory.whisker_exchange]
    rw [MonoidalCategory.tensorHom_def]

namespace Mathlib.Tactic.Widget.StringDiagram

open Mathlib.Tactic.Coherence

open Lean Meta

/- ## Test for `eval`. -/

/-- The context for evaluating expressions. -/
structure Context where
  /-- The expression for the underlying category. -/
  C : Expr

/-- Populate a `context` object for evaluating `e`. -/
def mkContext (e : Expr) : MetaM (Context) := do
  match (← inferType e).getAppFnArgs with
  | (``Quiver.Hom, #[C, _, _, _]) =>
    return { C := C }
  | _ => throwError "not a morphism"

/-- The monad for the normalization of 2-morphisms. -/
abbrev M := ReaderT Context MetaM

/-- Run a computation in the `M` monad. -/
abbrev M.run {α : Type} (c : Context) (m : M α) : MetaM α :=
  ReaderT.run m c

/-- Extract a Lean expression from a `Mor₁` expression. -/
def Mor₁.e : Mor₁ → M Expr
  | .id => do
    let ctx ← read
    mkAppOptM ``MonoidalCategoryStruct.tensorUnit #[ctx.C, none, none]
  | .comp f g => do
    mkAppM ``MonoidalCategoryStruct.tensorObj #[← Mor₁.e f, ← Mor₁.e g]
  | .of f => return f.e

/-- Extract a Lean expression from a `StructuralAtom` expression. -/
def StructuralAtom.e : StructuralAtom → M Expr
  | .associator f g h => do
    mkAppM ``Iso.hom #[← mkAppM ``MonoidalCategoryStruct.associator #[← f.e, ← g.e, ← h.e]]
  | .associatorInv f g h => do
    mkAppM ``Iso.inv #[← mkAppM ``MonoidalCategoryStruct.associator #[← f.e, ← g.e, ← h.e]]
  | .leftUnitor f => do
    mkAppM ``Iso.hom #[← mkAppM ``MonoidalCategoryStruct.leftUnitor #[← f.e]]
  | .leftUnitorInv f => do
    mkAppM ``Iso.inv #[← mkAppM ``MonoidalCategoryStruct.leftUnitor #[← f.e]]
  | .rightUnitor f => do
    mkAppM ``Iso.hom #[← mkAppM ``MonoidalCategoryStruct.rightUnitor #[← f.e]]
  | .rightUnitorInv f => do
    mkAppM ``Iso.inv #[← mkAppM ``MonoidalCategoryStruct.rightUnitor #[← f.e]]
  | .monoidalCoherence _ _ e => do
    mkAppOptM ``MonoidalCoherence.hom #[none, none, none, none, e]

/-- Extract a Lean expression from a `Structural` expression. -/
partial def Structural.e : Structural → M Expr
  | .atom η => η.e
  | .id f => do mkAppM ``CategoryStruct.id #[← f.e]
  | .comp α β => do mkAppM ``CategoryStruct.comp #[← α.e, ← β.e]
  | .whiskerLeft f η => do mkAppM ``MonoidalCategoryStruct.whiskerLeft #[← f.e, ← η.e]
  | .whiskerRight η f => do mkAppM ``MonoidalCategoryStruct.whiskerRight #[← η.e, ← f.e]
  | .tensorHom η θ => do mkAppM ``MonoidalCategoryStruct.tensorHom #[← η.e, ← θ.e]

/-- Extract a Lean expression from a `WhiskerRightExpr` expression. -/
def WhiskerRightExpr.e : WhiskerRightExpr → M Expr
  | WhiskerRightExpr.of η => return η.e
  | WhiskerRightExpr.whisker η f => do
    mkAppM ``MonoidalCategoryStruct.whiskerRight #[← η.e, f.e]

/-- Extract a Lean expression from a `TensorHomExpr` expression. -/
def TensorHomExpr.e : TensorHomExpr → M Expr
  | TensorHomExpr.of η => η.e
  | TensorHomExpr.cons η ηs => do
    mkAppM ``MonoidalCategoryStruct.tensorHom #[← η.e, ← ηs.e]

/-- Extract a Lean expression from a `WhiskerLeftExpr` expression. -/
def WhiskerLeftExpr.e : WhiskerLeftExpr → M Expr
  | WhiskerLeftExpr.of η => η.e
  | WhiskerLeftExpr.whisker f η => do
    mkAppM ``MonoidalCategoryStruct.whiskerLeft #[f.e, ← η.e]

/-- Extract a Lean expression from a `NormalExpr` expression. -/
def NormalExpr.e : NormalExpr → M Expr
  | NormalExpr.nil α => α.e
  | NormalExpr.cons α η θ => do
    mkAppM ``CategoryStruct.comp #[← α.e, ← mkAppM ``CategoryStruct.comp #[← η.e, ← θ.e]]

/-- `normalize% η` is the normalization of the 2-morphism `η`. It is of the form
`α₀ ≫ η₀ ≫ α₁ ≫ η₁ ≫ ... αₙ ≫ ηₙ ≫ αₙ₊₁`, where `αᵢ` are structural 2-morphisms
and `ηᵢ` are non-structural 2-morphisms. -/
elab "normalize% " t:term:51 : term => do
  let e ← Lean.Elab.Term.elabTerm t none
  M.run (← mkContext e) do
    (← Mathlib.Tactic.Widget.StringDiagram.eval e).e

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {X Y Z W U V W : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)

#guard_expr normalize% X ◁ 𝟙 Y = X ◁ 𝟙 Y
#guard_expr normalize% 𝟙 X ▷ Y = 𝟙 X ▷ Y
#guard_expr normalize% X ◁ (f ≫ g) = _ ≫ X ◁ f ≫ _ ≫ X ◁ g ≫ _
#guard_expr normalize% (f ≫ g) ▷ Y = _ ≫ f ▷ Y ≫ _ ≫ g ▷ Y ≫ _
#guard_expr normalize% 𝟙_ C ◁ f = _ ≫ f ≫ _
#guard_expr normalize% (X ⊗ Y) ◁ f = _ ≫ X ◁ Y ◁ f ≫ _
#guard_expr normalize% f ▷ 𝟙_ C = _ ≫ f ≫ _
#guard_expr normalize% f ▷ (X ⊗ Y) = _ ≫ f ▷ X ▷ Y ≫ _
#guard_expr normalize% (X ◁ f) ▷ Y = _ ≫ X ◁ f ▷ Y ≫ _
#guard_expr normalize% (λ_ X).hom = (λ_ X).hom
#guard_expr normalize% (λ_ X).inv = (λ_ X).inv
#guard_expr normalize% (ρ_ X).hom = (ρ_ X).hom
#guard_expr normalize% (ρ_ X).inv = (ρ_ X).inv
#guard_expr normalize% (α_ X Y Z).hom = (α_ _ _ _).hom
#guard_expr normalize% (α_ X Y Z).inv = (α_ _ _ _).inv
#guard_expr normalize% 𝟙 (X ⊗ Y) = 𝟙 (X ⊗ Y)
#guard_expr normalize% f ⊗ h = _ ≫ (f ⊗ h) ≫ _
variable {V₁ V₂ V₃ : C} (R : ∀ V₁ V₂ : C, V₁ ⊗ V₂ ⟶ V₂ ⊗ V₁) in
#guard_expr normalize% R V₁ V₂ ▷ V₃ ⊗≫ V₂ ◁ R V₁ V₃ = _ ≫ R V₁ V₂ ▷ V₃ ≫ _ ≫ V₂ ◁ R V₁ V₃ ≫ _
#guard_expr normalize% f ⊗ (U ◁ h) = _ ≫ ((f ▷ U) ⊗ h) ≫ _
#guard_expr normalize% (U ◁ f) ⊗ g = _ ≫ U ◁ (f ⊗ g) ≫ _
#guard_expr normalize% (U ◁ f) ⊗ (V ◁ g) = _ ≫ U ◁ ((f ▷ V) ⊗ g) ≫ _
#guard_expr normalize% U ◁ (f ⊗ h) = _ ≫ U ◁ (f ⊗ h) ≫ _
#guard_expr normalize% (f ⊗ h) ▷ U = _ ≫ (f ⊗ (h ▷ U)) ≫ _

end Tactic.Widget.StringDiagram
