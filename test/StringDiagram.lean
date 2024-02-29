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

/-- Extract a Lean expression from a `Structural` expression. -/
partial def Structural.e : Structural → M Expr
  | .atom η => η.e
  | .id f => do mkAppM ``CategoryStruct.id #[← f.e]
  | .comp α β => do match α, β with
    | _, _ => mkAppM ``CategoryStruct.comp #[← α.e, ← β.e]
  | .whiskerLeft f η => do mkAppM ``MonoidalCategoryStruct.whiskerLeft #[← f.e, ← η.e]
  | .whiskerRight η f => do mkAppM ``MonoidalCategoryStruct.whiskerRight #[← η.e, ← f.e]
  | .tensorHom η θ => do mkAppM ``MonoidalCategoryStruct.tensorHom #[← η.e, ← θ.e]
  | .monoidalCoherence _ _ e => do
    mkAppOptM ``MonoidalCoherence.hom #[none, none, none, none, none, none, e]

/-- Extract a Lean expression from a `WhiskerRightExpr` expression. -/
def WhiskerRightExpr.e : WhiskerRightExpr → M Expr
  | WhiskerRightExpr.of η => return η.e
  | WhiskerRightExpr.whisker η f => do
    mkAppM ``MonoidalCategoryStruct.whiskerRight #[← η.e, f.e]

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
variable {X Y Z U V W : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)

example : normalize% f ⊗ g = sorry := by
  sorry

#guard_expr normalize% f = _ ≫ f ≫ _
#guard_expr normalize% X ◁ 𝟙 Y = 𝟙 (X ⊗ Y)
#guard_expr normalize% 𝟙 X ▷ Y = 𝟙 (X ⊗ Y)
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
#guard_expr normalize% f ⊗ g = _ ≫ (f ⊗ g) ≫ _
variable {V₁ V₂ V₃ : C} (R : ∀ V₁ V₂ : C, V₁ ⊗ V₂ ⟶ V₂ ⊗ V₁) in
#guard_expr normalize% R V₁ V₂ ▷ V₃ ⊗≫ V₂ ◁ R V₁ V₃ = _ ≫ R V₁ V₂ ▷ V₃ ≫ _ ≫ V₂ ◁ R V₁ V₃ ≫ _
#guard_expr normalize% f ⊗ (U ◁ h) = _ ≫ ((f ▷ U) ⊗ h) ≫ _
#guard_expr normalize% (U ◁ f) ⊗ g = _ ≫ U ◁ (f ⊗ g) ≫ _
#guard_expr normalize% (U ◁ f) ⊗ (V ◁ g) = _ ≫ U ◁ ((f ▷ V) ⊗ g) ≫ _
#guard_expr normalize% U ◁ (f ⊗ h) = _ ≫ U ◁ (f ⊗ h) ≫ _
#guard_expr normalize% (f ⊗ h) ▷ U = _ ≫ (f ⊗ (h ▷ U)) ≫ _

#check normalize% f ▷ (X ⊗ Y)

#check normalize% X ◁ 𝟙 Y
#check normalize% 𝟙 X ▷ Y
#check normalize% X ◁ (f ≫ g)
#check normalize% (f ≫ g) ▷ Y
#check normalize% 𝟙_ C ◁ f
#check normalize% (X ⊗ Y) ◁ f
#check normalize% f ▷ 𝟙_ C
#check normalize% f ▷ (X ⊗ Y)
#check normalize% (X ◁ f) ▷ Y

open MonoidalCategory

example : normalize% f ⊗ g = sorry := by
  with_panel_widgets [GoalTypePanel]
    simp [tensorHom_def]
    sorry

example : normalize% f = sorry := by
  simp
  with_panel_widgets [GoalTypePanel]
    sorry

open MonoidalCategory

example : normalize% f ⊗ (U ◁ h) = sorry := by
  sorry

example : normalize% (W ◁ f) ⊗ g = sorry := by
  sorry

example : normalize% (Z ◁ f) ⊗ (Y ◁ g) = sorry := by
  sorry

example : f ⊗ (Y ◁ g) = (α_ _ _ _).inv ≫ ((f ▷ Y) ⊗ g) ≫ (α_ _ _ _).hom := by
  with_panel_widgets [GoalTypePanel]
    simp [tensorHom_def]

example : (Z ◁ f) ⊗ (Y ◁ g) = (α_ _ _ _).hom ≫ Z ◁ (α_ _ _ _).inv ≫
  Z ◁ ((f ▷ Y) ⊗ g) ≫ Z ◁  (α_ _ _ _).hom ≫ (α_ _ _ _).inv := by
  with_panel_widgets [GoalTypePanel]
    simp [tensorHom_def]

example : (Y ◁ f) ⊗ g = (α_ _ _ _).hom ≫ Y ◁ (f ⊗ g) ≫ (α_ _ _ _).inv := by
  with_panel_widgets [GoalTypePanel]
    simp [tensorHom_def]

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory.{v₁} C] (D : Type u₂) [Category.{v₂} D]
  [MonoidalCategory.{v₂} D]
open Category MonoidalCategory Functor

variable (F : MonoidalFunctor C D) {G : D ⥤ C} (Y : D) in
#whnfR (F.toPrefunctor.obj (G.toPrefunctor.obj Y))

variable (X : D) in
#whnfR (𝟭 D).toPrefunctor.obj X

noncomputable
example (F : MonoidalFunctor C D) {G : D ⥤ C} (h : F.toFunctor ⊣ G) :
    LaxMonoidalFunctor D C where
  toFunctor := G
  ε := h.homEquiv _ _ (inv F.ε)
  μ := fun X Y =>
    h.homEquiv _ _ (inv (F.μ (G.obj X) (G.obj Y)) ≫ (h.counit.app X ⊗ h.counit.app Y))
  μ_natural_left {X Y} f X' := by
    rw [← h.homEquiv_naturality_left, ← h.homEquiv_naturality_right, Equiv.apply_eq_iff_eq,
      assoc, IsIso.eq_inv_comp,
      ← F.toLaxMonoidalFunctor.μ_natural_left_assoc, IsIso.hom_inv_id_assoc, tensorHom_def,
      ← comp_whiskerRight_assoc, Adjunction.counit_naturality, comp_whiskerRight_assoc,
      ← whisker_exchange, ← tensorHom_def_assoc]
  μ_natural_right {X Y} X' f := by
    with_panel_widgets [GoalTypePanel]
    with_panel_widgets [SelectionPanel]
    dsimp only
    rw [← h.homEquiv_naturality_left, ← h.homEquiv_naturality_right, Equiv.apply_eq_iff_eq,
      assoc, IsIso.eq_inv_comp,
      ← F.toLaxMonoidalFunctor.μ_natural_right_assoc, IsIso.hom_inv_id_assoc, tensorHom_def',
      ← MonoidalCategory.whiskerLeft_comp_assoc, Adjunction.counit_naturality, whisker_exchange,
      MonoidalCategory.whiskerLeft_comp, ← tensorHom_def_assoc]
  associativity X Y Z := by
    with_panel_widgets [GoalTypePanel]
    with_panel_widgets [SelectionPanel]
    dsimp only
    rw [← h.homEquiv_naturality_right, ← h.homEquiv_naturality_left, ← h.homEquiv_naturality_left,
      ← h.homEquiv_naturality_left, Equiv.apply_eq_iff_eq,
      ← cancel_epi (F.μ (G.obj X ⊗ G.obj Y) (G.obj Z)),
      ← cancel_epi (F.μ (G.obj X) (G.obj Y) ▷ (F.obj (G.obj Z)))]
    simp only [assoc]
    calc
      _ = (α_ _ _ _).hom ≫ (h.counit.app X ⊗ h.counit.app Y ⊗ h.counit.app Z) := by
        rw [← F.μ_natural_left_assoc, IsIso.hom_inv_id_assoc, h.homEquiv_unit,
          tensorHom_def_assoc (h.counit.app (X ⊗ Y)) (h.counit.app Z)]
        dsimp only [comp_obj, id_obj]
        simp_rw [← MonoidalCategory.comp_whiskerRight_assoc]
        rw [F.map_comp_assoc, h.counit_naturality, h.left_triangle_components_assoc,
          IsIso.hom_inv_id_assoc, ← tensorHom_def_assoc, associator_naturality]
      _ = _ := by
        rw [F.associativity_assoc, ← F.μ_natural_right_assoc, IsIso.hom_inv_id_assoc,
          h.homEquiv_unit, tensorHom_def (h.counit.app X) (h.counit.app (Y ⊗ Z))]
        dsimp only [id_obj, comp_obj]
        rw [whisker_exchange_assoc, ← MonoidalCategory.whiskerLeft_comp, F.map_comp_assoc,
          h.counit_naturality, h.left_triangle_components_assoc, whisker_exchange_assoc,
          ← MonoidalCategory.whiskerLeft_comp, ← tensorHom_def, IsIso.hom_inv_id_assoc]
  left_unitality X := by
    with_panel_widgets [GoalTypePanel]
    with_panel_widgets [SelectionPanel]
    rw [← h.homEquiv_naturality_right, ← h.homEquiv_naturality_left, ← Equiv.symm_apply_eq,
      h.homEquiv_counit, F.map_leftUnitor_assoc, h.homEquiv_unit, F.map_whiskerRight_assoc, assoc,
      IsIso.hom_inv_id_assoc, tensorHom_def_assoc, ← MonoidalCategory.comp_whiskerRight_assoc,
      F.map_comp_assoc, h.counit_naturality, h.left_triangle_components_assoc]
    simp
  right_unitality X := by
    rw [← h.homEquiv_naturality_right, ← h.homEquiv_naturality_left, ← Equiv.symm_apply_eq,
      h.homEquiv_counit, F.map_rightUnitor_assoc, h.homEquiv_unit, F.map_whiskerLeft_assoc, assoc,
      IsIso.hom_inv_id_assoc, tensorHom_def'_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
      F.map_comp_assoc, h.counit_naturality, h.left_triangle_components_assoc]
    simp

end Tactic.Widget.StringDiagram
