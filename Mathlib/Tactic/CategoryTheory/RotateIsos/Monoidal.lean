/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.Tactic.CategoryTheory.RotateIsos.Cancelable

/-!
# Monoidal category lemmas for `rotate_iso`

This file registers the following patterns in a monoidal category to the rotate_isos tactic:

- `e ⊗ e'` for a isomorphisms `e` `e'`.
- `x ◁ e` for an isomorphism `e` and an object `x`.
- `e ▷ x` for an isomorphism `e` and an object `x`.
- `f ⊗ g` for cancelable morphisms `f` and `g`.
- `x ◁ f` for a cancelable morphism `f` and an object x.
- `f ▷ x` for a cancelable morphism `f` and an object x.
-/

namespace Tactic.CategoryTheory.RotateIsos.MonoidalCategory
open Lean Parser.Tactic Elab Command Elab.Tactic Meta _root_.CategoryTheory MonoidalCategory

section Lemmas

variable {C : Type*} [Category C] [MonoidalCategory C]

section tensorHomIso

lemma tensorIso.eq_symm_trans
    {x y x' y': C} {α : x ≅ y} {α' : y ≅ x} {β : x' ≅ y'} {β' : y' ≅ x'}
    (refl_eq_symm_trans_α: Iso.refl _ = α' ≪≫ α) (refl_eq_symm_trans_β: Iso.refl _ = β' ≪≫ β)
    {z' : C} {φ : y ⊗ y' ≅ z'} {ψ : x ⊗ x' ≅ z'}
    (w : (α ⊗ β) ≪≫ φ = ψ) :
    φ = (α' ⊗ β') ≪≫ ψ := by
  have e₁ := congrArg (fun t ↦ t.hom) refl_eq_symm_trans_α
  have e₂ := congrArg (fun t ↦ t.hom) refl_eq_symm_trans_β
  ext
  simp only [Iso.refl_hom, Iso.trans_hom] at e₁ e₂
  simp [← w, Iso.trans_hom, Iso.trans_hom, tensorIso_hom, tensorIso_hom, ← tensor_comp_assoc,
    ← e₁, ← e₂]

lemma tensorIso.eq_trans_symm
    {x y x' y': C} {α : x ≅ y} {α' : y ≅ x} {β : x' ≅ y'} {β' : y' ≅ x'}
    (refl_eq_trans_symm_α : Iso.refl _ = α ≪≫ α') (refl_eq_trans_symm_β : Iso.refl _ = β ≪≫ β')
    {z' : C} {φ : z' ≅ x ⊗ x'} {ψ : z' ≅ y ⊗ y'}
    (w : φ ≪≫ (α ⊗ β) = ψ) :
    φ = ψ ≪≫ (α' ⊗ β') := by
  have e₂ := congrArg (fun t ↦ t.hom) refl_eq_trans_symm_α
  have e₁ := congrArg (fun t ↦ t.hom) refl_eq_trans_symm_β
  ext
  simp only [Iso.refl_hom, Iso.trans_hom] at e₁ e₂
  simp [← w, Iso.trans_hom, Iso.trans_hom, tensorIso_hom, tensorIso_hom, ← tensor_comp, ← e₁, ← e₂]

lemma tensorIso.refl_eq_symm_trans
    {x y x' y': C} {α : x ≅ y} {α' : y ≅ x} {β : x' ≅ y'} {β' : y' ≅ x'}
    (refl_eq_symm_trans_α : Iso.refl _ = α' ≪≫ α) (refl_eq_symm_trans_β : Iso.refl _ = β' ≪≫ β)
    {ψ : x ⊗ x' ≅ y ⊗ y'} (w : α ⊗ β = ψ) :
    Iso.refl _ = (α' ⊗ β') ≪≫ ψ := by
  haveI e₁ := congrArg (fun t ↦ t.hom) refl_eq_symm_trans_α
  haveI e₂ := congrArg (fun t ↦ t.hom) refl_eq_symm_trans_β
  simp only [Iso.refl_hom, Iso.trans_hom] at e₁ e₂
  ext
  simp [← w, Iso.trans_hom, Iso.trans_hom, tensorIso_hom, tensorIso_hom, ← tensor_comp, ← e₁, ← e₂]

lemma tensorIso.refl_eq_trans_symm
    {x y x' y': C} {α : x ≅ y} {α' : y ≅ x} {β : x' ≅ y'} {β' : y' ≅ x'}
    (refl_eq_trans_symm_α : Iso.refl _ = α ≪≫ α') (refl_eq_trans_symm_β : Iso.refl _ = β ≪≫ β')
    {ψ : x ⊗ x' ≅ y ⊗ y'} (w : α ⊗ β = ψ) :
    Iso.refl _ = ψ ≪≫ (α' ⊗ β') := by
  haveI e₁ := congrArg (fun t ↦ t.hom) refl_eq_trans_symm_α
  haveI e₂ := congrArg (fun t ↦ t.hom) refl_eq_trans_symm_β
  simp only [Iso.refl_hom, Iso.trans_hom] at e₁ e₂
  ext
  simp [← w, Iso.trans_hom, Iso.trans_hom, tensorIso_hom, tensorIso_hom, ← tensor_comp, ← e₁, ← e₂]

/-- Try matching `e` with an expression of the form `α ⊗ β`, and gives
a `Cancelable` with expression `e` if it matches. -/
def tryCancelTensorIso (e whnfR_e : Expr) : CancelM <| Option Cancelable := do
  match_expr whnfR_e with
  | tensorIso _ _ _ _ _ _ _ e_α e_β => do
    match ← (← read) e_α, ← (← read) e_β with
    | some c, some c' =>
      return some
        { expr := e
          inv := ← mkAppM ``MonoidalCategory.tensorIso #[c.inv, c'.inv]
          eq_inv_comp :=
            ← mkAppOptM ``tensorIso.eq_symm_trans <|
              (Array.replicate 7 none) ++
              #[some e_α, c.inv, some e_β, c'.inv,
                ← mkAppM' c.id_eq_inv_comp #[← mkAppM ``Eq.refl #[c.expr]],
                ← mkAppM' c'.id_eq_inv_comp #[← mkAppM ``Eq.refl #[c'.expr]]]
          eq_comp_inv :=
            ← mkAppOptM ``tensorIso.eq_trans_symm <|
              (Array.replicate 7 none) ++
              #[some e_α, c.inv, e_β, c'.inv,
                ← mkAppM' c.id_eq_comp_inv #[← mkAppM ``Eq.refl #[c.expr]],
                ← mkAppM' c'.id_eq_comp_inv #[← mkAppM ``Eq.refl #[c'.expr]]]
          id_eq_comp_inv :=
            ← mkAppOptM ``tensorIso.refl_eq_trans_symm <|
              (Array.replicate 7 none) ++
              #[some e_α, c.inv, e_β, c'.inv,
                ← mkAppM' c.id_eq_comp_inv #[← mkAppM ``Eq.refl #[c.expr]],
                ← mkAppM' c'.id_eq_comp_inv #[← mkAppM ``Eq.refl #[c'.expr]]]
          id_eq_inv_comp :=
            ← mkAppOptM ``tensorIso.refl_eq_symm_trans <|
              (Array.replicate 7 none) ++
              #[some e_α, c.inv, e_β, c'.inv,
                ← mkAppM' c.id_eq_inv_comp #[← mkAppM ``Eq.refl #[c.expr]],
                ← mkAppM' c'.id_eq_inv_comp #[← mkAppM ``Eq.refl #[c'.expr]]] }
    | _, _ => return none
  | _ => return none

initialize ← return insertCancelableFactory' tryCancelTensorIso 1100

end tensorHomIso

section whiskerLeftIso

lemma whiskerLeftIso.eq_whiskerLeftIso_symm_trans {x y : C} {α : x ≅ y} {α' : y ≅ x}
    (id_eq_symm_trans : Iso.refl _ = α' ≪≫ α) {z z' : C} {φ : z ⊗ y ≅ z'} {ψ : z ⊗ x ≅ z'}
    (w : whiskerLeftIso z α ≪≫ φ = ψ) :
    φ = whiskerLeftIso z α' ≪≫ ψ := by
  haveI := congrArg (fun t ↦ z ◁ t.hom) id_eq_symm_trans
  ext
  simp only [Iso.refl_hom, MonoidalCategory.whiskerLeft_id, Iso.trans_hom,
    MonoidalCategory.whiskerLeft_comp] at this
  simp [← w, ← reassoc_of% this]

lemma whiskerLeftIso.eq_trans_whiskerLeftIso_symm {x y : C} {α : x ≅ y} {α' : y ≅ x}
    (id_eq_trans_symm : Iso.refl _ = α ≪≫ α') {z z' : C} {φ : z' ≅ z ⊗ x} {ψ : z' ≅ z ⊗ y}
    (w : φ ≪≫ whiskerLeftIso z α = ψ) :
    φ = ψ ≪≫ whiskerLeftIso z α' := by
  haveI := congrArg (fun t ↦ z ◁ t.hom) id_eq_trans_symm
  ext
  simp only [Iso.refl_hom, MonoidalCategory.whiskerLeft_id, Iso.trans_hom,
    MonoidalCategory.whiskerLeft_comp] at this
  simp [← w, ← this]

lemma whiskerLeftIso.refl_eq_whiskerLeftIso_symm_trans {x y : C} {α : x ≅ y} {α' : y ≅ x}
    (id_eq_symm_trans : Iso.refl _ = α' ≪≫ α) {z : C}
    {ψ : z ⊗ x ≅ z ⊗ y} (w : whiskerLeftIso z α = ψ) :
    Iso.refl _ = whiskerLeftIso z α' ≪≫ ψ := by
  haveI := congrArg (fun t ↦ z ◁ t.hom) id_eq_symm_trans
  ext
  simpa [← w] using this

lemma whiskerLeftIso.refl_eq_trans_whiskerLeftIso_symm {x y : C} {α : x ≅ y} {α' : y ≅ x}
    (id_eq_trans_symm : Iso.refl _ = α ≪≫ α') {z : C}
    {ψ : z ⊗ x ≅ z ⊗ y} (w : whiskerLeftIso z α = ψ) :
    Iso.refl _ = ψ ≪≫ whiskerLeftIso z α' := by
  ext
  haveI := congrArg (fun t ↦ z ◁ t.hom) id_eq_trans_symm
  simpa [← w] using this

/-- Try matching `e` with an expression of the form `whiskerLeftIso z α`, and gives
a `Cancelable` with expression `e` if it matches. -/
def tryCancelWhiskerLeftIso (e whnfR_e : Expr) : CancelM <| Option Cancelable := do
  match_expr whnfR_e with
  | whiskerLeftIso _ _ _ e_x _ _ e_α => do
    trace[debug] "testing whiskerLeftIso with {e_x} {e_α}"
    (← (← read) e_α).mapM fun c => do
      trace[debug] "Some!"
      pure
        { expr := e
          inv := ← mkAppM ``MonoidalCategory.whiskerLeftIso #[e_x, c.inv]
          eq_inv_comp :=
            ← mkAppOptM ``whiskerLeftIso.eq_whiskerLeftIso_symm_trans <|
              (Array.replicate 5 none) ++
              #[some e_α, c.inv,
                ← mkAppM' c.id_eq_inv_comp #[← mkAppM ``Eq.refl #[c.expr]]]
          eq_comp_inv :=
            ← mkAppOptM ``whiskerLeftIso.eq_trans_whiskerLeftIso_symm <|
              (Array.replicate 5 none) ++
              #[some e_α, c.inv,
                ← mkAppM' c.id_eq_comp_inv #[← mkAppM ``Eq.refl #[c.expr]]]
          id_eq_comp_inv :=
            ← mkAppOptM ``whiskerLeftIso.refl_eq_trans_whiskerLeftIso_symm <|
              (Array.replicate 5 none) ++
              #[some e_α, c.inv,
                ← mkAppM' c.id_eq_comp_inv #[← mkAppM ``Eq.refl #[c.expr]]]
          id_eq_inv_comp :=
            ← mkAppOptM ``whiskerLeftIso.refl_eq_whiskerLeftIso_symm_trans <|
              (Array.replicate 5 none) ++
              #[some e_α, c.inv,
                ← mkAppM' c.id_eq_inv_comp #[← mkAppM ``Eq.refl #[c.expr]]] }
  | _ => return none

-- Has higher priority than `tryCancelIso`, since we want
-- `whiskerLeftIso z (whiskerLeftIso g α)` to have inverse
-- `whiskerLeftIso z (whiskerLeftIso g α.symm)`
initialize ← return insertCancelableFactory' tryCancelWhiskerLeftIso 1100

end whiskerLeftIso

section whiskerRightIso

lemma whiskerRightIso.eq_whiskerRightIso_symm_trans {x y : C}
    {α : x ≅ y} {α' : y ≅ x} (id_eq_symm_trans : Iso.refl _ = α' ≪≫ α)
    {z z' : C} {φ : y ⊗ z ≅ z'} {ψ : x ⊗ z ≅ z'}
    (w : whiskerRightIso α z ≪≫ φ = ψ) :
    φ = whiskerRightIso α' z ≪≫ ψ := by
  haveI := congrArg (fun t ↦ t.hom ▷ z) id_eq_symm_trans
  ext
  simp only [Iso.refl_hom, MonoidalCategory.whiskerRight_id, Iso.trans_hom,
    comp_whiskerRight] at this
  simp [← w, ← reassoc_of% this]

lemma whiskerRightIso.eq_trans_whiskerRightIso_symm {x y : C}
    {α : x ≅ y} {α' : y ≅ x} (id_eq_trans_symm : Iso.refl _ = α ≪≫ α') {z z' : C}
    {φ : z' ≅ x ⊗ z} {ψ : z' ≅ y ⊗ z} (w : φ ≪≫ whiskerRightIso α z = ψ) :
    φ = ψ ≪≫ whiskerRightIso α' z := by
  haveI := congrArg (fun t ↦ t.hom ▷ z) id_eq_trans_symm
  ext
  simp only [Iso.refl_hom, MonoidalCategory.whiskerRight_id, Iso.trans_hom,
    comp_whiskerRight] at this
  simp [← w, ← this]

lemma whiskerRightIso.refl_eq_whiskerRightIso_symm_trans {x y : C}
    {α : x ≅ y} {α' : y ≅ x} (id_eq_symm_trans : Iso.refl _ = α' ≪≫ α) {z : C}
    {ψ : x ⊗ z ≅ y ⊗ z} (w : whiskerRightIso α z = ψ) :
    Iso.refl _ = whiskerRightIso α' z ≪≫ ψ := by
  haveI := congrArg (fun t ↦ t.hom ▷ z) id_eq_symm_trans
  ext
  simpa [← w] using this

lemma whiskerRightIso.refl_eq_trans_whiskerRightIso_symm {x y : C}
    {α : x ≅ y} {α' : y ≅ x} (id_eq_trans_symm : Iso.refl _ = α ≪≫ α') {z : C}
    {ψ : x ⊗ z ≅ y ⊗ z} (w : whiskerRightIso α z = ψ) :
    Iso.refl _ = ψ ≪≫ whiskerRightIso α' z := by
  ext
  haveI := congrArg (fun t ↦ t.hom ▷ z) id_eq_trans_symm
  simpa [← w] using this

/-- Try matching `e` with an expression of the form `whiskerRightIso α f`, and gives
a `Cancelable` with expression `e` if it matches. -/
def tryCancelWhiskerRightIso (e whnfR_e : Expr) : CancelM <| Option Cancelable := do
  match_expr whnfR_e with
  | whiskerRightIso _ _ _ _ _ e_α e_f => do
    trace[debug] "testing whiskerRightIso with {e_f} {e_α}"
    (← (← read) e_α).mapM fun c => do
      trace[debug] "Some"
      pure
        { expr := e
          inv := ← mkAppM ``MonoidalCategory.whiskerRightIso #[c.inv, e_f]
          eq_inv_comp :=
            ← mkAppOptM ``whiskerRightIso.eq_whiskerRightIso_symm_trans <|
              (Array.replicate 5 none) ++
              #[some e_α, c.inv,
                ← mkAppM' c.id_eq_inv_comp #[← mkAppM ``Eq.refl #[c.expr]]]
          eq_comp_inv :=
            ← mkAppOptM ``whiskerRightIso.eq_trans_whiskerRightIso_symm <|
              (Array.replicate 5 none) ++
              #[some e_α, c.inv,
                ← mkAppM' c.id_eq_comp_inv #[← mkAppM ``Eq.refl #[c.expr]]]
          id_eq_comp_inv :=
            ← mkAppOptM ``whiskerRightIso.refl_eq_trans_whiskerRightIso_symm <|
              (Array.replicate 5 none) ++
              #[some e_α, c.inv,
                ← mkAppM' c.id_eq_comp_inv #[← mkAppM ``Eq.refl #[c.expr]]]
          id_eq_inv_comp :=
            ← mkAppOptM ``whiskerRightIso.refl_eq_whiskerRightIso_symm_trans <|
              (Array.replicate 5 none) ++
              #[some e_α, c.inv,
                ← mkAppM' c.id_eq_inv_comp #[← mkAppM ``Eq.refl #[c.expr]]] }
  | _ => return none

-- Has higher priority than `tryCancelIso`, since we want e.g
-- `whiskerRightIso (whiskerRightIso α g) f` to have inverse
-- `whiskerRightIso (whiskerRightIso α.symm g) f`
initialize ← return insertCancelableFactory' tryCancelWhiskerRightIso 1100

end whiskerRightIso

section tensorHom

lemma tensorHom.eq_inv_comp
    {x y x' y': C} {α : x ⟶ y} {α' : y ⟶ x} {β : x' ⟶ y'} {β' : y' ⟶ x'}
    (id_eq_inv_comp_α: 𝟙 _ = α' ≫ α) (id_eq_inv_comp_β: 𝟙 _ = β' ≫ β)
    {z' : C} {φ : y ⊗ y' ⟶ z'} {ψ : x ⊗ x' ⟶ z'}
    (w : (α ⊗ β) ≫ φ = ψ) :
    φ = (α' ⊗ β') ≫ ψ := by
  simp [← w, ← tensor_comp_assoc, ← id_eq_inv_comp_α, ← id_eq_inv_comp_β]

lemma tensorHom.eq_comp_inv
    {x y x' y': C} {α : x ⟶ y} {α' : y ⟶ x} {β : x' ⟶ y'} {β' : y' ⟶ x'}
    (id_eq_comp_inv_α : 𝟙 _ = α ≫ α') (id_eq_comp_inv_β : 𝟙 _ = β ≫ β')
    {z' : C} {φ : z' ⟶ x ⊗ x'} {ψ : z' ⟶ y ⊗ y'}
    (w : φ ≫ (α ⊗ β) = ψ) :
    φ = ψ ≫ (α' ⊗ β') := by
  simp [← w, ← tensor_comp, ← id_eq_comp_inv_α, ← id_eq_comp_inv_β]

lemma tensorHom.id_eq_inv_comp
    {x y x' y': C} {α : x ⟶ y} {α' : y ⟶ x} {β : x' ⟶ y'} {β' : y' ⟶ x'}
    (id_eq_inv_comp_α : 𝟙 _ = α' ≫ α) (id_eq_inv_comp_β : 𝟙 _ = β' ≫ β)
    {ψ : x ⊗ x' ⟶ y ⊗ y'} (w : α ⊗ β = ψ) :
    𝟙 _ = (α' ⊗ β') ≫ ψ := by
  simp [← w, ← tensor_comp, ← id_eq_inv_comp_α, ← id_eq_inv_comp_β]

lemma tensorHom.id_eq_comp_inv
    {x y x' y': C} {α : x ⟶ y} {α' : y ⟶ x} {β : x' ⟶ y'} {β' : y' ⟶ x'}
    (id_eq_comp_inv_α : 𝟙 _ = α ≫ α') (id_eq_comp_inv_β : 𝟙 _ = β ≫ β')
    {ψ : x ⊗ x' ⟶ y ⊗ y'} (w : α ⊗ β = ψ) :
    𝟙 _ = ψ ≫ (tensorHom α' β') := by
  simp [← w, ← tensor_comp, ← id_eq_comp_inv_α, ← id_eq_comp_inv_β]

/-- Try matching `e` with an expression of the form `α ⊗ β`, tests if both `α` and `beta`
are cancelable and gives a `Cancelable` with expression `e` if it matches. -/
def tryCancelTensorHom (e whnfR_e : Expr) : CancelM <| Option Cancelable := do
  match_expr whnfR_e with
  | tensorHom _ _ _ _ _ _ _ e_α e_β => do
    match ← (← read) e_α, ← (← read) e_β with
    | some c, some c' =>
      return some
        { expr := e
          inv := ← mkAppM ``MonoidalCategory.tensorHom #[c.inv, c'.inv]
          eq_inv_comp :=
            ← mkAppOptM ``tensorHom.eq_inv_comp <|
              (Array.replicate 7 none) ++
              #[some e_α, c.inv, some e_β, c'.inv,
                ← mkAppM' c.id_eq_inv_comp #[← mkAppM ``Eq.refl #[c.expr]],
                ← mkAppM' c'.id_eq_inv_comp #[← mkAppM ``Eq.refl #[c'.expr]]]
          eq_comp_inv :=
            ← mkAppOptM ``tensorHom.eq_comp_inv <|
              (Array.replicate 7 none) ++
              #[some e_α, c.inv, e_β, c'.inv,
                ← mkAppM' c.id_eq_comp_inv #[← mkAppM ``Eq.refl #[c.expr]],
                ← mkAppM' c'.id_eq_comp_inv #[← mkAppM ``Eq.refl #[c'.expr]]]
          id_eq_comp_inv :=
            ← mkAppOptM ``tensorHom.id_eq_comp_inv <|
              (Array.replicate 7 none) ++
              #[some e_α, c.inv, e_β, c'.inv,
                ← mkAppM' c.id_eq_comp_inv #[← mkAppM ``Eq.refl #[c.expr]],
                ← mkAppM' c'.id_eq_comp_inv #[← mkAppM ``Eq.refl #[c'.expr]]]
          id_eq_inv_comp :=
            ← mkAppOptM ``tensorHom.id_eq_inv_comp <|
              (Array.replicate 7 none) ++
              #[some e_α, c.inv, e_β, c'.inv,
                ← mkAppM' c.id_eq_inv_comp #[← mkAppM ``Eq.refl #[c.expr]],
                ← mkAppM' c'.id_eq_inv_comp #[← mkAppM ``Eq.refl #[c'.expr]]] }
    | _, _ => return none
  | _ => return none

initialize ← return insertCancelableFactory' tryCancelTensorHom 900

end tensorHom

section whiskerLeft

lemma whiskerLeft.eq_whiskerLeft_inv_comp {x y : C}
    {α : x ⟶ y} {α' : y ⟶ x} (id_eq_inv_comp : 𝟙 _ = α' ≫ α) {z z' : C}
    {φ : z ⊗ y ⟶ z'} {ψ : z ⊗ x ⟶ z'} (w : z ◁ α ≫ φ = ψ) :
    φ = z ◁ α' ≫ ψ := by
  haveI := congrArg (fun t ↦ z ◁ t) id_eq_inv_comp
  simp only [Iso.refl_hom, MonoidalCategory.whiskerLeft_id,
    MonoidalCategory.whiskerLeft_comp] at this
  simp [← w, ← reassoc_of% this]

lemma whiskerLeft.eq_comp_whiskerLeft_inv {x y : C}
    {α : x ⟶ y} {α' : y ⟶ x} (id_eq_comp_inv : 𝟙 _ = α ≫ α') {z z' : C}
    {φ : z' ⟶ z ⊗ x} {ψ : z' ⟶ z ⊗ y} (w : φ ≫ z ◁ α = ψ) :
    φ = ψ ≫ z ◁ α' := by
  haveI := congrArg (fun t ↦ z ◁ t) id_eq_comp_inv
  simp only [Iso.refl_hom, MonoidalCategory.whiskerLeft_id,
    MonoidalCategory.whiskerLeft_comp] at this
  simp [← w, ← this]

lemma whiskerLeft.refl_eq_whiskerLeft_inv_comp {x y : C}
    {α : x ⟶ y} {α' : y ⟶ x} (id_eq_inv_comp : 𝟙 _ = α' ≫ α) {z : C}
    {ψ : z ⊗ x ⟶ z ⊗ y} (w : z ◁ α = ψ) :
    𝟙 _ = z ◁ α' ≫ ψ := by
  haveI := congrArg (fun t ↦ z ◁ t) id_eq_inv_comp
  simpa [← w] using this

lemma whiskerLeft.refl_eq_comp_whiskerLeft_inv {x y : C}
    {α : x ⟶ y} {α' : y ⟶ x} (id_eq_comp_inv : 𝟙 _ = α ≫ α') {z : C}
    {ψ : z ⊗ x ⟶ z ⊗ y} (w : z ◁ α = ψ) :
    𝟙 _ = ψ ≫ z ◁ α' := by
  haveI := congrArg (fun t ↦ z ◁ t) id_eq_comp_inv
  simpa [← w] using this

/-- Try matching `e` with an expression of the form `whiskerLeft f α`, and gives
a `Cancelable` with expression `e` if it matches. -/
def tryCancelWhiskerLeft (e whnfR_e : Expr) : CancelM <| Option Cancelable := do
  match_expr whnfR_e with
  | MonoidalCategory.whiskerLeft _ _ _ e_f _ _ e_α => do
    (← (← read) e_α).mapM fun c => do
      pure
        { expr := e
          inv := ← mkAppM ``MonoidalCategory.whiskerLeft #[e_f, c.inv]
          eq_inv_comp :=
            ← mkAppOptM ``whiskerLeft.eq_whiskerLeft_inv_comp <|
              (Array.replicate 5 none) ++
              #[some e_α, c.inv,
                ← mkAppM' c.id_eq_inv_comp #[← mkAppM ``Eq.refl #[c.expr]]]
          eq_comp_inv :=
            ← mkAppOptM ``whiskerLeft.eq_comp_whiskerLeft_inv <|
              (Array.replicate 5 none) ++
              #[some e_α, c.inv,
                ← mkAppM' c.id_eq_comp_inv #[← mkAppM ``Eq.refl #[c.expr]]]
          id_eq_comp_inv :=
            ← mkAppOptM ``whiskerLeft.refl_eq_comp_whiskerLeft_inv <|
              (Array.replicate 5 none) ++
              #[some e_α, c.inv,
                ← mkAppM' c.id_eq_comp_inv #[← mkAppM ``Eq.refl #[c.expr]]]
          id_eq_inv_comp :=
            ← mkAppOptM ``whiskerLeft.refl_eq_whiskerLeft_inv_comp <|
              (Array.replicate 5 none) ++
              #[some e_α, c.inv,
                ← mkAppM' c.id_eq_inv_comp #[← mkAppM ``Eq.refl #[c.expr]]] }
  | _ => return none

initialize ← return insertCancelableFactory' tryCancelWhiskerLeft 900

end whiskerLeft

section whiskerRight

lemma whiskerRight.eq_whiskerRight_inv_comp {x y : C}
    {α : x ⟶ y} {α' : y ⟶ x} (id_eq_inv_comp : 𝟙 _ = α' ≫ α)
    {z z' : C} {φ : y ⊗ z ⟶ z'} {ψ : x ⊗ z ⟶ z'}
    (w : α ▷ z ≫ φ = ψ) :
    φ = α' ▷ z ≫ ψ := by
  haveI := congrArg (fun t ↦ t ▷ z) id_eq_inv_comp
  simp only [MonoidalCategory.whiskerRight_id, comp_whiskerRight] at this
  simp [← w, ← reassoc_of% this]

lemma whiskerRight.eq_comp_whiskerRight_inv {x y : C}
    {α : x ⟶ y} {α' : y ⟶ x} (id_eq_comp_inv : 𝟙 _ = α ≫ α') {z z' : C}
    {φ : z' ⟶ x ⊗ z} {ψ : z' ⟶ y ⊗ z} (w : φ ≫ α ▷ z = ψ) :
    φ = ψ ≫ α' ▷ z := by
  haveI := congrArg (fun t ↦ t ▷ z) id_eq_comp_inv
  simp only [MonoidalCategory.whiskerRight_id, comp_whiskerRight] at this
  simp [← w, ← this]

lemma whiskerRight.refl_eq_whiskerRight_inv_comp {x y : C}
    {α : x ⟶ y} {α' : y ⟶ x} (id_eq_inv_comp : 𝟙 _ = α' ≫ α) {z : C}
    {ψ : x ⊗ z ⟶ y ⊗ z} (w : α ▷ z = ψ) :
    𝟙 _ = α' ▷ z ≫ ψ := by
  haveI := congrArg (fun t ↦ t ▷ z) id_eq_inv_comp
  simpa [← w] using this

lemma whiskerRight.refl_eq_comp_whiskerRight_inv {x y : C}
    {α : x ⟶ y} {α' : y ⟶ x} (id_eq_comp_inv : 𝟙 _ = α ≫ α') {z : C}
    {ψ : x ⊗ z ⟶ y ⊗ z} (w : α ▷ z = ψ) :
    𝟙 _ = ψ ≫ α' ▷ z := by
  rw [← w]
  haveI := congrArg (fun t ↦ t ▷ z) id_eq_comp_inv
  simpa using this

/-- Try matching `e` with an expression of the form `whiskerRight α f`, and gives
a `Cancelable` with expression `e` if it matches. -/
def tryCancelWhiskerRight (e whnfR_e : Expr) : CancelM <| Option Cancelable := do
  match_expr whnfR_e with
  | MonoidalCategory.whiskerRight _ _ _ _ _ e_α e_f => do
    (← (← read) e_α).mapM fun c => do
      pure
        { expr := e
          inv := ← mkAppM ``MonoidalCategory.whiskerRight #[c.inv, e_f]
          eq_inv_comp :=
            ← mkAppOptM ``whiskerRight.eq_whiskerRight_inv_comp <|
              (Array.replicate 5 none) ++
              #[some e_α, c.inv,
                ← mkAppM' c.id_eq_inv_comp #[← mkAppM ``Eq.refl #[c.expr]]]
          eq_comp_inv :=
            ← mkAppOptM ``whiskerRight.eq_comp_whiskerRight_inv <|
              (Array.replicate 5 none) ++
              #[some e_α, c.inv,
                ← mkAppM' c.id_eq_comp_inv #[← mkAppM ``Eq.refl #[c.expr]]]
          id_eq_comp_inv :=
            ← mkAppOptM ``whiskerRight.refl_eq_comp_whiskerRight_inv <|
              (Array.replicate 5 none) ++
              #[some e_α, c.inv,
                ← mkAppM' c.id_eq_comp_inv #[← mkAppM ``Eq.refl #[c.expr]]]
          id_eq_inv_comp :=
            ← mkAppOptM ``whiskerRight.refl_eq_whiskerRight_inv_comp <|
              (Array.replicate 5 none) ++
              #[some e_α, c.inv,
                ← mkAppM' c.id_eq_inv_comp #[← mkAppM ``Eq.refl #[c.expr]]] }
  | _ => return none

initialize ← return insertCancelableFactory' tryCancelWhiskerRight 900

end whiskerRight

end Lemmas

end Tactic.CategoryTheory.RotateIsos.MonoidalCategory
