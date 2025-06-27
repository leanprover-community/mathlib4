/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.CategoryTheory.Bicategory.Basic
import Mathlib.Tactic.CategoryTheory.RotateIsos.Cancelable

/-!
# Bicategory lemmas for `rotate_iso`

This file registers the following patterns for 2-cells in a bicategory to the RotateIsos tactic:

- `f ◁ e` for an 2-isomorphism `e` and a 1-cell `f`.
- `e ▷ f` for a 2-isomorphism `e` and a 1-cell `f`.
- `f ◁ α` for a 1-cell `f` and a cancelable 2-cell `α`.
- `α ▷ f` for a 1-cell `f` and a cancelable 2-cell `α`.
-/

namespace Tactic.CategoryTheory.RotateIsos.Bicategory -- namespace is just for disambiguation
open Lean Parser.Tactic Elab Command Elab.Tactic Meta _root_.CategoryTheory Bicategory

section Lemmas

variable {B : Type*} [Bicategory B]

section whiskerLeftIso

lemma whiskerLeftIso.eq_whiskerLeftIso_symm_trans {y z : B} {g h : y ⟶ z}
    {α : g ≅ h} {α' : h ≅ g} (id_eq_symm_trans : Iso.refl _ = α' ≪≫ α) {x : B} {f : x ⟶ y}
    {h' : x ⟶ z} {φ : f ≫ h ≅ h'} {ψ : f ≫ g ≅ h'}
    (w : whiskerLeftIso f α ≪≫ φ = ψ) :
    φ = whiskerLeftIso f α' ≪≫ ψ := by
  rw [← w]
  haveI := congrArg (fun t ↦ f ◁ t.hom) id_eq_symm_trans
  ext
  simp only [Iso.refl_hom, whiskerLeft_id, Iso.trans_hom, whiskerLeft_comp] at this
  simp [← reassoc_of% this]

lemma whiskerLeftIso.eq_trans_whiskerLeftIso_symm {y z : B} {g h : y ⟶ z}
    {α : g ≅ h} {α' : h ≅ g} (id_eq_trans_symm : Iso.refl _ = α ≪≫ α') {x : B} {f : x ⟶ y}
    {h' : x ⟶ z} {φ : h' ≅ f ≫ g} {ψ : h' ≅ f ≫ h} (w : φ ≪≫ whiskerLeftIso f α = ψ) :
    φ = ψ ≪≫ whiskerLeftIso f α' := by
  rw [← w]
  haveI := congrArg (fun t ↦ f ◁ t.hom) id_eq_trans_symm
  ext
  simp only [Iso.refl_hom, whiskerLeft_id, Iso.trans_hom, whiskerLeft_comp] at this
  simp [← this]

lemma whiskerLeftIso.refl_eq_whiskerLeftIso_symm_trans {y z : B} {g h : y ⟶ z}
    {α : g ≅ h} {α' : h ≅ g} (id_eq_symm_trans : Iso.refl _ = α' ≪≫ α) {x : B} {f : x ⟶ y}
    {ψ : f ≫ g ≅ f ≫ h} (w : whiskerLeftIso f α = ψ) :
    Iso.refl _ = whiskerLeftIso f α' ≪≫ ψ := by
  rw [← w]
  haveI := congrArg (fun t ↦ f ◁ t.hom) id_eq_symm_trans
  ext
  simpa using this

lemma whiskerLeftIso.refl_eq_trans_whiskerLeftIso_symm {y z : B} {g h : y ⟶ z}
    {α : g ≅ h} {α' : h ≅ g} (id_eq_trans_symm : Iso.refl _ = α ≪≫ α') {x : B} {f : x ⟶ y}
    {ψ : f ≫ g ≅ f ≫ h} (w : whiskerLeftIso f α = ψ) :
    Iso.refl _ = ψ ≪≫ whiskerLeftIso f α' := by
  rw [← w]
  ext
  haveI := congrArg (fun t ↦ f ◁ t.hom) id_eq_trans_symm
  simpa using this

/-- Try matching `e` with an expression of the form `whiskerLeftIso f α`, and gives
a `Cancelable` with expression `e` if it matches. -/
def tryCancelWhiskerLeftIso (e whnfR_e : Expr) : CancelM <| Option Cancelable := do
  match_expr whnfR_e with
  | whiskerLeftIso _ _ _ _ _ e_f _ _ e_α => do
    (← (← read) e_α).mapM fun c => do
      pure
        { expr := e
          inv := ← mkAppM ``Bicategory.whiskerLeftIso #[e_f, c.inv]
          eq_inv_comp :=
            ← mkAppOptM ``whiskerLeftIso.eq_whiskerLeftIso_symm_trans <|
              (Array.replicate 6 none) ++
              #[some e_α, c.inv,
                ← mkAppM' c.id_eq_inv_comp #[← mkAppM ``Eq.refl #[c.expr]]]
          eq_comp_inv :=
            ← mkAppOptM ``whiskerLeftIso.eq_trans_whiskerLeftIso_symm <|
              (Array.replicate 6 none) ++
              #[some e_α, c.inv,
                ← mkAppM' c.id_eq_comp_inv #[← mkAppM ``Eq.refl #[c.expr]]]
          id_eq_comp_inv :=
            ← mkAppOptM ``whiskerLeftIso.refl_eq_trans_whiskerLeftIso_symm <|
              (Array.replicate 6 none) ++
              #[some e_α, c.inv,
                ← mkAppM' c.id_eq_comp_inv #[← mkAppM ``Eq.refl #[c.expr]]]
          id_eq_inv_comp :=
            ← mkAppOptM ``whiskerLeftIso.refl_eq_whiskerLeftIso_symm_trans <|
              (Array.replicate 6 none) ++
              #[some e_α, c.inv,
                ← mkAppM' c.id_eq_inv_comp #[← mkAppM ``Eq.refl #[c.expr]]] }
  | _ => return none

-- Has higher priority than `tryCancelIso`, since we want
-- `whiskerLeftIso f (whiskerLeftIso g α)` to have inverse
-- `whiskerLeftIso f (whiskerLeftIso g α.symm)`
initialize ← return insertCancelableFactory' tryCancelWhiskerLeftIso 1100

end whiskerLeftIso

section whiskerRightIso

lemma whiskerRightIso.eq_whiskerRightIso_symm_trans {x y : B} {g h : x ⟶ y}
    {α : g ≅ h} {α' : h ≅ g} (id_eq_symm_trans : Iso.refl _ = α' ≪≫ α)
    {z : B} {f : y ⟶ z}
    {h' : x ⟶ z} {φ : h ≫ f ≅ h'} {ψ : g ≫ f ≅ h'}
    (w : whiskerRightIso α f ≪≫ φ = ψ) :
    φ = whiskerRightIso α' f ≪≫ ψ := by
  rw [← w]
  haveI := congrArg (fun t ↦ t.hom ▷ f) id_eq_symm_trans
  ext
  simp only [Iso.refl_hom, whiskerRight_id, Iso.trans_hom, comp_whiskerRight] at this
  simp [← reassoc_of% this]

lemma whiskerRightIso.eq_trans_whiskerRightIso_symm {x y : B} {g h : x ⟶ y}
    {α : g ≅ h} {α' : h ≅ g} (id_eq_trans_symm : Iso.refl _ = α ≪≫ α') {z : B} {f : y ⟶ z}
    {h' : x ⟶ z} {φ : h' ≅ g ≫ f} {ψ : h' ≅ h ≫ f} (w : φ ≪≫ whiskerRightIso α f = ψ) :
    φ = ψ ≪≫ whiskerRightIso α' f := by
  rw [← w]
  haveI := congrArg (fun t ↦ t.hom ▷ f) id_eq_trans_symm
  ext
  simp only [Iso.refl_hom, whiskerRight_id, Iso.trans_hom, comp_whiskerRight] at this
  simp [← this]

lemma whiskerRightIso.refl_eq_whiskerRightIso_symm_trans {x y : B} {g h : x ⟶ y}
    {α : g ≅ h} {α' : h ≅ g} (id_eq_symm_trans : Iso.refl _ = α' ≪≫ α) {z : B} {f : y ⟶ z}
    {ψ : g ≫ f ≅ h ≫ f} (w : whiskerRightIso α f = ψ) :
    Iso.refl _ = whiskerRightIso α' f ≪≫ ψ := by
  rw [← w]
  haveI := congrArg (fun t ↦ t.hom ▷ f) id_eq_symm_trans
  ext
  simpa using this

lemma whiskerRightIso.refl_eq_trans_whiskerRightIso_symm {x y : B} {g h : x ⟶ y}
    {α : g ≅ h} {α' : h ≅ g} (id_eq_trans_symm : Iso.refl _ = α ≪≫ α') {z : B} {f : y ⟶ z}
    {ψ : g ≫ f ≅ h ≫ f} (w : whiskerRightIso α f = ψ) :
    Iso.refl _ = ψ ≪≫ whiskerRightIso α' f := by
  rw [← w]
  ext
  haveI := congrArg (fun t ↦ t.hom ▷ f) id_eq_trans_symm
  simpa using this

/-- Try matching `e` with an expression of the form `whiskerRightIso α f`, and gives
a `Cancelable` with expression `e` if it matches. -/
def tryCancelWhiskerRightIso (e whnfR_e : Expr) : CancelM <| Option Cancelable := do
  match_expr whnfR_e with
  | whiskerRightIso _ _ _ _ _ _ _ e_α e_f => do
    (← (← read) e_α).mapM fun c => do
      pure
        { expr := e
          inv := ← mkAppM ``Bicategory.whiskerRightIso #[c.inv, e_f]
          eq_inv_comp :=
            ← mkAppOptM ``whiskerRightIso.eq_whiskerRightIso_symm_trans <|
              (Array.replicate 6 none) ++
              #[some e_α, c.inv,
                ← mkAppM' c.id_eq_inv_comp #[← mkAppM ``Eq.refl #[c.expr]]]
          eq_comp_inv :=
            ← mkAppOptM ``whiskerRightIso.eq_trans_whiskerRightIso_symm <|
              (Array.replicate 6 none) ++
              #[some e_α, c.inv,
                ← mkAppM' c.id_eq_comp_inv #[← mkAppM ``Eq.refl #[c.expr]]]
          id_eq_comp_inv :=
            ← mkAppOptM ``whiskerRightIso.refl_eq_trans_whiskerRightIso_symm <|
              (Array.replicate 6 none) ++
              #[some e_α, c.inv,
                ← mkAppM' c.id_eq_comp_inv #[← mkAppM ``Eq.refl #[c.expr]]]
          id_eq_inv_comp :=
            ← mkAppOptM ``whiskerRightIso.refl_eq_whiskerRightIso_symm_trans <|
              (Array.replicate 6 none) ++
              #[some e_α, c.inv,
                ← mkAppM' c.id_eq_inv_comp #[← mkAppM ``Eq.refl #[c.expr]]] }
  | _ => return none

-- Has higher priority than `tryCancelIso`, since we want e.g
-- `whiskerRightIso (whiskerRightIso α g) f` to have inverse
-- `whiskerRightIso (whiskerRightIso α.symm g) f`
initialize ← return insertCancelableFactory' tryCancelWhiskerRightIso 1100

end whiskerRightIso

section whiskerLeft

lemma whiskerLeft.eq_whiskerLeft_inv_comp {y z : B} {g h : y ⟶ z}
    {α : g ⟶ h} {α' : h ⟶ g} (id_eq_inv_comp : 𝟙 _ = α' ≫ α) {x : B} {f : x ⟶ y}
    {h' : x ⟶ z} {φ : f ≫ h ⟶ h'} {ψ : f ≫ g ⟶ h'}
    (w : whiskerLeft f α ≫ φ = ψ) :
    φ = whiskerLeft f α' ≫ ψ := by
  rw [← w]
  haveI := congrArg (fun t ↦ f ◁ t) id_eq_inv_comp
  simp only [Iso.refl_hom, whiskerLeft_id, whiskerLeft_comp] at this
  simp [← reassoc_of% this]

lemma whiskerLeft.eq_comp_whiskerLeft_inv {y z : B} {g h : y ⟶ z}
    {α : g ⟶ h} {α' : h ⟶ g} (id_eq_comp_inv : 𝟙 _ = α ≫ α') {x : B} {f : x ⟶ y}
    {h' : x ⟶ z} {φ : h' ⟶ f ≫ g} {ψ : h' ⟶ f ≫ h} (w : φ ≫ whiskerLeft f α = ψ) :
    φ = ψ ≫ whiskerLeft f α' := by
  rw [← w]
  haveI := congrArg (fun t ↦ f ◁ t) id_eq_comp_inv
  simp only [Iso.refl_hom, whiskerLeft_id, whiskerLeft_comp] at this
  simp [← this]

lemma whiskerLeft.refl_eq_whiskerLeft_inv_comp {y z : B} {g h : y ⟶ z}
    {α : g ⟶ h} {α' : h ⟶ g} (id_eq_inv_comp : 𝟙 _ = α' ≫ α) {x : B} {f : x ⟶ y}
    {ψ : f ≫ g ⟶ f ≫ h} (w : whiskerLeft f α = ψ) :
    𝟙 _ = whiskerLeft f α' ≫ ψ := by
  rw [← w]
  haveI := congrArg (fun t ↦ f ◁ t) id_eq_inv_comp
  simpa using this

lemma whiskerLeft.refl_eq_comp_whiskerLeft_inv {y z : B} {g h : y ⟶ z}
    {α : g ⟶ h} {α' : h ⟶ g} (id_eq_comp_inv : 𝟙 _ = α ≫ α') {x : B} {f : x ⟶ y}
    {ψ : f ≫ g ⟶ f ≫ h} (w : whiskerLeft f α = ψ) :
    𝟙 _ = ψ ≫ whiskerLeft f α' := by
  rw [← w]
  haveI := congrArg (fun t ↦ f ◁ t) id_eq_comp_inv
  simpa using this

/-- Try matching `e` with an expression of the form `whiskerLeft f α`, and gives
a `Cancelable` with expression `e` if it matches. -/
def tryCancelWhiskerLeft (e whnfR_e : Expr) : CancelM <| Option Cancelable := do
  match_expr whnfR_e with
  | whiskerLeft _ _ _ _ _ e_f _ _ e_α => do
    (← (← read) e_α).mapM fun c => do
      pure
        { expr := e
          inv := ← mkAppM ``Bicategory.whiskerLeft #[e_f, c.inv]
          eq_inv_comp :=
            ← mkAppOptM ``whiskerLeft.eq_whiskerLeft_inv_comp <|
              (Array.replicate 6 none) ++
              #[some e_α, c.inv,
                ← mkAppM' c.id_eq_inv_comp #[← mkAppM ``Eq.refl #[c.expr]]]
          eq_comp_inv :=
            ← mkAppOptM ``whiskerLeft.eq_comp_whiskerLeft_inv <|
              (Array.replicate 6 none) ++
              #[some e_α, c.inv,
                ← mkAppM' c.id_eq_comp_inv #[← mkAppM ``Eq.refl #[c.expr]]]
          id_eq_comp_inv :=
            ← mkAppOptM ``whiskerLeft.refl_eq_comp_whiskerLeft_inv <|
              (Array.replicate 6 none) ++
              #[some e_α, c.inv,
                ← mkAppM' c.id_eq_comp_inv #[← mkAppM ``Eq.refl #[c.expr]]]
          id_eq_inv_comp :=
            ← mkAppOptM ``whiskerLeft.refl_eq_whiskerLeft_inv_comp <|
              (Array.replicate 6 none) ++
              #[some e_α, c.inv,
                ← mkAppM' c.id_eq_inv_comp #[← mkAppM ``Eq.refl #[c.expr]]] }
  | _ => return none

initialize ← return insertCancelableFactory' tryCancelWhiskerLeft 900

end whiskerLeft

section whiskerRight

lemma whiskerRight.eq_whiskerRight_inv_comp {x y : B} {g h : x ⟶ y}
    {α : g ⟶ h} {α' : h ⟶ g} (id_eq_inv_comp : 𝟙 _ = α' ≫ α)
    {z : B} {f : y ⟶ z}
    {h' : x ⟶ z} {φ : h ≫ f ⟶ h'} {ψ : g ≫ f ⟶ h'}
    (w : whiskerRight α f ≫ φ = ψ) :
    φ = whiskerRight α' f ≫ ψ := by
  rw [← w]
  haveI := congrArg (fun t ↦ t ▷ f) id_eq_inv_comp
  simp only [whiskerRight_id, comp_whiskerRight] at this
  simp [← reassoc_of% this]

lemma whiskerRight.eq_comp_whiskerRight_inv {x y : B} {g h : x ⟶ y}
    {α : g ⟶ h} {α' : h ⟶ g} (id_eq_comp_inv : 𝟙 _ = α ≫ α') {z : B} {f : y ⟶ z}
    {h' : x ⟶ z} {φ : h' ⟶ g ≫ f} {ψ : h' ⟶ h ≫ f} (w : φ ≫ whiskerRight α f = ψ) :
    φ = ψ ≫ whiskerRight α' f := by
  rw [← w]
  haveI := congrArg (fun t ↦ t ▷ f) id_eq_comp_inv
  simp only [whiskerRight_id, comp_whiskerRight] at this
  simp [← this]

lemma whiskerRight.refl_eq_whiskerRight_inv_comp {x y : B} {g h : x ⟶ y}
    {α : g ⟶ h} {α' : h ⟶ g} (id_eq_inv_comp : 𝟙 _ = α' ≫ α) {z : B} {f : y ⟶ z}
    {ψ : g ≫ f ⟶ h ≫ f} (w : whiskerRight α f = ψ) :
    𝟙 _ = whiskerRight α' f ≫ ψ := by
  rw [← w]
  haveI := congrArg (fun t ↦ t ▷ f) id_eq_inv_comp
  simpa using this

lemma whiskerRight.refl_eq_comp_whiskerRight_inv {x y : B} {g h : x ⟶ y}
    {α : g ⟶ h} {α' : h ⟶ g} (id_eq_comp_inv : 𝟙 _ = α ≫ α') {z : B} {f : y ⟶ z}
    {ψ : g ≫ f ⟶ h ≫ f} (w : whiskerRight α f = ψ) :
    𝟙 _ = ψ ≫ whiskerRight α' f := by
  rw [← w]
  haveI := congrArg (fun t ↦ t ▷ f) id_eq_comp_inv
  simpa using this

/-- Try matching `e` with an expression of the form `whiskerRight α f`, and gives
a `Cancelable` with expression `e` if it matches. -/
def tryCancelWhiskerRight (e whnfR_e : Expr) : CancelM <| Option Cancelable := do
  match_expr whnfR_e with
  | whiskerRight _ _ _ _ _ _ _ e_α e_f => do
    (← (← read) e_α).mapM fun c => do
      pure
        { expr := e
          inv := ← mkAppM ``Bicategory.whiskerRight #[c.inv, e_f]
          eq_inv_comp :=
            ← mkAppOptM ``whiskerRight.eq_whiskerRight_inv_comp <|
              (Array.replicate 6 none) ++
              #[some e_α, c.inv,
                ← mkAppM' c.id_eq_inv_comp #[← mkAppM ``Eq.refl #[c.expr]]]
          eq_comp_inv :=
            ← mkAppOptM ``whiskerRight.eq_comp_whiskerRight_inv <|
              (Array.replicate 6 none) ++
              #[some e_α, c.inv,
                ← mkAppM' c.id_eq_comp_inv #[← mkAppM ``Eq.refl #[c.expr]]]
          id_eq_comp_inv :=
            ← mkAppOptM ``whiskerRight.refl_eq_comp_whiskerRight_inv <|
              (Array.replicate 6 none) ++
              #[some e_α, c.inv,
                ← mkAppM' c.id_eq_comp_inv #[← mkAppM ``Eq.refl #[c.expr]]]
          id_eq_inv_comp :=
            ← mkAppOptM ``whiskerRight.refl_eq_whiskerRight_inv_comp <|
              (Array.replicate 6 none) ++
              #[some e_α, c.inv,
                ← mkAppM' c.id_eq_inv_comp #[← mkAppM ``Eq.refl #[c.expr]]] }
  | _ => return none

initialize ← return insertCancelableFactory' tryCancelWhiskerRight 900

end whiskerRight

end Lemmas

end Tactic.CategoryTheory.RotateIsos.Bicategory
