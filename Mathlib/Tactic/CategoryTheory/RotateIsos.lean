/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.Lean.Meta.Simp

/-!
# The `rotate_isos` tactic

Given a term of the form `e : α₁ ≫ ⋯ ≫ αₖ = β₁ ≫ ⋯ ≫ βₗ`, or of the form
`e : α₁ ≪≫ ⋯ ≪≫ αₖ = β₁ ≪≫ ⋯ ≪≫ βₗ` (possibly not fully right-associated, or under ∀ binders),
the `rotate_isos` tactic moves specified numbers
of isomorphisms from the left-hand side of the equality to the right-hand side.
Depending on a flag given to the tactic, the isomorphisms are moved from the lhs starting from
the leftmost morphism or from the rightmost morphism.

```lean
variable {C : Type*} [Category C]

example (a b c d e : C) (g : b ≅ c) (h : d ≅ c) (i : d ⟶ e) (k : a ⟶ e)
    (hyp : ∀ (f : a ≅ b), f.hom ≫ g.hom ≫ h.inv ≫ i = k) :
    ∀ (f : a ≅ b), i = h.hom ≫ g.inv ≫ f.inv ≫ k := by
  rotate_isos ← 0 3 using hyp

```

The tactic is currently WIP and its core has not been implemented yet.

-/

open Lean Parser.Tactic Elab Command Elab.Tactic Meta

open Tactic

namespace Tactic.CategoryTheory.RotateIsos
open _root_.CategoryTheory

section Lemmas

variable {C : Type*} [Category C] {X Y : C}

-- We collect the variety of lemmas we need to "move around" terms in equalities for every
-- kind of "cancelable" morphism (see the `Cancelable` docstring below for precisions about what
-- is meant by cancelable morphism).
-- These are duplicate of already existing lemma and these are tailored for
-- application within the rotateIsos tactic, so they are better kept in this namespace in order
-- to keep the standard namespace clean.
-- Naming of the lemmas try to follow the `Cancelable` field they model, and are
-- named after the shape of the conclusion.

section Iso

lemma Iso.eq_symm_trans {f : X ≅ Y} {Z : C} {g : Y ≅ Z} {h : X ≅ Z}
    (w : f ≪≫ g = h) : g = f.symm ≪≫ h := by
  rw [←w, Iso.symm_self_id_assoc]

lemma Iso.eq_trans_symm {f : X ≅ Y} {Z : C} {g : Z ≅ X} {h : Z ≅ Y}
    (w : g ≪≫ f = h) : g = h ≪≫ f.symm := by
  rw [←w, Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl]

lemma Iso.refl_eq_trans_symm {f : X ≅ Y} {g : X ≅ Y}
    (w : f = g) : Iso.refl X = f ≪≫ g.symm := by
  rw [w, Iso.self_symm_id]

lemma Iso.refl_eq_symm_trans {f : X ≅ Y} {g : X ≅ Y}
    (w : f = g) : Iso.refl Y = g.symm ≪≫ f := by
  rw [w, Iso.symm_self_id]

end Iso

section IsoHom

lemma Iso.eq_inv_comp {f : X ≅ Y} {Z : C} {g : Y ⟶ Z} {h : X ⟶ Z} (w : f.hom ≫ g = h) :
    g = f.inv ≫ h := by
  rw [← w, Iso.inv_hom_id_assoc]

lemma Iso.eq_comp_inv {f : X ≅ Y} {Z : C} {g : Z ⟶ X} {h : Z ⟶ Y} (w : g ≫ f.hom = h) :
    g = h ≫ f.inv := by
  rw [← w, Category.assoc, Iso.hom_inv_id, Category.comp_id]

lemma Iso.id_eq_inv_comp {f : X ≅ Y} {g : X ⟶ Y} (w : f.hom = g) :
    𝟙 _ = f.inv ≫ g  := by
  rw [← w, Iso.inv_hom_id]

lemma Iso.id_eq_comp_inv {f : X ≅ Y} {g : X ⟶ Y} (w : f.hom = g) :
    𝟙 _ = g ≫ f.inv  := by
  rw [← w, Iso.hom_inv_id]

end IsoHom

section IsoInv

lemma Iso.eq_hom_comp {f : X ≅ Y} {Z : C} {g : X ⟶ Z} {h : Y ⟶ Z} (w : f.inv ≫ g = h) :
    g = f.hom ≫ h :=
  Iso.inv_comp_eq f|>.mp w

lemma Iso.eq_comp_hom {f : X ≅ Y} {Z : C} {g : Z ⟶ Y} {h : Z ⟶ X} (w : g ≫ f.inv = h) :
    g = h ≫ f.hom :=
  Iso.comp_inv_eq f|>.mp w

lemma Iso.id_eq_hom_comp {f : X ≅ Y} {g : Y ⟶ X} (w : f.inv = g) :
    𝟙 _ = f.hom ≫ g  := by
  rw [← w, Iso.hom_inv_id]

lemma Iso.id_eq_comp_hom {f : X ≅ Y} {g : Y ⟶ X} (w : f.inv = g) :
    𝟙 _ = g ≫ f.hom  := by
  rw [← w, Iso.inv_hom_id]

end IsoInv

section IsIsoHom

lemma IsIso.eq_inv_comp {f : X ⟶ Y} [IsIso f] {Z : C} {g : Y ⟶ Z} {h : X ⟶ Z}
    (w : f ≫ g = h) : g = inv f ≫ h := by
  rw [_root_.CategoryTheory.IsIso.eq_inv_comp, w]

lemma IsIso.eq_comp_inv {f : X ⟶ Y}  [IsIso f] {Z : C} {g : Z ⟶ X} {h : Z ⟶ Y}
    (w : g ≫ f = h) : g = h ≫ inv f := by
  rw [_root_.CategoryTheory.IsIso.eq_comp_inv, w]

lemma IsIso.id_eq_inv_comp {f : X ⟶ Y} [IsIso f] {g : X ⟶ Y} (w : f = g) :
    𝟙 _ = inv f ≫ g  := by
  rw [_root_.CategoryTheory.IsIso.eq_inv_comp, w, Category.comp_id]

lemma IsIso.id_eq_comp_inv {f : X ⟶ Y}  [IsIso f] {g : X ⟶ Y} (w : f = g) :
    𝟙 _ = g ≫ inv f  := by
  rw [_root_.CategoryTheory.IsIso.eq_comp_inv, w, Category.id_comp]

end IsIsoHom

section NatTrans

lemma NatTrans.eq_inv_comp {D : Type*} [Category D] {F G : C ⥤ D} {α : F ⟶ G} {α' : G ⟶ F}
    (id_eq_inv_comp : 𝟙 _ = α' ≫ α)
    (c : C) {Z : D} {g : G.obj c ⟶ Z} {h : F.obj c ⟶ Z} (w : α.app c ≫ g = h) :
    g = α'.app c ≫ h := by
  rw [← w, ← Category.assoc, ← NatTrans.comp_app, ← congrArg (fun t ↦ t.app c) id_eq_inv_comp,
    NatTrans.id_app, Category.id_comp]

lemma NatTrans.eq_comp_inv {D : Type*} [Category D] {F G : C ⥤ D} {α : F ⟶ G} {α' : G ⟶ F}
    (id_eq_comp_inv : 𝟙 _ = α ≫ α')
    (c : C) {Z : D} {g : Z ⟶ F.obj c} {h : Z ⟶ G.obj c} (w : g ≫ α.app c = h) :
    g = h ≫ α'.app c := by
  rw [← w, Category.assoc, ← NatTrans.comp_app, ← congrArg (fun t ↦ t.app c) id_eq_comp_inv,
    NatTrans.id_app, Category.comp_id]

lemma NatTrans.id_eq_inv_comp {D : Type*} [Category D] {F G : C ⥤ D} {α : F ⟶ G} {α' : G ⟶ F}
    (id_eq_inv_comp : 𝟙 _ = α' ≫ α)
    (c : C) {f : F.obj c ⟶ G.obj c} (w : α.app c = f) :
    𝟙 _ = α'.app c ≫ f := by
  rw [← w, ← NatTrans.comp_app, ← congrArg (fun t ↦ t.app c) id_eq_inv_comp,
    NatTrans.id_app]

lemma NatTrans.id_eq_comp_inv {D : Type*} [Category D] {F G : C ⥤ D} {α : F ⟶ G} {α' : G ⟶ F}
    (id_eq_comp_inv : 𝟙 _ = α ≫ α')
    (c : C) {f : F.obj c ⟶ G.obj c} (w : α.app c = f) :
    𝟙 _ = f ≫ α'.app c := by
  rw [← w, ← NatTrans.comp_app, ← congrArg (fun t ↦ t.app c) id_eq_comp_inv,
    NatTrans.id_app]

end NatTrans

section Functor

lemma Functor.eq_inv_comp {D : Type*} [Category D] (F : C ⥤ D) {f : X ⟶ Y} {f' : Y ⟶ X}
    (id_eq_inv_comp : 𝟙 _ = f' ≫ f)
    {Z : D} {g : F.obj Y ⟶ Z} {h : F.obj X ⟶ Z} (w : F.map f ≫ g = h) :
    g = F.map f' ≫ h := by
  rw [← w, ← Category.assoc, ← Functor.map_comp, ← id_eq_inv_comp, Functor.map_id,
    Category.id_comp]

lemma Functor.eq_comp_inv {D : Type*} [Category D] (F : C ⥤ D) {f : X ⟶ Y} {f' : Y ⟶ X}
    (id_eq_comp_inv : 𝟙 _ = f ≫ f')
    {Z : D} {g : Z ⟶ F.obj X} {h : Z ⟶ F.obj Y} (w : g ≫ F.map f = h) :
    g = h ≫ F.map f' := by
  rw [← w, Category.assoc, ← Functor.map_comp, ← id_eq_comp_inv, Functor.map_id,
    Category.comp_id]

lemma Functor.id_eq_inv_comp {D : Type*} [Category D] (F : C ⥤ D) {f : X ⟶ Y} {f' : Y ⟶ X}
    (id_eq_inv_comp : 𝟙 _ = f' ≫ f) {g : F.obj X ⟶ F.obj Y} (w : F.map f = g) :
    𝟙 _ = F.map f' ≫ g := by
  rw [← w, ← Functor.map_comp, ← id_eq_inv_comp, Functor.map_id]

lemma Functor.id_eq_comp_inv {D : Type*} [Category D] (F : C ⥤ D) {f : X ⟶ Y} {f' : Y ⟶ X}
    (id_eq_comp_inv : 𝟙 _ = f ≫ f') {g : F.obj X ⟶ F.obj Y} (w : F.map f = g) :
    𝟙 _ = g ≫ F.map f' := by
  rw [← w, ← Functor.map_comp, ← id_eq_comp_inv, Functor.map_id]

end Functor

/-- Version of `trans_assoc` used to left_associate compositions in a `simpOnlyNames` call within a
tactic. -/
theorem trans_assoc_rev {Z Z' : C} (α : X ≅ Y) (β : Y ≅ Z) (γ : Z ≅ Z') :
    α ≪≫ β ≪≫ γ = (α ≪≫ β) ≪≫ γ :=
  Iso.trans_assoc α β γ|>.symm

/-- Version of `comp_assoc` used to left_associate compositions in a `simpOnlyNames` call within a
tactic. -/
theorem comp_assoc_rev {Z Z' : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ Z') :
    f ≫ g ≫ h = (f ≫ g) ≫ h :=
  Category.assoc f g h|>.symm

end Lemmas

/-- An expression is cancellable if it is of the the following form :
- An isomorphism.
- `e.hom` or `e.inv` for an isomorphism `e`.
- `e.hom.app _` or `e.inv.app _` for a natural isomorphism `e`.
- `F.map f` for `f` a cancellable morphism.
- `inv f` for `f` with an `IsIso` instance. TODO: is this really needed? we can simp inv_inv
- `f` for `IsIso f`.

The structure `Cancelable` is a book-keeping structure that holds the expression,
an expression of its inverse, as well as expressions of proofs of the lemmas needed to cancel it. -/
structure Cancelable where
  /-- The expression -/
  expr : Expr
  /-- An expression of the inverse of `expr`. -/
  inv : Expr
  /-- An epression of type ∀ {h h'}, expr ≫ h = h' → h = inv ≫ h'`. -/
  eq_inv_comp : Expr
  /-- An epression of type `∀ {h h'}, h ≫ expr = h' → h = h' ≫ inv`. -/
  eq_comp_inv : Expr
  /-- An epression of type ∀ {h}, expr = h → 𝟙 _ = inv ≫ h`. -/
  id_eq_inv_comp : Expr
  /-- An epression of type ∀ {h}, expr = h → 𝟙 _ = h ≫ inv`. -/
  id_eq_comp_inv : Expr

/-- If `e` is an expression for a morphism in a category that has an `IsIso` instance,
return `inv f`. Otherwise, return none. -/
def tryCancelIsIso (e : Expr) : MetaM (Option Cancelable) := do
  -- Code inspired from `CategoryTheory/Tactic/ToApp`.
  match (← inferType e).getAppFnArgs with
  | (`Quiver.Hom, #[_, (.app _ <| .app _ _), _, _]) =>
    (← synthInstance? <| ← mkAppM ``IsIso #[e]).mapM fun i => do
      pure
        { expr := e
          inv := ← mkAppOptM ``CategoryTheory.inv <| (Array.replicate 4 none) ++ #[some e, i]
          eq_inv_comp :=
            ← mkAppOptM ``IsIso.eq_inv_comp <| (Array.replicate 4 none) ++ #[some e, i]
          eq_comp_inv :=
            ← mkAppOptM ``IsIso.eq_comp_inv <| (Array.replicate 4 none) ++ #[some e, i]
          id_eq_comp_inv :=
            ← mkAppOptM ``IsIso.id_eq_comp_inv <| (Array.replicate 4 none) ++ #[some e, i]
          id_eq_inv_comp :=
            ← mkAppOptM ``IsIso.id_eq_inv_comp <| (Array.replicate 4 none) ++ #[some e, i] }
  | _ => throwError "rotate_isos can only be used on equalities of (iso)morphisms in categories."

/-- Assuming `e₁` is an expression for an isomorphism and `e` is an exprission for `e₁.hom`,
gets a `Cancelable` structure with expression `e`. -/
def cancelIsoHom (e e₁ : Expr) : MetaM Cancelable := do
  pure
    { expr := e
      inv := ← mkAppM ``Iso.inv #[e₁]
      eq_inv_comp := ← mkAppOptM ``Iso.eq_inv_comp <| (Array.replicate 4 none) ++ #[some e₁]
      eq_comp_inv := ← mkAppOptM ``Iso.eq_comp_inv <| (Array.replicate 4 none) ++ #[some e₁]
      id_eq_inv_comp := ← mkAppOptM ``Iso.id_eq_inv_comp <| (Array.replicate 4 none) ++ #[some e₁]
      id_eq_comp_inv := ← mkAppOptM ``Iso.id_eq_comp_inv <| (Array.replicate 4 none) ++ #[some e₁] }

/-- Assuming `e₁` is an expression for an isomorphism and `e` is an exprission for `e₁.inv`,
gets a `Cancelable` structure with expression `e`. -/
def cancelIsoInv (e e₁ : Expr): MetaM Cancelable := do
  pure
    { expr := e
      inv := ← mkAppM ``Iso.hom #[e₁]
      eq_inv_comp := ← mkAppOptM ``Iso.eq_hom_comp <| (Array.replicate 4 none) ++ #[some e₁]
      eq_comp_inv := ← mkAppOptM ``Iso.eq_comp_hom <| (Array.replicate 4 none) ++ #[some e₁]
      id_eq_inv_comp := ← mkAppOptM ``Iso.id_eq_hom_comp <| (Array.replicate 4 none) ++ #[some e₁]
      id_eq_comp_inv := ← mkAppOptM ``Iso.id_eq_comp_hom <| (Array.replicate 4 none) ++ #[some e₁] }

/-- Assuming `e` is an expression for an isomorphism, gets a `Cancelable` structure with
expression `e`. -/
def cancelIso (e : Expr): MetaM Cancelable := do
  pure
    { expr := e
      inv := ← mkAppM ``CategoryTheory.Iso.symm #[e]
      eq_inv_comp := ← mkAppOptM ``Iso.eq_symm_trans <| (Array.replicate 4 none) ++ #[some e]
      eq_comp_inv := ← mkAppOptM ``Iso.eq_trans_symm <| (Array.replicate 4 none) ++ #[some e]
      id_eq_inv_comp :=
        ← mkAppOptM ``Iso.refl_eq_symm_trans <| (Array.replicate 4 none) ++ #[some e]
      id_eq_comp_inv :=
        ← mkAppOptM ``Iso.refl_eq_trans_symm <| (Array.replicate 4 none) ++ #[some e] }

/-- Assuming `e` is an expression of the form `e₁.app e'` for a cancellable natural transformation
`e₁`, and given a `Cancelable` structure `c` with expression `e₁`, build a `Cancelable` structure
with expression `e`. -/
def cancelNatTransApp (e e' : Expr) (c : Cancelable) : MetaM Cancelable := do
  pure
    { expr := e
      inv := ← mkAppM ``NatTrans.app #[c.inv, e']
      eq_inv_comp :=
        ← mkAppOptM ``NatTrans.eq_inv_comp <| (Array.replicate 6 none) ++
            #[some c.expr, c.inv, ← mkAppM' c.id_eq_inv_comp #[← mkAppM ``Eq.refl #[c.expr]], e']
      eq_comp_inv :=
        ← mkAppOptM ``NatTrans.eq_comp_inv <| (Array.replicate 6 none) ++
            #[some c.expr, c.inv, ← mkAppM' c.id_eq_comp_inv #[← mkAppM ``Eq.refl #[c.expr]], e']
      id_eq_comp_inv :=
        ← mkAppOptM ``NatTrans.id_eq_comp_inv <| (Array.replicate 6 none) ++
            #[some c.expr, c.inv, ← mkAppM' c.id_eq_comp_inv #[← mkAppM ``Eq.refl #[c.expr]], e']
      id_eq_inv_comp :=
        ← mkAppOptM ``NatTrans.id_eq_inv_comp <| (Array.replicate 6 none) ++
            #[some c.expr, c.inv, ← mkAppM' c.id_eq_inv_comp #[← mkAppM ``Eq.refl #[c.expr]], e'] }

/-- Given expressions `e F` such that `F` is an expression for a functor, `e₂ an expression for
`F.map e'` where `e'` is a cancelable map and given a `Cancelable` structure with
expression `e₂`, gives a `Cancelable` structure with expression `e`. -/
def cancelFunctorMap (e F: Expr) (c : Cancelable) : MetaM Cancelable := do
  pure
    { expr := e
      inv := ← mkAppM ``Prefunctor.map #[← mkAppM ``Functor.toPrefunctor #[F], c.inv]
      eq_inv_comp :=
        ← mkAppOptM ``Functor.eq_inv_comp <| (Array.replicate 6 none) ++
            #[some F, c.expr, c.inv, ← mkAppM' c.id_eq_inv_comp #[← mkAppM ``Eq.refl #[c.expr]]]
      eq_comp_inv :=
        ← mkAppOptM ``Functor.eq_comp_inv <| (Array.replicate 6 none) ++
            #[some F, c.expr, c.inv, ← mkAppM' c.id_eq_comp_inv #[← mkAppM ``Eq.refl #[c.expr]]]
      id_eq_comp_inv :=
        ← mkAppOptM ``Functor.id_eq_comp_inv <| (Array.replicate 6 none) ++
            #[some F, c.expr, c.inv, ← mkAppM' c.id_eq_comp_inv #[← mkAppM ``Eq.refl #[c.expr]]]
      id_eq_inv_comp :=
        ← mkAppOptM ``Functor.id_eq_inv_comp <| (Array.replicate 6 none) ++
            #[some F, c.expr, c.inv, ← mkAppM' c.id_eq_inv_comp #[← mkAppM ``Eq.refl #[c.expr]]] }

end Tactic.CategoryTheory.RotateIsos
