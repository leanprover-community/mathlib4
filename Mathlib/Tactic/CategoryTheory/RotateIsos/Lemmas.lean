/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.Tactic.CategoryTheory.RotateIsos.Cancelable

/-!
# Basic lemmas for `rotate_iso`

This file records some basic lemmas for the `rotate_iso` tactic, and register
some initial ways to produce cancelable morphisms. The lemmas comes in
group of four, and are tailored to fit in a `Cancelable` structure.

The initial set of supported "cancelable" terms is the following:
- The term is of type `e : X ≅ Y`. In this case, the term added to the opposite side of the equality
  is `e.symm`
- The term is of type `e.hom` (resp. `e.inv') for `e : _ ≅ _`. In this case, the term added to
  the opposite side of the equality is `e.inv` (resp. e.hom).
- The term is of type `e.app x` for a movable natural transformation `e`. In this case the term
  added to the opposite side of the equality is `e'.app _` where `e'` is the constructed inverse of
  `e`.
- The term is of type `F.map f` for a functor `F` and `f` is movable. In this case, the term
  added to the opposite side of the equality is `F.map f'` where `f'` is the constructed inverse
  of `f`.
- The term is of type `f` and `f` has an `IsIso` instance. In this case, the inverse is `inv f`.

This file also provides two terms elaborators: `rotate_isos%` and `rotate_isos_iff%`, that
are used to apply the tactic at a term and use it as a `e.g` a rewrite rule or as simp lemmas.
-/

namespace Tactic.CategoryTheory.RotateIsos
open Lean Parser.Tactic Elab Command Elab.Tactic Meta _root_.CategoryTheory

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
    (w : f = g) : Iso.refl X = g ≪≫ f.symm := by
  rw [w, Iso.self_symm_id]

lemma Iso.refl_eq_symm_trans {f : X ≅ Y} {g : X ≅ Y}
    (w : f = g) : Iso.refl Y = f.symm ≪≫ g := by
  rw [w, Iso.symm_self_id]

/-- Try matching `e` with an expression for an isomorphism and gets a `Cancelable` structure with
expression `e` if it matches.. -/
@[nolint unusedArguments]
def tryCancelIso (e _whnfR_e: Expr) : MetaM <| Option Cancelable := do
  match_expr (← whnfR <| ← inferType e) with
  | Iso _ _ _ _ =>
    return some
      { expr := e
        inv := ← mkAppM ``CategoryTheory.Iso.symm #[e]
        eq_inv_comp := ← mkAppOptM ``Iso.eq_symm_trans <| (Array.replicate 4 none) ++ #[some e]
        eq_comp_inv := ← mkAppOptM ``Iso.eq_trans_symm <| (Array.replicate 4 none) ++ #[some e]
        id_eq_inv_comp :=
          ← mkAppOptM ``Iso.refl_eq_symm_trans <| (Array.replicate 4 none) ++ #[some e]
        id_eq_comp_inv :=
          ← mkAppOptM ``Iso.refl_eq_trans_symm <| (Array.replicate 4 none) ++ #[some e] }
  | _ => return none

-- register `tryCancelIsIso` as a way to cancel morphisms. Priority is `1000` (i.e "high") as this
-- should be tried first.
initialize ← return insertCancelableFactory tryCancelIso 1000

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

/-- Try matching `e` with an expresionn for `e₁.hom`, where `e₁` is an expression for an
isomorphism and gets a `Cancelable` structure with expression `e` if it matches. -/
def tryCancelIsoHom (e wnfhR_e : Expr) : MetaM (Option Cancelable) := do
  match wnfhR_e with
  | .proj ``Iso 0 e₁ =>
    return some
      { expr := e
        inv := ← mkAppM ``Iso.inv #[e₁]
        eq_inv_comp := ← mkAppOptM ``Iso.eq_inv_comp <| (Array.replicate 4 none) ++ #[some e₁]
        eq_comp_inv := ← mkAppOptM ``Iso.eq_comp_inv <| (Array.replicate 4 none) ++ #[some e₁]
        id_eq_inv_comp := ← mkAppOptM ``Iso.id_eq_inv_comp <| (Array.replicate 4 none) ++ #[some e₁]
        id_eq_comp_inv :=
          ← mkAppOptM ``Iso.id_eq_comp_inv <| (Array.replicate 4 none) ++ #[some e₁] }
  | _ => return none

-- it should be fine for it to have same priority as `tryCancelIsoInv`, but let’s be safe.
initialize ← return insertCancelableFactory tryCancelIsoHom 510

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

/-- Try matching `e` with an expresionn for `e₁.inv`, where `e₁` is an expression for an
isomorphism and gets a `Cancelable` structure with expression `e` if it matches. -/
def tryCancelIsoInv (e whnfR_e: Expr): MetaM <| Option Cancelable := do
  match whnfR_e with
  | .proj ``Iso 1 e₁ =>
    return some
      { expr := e
        inv := ← mkAppM ``Iso.hom #[e₁]
        eq_inv_comp := ← mkAppOptM ``Iso.eq_hom_comp <| (Array.replicate 4 none) ++ #[some e₁]
        eq_comp_inv := ← mkAppOptM ``Iso.eq_comp_hom <| (Array.replicate 4 none) ++ #[some e₁]
        id_eq_inv_comp := ← mkAppOptM ``Iso.id_eq_hom_comp <| (Array.replicate 4 none) ++ #[some e₁]
        id_eq_comp_inv :=
          ← mkAppOptM ``Iso.id_eq_comp_hom <| (Array.replicate 4 none) ++ #[some e₁] }
  | _ => return none

-- Register `tryCancelIsoInv` as a way to cancel morphisms.
initialize ← return insertCancelableFactory tryCancelIsoInv 500

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

/-- If `e` is an expression for a morphism in a category that has an `IsIso` instance,
return `inv f`. Otherwise, return none. This is the "fallback" of the tactic, and this
should always be the last element in the list of things `getCancelTerm` tries. -/
@[nolint unusedArguments]
def tryCancelIsIso (e _whnfR_e: Expr) : MetaM (Option Cancelable) := do
  match_expr ← inferType e with
  | Quiver.Hom _ _ _ _ =>
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

-- register `tryCancelIsIso` as a way to cancel morphisms. Priority is `0` as this is the fallback.
initialize ← return insertCancelableFactory tryCancelIsIso 0

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

/-- Try matching `e` with an expression of the form `e₁.app e'` for a cancelable natural
transformation `e₁` and build a `Cancelable` structure with expression `e` if it matches. -/
def tryCancelNatTransApp (e whnfR_e : Expr) : CancelM (Option Cancelable) := do
  match whnfR_e with
  | .app (.proj ``CategoryTheory.NatTrans 0 e₁) e' =>
    (← (← read) e₁).mapM fun c => do
      pure
        { expr := e
          inv := ← mkAppM ``NatTrans.app #[c.inv, e']
          eq_inv_comp :=
            ← mkAppOptM ``NatTrans.eq_inv_comp <| (Array.replicate 6 none) ++
                #[some c.expr, c.inv, ← mkAppM' c.id_eq_inv_comp #[← mkAppM ``Eq.refl #[c.expr]],
                  e']
          eq_comp_inv :=
            ← mkAppOptM ``NatTrans.eq_comp_inv <| (Array.replicate 6 none) ++
                #[some c.expr, c.inv, ← mkAppM' c.id_eq_comp_inv #[← mkAppM ``Eq.refl #[c.expr]],
                  e']
          id_eq_comp_inv :=
            ← mkAppOptM ``NatTrans.id_eq_comp_inv <| (Array.replicate 6 none) ++
                #[some c.expr, c.inv, ← mkAppM' c.id_eq_comp_inv #[← mkAppM ``Eq.refl #[c.expr]],
                  e']
          id_eq_inv_comp :=
            ← mkAppOptM ``NatTrans.id_eq_inv_comp <| (Array.replicate 6 none) ++
                #[some c.expr, c.inv, ← mkAppM' c.id_eq_inv_comp #[← mkAppM ``Eq.refl #[c.expr]],
                  e'] }
  | _ => return none

-- register `tryCancelNatTransApp` as a way to cancel morphisms.
initialize ← return insertCancelableFactory' tryCancelNatTransApp 600

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
    𝟙 (F.obj Y) = F.map f' ≫ g := by
  rw [← w, ← Functor.map_comp, ← id_eq_inv_comp, Functor.map_id]

lemma Functor.id_eq_comp_inv {D : Type*} [Category D] (F : C ⥤ D) {f : X ⟶ Y} {f' : Y ⟶ X}
    (id_eq_comp_inv : 𝟙 _ = f ≫ f') {g : F.obj X ⟶ F.obj Y} (w : F.map f = g) :
    𝟙 (F.obj X) = g ≫ F.map f' := by
  rw [← w, ← Functor.map_comp, ← id_eq_comp_inv, Functor.map_id]

/-- Try matching `e` with an expression of the form `F.map e'`, test if `e'`
is an expression of a cancelable term and gives a `Cancelable` structure with
expression `e` if that is the case. -/
def tryCancelFunctorMap (e whnfR_e: Expr) : CancelM (Option Cancelable) := do
  match whnfR_e with
  | .app (.app (.app (.proj ``Prefunctor 1 (.app _ F)) _) _) e₂ =>
    (← (← read) e₂).mapM fun c => do
      pure
        { expr := e
          inv := ← mkAppM ``Prefunctor.map #[← mkAppM ``Functor.toPrefunctor #[F], c.inv]
          eq_inv_comp :=
            ← mkAppOptM ``Functor.eq_inv_comp <| (Array.replicate 6 none) ++
                #[some F, c.expr, c.inv,
                  ← mkAppM' c.id_eq_inv_comp #[← mkAppM ``Eq.refl #[c.expr]]]
          eq_comp_inv :=
            ← mkAppOptM ``Functor.eq_comp_inv <| (Array.replicate 6 none) ++
                #[some F, c.expr, c.inv,
                  ← mkAppM' c.id_eq_comp_inv #[← mkAppM ``Eq.refl #[c.expr]]]
          id_eq_comp_inv :=
            ← mkAppOptM ``Functor.id_eq_comp_inv <| (Array.replicate 6 none) ++
                #[some F, c.expr, c.inv,
                  ← mkAppM' c.id_eq_comp_inv #[← mkAppM ``Eq.refl #[c.expr]]]
          id_eq_inv_comp :=
            ← mkAppOptM ``Functor.id_eq_inv_comp <| (Array.replicate 6 none) ++
                #[some F, c.expr, c.inv,
                  ← mkAppM' c.id_eq_inv_comp #[← mkAppM ``Eq.refl #[c.expr]]] }
  | _ => return none

-- register `tryCancelFunctorMap` as a way to cancel morphisms.
initialize ← return insertCancelableFactory' tryCancelFunctorMap 600

end Functor

end Lemmas

end Tactic.CategoryTheory.RotateIsos
