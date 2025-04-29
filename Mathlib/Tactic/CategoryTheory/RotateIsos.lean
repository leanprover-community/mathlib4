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

The tactic analyzes terms in the given composition and detects morphisms that are isomorphisms
("movable") and constructs their inverses based on the following rules:
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

/-- Given an expression `e`, if `e` is an expression for a cancelable morphism, returns
a `Cancelable` structure such that `e.expr` is the original expression.
Otherwise, returns none. -/
partial def getCancelTerm (e : Expr) : MetaM (Option Cancelable) := do
  let t ← whnfR <| ← inferType e
  match t.app4? ``Iso with
  | some _ => cancelIso e
  | _ =>
    match (← whnfR e) with
    | .proj ``Iso 0 e₁ => cancelIsoHom e e₁
    | .proj ``Iso 1 e₁ => cancelIsoInv e e₁
    | .app (.proj ``CategoryTheory.NatTrans 0 e₁) e₂ =>
      (← getCancelTerm e₁).mapM (cancelNatTransApp e e₂ ·)
    | .app e₁ e₂ =>
      match e₁ with
      | .app (.app (.proj ``Prefunctor 1 G) _) _ =>
        if let some c ← getCancelTerm e₂ then
          if let .app _ F := G then cancelFunctorMap e F c
          else return none
        else tryCancelIsIso e
      | _ => tryCancelIsIso e
    | _ => tryCancelIsIso e

/-- Given an expression of type `f₁ ≫ ⋯ ≫ fₙ`or `f₁ ≪≫ ⋯ ≪≫ fₙ`,
assumed to be either fully left-associated or right-associated
(depending on the argument `rev_assoc`),
build a list of the cancellable morphisms (with their cancellation data) starting from
the leftmost or rightmost (depending on the argument `rev`) until we hit a non-cancellable term.
The function also returns a flag that is set if all of the morphisms are cancellable. -/
partial def getCancelables (e : Expr) (rev rev_assoc: Bool) : MetaM (List Cancelable × Bool) := do
  match (← whnfR e).getAppFnArgs with
  | (``CategoryStruct.comp, #[_, _, _, _, _, l, r])
  | (``Iso.trans, #[_, _, _, _, _, l, r]) =>
    match rev_assoc, rev with
    | true, true =>
      -- expression is left-associated and we look at morphisms from left to right
      let (t, b) ← getCancelables l rev rev_assoc
      if b then
        if let some c ← getCancelTerm r then return (t ++ [c], b)
        else return (t, false)
      else return (t, false)
    | true, false =>
      -- expression is left-associated and we look at morphisms from right to left
      if let some c ← getCancelTerm r then
        let (t, b) ← getCancelables l rev rev_assoc
        return (c::t, b)
      else return ([], False)
    | false, true =>
      -- expression is right-associated and we look at morphisms from right to left
      let (t, b) ← getCancelables r rev rev_assoc
      if b then
        if let some c ← getCancelTerm l then return (t ++ [c], b)
        else return (t, false)
      else return (t, false)
    | false, false =>
      -- expression is right-associated and we look at morphisms from left to right
      if let some c ← getCancelTerm l then
        let (t, b) ← getCancelables r rev rev_assoc
        return (c::t, b)
      else return ([], false)
  | _ => if let some c ← getCancelTerm e then return ([c], true) else return ([], false)

/-- Auxiliary definition for `RotateIsosCore`, isolating the main loop of
the tactic. -/
def rotateIsosCoreAux (e : Expr) (a : ℕ) (rev : Bool) (try_id : Bool)
    (cancels : List Cancelable × Bool) :
    MetaM Expr := do
  match a with
  | 0 => return e
  | a' + 1 =>
    let (c::cancels', v) := cancels | throwError "Not enough cancelable morphisms in one \
      of the sides of the provided equality."
    -- We need to check the edge case in which there is only one morphism left to cancel
    -- In this case, we must use the `id_` versions of the lemmas in the
    -- `Cancelable` structure.
    -- We know we're in this case if we reached the last element of `cancels` and if the
    -- boolean value in the return type of `getCancelables` is set to true.
    -- We also check for edge cases where the rhs is an identity.
    match rev, (try_id && v && cancels'.length == 0) with
    | false, false =>
      -- Expression is of the form expr ≫ h = h' and we use `eq_inv_comp`.
      rotateIsosCoreAux (← mkAppM' c.eq_inv_comp #[e]) a' rev try_id (cancels', v)
    | false, true =>
      -- Expression is of the form expr = h, and we use `id_eq_inv_comp`.
      rotateIsosCoreAux (← mkAppM' c.id_eq_inv_comp #[e]) a' rev try_id (cancels', v)
    | true, false =>
      -- Expression is of the form h ≫ expr = h' and we use `eq_comp_inv`.
      rotateIsosCoreAux (← mkAppM' c.eq_comp_inv #[e]) a' rev try_id (cancels', v)
    | true, true =>
      -- Expression is of the form expr = h' and we use `id_eq_comp_inv`.
      rotateIsosCoreAux (← mkAppM' c.id_eq_comp_inv #[e]) a' rev try_id (cancels', v)

/-- Core for the rotate_isos tactic. Take as input an expression of the form
`f = g` between two (iso)morphisms in a category, as well as the number of
of cancellable morphisms to moves from the lhs to the rhs, and from the
rhs to the lhs, and returns an expression of type `e → e'`, where `e` is the original equality,
and `e'` is the equality in which the (iso)morphisms have been moved according to the arguments, as
well as a proof of the implication. -/
def rotateIsosCore (e : Expr) (a b : ℕ) (rev : Bool) : MetaM (Expr × Expr) := do
  -- We start by re-associating everything in the expression. We need to reassociate differently
  -- depending on wether we want to remove terms from the left or from the right, which depends
  -- `rev`
  -- SimpEq throws an error for us if `e` is not an equality.
  -- `g` will be abstracted in the return type.
  let e' ← whnfR e
  let g ← mkFreshExprMVar <| ← instantiateMVars e'
  let (s_e, p_e) ←
    if rev then simpEq (fun e => simpOnlyNames
        [``Iso.trans_symm, ``trans_assoc_rev, ``comp_assoc_rev]
      e (config := { decide := false })) e' g
    else simpEq (fun e => simpOnlyNames
        [``Iso.trans_symm, ``Iso.trans_assoc, ``Category.assoc]
      e (config := { decide := false })) e' g
  let some (_, lhs, rhs) := s_e.eq? | throwError "unreachable"
  let (cancels_lhs, cancels_rhs) :=
    (← getCancelables lhs false rev, ← getCancelables rhs true rev)
  let e' ← (do
    -- First pass.
    let e₁ ← rotateIsosCoreAux p_e a rev true cancels_lhs
    -- If we need to also move things from the rhs to the lhs, we first take the symmetric of the
    -- result of the first pass, reassociate in the opposite direction, and then do a second pass
    if b != 0 then
      let symm ← mkAppM ``Eq.symm #[e₁]
      let s_e ←
        if rev then simpEq (fun e => simpOnlyNames
            [``Iso.trans_symm, ``Iso.trans_assoc, ``Category.assoc]
          e (config := { decide := false })) (← inferType symm) symm
        else simpEq (fun e => simpOnlyNames
            [``Iso.trans_symm, ``trans_assoc_rev, ``comp_assoc_rev]
          e (config := { decide := false })) (← inferType symm) symm
      return ← mkAppM ``Eq.symm #[← rotateIsosCoreAux s_e.2 b (not rev) (a == 0) cancels_rhs]
    else return e₁)
  let final_expr ← simpEq (fun e => simpOnlyNames
      [``Iso.trans_symm, ``Iso.trans_assoc, ``Iso.symm_symm_eq, ``IsIso.inv_inv,
        ``Functor.mapIso_symm, ``Category.assoc, ``Category.id_comp, ``Category.comp_id,
        ``Iso.trans_refl, ``Iso.refl_trans]
      e (config := { decide := false })) (← inferType e') e'
  return (← mkLambdaFVars #[g] final_expr.2 (binderInfoForMVars := .default), final_expr.1)

/-- A variant of `rotateIsosCore` in which we return an expression of the form `e ↔ e'`
(see the `rotateIsosCore` docstring for interpretation of `e` and `e''`) which is useful in case
we want to use the tactic at a goal and need the reverse direction to close the goal. -/
def rotateIsosCoreIff (e : Expr) (a b : ℕ) (rev : Bool) : MetaM (Expr × Expr) := do
  -- The idea is to apply `rotateIsosCore` twice: once with the given expression, and then
  -- apply it again to the result, with `a` and `b` swapped, as well as the truth value of `rev`.
  -- This yields an expression equivalent to the original up to some simp lemmas.
  let (mp, e') ← rotateIsosCore e a b rev
  let (mp', e'') ← rotateIsosCore e' b a !rev
  -- We build a proof that the target of `e''` is equivalent to `e`.
  let some r ← Simp.Result.ofTrue <| ← simpOnlyNames
      [``Iso.trans_symm, ``Iso.trans_assoc, ``Iso.symm_symm_eq, ``IsIso.inv_inv,
        ``Functor.mapIso_symm, ``Category.assoc, ``Category.id_comp, ``Category.comp_id,
        ``Iso.trans_refl, ``Iso.refl_trans]
      (mkIff e e'') (config := { decide := false }) | throwError "Could not prove that {e} ↔ {e''}"
  let g ← mkFreshExprMVar e'
  let m₀ ← mkAppM' mp' #[g] -- of type e''
  return (← mkAppM ``Iff.intro #[mp, ← mkLambdaFVars #[g] <| ← mkAppM ``Iff.mpr #[r, m₀]], e')

/-- Wrapper to apply `RotateIsosCore` for expressions in binders. -/
def rotateIsosForallTelescope (e : Expr) (a b : ℕ) (rev : Bool) : MetaM Expr := do
  mapForallTelescope (fun e => do mkAppM' (← rotateIsosCore (← inferType e) a b rev).1 #[e]) e

/-- Wrapper to apply `RotateIsosCore` for expressions in binders. -/
def rotateIsosForallTelescopeIff (e : Expr) (a b : ℕ) (rev : Bool) : MetaM Expr := do
  mapForallTelescope (fun e => do return (← rotateIsosCoreIff (← inferType e) a b rev).1) e

open Term in
/-- A term elaborator to produce the result of `rotate_isos` at a term.. -/
elab "rotate_isos% " p:patternIgnore("←" <|> "<-")? ppSpace n:num ppSpace m:num ppSpace t:term :
    term => do rotateIsosForallTelescope (← elabTerm t none) n.getNat m.getNat p.isSome

open Term in
/-- A term elaborator to produce the iff statement betwen the given term and the result of
running `rotate_isos` at that term. -/
elab "rotate_isos_iff% " p:patternIgnore("←" <|> "<-")? ppSpace n:num ppSpace m:num ppSpace t:term :
    term => do rotateIsosForallTelescopeIff (← elabTerm t none) n.getNat m.getNat p.isSome

/-- Wrapper to run `rotateIsosForallTelescope` at an hypothesis in the local context. -/
def rotateIsosAtHyp (a b : ℕ) (rev : Bool) (h : FVarId) (g : MVarId) :
    TacticM MVarId := do
  let d ← h.getDecl
  let new_h ← rotateIsosForallTelescope (← instantiateMVars <| .fvar h) a b rev
  let g ← g.clear h
  let (_, g) ← g.note d.userName new_h
  return g

/-- Wrapper to run `rotateIsosForallTelescope` at the current goal. -/
def rotateIsosAtGoal (a b : ℕ) (rev : Bool) (g : MVarId) : TacticM MVarId := withMainContext do
  let gty ← whnfR <| ← instantiateMVars <| ← g.getType
  let forall_iff ← rotateIsosForallTelescopeIff (.mvar g) a b rev
  let target_type ← forallTelescope (← inferType forall_iff)
    (fun xs t => do mkForallFVars xs t.appArg!)
  let (args, _, _) ← forallMetaTelescope <| gty
  -- g' is for the new goal
  let g' ← mkFreshExprSyntheticOpaqueMVar (target_type) (← g.getTag)
  let e₂ ← mkLambdaFVars args <|
    ← mkAppM'
      (← mkAppM ``Iff.mpr #[← mkAppOptM' forall_iff (args.map pure)])
      #[← mkAppOptM' g' (args.map pure)]
  -- The metavariable `g` might be a syntheticOpaque MVar so IsDefeq can’t assign it.
  let _ ← isDefEq (← g.getType) (← instantiateMVars <| ← inferType e₂)
  let _ ← isDefEq (.mvar g) (← instantiateMVars e₂)
  g.assign e₂
  return (← instantiateMVars g').mvarId!

/--
# The `rotate_isos` tactic

Given a term of the form `e : α₁ ≫ ⋯ ≫ αₖ = β₁ ≫ ⋯ ≫ βₗ`, or of the form
`e : α₁ ≪≫ ⋯ ≪≫ αₖ = β₁ ≪≫ ⋯ ≪≫ βₗ` (possibly not fully right-associated, or under ∀ binders),
the `rotate_isos` tactic moves specified numbers
of isomorphisms from the left-hand side of the equality to the right-hand side.
Depending on a flag given to the tactic, the isomorphisms are moved from the lhs starting from
the leftmost morphism or from the rightmost morphism.

Note that the tactic will first simplify the given expression according to some basic category
theory rules, such as `Functor.map_comp` and `Iso.trans_hom`.
In particular, within the expression `F.map (f ≪≫ g).hom`, the first morphism the tactic recognizes
will be `F.map f.hom`. So beware that in the event that a composition `f ≫ g` is an isomorphisms but
neither `f` nor `g` is, the tactic might not count `f ≫ g` as an isomorphisms.

Valid syntaxes are
* `rotate_isos n m` : move the first `n` (starting from the left) morphism from the lhs to the
  rhs of the current goal, and move the last `m` morphisms from the rhs to the rhs.
  The resulting expression is ther reasociated from left to right, composition of a morphism with
  its inverse are removed, and composition with idenitiy are removed.
* `rotate_isos ← n m`: same as above, but instead moves the last `n` morphism of the lhs to the rhs
  and the first `m` morphism of the rhs to the lhs.
* `rotate_isos n m at h₁,⋯,hₙ` or `rotate_isos ← n m at h₁, …, hₙ`: replace local hypotheses
  `h₁, …, hₙ` with the result of running `rotate_isos` at their expressions.
* `rotate_isos n m using t` or `rotate_isos ← n m using t`: runs `rotate_isos` at the goal, and then
  tries to close it by matching it with the term obtained from `t` by left-associating compositions
  removing compositions with identities, and simplifying compositions of a morphism with its
  inverse. A particular kind is `rotate_isos n m using rfl`, which tries to solve the goal by
  simplifying the resulting expression in the way described above.
  Note that using a `using` clause will turn `rotate_isos` into a finishing tactic, and will
  throw an error if it fails to close the current goal.
-/
syntax (name := rotate_isos) "rotate_isos "
    ("←" <|> "<-")? ppSpace num ppSpace num ppSpace ("using " term)? (location)? : tactic

elab_rules : tactic |
    `(tactic| rotate_isos $[$rev]? $a:num $b:num $[using $use]? $[$loc]?) => do
  withLocation (expandOptLocation (Lean.mkOptionalNode loc))
    (atLocal := fun h => do
      if use.isSome then throwUnsupportedSyntax
      replaceMainGoal [← rotateIsosAtHyp a.getNat b.getNat rev.isSome h <| ← getMainGoal])
    (atTarget := withMainContext do
      replaceMainGoal [← rotateIsosAtGoal a.getNat b.getNat rev.isSome <| ← getMainGoal]
      if let some t := use then
        -- Needed to make the unusedSimpa linter happy with "using rfl"
        if t.raw.matchesIdent `rfl then
          evalTactic <| ← `(tactic|
            simp only [Iso.trans_symm, Iso.trans_assoc, Iso.symm_symm_eq, IsIso.inv_inv,
              Functor.mapIso_symm, Category.assoc, Category.id_comp, Category.comp_id,
              Iso.trans_refl, Iso.refl_trans]; done)
        else
          evalTactic <| ← `(tactic|
            simpa only [Iso.trans_symm, Iso.trans_assoc, Iso.symm_symm_eq, IsIso.inv_inv,
              Functor.mapIso_symm, Category.assoc, Category.id_comp, Category.comp_id,
              Iso.trans_refl, Iso.refl_trans] using $t))
    (failed := fun _ => throwError "rotate_isos failed")

end Tactic.CategoryTheory.RotateIsos
