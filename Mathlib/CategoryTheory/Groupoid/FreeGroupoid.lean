/-
Copyright (c) 2022 Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli
-/
module

public import Mathlib.CategoryTheory.PathCategory.Basic
import Batteries.Tactic.Init
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Util.CompileInductive

/-!
# Free groupoid on a quiver

This file defines the free groupoid on a quiver, the lifting of a prefunctor to its unique
extension as a functor from the free groupoid, and proves uniqueness of this extension.

## Main results

Given the type `V` and a quiver instance on `V`:

- `Quiver.FreeGroupoid V`: a type synonym for `V`.
- `Quiver.FreeGroupoid.instGroupoid`: the `Groupoid` instance on `Quiver.FreeGroupoid V`.
- `lift`: the lifting of a prefunctor from `V` to `V'` where `V'` is a groupoid, to a functor.
  `Quiver.FreeGroupoid V ⥤ V'`.
- `lift_spec` and `lift_unique`: the proofs that, respectively, `lift` indeed is a lifting
  and is the unique one.

## Implementation notes

The free groupoid is first defined by symmetrifying the quiver, taking the induced path category
and finally quotienting by the reducibility relation.

-/

@[expose] public section

open Set Function

namespace Quiver

open CategoryTheory

universe u v u' v' u'' v''

variable {V : Type u} [Quiver.{v} V]

/-- Shorthand for the "forward" arrow corresponding to `f` in `paths <| symmetrify V` -/
abbrev Hom.toPosPath {X Y : V} (f : X ⟶ Y) :
    (CategoryTheory.Paths.categoryPaths <| Quiver.Symmetrify V).Hom X Y :=
  f.toPos.toPath

/-- Shorthand for the "forward" arrow corresponding to `f` in `paths <| symmetrify V` -/
abbrev Hom.toNegPath {X Y : V} (f : X ⟶ Y) :
    (CategoryTheory.Paths.categoryPaths <| Quiver.Symmetrify V).Hom Y X :=
  f.toNeg.toPath

/-- The "reduction" relation -/
inductive FreeGroupoid.redStep : HomRel (Paths (Quiver.Symmetrify V))
  | step (X Z : Quiver.Symmetrify V) (f : X ⟶ Z) :
    redStep (𝟙 ((Paths.of (Quiver.Symmetrify V)).obj X)) (f.toPath ≫ (Quiver.reverse f).toPath)

/-- The underlying vertices of the free groupoid -/
protected def FreeGroupoid (V) [Q : Quiver V] :=
  CategoryTheory.Quotient (@FreeGroupoid.redStep V Q)

namespace FreeGroupoid

open Quiver

instance {V} [Quiver V] [Nonempty V] : Nonempty (Quiver.FreeGroupoid V) := by
  inhabit V; exact ⟨⟨@default V _⟩⟩

set_option backward.isDefEq.respectTransparency false in
theorem congr_reverse {X Y : Paths <| Quiver.Symmetrify V} (p q : X ⟶ Y) :
    HomRel.CompClosure redStep p q → HomRel.CompClosure redStep p.reverse q.reverse := by
  rintro ⟨_, _, XW, _, _, WY, _, _, f⟩
  have : HomRel.CompClosure redStep (WY.reverse ≫ 𝟙 _ ≫ XW.reverse)
      (WY.reverse ≫ (f.toPath ≫ (Quiver.reverse f).toPath) ≫ XW.reverse) := by
    constructor
    constructor
  simpa only [CategoryStruct.comp, CategoryStruct.id, Quiver.Path.reverse, Quiver.Path.nil_comp,
    Quiver.Path.reverse_comp, Quiver.reverse_reverse, Quiver.Path.reverse_toPath,
    Quiver.Path.comp_assoc] using this

open Relation in
theorem congr_comp_reverse {X Y : Paths <| Quiver.Symmetrify V} (p : X ⟶ Y) :
    Quot.mk (@HomRel.CompClosure _ _ redStep _ _) (p ≫ p.reverse) =
      Quot.mk (@HomRel.CompClosure _ _ redStep _ _) (𝟙 X) := by
  apply Quot.eqvGen_sound
  induction p with
  | nil => apply EqvGen.refl
  | cons q f ih =>
    simp only [Quiver.Path.reverse]
    fapply EqvGen.trans
    -- Porting note: dot notation for `Quiver.Path.*` and `Quiver.Hom.*` not working
    · exact q ≫ Quiver.Path.reverse q
    · apply EqvGen.symm
      apply EqvGen.rel
      have : HomRel.CompClosure redStep (q ≫ 𝟙 _ ≫ Quiver.Path.reverse q)
          (q ≫ (Quiver.Hom.toPath f ≫ Quiver.Hom.toPath (Quiver.reverse f)) ≫
            Quiver.Path.reverse q) := by
        apply HomRel.CompClosure.intro
        apply redStep.step
      simp only [Category.assoc, Category.id_comp] at this ⊢
      -- Porting note: `simp` cannot see how `Quiver.Path.comp_assoc` is relevant, so change to
      -- category notation
      change HomRel.CompClosure redStep (q ≫ Quiver.Path.reverse q)
        (Quiver.Path.cons q f ≫ (Quiver.Hom.toPath (Quiver.reverse f)) ≫ (Quiver.Path.reverse q))
      simp only [← Category.assoc] at this ⊢
      exact this
    · exact ih

theorem congr_reverse_comp {X Y : Paths <| Quiver.Symmetrify V} (p : X ⟶ Y) :
    Quot.mk (@HomRel.CompClosure _ _ redStep _ _) (p.reverse ≫ p) =
      Quot.mk (@HomRel.CompClosure _ _ redStep _ _) (𝟙 Y) := by
  nth_rw 2 [← Quiver.Path.reverse_reverse p]
  apply congr_comp_reverse

instance : Category (Quiver.FreeGroupoid V) :=
  Quotient.category redStep

/-- The inverse of an arrow in the free groupoid -/
def quotInv {X Y : Quiver.FreeGroupoid V} (f : X ⟶ Y) : Y ⟶ X :=
  Quot.liftOn f (fun pp => Quot.mk _ <| pp.reverse) fun pp qq con =>
    Quot.sound <| congr_reverse pp qq con

instance instGroupoid : Groupoid (Quiver.FreeGroupoid V) where
  inv := quotInv
  inv_comp p := Quot.inductionOn p fun pp => congr_reverse_comp pp
  comp_inv p := Quot.inductionOn p fun pp => congr_comp_reverse pp

/-- The inclusion of the quiver on `V` to the underlying quiver on `FreeGroupoid V` -/
def of (V) [Quiver V] : V ⥤q Quiver.FreeGroupoid V where
  obj X := ⟨X⟩
  map f := Quot.mk _ f.toPosPath

theorem of_eq :
    of V = (Quiver.Symmetrify.of ⋙q (Paths.of (Quiver.Symmetrify V))).comp
      (Quotient.functor <| @redStep V _).toPrefunctor := rfl

section UniversalProperty

variable {V' : Type u'} [Groupoid V']

/-- The lift of a prefunctor to a groupoid, to a functor from `FreeGroupoid V` -/
def lift (φ : V ⥤q V') : Quiver.FreeGroupoid V ⥤ V' :=
  CategoryTheory.Quotient.lift _ (Paths.lift <| Quiver.Symmetrify.lift φ) <| by
    rintro _ _ _ _ ⟨X, Y, f⟩
    -- Porting note: `simp` does not work, so manually `rewrite`
    erw [Paths.lift_nil, Paths.lift_cons, Quiver.Path.comp_nil, Paths.lift_toPath,
      Quiver.Symmetrify.lift_reverse]
    symm
    apply Groupoid.comp_inv

set_option backward.isDefEq.respectTransparency false in
theorem lift_spec (φ : V ⥤q V') : of V ⋙q (lift φ).toPrefunctor = φ := by
  rw [of_eq, Prefunctor.comp_assoc, Prefunctor.comp_assoc, Functor.toPrefunctor_comp]
  dsimp [lift]
  rw [Quotient.lift_spec, Paths.lift_spec, Quiver.Symmetrify.lift_spec]

theorem lift_unique (φ : V ⥤q V') (Φ : Quiver.FreeGroupoid V ⥤ V')
    (hΦ : of V ⋙q Φ.toPrefunctor = φ) : Φ = lift φ := by
  apply Quotient.lift_unique
  apply Paths.lift_unique
  fapply @Quiver.Symmetrify.lift_unique _ _ _ _ _ _ _ _ _
  · rw [← Functor.toPrefunctor_comp]
    exact hΦ
  · rintro X Y f
    simp only [← Functor.toPrefunctor_comp, Prefunctor.comp_map, Paths.of_map]
    change Φ.map (Groupoid.inv ((Quotient.functor redStep).toPrefunctor.map f.toPath)) =
      Groupoid.inv (Φ.map ((Quotient.functor redStep).toPrefunctor.map f.toPath))
    have := Functor.map_inv Φ ((Quotient.functor redStep).toPrefunctor.map f.toPath)
    convert this <;> simp only [Groupoid.inv_eq_inv]

end UniversalProperty

end FreeGroupoid

section Functoriality

open FreeGroupoid

variable {V' : Type u'} [Quiver.{v'} V'] {V'' : Type u''} [Quiver.{v''} V'']

/-- The functor of free groupoid induced by a prefunctor of quivers -/
def freeGroupoidFunctor (φ : V ⥤q V') : Quiver.FreeGroupoid V ⥤ Quiver.FreeGroupoid V' :=
  lift (φ ⋙q of V')

theorem freeGroupoidFunctor_id :
    freeGroupoidFunctor (Prefunctor.id V) = Functor.id (Quiver.FreeGroupoid V) := by
  dsimp only [freeGroupoidFunctor]; symm
  apply lift_unique; rfl

theorem freeGroupoidFunctor_comp (φ : V ⥤q V') (φ' : V' ⥤q V'') :
    freeGroupoidFunctor (φ ⋙q φ') = freeGroupoidFunctor φ ⋙ freeGroupoidFunctor φ' := by
  dsimp only [freeGroupoidFunctor]; symm
  apply lift_unique; rfl

end Functoriality

end Quiver
