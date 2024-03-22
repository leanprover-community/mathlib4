/-
Copyright (c) 2022 Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Groupoid
import Mathlib.Tactic.NthRewrite
import Mathlib.CategoryTheory.PathCategory
import Mathlib.CategoryTheory.Quotient
import Mathlib.Combinatorics.Quiver.Symmetric

#align_import category_theory.groupoid.free_groupoid from "leanprover-community/mathlib"@"706d88f2b8fdfeb0b22796433d7a6c1a010af9f2"

/-!
# Free groupoid on a quiver

This file defines the free groupoid on a quiver, the lifting of a prefunctor to its unique
extension as a functor from the free groupoid, and proves uniqueness of this extension.

## Main results

Given the type `V` and a quiver instance on `V`:

- `FreeGroupoid V`: a type synonym for `V`.
- `FreeGroupoid.instGroupoid`: the `Groupoid` instance on `FreeGroupoid V`.
- `lift`: the lifting of a prefunctor from `V` to `V'` where `V'` is a groupoid, to a functor.
  `FreeGroupoid V ⥤ V'`.
- `lift_spec` and `lift_unique`: the proofs that, respectively, `lift` indeed is a lifting
  and is the unique one.

## Implementation notes

The free groupoid is first defined by symmetrifying the quiver, taking the induced path category
and finally quotienting by the reducibility relation.

-/


open Set Classical Function

attribute [local instance] propDecidable

namespace CategoryTheory

namespace Groupoid

namespace Free

universe u v u' v' u'' v''

variable {V : Type u} [Quiver.{v + 1} V]

/-- Shorthand for the "forward" arrow corresponding to `f` in `paths <| symmetrify V` -/
abbrev _root_.Quiver.Hom.toPosPath {X Y : V} (f : X ⟶ Y) :
    (CategoryTheory.Paths.categoryPaths <| Quiver.Symmetrify V).Hom X Y :=
  f.toPos.toPath
#align category_theory.groupoid.free.quiver.hom.to_pos_path Quiver.Hom.toPosPath

/-- Shorthand for the "forward" arrow corresponding to `f` in `paths <| symmetrify V` -/
abbrev _root_.Quiver.Hom.toNegPath {X Y : V} (f : X ⟶ Y) :
    (CategoryTheory.Paths.categoryPaths <| Quiver.Symmetrify V).Hom Y X :=
  f.toNeg.toPath
#align category_theory.groupoid.free.quiver.hom.to_neg_path Quiver.Hom.toNegPath

/-- The "reduction" relation -/
inductive redStep : HomRel (Paths (Quiver.Symmetrify V))
  | step (X Z : Quiver.Symmetrify V) (f : X ⟶ Z) :
    redStep (𝟙 (Paths.of.obj X)) (f.toPath ≫ (Quiver.reverse f).toPath)
#align category_theory.groupoid.free.red_step CategoryTheory.Groupoid.Free.redStep

/-- The underlying vertices of the free groupoid -/
def _root_.CategoryTheory.FreeGroupoid (V) [Q : Quiver V] :=
  Quotient (@redStep V Q)
#align category_theory.free_groupoid CategoryTheory.FreeGroupoid

instance {V} [Quiver V] [Nonempty V] : Nonempty (FreeGroupoid V) := by
  inhabit V; exact ⟨⟨@default V _⟩⟩

theorem congr_reverse {X Y : Paths <| Quiver.Symmetrify V} (p q : X ⟶ Y) :
    Quotient.CompClosure redStep p q → Quotient.CompClosure redStep p.reverse q.reverse := by
  rintro ⟨XW, pp, qq, WY, _, Z, f⟩
  have : Quotient.CompClosure redStep (WY.reverse ≫ 𝟙 _ ≫ XW.reverse)
      (WY.reverse ≫ (f.toPath ≫ (Quiver.reverse f).toPath) ≫ XW.reverse) := by
    constructor
    constructor
  simpa only [CategoryStruct.comp, CategoryStruct.id, Quiver.Path.reverse, Quiver.Path.nil_comp,
    Quiver.Path.reverse_comp, Quiver.reverse_reverse, Quiver.Path.reverse_toPath,
    Quiver.Path.comp_assoc] using this
#align category_theory.groupoid.free.congr_reverse CategoryTheory.Groupoid.Free.congr_reverse

theorem congr_comp_reverse {X Y : Paths <| Quiver.Symmetrify V} (p : X ⟶ Y) :
    Quot.mk (@Quotient.CompClosure _ _ redStep _ _) (p ≫ p.reverse) =
      Quot.mk (@Quotient.CompClosure _ _ redStep _ _) (𝟙 X) := by
  apply Quot.EqvGen_sound
  induction' p with a b q f ih
  · apply EqvGen.refl
  · simp only [Quiver.Path.reverse]
    fapply EqvGen.trans
    -- Porting note: `Quiver.Path.*` and `Quiver.Hom.*` notation not working
    · exact q ≫ Quiver.Path.reverse q
    · apply EqvGen.symm
      apply EqvGen.rel
      have : Quotient.CompClosure redStep (q ≫ 𝟙 _ ≫ Quiver.Path.reverse q)
          (q ≫ (Quiver.Hom.toPath f ≫ Quiver.Hom.toPath (Quiver.reverse f)) ≫
            Quiver.Path.reverse q) := by
        apply Quotient.CompClosure.intro
        apply redStep.step
      simp only [Category.assoc, Category.id_comp] at this ⊢
      -- Porting note: `simp` cannot see how `Quiver.Path.comp_assoc` is relevant, so change to
      -- category notation
      change Quotient.CompClosure redStep (q ≫ Quiver.Path.reverse q)
        (Quiver.Path.cons q f ≫ (Quiver.Hom.toPath (Quiver.reverse f)) ≫ (Quiver.Path.reverse q))
      simp only [← Category.assoc] at this ⊢
      exact this
    · exact ih
#align category_theory.groupoid.free.congr_comp_reverse CategoryTheory.Groupoid.Free.congr_comp_reverse

theorem congr_reverse_comp {X Y : Paths <| Quiver.Symmetrify V} (p : X ⟶ Y) :
    Quot.mk (@Quotient.CompClosure _ _ redStep _ _) (p.reverse ≫ p) =
      Quot.mk (@Quotient.CompClosure _ _ redStep _ _) (𝟙 Y) := by
  nth_rw 2 [← Quiver.Path.reverse_reverse p]
  apply congr_comp_reverse
#align category_theory.groupoid.free.congr_reverse_comp CategoryTheory.Groupoid.Free.congr_reverse_comp

instance : Category (FreeGroupoid V) :=
  Quotient.category redStep

/-- The inverse of an arrow in the free groupoid -/
def quotInv {X Y : FreeGroupoid V} (f : X ⟶ Y) : Y ⟶ X :=
  Quot.liftOn f (fun pp => Quot.mk _ <| pp.reverse) fun pp qq con =>
    Quot.sound <| congr_reverse pp qq con
#align category_theory.groupoid.free.quot_inv CategoryTheory.Groupoid.Free.quotInv

instance _root_.CategoryTheory.FreeGroupoid.instGroupoid : Groupoid (FreeGroupoid V) where
  inv := quotInv
  inv_comp p := Quot.inductionOn p fun pp => congr_reverse_comp pp
  comp_inv p := Quot.inductionOn p fun pp => congr_comp_reverse pp
#align category_theory.groupoid.free.category_theory.free_groupoid.category_theory.groupoid CategoryTheory.FreeGroupoid.instGroupoid

/-- The inclusion of the quiver on `V` to the underlying quiver on `FreeGroupoid V`-/
def of (V) [Quiver V] : V ⥤q FreeGroupoid V where
  obj X := ⟨X⟩
  map f := Quot.mk _ f.toPosPath
#align category_theory.groupoid.free.of CategoryTheory.Groupoid.Free.of

theorem of_eq :
    of V = (Quiver.Symmetrify.of ⋙q Paths.of).comp
      (Quotient.functor <| @redStep V _).toPrefunctor := rfl
#align category_theory.groupoid.free.of_eq CategoryTheory.Groupoid.Free.of_eq

section UniversalProperty

variable {V' : Type u'} [Groupoid V'] (φ : V ⥤q V')

/-- The lift of a prefunctor to a groupoid, to a functor from `FreeGroupoid V` -/
def lift (φ : V ⥤q V') : FreeGroupoid V ⥤ V' :=
  Quotient.lift _ (Paths.lift <| Quiver.Symmetrify.lift φ) <| by
    rintro _ _ _ _ ⟨X, Y, f⟩
    -- Porting note: `simp` does not work, so manually `rewrite`
    erw [Paths.lift_nil, Paths.lift_cons, Quiver.Path.comp_nil, Paths.lift_toPath,
      Quiver.Symmetrify.lift_reverse]
    symm
    apply Groupoid.comp_inv
#align category_theory.groupoid.free.lift CategoryTheory.Groupoid.Free.lift

theorem lift_spec (φ : V ⥤q V') : of V ⋙q (lift φ).toPrefunctor = φ := by
  rw [of_eq, Prefunctor.comp_assoc, Prefunctor.comp_assoc, Functor.toPrefunctor_comp]
  dsimp [lift]
  rw [Quotient.lift_spec, Paths.lift_spec, Quiver.Symmetrify.lift_spec]
#align category_theory.groupoid.free.lift_spec CategoryTheory.Groupoid.Free.lift_spec

theorem lift_unique (φ : V ⥤q V') (Φ : FreeGroupoid V ⥤ V') (hΦ : of V ⋙q Φ.toPrefunctor = φ) :
    Φ = lift φ := by
  apply Quotient.lift_unique
  apply Paths.lift_unique
  fapply @Quiver.Symmetrify.lift_unique _ _ _ _ _ _ _ _ _
  · rw [← Functor.toPrefunctor_comp]
    exact hΦ
  · rintro X Y f
    simp only [← Functor.toPrefunctor_comp, Prefunctor.comp_map, Paths.of_map, inv_eq_inv]
    change Φ.map (inv ((Quotient.functor redStep).toPrefunctor.map f.toPath)) =
      inv (Φ.map ((Quotient.functor redStep).toPrefunctor.map f.toPath))
    have := Functor.map_inv Φ ((Quotient.functor redStep).toPrefunctor.map f.toPath)
    convert this <;> simp only [inv_eq_inv]
#align category_theory.groupoid.free.lift_unique CategoryTheory.Groupoid.Free.lift_unique

end UniversalProperty

section Functoriality

variable {V' : Type u'} [Quiver.{v' + 1} V'] {V'' : Type u''} [Quiver.{v'' + 1} V'']

/-- The functor of free groupoid induced by a prefunctor of quivers -/
def _root_.CategoryTheory.freeGroupoidFunctor (φ : V ⥤q V') : FreeGroupoid V ⥤ FreeGroupoid V' :=
  lift (φ ⋙q of V')
#align category_theory.free_groupoid_functor CategoryTheory.freeGroupoidFunctor

theorem freeGroupoidFunctor_id :
    freeGroupoidFunctor (Prefunctor.id V) = Functor.id (FreeGroupoid V) := by
  dsimp only [freeGroupoidFunctor]; symm
  apply lift_unique; rfl
#align category_theory.groupoid.free.free_groupoid_functor_id CategoryTheory.Groupoid.Free.freeGroupoidFunctor_id

theorem freeGroupoidFunctor_comp (φ : V ⥤q V') (φ' : V' ⥤q V'') :
    freeGroupoidFunctor (φ ⋙q φ') = freeGroupoidFunctor φ ⋙ freeGroupoidFunctor φ' := by
  dsimp only [freeGroupoidFunctor]; symm
  apply lift_unique; rfl
#align category_theory.groupoid.free.free_groupoid_functor_comp CategoryTheory.Groupoid.Free.freeGroupoidFunctor_comp

end Functoriality

end Free

end Groupoid

end CategoryTheory
