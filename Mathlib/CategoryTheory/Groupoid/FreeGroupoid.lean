/-
Copyright (c) 2022 Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli

! This file was ported from Lean 3 source module category_theory.groupoid.free_groupoid
! leanprover-community/mathlib commit 706d88f2b8fdfeb0b22796433d7a6c1a010af9f2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Category.Basic
import Mathbin.CategoryTheory.Functor.Basic
import Mathbin.CategoryTheory.Groupoid
import Mathbin.Tactic.NthRewrite.Default
import Mathbin.CategoryTheory.PathCategory
import Mathbin.CategoryTheory.Quotient
import Mathbin.Combinatorics.Quiver.Symmetric

/-!
# Free groupoid on a quiver

This file defines the free groupoid on a quiver, the lifting of a prefunctor to its unique
extension as a functor from the free groupoid, and proves uniqueness of this extension.

## Main results

Given the type `V` and a quiver instance on `V`:

- `free_groupoid V`: a type synonym for `V`.
- `free_groupoid_groupoid`: the `groupoid` instance on `free_groupoid V`.
- `lift`: the lifting of a prefunctor from `V` to `V'` where `V'` is a groupoid, to a functor.
  `free_groupoid V ⥤ V'`.
- `lift_spec` and `lift_unique`: the proofs that, respectively, `lift` indeed is a lifting
  and is the unique one.

## Implementation notes

The free groupoid is first defined by symmetrifying the quiver, taking the induced path category
and finally quotienting by the reducibility relation.

-/


open Set Classical Function

attribute [local instance] prop_decidable

namespace CategoryTheory

namespace Groupoid

namespace Free

universe u v u' v' u'' v''

variable {V : Type u} [Quiver.{v + 1} V]

/-- Shorthand for the "forward" arrow corresponding to `f` in `paths $ symmetrify V` -/
abbrev Quiver.Hom.toPosPath {X Y : V} (f : X ⟶ Y) :
    (CategoryTheory.Paths.categoryPaths <| Quiver.Symmetrify V).Hom X Y :=
  f.toPos.toPath
#align category_theory.groupoid.free.quiver.hom.to_pos_path CategoryTheory.Groupoid.Free.Quiver.Hom.toPosPath

/-- Shorthand for the "forward" arrow corresponding to `f` in `paths $ symmetrify V` -/
abbrev Quiver.Hom.toNegPath {X Y : V} (f : X ⟶ Y) :
    (CategoryTheory.Paths.categoryPaths <| Quiver.Symmetrify V).Hom Y X :=
  f.toNeg.toPath
#align category_theory.groupoid.free.quiver.hom.to_neg_path CategoryTheory.Groupoid.Free.Quiver.Hom.toNegPath

/-- The "reduction" relation -/
inductive redStep : HomRel (Paths (Quiver.Symmetrify V))
  |
  step (X Z : Quiver.Symmetrify V) (f : X ⟶ Z) :
    red_step (𝟙 X) (f.toPath ≫ (Quiver.reverse f).toPath)
#align category_theory.groupoid.free.red_step CategoryTheory.Groupoid.Free.redStep

/-- The underlying vertices of the free groupoid -/
def CategoryTheory.FreeGroupoid (V) [Q : Quiver V] :=
  Quotient (@redStep V Q)
#align category_theory.free_groupoid CategoryTheory.FreeGroupoid

instance {V} [Q : Quiver V] [h : Nonempty V] : Nonempty (FreeGroupoid V) :=
  ⟨⟨h.some⟩⟩

theorem congr_reverse {X Y : Paths <| Quiver.Symmetrify V} (p q : X ⟶ Y) :
    Quotient.CompClosure redStep p q → Quotient.CompClosure redStep p.reverse q.reverse :=
  by
  rintro ⟨XW, pp, qq, WY, _, Z, f⟩
  have :
    quotient.comp_closure red_step (WY.reverse ≫ 𝟙 _ ≫ XW.reverse)
      (WY.reverse ≫ (f.to_path ≫ (Quiver.reverse f).toPath) ≫ XW.reverse) :=
    by
    apply quotient.comp_closure.intro
    apply red_step.step
  simpa only [category_struct.comp, category_struct.id, Quiver.Path.reverse, Quiver.Path.nil_comp,
    Quiver.Path.reverse_comp, Quiver.reverse_reverse, Quiver.Path.reverse_toPath,
    Quiver.Path.comp_assoc] using this
#align category_theory.groupoid.free.congr_reverse CategoryTheory.Groupoid.Free.congr_reverse

theorem congr_comp_reverse {X Y : Paths <| Quiver.Symmetrify V} (p : X ⟶ Y) :
    Quot.mk (@Quotient.CompClosure _ _ redStep _ _) (p ≫ p.reverse) =
      Quot.mk (@Quotient.CompClosure _ _ redStep _ _) (𝟙 X) :=
  by
  apply Quot.EqvGen_sound
  induction' p with _ _ q f ih
  · apply EqvGen.refl
  · simp only [Quiver.Path.reverse]
    fapply EqvGen.trans
    · exact q ≫ q.reverse
    · apply EqvGen.symm
      apply EqvGen.rel
      have :
        quotient.comp_closure red_step (q ≫ 𝟙 _ ≫ q.reverse)
          (q ≫ (f.to_path ≫ (Quiver.reverse f).toPath) ≫ q.reverse) :=
        by
        apply quotient.comp_closure.intro
        apply red_step.step
      have that : q.cons f = q.comp f.to_path := by rfl
      rw [that]
      simp only [category.assoc, category.id_comp] at this⊢
      simp only [category_struct.comp, Quiver.Path.comp_assoc] at this⊢
      exact this
    · exact ih
#align category_theory.groupoid.free.congr_comp_reverse CategoryTheory.Groupoid.Free.congr_comp_reverse

theorem congr_reverse_comp {X Y : Paths <| Quiver.Symmetrify V} (p : X ⟶ Y) :
    Quot.mk (@Quotient.CompClosure _ _ redStep _ _) (p.reverse ≫ p) =
      Quot.mk (@Quotient.CompClosure _ _ redStep _ _) (𝟙 Y) :=
  by
  nth_rw 2 [← Quiver.Path.reverse_reverse p]
  apply congr_comp_reverse
#align category_theory.groupoid.free.congr_reverse_comp CategoryTheory.Groupoid.Free.congr_reverse_comp

instance : Category (FreeGroupoid V) :=
  Quotient.category redStep

/-- The inverse of an arrow in the free groupoid -/
def quotInv {X Y : FreeGroupoid V} (f : X ⟶ Y) : Y ⟶ X :=
  Quot.liftOn f (fun pp => Quot.mk _ <| pp.reverse) fun pp qq con =>
    Quot.sound <| congr_reverse pp qq Con
#align category_theory.groupoid.free.quot_inv CategoryTheory.Groupoid.Free.quotInv

instance : Groupoid (FreeGroupoid V)
    where
  inv X Y f := quotInv f
  inv_comp' X Y p := Quot.inductionOn p fun pp => congr_reverse_comp pp
  comp_inv' X Y p := Quot.inductionOn p fun pp => congr_comp_reverse pp

/-- The inclusion of the quiver on `V` to the underlying quiver on `free_groupoid V`-/
def of (V) [Quiver V] : V ⥤q FreeGroupoid V
    where
  obj X := ⟨X⟩
  map X Y f := Quot.mk _ f.toPosPath
#align category_theory.groupoid.free.of CategoryTheory.Groupoid.Free.of

theorem of_eq :
    of V =
      (Quiver.Symmetrify.of ⋙q Paths.of).comp (Quotient.functor <| @redStep V _).toPrefunctor :=
  by
  apply Prefunctor.ext; rotate_left
  · rintro X
    rfl
  · rintro X Y f
    rfl
#align category_theory.groupoid.free.of_eq CategoryTheory.Groupoid.Free.of_eq

section UniversalProperty

variable {V' : Type u'} [Groupoid V'] (φ : V ⥤q V')

/-- The lift of a prefunctor to a groupoid, to a functor from `free_groupoid V` -/
def lift (φ : V ⥤q V') : FreeGroupoid V ⥤ V' :=
  Quotient.lift _ (Paths.lift <| Quiver.Symmetrify.lift φ)
    (by
      rintro _ _ _ _ ⟨X, Y, f⟩
      simp only [Quiver.Symmetrify.lift_reverse, paths.lift_nil, Quiver.Path.comp_nil,
        paths.lift_cons, paths.lift_to_path]
      symm
      apply groupoid.comp_inv)
#align category_theory.groupoid.free.lift CategoryTheory.Groupoid.Free.lift

theorem lift_spec (φ : V ⥤q V') : of V ⋙q (lift φ).toPrefunctor = φ :=
  by
  rw [of_eq, Prefunctor.comp_assoc, Prefunctor.comp_assoc, functor.to_prefunctor_comp]
  dsimp [lift]
  rw [quotient.lift_spec, paths.lift_spec, Quiver.Symmetrify.lift_spec]
#align category_theory.groupoid.free.lift_spec CategoryTheory.Groupoid.Free.lift_spec

theorem lift_unique (φ : V ⥤q V') (Φ : FreeGroupoid V ⥤ V') (hΦ : of V ⋙q Φ.toPrefunctor = φ) :
    Φ = lift φ := by
  apply quotient.lift_unique
  apply paths.lift_unique
  fapply @Quiver.Symmetrify.lift_unique _ _ _ _ _ _ _ _ _
  · rw [← functor.to_prefunctor_comp]
    exact hΦ
  · constructor
    rintro X Y f
    simp only [← functor.to_prefunctor_comp, Prefunctor.comp_map, paths.of_map, inv_eq_inv]
    change
      Φ.map (inv ((quotient.functor red_step).toPrefunctor.map f.to_path)) =
        inv (Φ.map ((quotient.functor red_step).toPrefunctor.map f.to_path))
    have := functor.map_inv Φ ((quotient.functor red_step).toPrefunctor.map f.to_path)
    convert this <;> simp only [inv_eq_inv]
#align category_theory.groupoid.free.lift_unique CategoryTheory.Groupoid.Free.lift_unique

end UniversalProperty

section Functoriality

variable {V' : Type u'} [Quiver.{v' + 1} V'] {V'' : Type u''} [Quiver.{v'' + 1} V'']

/-- The functor of free groupoid induced by a prefunctor of quivers -/
def CategoryTheory.freeGroupoidFunctor (φ : V ⥤q V') : FreeGroupoid V ⥤ FreeGroupoid V' :=
  lift (φ ⋙q of V')
#align category_theory.free_groupoid_functor CategoryTheory.freeGroupoidFunctor

theorem freeGroupoidFunctor_id :
    freeGroupoidFunctor (Prefunctor.id V) = Functor.id (FreeGroupoid V) :=
  by
  dsimp only [free_groupoid_functor]; symm
  apply lift_unique; rfl
#align category_theory.groupoid.free.free_groupoid_functor_id CategoryTheory.Groupoid.Free.freeGroupoidFunctor_id

theorem freeGroupoidFunctor_comp (φ : V ⥤q V') (φ' : V' ⥤q V'') :
    freeGroupoidFunctor (φ ⋙q φ') = freeGroupoidFunctor φ ⋙ freeGroupoidFunctor φ' :=
  by
  dsimp only [free_groupoid_functor]; symm
  apply lift_unique; rfl
#align category_theory.groupoid.free.free_groupoid_functor_comp CategoryTheory.Groupoid.Free.freeGroupoidFunctor_comp

end Functoriality

end Free

end Groupoid

end CategoryTheory

