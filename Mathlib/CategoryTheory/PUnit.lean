/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta

! This file was ported from Lean 3 source module category_theory.punit
! leanprover-community/mathlib commit 2738d2ca56cbc63be80c3bd48e9ed90ad94e947d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.CategoryTheory.Functor.Const
import Mathlib.CategoryTheory.DiscreteCategory

/-!
# The category `Discrete PUnit`

We define `star : C ⥤ Discrete PUnit` sending everything to `PUnit.star`,
show that any two functors to `Discrete PUnit` are naturally isomorphic,
and construct the equivalence `(Discrete PUnit ⥤ C) ≌ C`.
-/


universe v u

-- morphism levels before object levels. See note [CategoryTheory universes].
namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

namespace Functor

/-- The constant functor sending everything to `PUnit.star`. -/
@[simps!]
def star : C ⥤ Discrete PUnit :=
  (Functor.const _).obj ⟨⟨⟩⟩
#align category_theory.functor.star CategoryTheory.Functor.star
-- Porting note: simp can simplify this
attribute [nolint simpNF] star_map_down_down
variable {C}

/-- Any two functors to `Discrete PUnit` are isomorphic. -/
@[simps!]
def pUnitExt (F G : C ⥤ Discrete PUnit) : F ≅ G :=
  NatIso.ofComponents fun X => eqToIso (by simp only [eq_iff_true_of_subsingleton])
#align category_theory.functor.punit_ext CategoryTheory.Functor.pUnitExt
-- Porting note: simp does indeed fire for these despite the linter warning
attribute [nolint simpNF] pUnitExt_hom_app_down_down pUnitExt_inv_app_down_down

/-- Any two functors to `Discrete PUnit` are *equal*.
You probably want to use `pUnitExt` instead of this. -/
theorem pUnit_ext' (F G : C ⥤ Discrete PUnit) : F = G :=
  Functor.ext fun X => by simp only [eq_iff_true_of_subsingleton]
#align category_theory.functor.punit_ext' CategoryTheory.Functor.pUnit_ext'

/-- The functor from `Discrete PUnit` sending everything to the given object. -/
abbrev fromPUnit (X : C) : Discrete PUnit.{v + 1} ⥤ C :=
  (Functor.const _).obj X
#align category_theory.functor.from_punit CategoryTheory.Functor.fromPUnit

/-- Functors from `Discrete PUnit` are equivalent to the category itself. -/
@[simps]
def equiv : Discrete PUnit ⥤ C ≌ C where
  functor :=
    { obj := fun F => F.obj ⟨⟨⟩⟩
      map := fun θ => θ.app ⟨⟨⟩⟩ }
  inverse := Functor.const _
  unitIso := NatIso.ofComponents fun X => Discrete.natIso fun i => Iso.refl _
  counitIso := NatIso.ofComponents Iso.refl
#align category_theory.functor.equiv CategoryTheory.Functor.equiv

end Functor

/-- A category being equivalent to `PUnit` is equivalent to it having a unique morphism between
  any two objects. (In fact, such a category is also a groupoid;
  see `CategoryTheory.Groupoid.ofHomUnique`) -/
theorem equiv_pUnit_iff_unique :
    Nonempty (C ≌ Discrete PUnit) ↔ Nonempty C ∧ ∀ x y : C, Nonempty <| Unique (x ⟶ y) := by
  constructor
  · rintro ⟨h⟩
    refine' ⟨⟨h.inverse.obj ⟨⟨⟩⟩⟩, fun x y => Nonempty.intro _⟩
    let f : x ⟶  y := by
      have hx : x ⟶ h.inverse.obj ⟨⟨⟩⟩ := by convert h.unit.app x
      have hy : h.inverse.obj ⟨⟨⟩⟩ ⟶ y := by convert h.unitInv.app y
      exact hx ≫ hy
    suffices sub : Subsingleton (x ⟶  y) from uniqueOfSubsingleton f
    have : ∀ z, z = h.unit.app x ≫ (h.functor ⋙ h.inverse).map z ≫ h.unitInv.app y := by
      intro z
      simp [congrArg (· ≫ h.unitInv.app y) (h.unit.naturality z)]
    apply Subsingleton.intro
    intro a b
    rw [this a, this b]
    simp only [Functor.comp_map]
    congr 3
    apply ULift.ext
    simp
  · rintro ⟨⟨p⟩, h⟩
    haveI := fun x y => (h x y).some
    refine'
      Nonempty.intro
        (CategoryTheory.Equivalence.mk ((Functor.const _).obj ⟨⟨⟩⟩)
          ((@Functor.const <| Discrete PUnit).obj p) ?_ (by apply Functor.pUnitExt))
    exact
      NatIso.ofComponents fun _ =>
        { hom := default
          inv := default }
#align category_theory.equiv_punit_iff_unique CategoryTheory.equiv_pUnit_iff_unique

end CategoryTheory
