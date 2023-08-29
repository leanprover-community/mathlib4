/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import Mathlib.CategoryTheory.Functor.Const
import Mathlib.CategoryTheory.DiscreteCategory

#align_import category_theory.punit from "leanprover-community/mathlib"@"2738d2ca56cbc63be80c3bd48e9ed90ad94e947d"

/-!
# The category `Discrete PUnit`

We define `star : C ⥤ Discrete PUnit` sending everything to `PUnit.star`,
show that any two functors to `Discrete PUnit` are naturally isomorphic,
and construct the equivalence `(Discrete PUnit ⥤ C) ≌ C`.
-/


universe w v u

-- morphism levels before object levels. See note [CategoryTheory universes].
namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

namespace Functor

/-- The constant functor sending everything to `PUnit.star`. -/
@[simps!]
def star : C ⥤ Discrete PUnit.{w + 1} :=
  (Functor.const _).obj ⟨⟨⟩⟩
#align category_theory.functor.star CategoryTheory.Functor.star
-- Porting note: simp can simplify this
attribute [nolint simpNF] star_map_down_down
variable {C}

/-- Any two functors to `Discrete PUnit` are isomorphic. -/
@[simps!]
def punitExt (F G : C ⥤ Discrete PUnit.{w + 1}) : F ≅ G :=
  NatIso.ofComponents fun X => eqToIso (by simp only [eq_iff_true_of_subsingleton])
                                           -- 🎉 no goals
#align category_theory.functor.punit_ext CategoryTheory.Functor.punitExt
-- Porting note: simp does indeed fire for these despite the linter warning
attribute [nolint simpNF] punitExt_hom_app_down_down punitExt_inv_app_down_down

/-- Any two functors to `Discrete PUnit` are *equal*.
You probably want to use `punitExt` instead of this. -/
theorem punit_ext' (F G : C ⥤ Discrete PUnit.{w + 1}) : F = G :=
  Functor.ext fun X => by simp only [eq_iff_true_of_subsingleton]
                          -- 🎉 no goals
#align category_theory.functor.punit_ext' CategoryTheory.Functor.punit_ext'

/-- The functor from `Discrete PUnit` sending everything to the given object. -/
abbrev fromPUnit (X : C) : Discrete PUnit.{w + 1} ⥤ C :=
  (Functor.const _).obj X
#align category_theory.functor.from_punit CategoryTheory.Functor.fromPUnit

/-- Functors from `Discrete PUnit` are equivalent to the category itself. -/
@[simps]
def equiv : Discrete PUnit.{w + 1} ⥤ C ≌ C where
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
theorem equiv_punit_iff_unique :
    Nonempty (C ≌ Discrete PUnit.{w + 1}) ↔ Nonempty C ∧ ∀ x y : C, Nonempty <| Unique (x ⟶ y) := by
  constructor
  -- ⊢ Nonempty (C ≌ Discrete PUnit) → Nonempty C ∧ ∀ (x y : C), Nonempty (Unique ( …
  · rintro ⟨h⟩
    -- ⊢ Nonempty C ∧ ∀ (x y : C), Nonempty (Unique (x ⟶ y))
    refine' ⟨⟨h.inverse.obj ⟨⟨⟩⟩⟩, fun x y => Nonempty.intro _⟩
    -- ⊢ Unique (x ⟶ y)
    let f : x ⟶ y := by
      have hx : x ⟶ h.inverse.obj ⟨⟨⟩⟩ := by convert h.unit.app x
      have hy : h.inverse.obj ⟨⟨⟩⟩ ⟶ y := by convert h.unitInv.app y
      exact hx ≫ hy
    suffices sub : Subsingleton (x ⟶ y) from uniqueOfSubsingleton f
    -- ⊢ Subsingleton (x ⟶ y)
    have : ∀ z, z = h.unit.app x ≫ (h.functor ⋙ h.inverse).map z ≫ h.unitInv.app y := by
      intro z
      simp [congrArg (· ≫ h.unitInv.app y) (h.unit.naturality z)]
    apply Subsingleton.intro
    -- ⊢ ∀ (a b : x ⟶ y), a = b
    intro a b
    -- ⊢ a = b
    rw [this a, this b]
    -- ⊢ NatTrans.app (Equivalence.unit h) x ≫ (h.functor ⋙ h.inverse).map a ≫ NatTra …
    simp only [Functor.comp_map]
    -- ⊢ NatTrans.app (Equivalence.unit h) x ≫ h.inverse.map (h.functor.map a) ≫ NatT …
    congr 3
    -- ⊢ h.functor.map a = h.functor.map b
    apply ULift.ext
    -- ⊢ (h.functor.map a).down = (h.functor.map b).down
    simp
    -- 🎉 no goals
  · rintro ⟨⟨p⟩, h⟩
    -- ⊢ Nonempty (C ≌ Discrete PUnit)
    haveI := fun x y => (h x y).some
    -- ⊢ Nonempty (C ≌ Discrete PUnit)
    refine'
      Nonempty.intro
        (CategoryTheory.Equivalence.mk ((Functor.const _).obj ⟨⟨⟩⟩)
          ((@Functor.const <| Discrete PUnit).obj p) ?_ (by apply Functor.punitExt))
    exact
      NatIso.ofComponents fun _ =>
        { hom := default
          inv := default }
#align category_theory.equiv_punit_iff_unique CategoryTheory.equiv_punit_iff_unique

end CategoryTheory
