/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Bhavik Mehta
-/
import Mathlib.CategoryTheory.Functor.Const
import Mathlib.CategoryTheory.Discrete.Basic

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
variable {C}

/-- Any two functors to `Discrete PUnit` are isomorphic. -/
@[simps!]
def punitExt (F G : C ⥤ Discrete PUnit.{w + 1}) : F ≅ G :=
  NatIso.ofComponents fun X => eqToIso (by simp only [eq_iff_true_of_subsingleton])

/-- Any two functors to `Discrete PUnit` are *equal*.
You probably want to use `punitExt` instead of this. -/
theorem punit_ext' (F G : C ⥤ Discrete PUnit.{w + 1}) : F = G :=
  Functor.ext fun X => by simp only [eq_iff_true_of_subsingleton]

/-- The functor from `Discrete PUnit` sending everything to the given object. -/
abbrev fromPUnit (X : C) : Discrete PUnit.{w + 1} ⥤ C :=
  (Functor.const _).obj X

/-- Functors from `Discrete PUnit` are equivalent to the category itself. -/
@[simps]
def equiv : Discrete PUnit.{w + 1} ⥤ C ≌ C where
  functor :=
    { obj := fun F => F.obj ⟨⟨⟩⟩
      map := fun θ => θ.app ⟨⟨⟩⟩ }
  inverse := Functor.const _
  unitIso := NatIso.ofComponents fun _ => Discrete.natIso fun _ => Iso.refl _
  counitIso := NatIso.ofComponents Iso.refl

end Functor

/-- A category being equivalent to `PUnit` is equivalent to it having a unique morphism between
  any two objects. (In fact, such a category is also a groupoid;
  see `CategoryTheory.Groupoid.ofHomUnique`) -/
theorem equiv_punit_iff_unique :
    Nonempty (C ≌ Discrete PUnit.{w + 1}) ↔ Nonempty C ∧ ∀ x y : C, Nonempty <| Unique (x ⟶ y) := by
  constructor
  · rintro ⟨h⟩
    refine ⟨⟨h.inverse.obj ⟨⟨⟩⟩⟩, fun x y => Nonempty.intro ?_⟩
    let f : x ⟶ y := by
      have hx : x ⟶ h.inverse.obj ⟨⟨⟩⟩ := by convert h.unit.app x
      have hy : h.inverse.obj ⟨⟨⟩⟩ ⟶ y := by convert h.unitInv.app y
      exact hx ≫ hy
    suffices sub : Subsingleton (x ⟶ y) from uniqueOfSubsingleton f
    have : ∀ z, z = h.unit.app x ≫ (h.functor ⋙ h.inverse).map z ≫ h.unitInv.app y := by
      intro z
      simp
    apply Subsingleton.intro
    intro a b
    rw [this a, this b]
    simp only [Functor.comp_map]
    congr 3
    apply ULift.ext
    simp [eq_iff_true_of_subsingleton]
  · rintro ⟨⟨p⟩, h⟩
    haveI := fun x y => (h x y).some
    refine
      Nonempty.intro
        (CategoryTheory.Equivalence.mk ((Functor.const _).obj ⟨⟨⟩⟩)
          ((@Functor.const <| Discrete PUnit).obj p) ?_ (by apply Functor.punitExt))
    exact
      NatIso.ofComponents fun _ =>
        { hom := default
          inv := default }

end CategoryTheory
