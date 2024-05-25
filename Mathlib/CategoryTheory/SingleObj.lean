/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.FinCategory.Basic
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.Algebra.Category.MonCat.Basic
import Mathlib.Combinatorics.Quiver.SingleObj

#align_import category_theory.single_obj from "leanprover-community/mathlib"@"56adee5b5eef9e734d82272918300fca4f3e7cef"

/-!
# Single-object category

Single object category with a given monoid of endomorphisms.
It is defined to facilitate transferring some definitions and lemmas (e.g., conjugacy etc.)
from category theory to monoids and groups.

## Main definitions

Given a type `M` with a monoid structure, `SingleObj M` is `Unit` type with `Category` structure
such that `End (SingleObj M).star` is the monoid `M`.  This can be extended to a functor
`MonCat ⥤ Cat`.

If `M` is a group, then `SingleObj M` is a groupoid.

An element `x : M` can be reinterpreted as an element of `End (SingleObj.star M)` using
`SingleObj.toEnd`.

## Implementation notes

- `categoryStruct.comp` on `End (SingleObj.star M)` is `flip (*)`, not `(*)`. This way
  multiplication on `End` agrees with the multiplication on `M`.

- By default, Lean puts instances into `CategoryTheory` namespace instead of
  `CategoryTheory.SingleObj`, so we give all names explicitly.
-/


universe u v w

namespace CategoryTheory

/-- Abbreviation that allows writing `CategoryTheory.SingleObj` rather than `Quiver.SingleObj`.
-/
abbrev SingleObj :=
  Quiver.SingleObj
#align category_theory.single_obj CategoryTheory.SingleObj

namespace SingleObj

variable (M G : Type u)

/-- One and `flip (*)` become `id` and `comp` for morphisms of the single object category. -/
instance categoryStruct [One M] [Mul M] : CategoryStruct (SingleObj M) where
  Hom _ _ := M
  comp x y := y * x
  id _ := 1
#align category_theory.single_obj.category_struct CategoryTheory.SingleObj.categoryStruct

variable [Monoid M] [Group G]

/-- Monoid laws become category laws for the single object category. -/
instance category : Category (SingleObj M) where
  comp_id := one_mul
  id_comp := mul_one
  assoc x y z := (mul_assoc z y x).symm
#align category_theory.single_obj.category CategoryTheory.SingleObj.category

theorem id_as_one (x : SingleObj M) : 𝟙 x = 1 :=
  rfl
#align category_theory.single_obj.id_as_one CategoryTheory.SingleObj.id_as_one

theorem comp_as_mul {x y z : SingleObj M} (f : x ⟶ y) (g : y ⟶ z) : f ≫ g = g * f :=
  rfl
#align category_theory.single_obj.comp_as_mul CategoryTheory.SingleObj.comp_as_mul

/-- If `M` is finite and in universe zero, then `SingleObj M` is a `FinCategory`. -/
instance finCategoryOfFintype (M : Type) [Fintype M] [Monoid M] : FinCategory (SingleObj M) where

/-- Groupoid structure on `SingleObj M`.

See <https://stacks.math.columbia.edu/tag/0019>.
-/
instance groupoid : Groupoid (SingleObj G) where
  inv x := x⁻¹
  inv_comp := mul_right_inv
  comp_inv := mul_left_inv
#align category_theory.single_obj.groupoid CategoryTheory.SingleObj.groupoid

theorem inv_as_inv {x y : SingleObj G} (f : x ⟶ y) : inv f = f⁻¹ := by
  apply IsIso.inv_eq_of_hom_inv_id
  rw [comp_as_mul, inv_mul_self, id_as_one]
#align category_theory.single_obj.inv_as_inv CategoryTheory.SingleObj.inv_as_inv

/-- Abbreviation that allows writing `CategoryTheory.SingleObj.star` rather than
`Quiver.SingleObj.star`.
-/
abbrev star : SingleObj M :=
  Quiver.SingleObj.star M
#align category_theory.single_obj.star CategoryTheory.SingleObj.star

/-- The endomorphisms monoid of the only object in `SingleObj M` is equivalent to the original
     monoid M. -/
def toEnd : M ≃* End (SingleObj.star M) :=
  { Equiv.refl M with map_mul' := fun _ _ => rfl }
#align category_theory.single_obj.to_End CategoryTheory.SingleObj.toEnd

theorem toEnd_def (x : M) : toEnd M x = x :=
  rfl
#align category_theory.single_obj.to_End_def CategoryTheory.SingleObj.toEnd_def

variable (N : Type v) [Monoid N]

/-- There is a 1-1 correspondence between monoid homomorphisms `M → N` and functors between the
    corresponding single-object categories. It means that `SingleObj` is a fully faithful
    functor.

See <https://stacks.math.columbia.edu/tag/001F> --
although we do not characterize when the functor is full or faithful.
-/
def mapHom : (M →* N) ≃ SingleObj M ⥤ SingleObj N where
  toFun f :=
    { obj := id
      map := ⇑f
      map_id := fun _ => f.map_one
      map_comp := fun x y => f.map_mul y x }
  invFun f :=
    { toFun := fun x => f.map ((toEnd M) x)
      map_one' := f.map_id _
      map_mul' := fun x y => f.map_comp y x }
  left_inv := by aesop_cat
  right_inv := by aesop_cat
#align category_theory.single_obj.map_hom CategoryTheory.SingleObj.mapHom

theorem mapHom_id : mapHom M M (MonoidHom.id M) = 𝟭 _ :=
  rfl
#align category_theory.single_obj.map_hom_id CategoryTheory.SingleObj.mapHom_id

variable {M N G}

theorem mapHom_comp (f : M →* N) {P : Type w} [Monoid P] (g : N →* P) :
    mapHom M P (g.comp f) = mapHom M N f ⋙ mapHom N P g :=
  rfl
#align category_theory.single_obj.map_hom_comp CategoryTheory.SingleObj.mapHom_comp

variable {C : Type v} [Category.{w} C]

/-- Given a function `f : C → G` from a category to a group, we get a functor
    `C ⥤ G` sending any morphism `x ⟶ y` to `f y * (f x)⁻¹`. -/
@[simps]
def differenceFunctor (f : C → G) : C ⥤ SingleObj G where
  obj _ := ()
  map {x y} _ := f y * (f x)⁻¹
  map_id := by
    intro
    simp only [SingleObj.id_as_one, mul_right_inv]
  map_comp := by
    intros
    dsimp
    rw [SingleObj.comp_as_mul, ← mul_assoc, mul_left_inj, mul_assoc, inv_mul_self, mul_one]
#align category_theory.single_obj.difference_functor CategoryTheory.SingleObj.differenceFunctor

/-- A monoid homomorphism `f: M → End X` into the endomorphisms of an object `X` of a category `C`
induces a functor `SingleObj M ⥤ C`. -/
@[simps]
def functor {X : C} (f : M →* End X) : SingleObj M ⥤ C where
  obj _ := X
  map a := f a
  map_id _ := MonoidHom.map_one f
  map_comp a b := MonoidHom.map_mul f b a

/-- Construct a natural transformation between functors `SingleObj M ⥤ C` by
giving a compatible morphism `SingleObj.star M`. -/
@[simps]
def natTrans {F G : SingleObj M ⥤ C} (u : F.obj (SingleObj.star M) ⟶ G.obj (SingleObj.star M))
    (h : ∀ a : M, F.map a ≫ u = u ≫ G.map a) : F ⟶ G where
  app _ := u
  naturality _ _ a := h a

end SingleObj

end CategoryTheory

open CategoryTheory

namespace MonoidHom

variable {M : Type u} {N : Type v} [Monoid M] [Monoid N]

/-- Reinterpret a monoid homomorphism `f : M → N` as a functor `(single_obj M) ⥤ (single_obj N)`.
See also `CategoryTheory.SingleObj.mapHom` for an equivalence between these types. -/
abbrev toFunctor (f : M →* N) : SingleObj M ⥤ SingleObj N :=
  SingleObj.mapHom M N f
#align monoid_hom.to_functor MonoidHom.toFunctor

@[simp]
theorem comp_toFunctor (f : M →* N) {P : Type w} [Monoid P] (g : N →* P) :
    (g.comp f).toFunctor = f.toFunctor ⋙ g.toFunctor :=
  rfl
#align monoid_hom.comp_to_functor MonoidHom.comp_toFunctor

variable (M)

@[simp]
theorem id_toFunctor : (id M).toFunctor = 𝟭 _ :=
  rfl
#align monoid_hom.id_to_functor MonoidHom.id_toFunctor

end MonoidHom

namespace MulEquiv

variable {M : Type u} {N : Type v} [Monoid M] [Monoid N]

/-- Reinterpret a monoid isomorphism `f : M ≃* N` as an equivalence `SingleObj M ≌ SingleObj N`. -/
@[simps!]
def toSingleObjEquiv (e : M ≃* N) : SingleObj M ≌ SingleObj N where
  functor := e.toMonoidHom.toFunctor
  inverse := e.symm.toMonoidHom.toFunctor
  unitIso := eqToIso (by
    rw [← MonoidHom.comp_toFunctor, ← MonoidHom.id_toFunctor]
    congr 1
    aesop_cat)
  counitIso := eqToIso (by
    rw [← MonoidHom.comp_toFunctor, ← MonoidHom.id_toFunctor]
    congr 1
    aesop_cat)

end MulEquiv

namespace Units

variable (M : Type u) [Monoid M]

/-- The units in a monoid are (multiplicatively) equivalent to
the automorphisms of `star` when we think of the monoid as a single-object category. -/
def toAut : Mˣ ≃* Aut (SingleObj.star M) :=
  MulEquiv.trans (Units.mapEquiv (SingleObj.toEnd M))
    (Aut.unitsEndEquivAut (SingleObj.star M))
set_option linter.uppercaseLean3 false in
#align units.to_Aut Units.toAut

@[simp]
theorem toAut_hom (x : Mˣ) : (toAut M x).hom = SingleObj.toEnd M x :=
  rfl
set_option linter.uppercaseLean3 false in
#align units.to_Aut_hom Units.toAut_hom

@[simp]
theorem toAut_inv (x : Mˣ) : (toAut M x).inv = SingleObj.toEnd M (x⁻¹ : Mˣ) :=
  rfl
set_option linter.uppercaseLean3 false in
#align units.to_Aut_inv Units.toAut_inv

end Units

namespace MonCat

open CategoryTheory

/-- The fully faithful functor from `MonCat` to `Cat`. -/
def toCat : MonCat ⥤ Cat where
  obj x := Cat.of (SingleObj x)
  map {x y} f := SingleObj.mapHom x y f
set_option linter.uppercaseLean3 false in
#align Mon.to_Cat MonCat.toCat

instance toCat_full : toCat.Full  where
  map_surjective := (SingleObj.mapHom _ _).surjective
set_option linter.uppercaseLean3 false in
#align Mon.to_Cat_full MonCat.toCat_full

instance toCat_faithful : toCat.Faithful where
  map_injective h := by rwa [toCat, (SingleObj.mapHom _ _).apply_eq_iff_eq] at h
set_option linter.uppercaseLean3 false in
#align Mon.to_Cat_faithful MonCat.toCat_faithful

end MonCat
