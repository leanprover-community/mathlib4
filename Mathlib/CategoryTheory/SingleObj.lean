/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module category_theory.single_obj
! leanprover-community/mathlib commit 56adee5b5eef9e734d82272918300fca4f3e7cef
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Endomorphism
import Mathbin.CategoryTheory.Category.Cat
import Mathbin.Algebra.Category.Mon.Basic
import Mathbin.Combinatorics.Quiver.SingleObj

/-!
# Single-object category

Single object category with a given monoid of endomorphisms.
It is defined to facilitate transfering some definitions and lemmas (e.g., conjugacy etc.)
from category theory to monoids and groups.

## Main definitions

Given a type `α` with a monoid structure, `single_obj α` is `unit` type with `category` structure
such that `End (single_obj α).star` is the monoid `α`.  This can be extended to a functor `Mon ⥤
Cat`.

If `α` is a group, then `single_obj α` is a groupoid.

An element `x : α` can be reinterpreted as an element of `End (single_obj.star α)` using
`single_obj.to_End`.

## Implementation notes

- `category_struct.comp` on `End (single_obj.star α)` is `flip (*)`, not `(*)`. This way
  multiplication on `End` agrees with the multiplication on `α`.

- By default, Lean puts instances into `category_theory` namespace instead of
  `category_theory.single_obj`, so we give all names explicitly.
-/


universe u v w

namespace CategoryTheory

/-- Abbreviation that allows writing `category_theory.single_obj` rather than `quiver.single_obj`.
-/
abbrev SingleObj :=
  Quiver.SingleObj
#align category_theory.single_obj CategoryTheory.SingleObj

namespace SingleObj

variable (α : Type u)

/-- One and `flip (*)` become `id` and `comp` for morphisms of the single object category. -/
instance categoryStruct [One α] [Mul α] : CategoryStruct (SingleObj α)
    where
  Hom _ _ := α
  comp _ _ _ x y := y * x
  id _ := 1
#align category_theory.single_obj.category_struct CategoryTheory.SingleObj.categoryStruct

/-- Monoid laws become category laws for the single object category. -/
instance category [Monoid α] : Category (SingleObj α)
    where
  comp_id' _ _ := one_mul
  id_comp' _ _ := mul_one
  assoc' _ _ _ _ x y z := (mul_assoc z y x).symm
#align category_theory.single_obj.category CategoryTheory.SingleObj.category

theorem id_as_one [Monoid α] (x : SingleObj α) : 𝟙 x = 1 :=
  rfl
#align category_theory.single_obj.id_as_one CategoryTheory.SingleObj.id_as_one

theorem comp_as_mul [Monoid α] {x y z : SingleObj α} (f : x ⟶ y) (g : y ⟶ z) : f ≫ g = g * f :=
  rfl
#align category_theory.single_obj.comp_as_mul CategoryTheory.SingleObj.comp_as_mul

/-- Groupoid structure on `single_obj α`.

See <https://stacks.math.columbia.edu/tag/0019>.
-/
instance groupoid [Group α] : Groupoid (SingleObj α)
    where
  inv _ _ x := x⁻¹
  inv_comp' _ _ := mul_right_inv
  comp_inv' _ _ := mul_left_inv
#align category_theory.single_obj.groupoid CategoryTheory.SingleObj.groupoid

theorem inv_as_inv [Group α] {x y : SingleObj α} (f : x ⟶ y) : inv f = f⁻¹ :=
  by
  ext
  rw [comp_as_mul, inv_mul_self, id_as_one]
#align category_theory.single_obj.inv_as_inv CategoryTheory.SingleObj.inv_as_inv

/-- Abbreviation that allows writing `category_theory.single_obj.star` rather than
`quiver.single_obj.star`.
-/
abbrev star : SingleObj α :=
  Quiver.SingleObj.star α
#align category_theory.single_obj.star CategoryTheory.SingleObj.star

/-- The endomorphisms monoid of the only object in `single_obj α` is equivalent to the original
     monoid α. -/
def toEnd [Monoid α] : α ≃* End (SingleObj.star α) :=
  { Equiv.refl α with map_mul' := fun x y => rfl }
#align category_theory.single_obj.to_End CategoryTheory.SingleObj.toEnd

theorem toEnd_def [Monoid α] (x : α) : toEnd α x = x :=
  rfl
#align category_theory.single_obj.to_End_def CategoryTheory.SingleObj.toEnd_def

/-- There is a 1-1 correspondence between monoid homomorphisms `α → β` and functors between the
    corresponding single-object categories. It means that `single_obj` is a fully faithful
    functor.

See <https://stacks.math.columbia.edu/tag/001F> --
although we do not characterize when the functor is full or faithful.
-/
def mapHom (α : Type u) (β : Type v) [Monoid α] [Monoid β] : (α →* β) ≃ SingleObj α ⥤ SingleObj β
    where
  toFun f :=
    { obj := id
      map := fun _ _ => ⇑f
      map_id' := fun _ => f.map_one
      map_comp' := fun _ _ _ x y => f.map_mul y x }
  invFun f :=
    { toFun := @Functor.map _ _ _ _ f (SingleObj.star α) (SingleObj.star α)
      map_one' := f.map_id _
      map_mul' := fun x y => f.map_comp y x }
  left_inv := fun ⟨f, h₁, h₂⟩ => rfl
  right_inv f := by cases f <;> obviously
#align category_theory.single_obj.map_hom CategoryTheory.SingleObj.mapHom

theorem mapHom_id (α : Type u) [Monoid α] : mapHom α α (MonoidHom.id α) = 𝟭 _ :=
  rfl
#align category_theory.single_obj.map_hom_id CategoryTheory.SingleObj.mapHom_id

theorem mapHom_comp {α : Type u} {β : Type v} [Monoid α] [Monoid β] (f : α →* β) {γ : Type w}
    [Monoid γ] (g : β →* γ) : mapHom α γ (g.comp f) = mapHom α β f ⋙ mapHom β γ g :=
  rfl
#align category_theory.single_obj.map_hom_comp CategoryTheory.SingleObj.mapHom_comp

/-- Given a function `f : C → G` from a category to a group, we get a functor
    `C ⥤ G` sending any morphism `x ⟶ y` to `f y * (f x)⁻¹`. -/
@[simps]
def differenceFunctor {C G} [Category C] [Group G] (f : C → G) : C ⥤ SingleObj G
    where
  obj _ := ()
  map x y _ := f y * (f x)⁻¹
  map_id' := by
    intro
    rw [single_obj.id_as_one, mul_right_inv]
  map_comp' := by
    intros
    rw [single_obj.comp_as_mul, ← mul_assoc, mul_left_inj, mul_assoc, inv_mul_self, mul_one]
#align category_theory.single_obj.difference_functor CategoryTheory.SingleObj.differenceFunctor

end SingleObj

end CategoryTheory

open CategoryTheory

namespace MonoidHom

/-- Reinterpret a monoid homomorphism `f : α → β` as a functor `(single_obj α) ⥤ (single_obj β)`.
See also `category_theory.single_obj.map_hom` for an equivalence between these types. -/
@[reducible]
def toFunctor {α : Type u} {β : Type v} [Monoid α] [Monoid β] (f : α →* β) :
    SingleObj α ⥤ SingleObj β :=
  SingleObj.mapHom α β f
#align monoid_hom.to_functor MonoidHom.toFunctor

@[simp]
theorem id_toFunctor (α : Type u) [Monoid α] : (id α).toFunctor = 𝟭 _ :=
  rfl
#align monoid_hom.id_to_functor MonoidHom.id_toFunctor

@[simp]
theorem comp_toFunctor {α : Type u} {β : Type v} [Monoid α] [Monoid β] (f : α →* β) {γ : Type w}
    [Monoid γ] (g : β →* γ) : (g.comp f).toFunctor = f.toFunctor ⋙ g.toFunctor :=
  rfl
#align monoid_hom.comp_to_functor MonoidHom.comp_toFunctor

end MonoidHom

namespace Units

variable (α : Type u) [Monoid α]

/-- The units in a monoid are (multiplicatively) equivalent to
the automorphisms of `star` when we think of the monoid as a single-object category. -/
def toAut : αˣ ≃* Aut (SingleObj.star α) :=
  (Units.mapEquiv (SingleObj.toEnd α)).trans <| Aut.unitsEndEquivAut _
#align units.to_Aut Units.toAut

@[simp]
theorem toAut_hom (x : αˣ) : (toAut α x).Hom = SingleObj.toEnd α x :=
  rfl
#align units.to_Aut_hom Units.toAut_hom

@[simp]
theorem toAut_inv (x : αˣ) : (toAut α x).inv = SingleObj.toEnd α (x⁻¹ : αˣ) :=
  rfl
#align units.to_Aut_inv Units.toAut_inv

end Units

namespace MonCat

open CategoryTheory

/-- The fully faithful functor from `Mon` to `Cat`. -/
def toCat : MonCat ⥤ Cat where
  obj x := Cat.of (SingleObj x)
  map x y f := SingleObj.mapHom x y f
#align Mon.to_Cat MonCat.toCat

instance toCatFull : Full toCat
    where
  preimage x y := (SingleObj.mapHom x y).invFun
  witness' x y := by apply Equiv.right_inv
#align Mon.to_Cat_full MonCat.toCatFull

instance toCat_faithful : Faithful toCat where map_injective' x y := by apply Equiv.injective
#align Mon.to_Cat_faithful MonCat.toCat_faithful

end MonCat

