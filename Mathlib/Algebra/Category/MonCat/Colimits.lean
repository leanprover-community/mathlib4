/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Category.MonCat.Basic
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.ConcreteCategory.Elementwise

#align_import algebra.category.Mon.colimits from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# The category of monoids has all colimits.

We do this construction knowing nothing about monoids.
In particular, I want to claim that this file could be produced by a python script
that just looks at what Lean 3's `#print monoid` printed a long time ago (it no longer looks like
this due to the addition of `npow` fields):
```
structure monoid : Type u → Type u
fields:
monoid.mul : Π {M : Type u} [self : monoid M], M → M → M
monoid.mul_assoc : ∀ {M : Type u} [self : monoid M] (a b c : M), a * b * c = a * (b * c)
monoid.one : Π {M : Type u} [self : monoid M], M
monoid.one_mul : ∀ {M : Type u} [self : monoid M] (a : M), 1 * a = a
monoid.mul_one : ∀ {M : Type u} [self : monoid M] (a : M), a * 1 = a
```

and if we'd fed it the output of Lean 3's `#print comm_ring`, this file would instead build
colimits of commutative rings.

A slightly bolder claim is that we could do this with tactics, as well.

Note: `Monoid` and `CommRing` are no longer flat structures in Mathlib4, and so `#print Monoid`
gives the less clear
```
inductive Monoid.{u} : Type u → Type u
number of parameters: 1
constructors:
Monoid.mk : {M : Type u} →
  [toSemigroup : Semigroup M] →
    [toOne : One M] →
      (∀ (a : M), 1 * a = a) →
        (∀ (a : M), a * 1 = a) →
          (npow : ℕ → M → M) →
            autoParam (∀ (x : M), npow 0 x = 1) _auto✝ →
              autoParam (∀ (n : ℕ) (x : M), npow (n + 1) x = x * npow n x) _auto✝¹ → Monoid M
```
-/


universe v

open CategoryTheory

open CategoryTheory.Limits

namespace MonCat.Colimits

/-!
We build the colimit of a diagram in `MonCat` by constructing the
free monoid on the disjoint union of all the monoids in the diagram,
then taking the quotient by the monoid laws within each monoid,
and the identifications given by the morphisms in the diagram.
-/


variable {J : Type v} [SmallCategory J] (F : J ⥤ MonCat.{v})

/-- An inductive type representing all monoid expressions (without relations)
on a collection of types indexed by the objects of `J`.
-/
inductive Prequotient
  -- There's always `of`
  | of : ∀ (j : J) (_ : F.obj j), Prequotient
  -- Then one generator for each operation
  | one : Prequotient
  | mul : Prequotient → Prequotient → Prequotient
set_option linter.uppercaseLean3 false in
#align Mon.colimits.prequotient MonCat.Colimits.Prequotient

instance : Inhabited (Prequotient F) :=
  ⟨Prequotient.one⟩

open Prequotient

/-- The relation on `Prequotient` saying when two expressions are equal
because of the monoid laws, or
because one element is mapped to another by a morphism in the diagram.
-/
inductive Relation : Prequotient F → Prequotient F → Prop-- Make it an equivalence relation:
  | refl : ∀ x, Relation x x
  | symm : ∀ (x y) (_ : Relation x y), Relation y x
  | trans : ∀ (x y z) (_ : Relation x y) (_ : Relation y z),
      Relation x z-- There's always a `map` relation
  | map :
    ∀ (j j' : J) (f : j ⟶ j') (x : F.obj j),
      Relation (Prequotient.of j' ((F.map f) x))
        (Prequotient.of j x)-- Then one relation per operation, describing the interaction with `of`
  | mul : ∀ (j) (x y : F.obj j), Relation (Prequotient.of j (x * y))
      (mul (Prequotient.of j x) (Prequotient.of j y))
  | one : ∀ j, Relation (Prequotient.of j 1) one-- Then one relation per argument of each operation
  | mul_1 : ∀ (x x' y) (_ : Relation x x'), Relation (mul x y) (mul x' y)
  | mul_2 : ∀ (x y y') (_ : Relation y y'), Relation (mul x y) (mul x y')
    -- And one relation per axiom
  | mul_assoc : ∀ x y z, Relation (mul (mul x y) z) (mul x (mul y z))
  | one_mul : ∀ x, Relation (mul one x) x
  | mul_one : ∀ x, Relation (mul x one) x
set_option linter.uppercaseLean3 false in
#align Mon.colimits.relation MonCat.Colimits.Relation

/-- The setoid corresponding to monoid expressions modulo monoid relations and identifications.
-/
def colimitSetoid : Setoid (Prequotient F) where
  r := Relation F
  iseqv := ⟨Relation.refl, Relation.symm _ _, Relation.trans _ _ _⟩
set_option linter.uppercaseLean3 false in
#align Mon.colimits.colimit_setoid MonCat.Colimits.colimitSetoid

attribute [instance] colimitSetoid

/-- The underlying type of the colimit of a diagram in `Mon`.
-/
def ColimitType : Type v :=
  Quotient (colimitSetoid F)
set_option linter.uppercaseLean3 false in
#align Mon.colimits.colimit_type MonCat.Colimits.ColimitType

instance : Inhabited (ColimitType F) := by
  dsimp [ColimitType]
  infer_instance

instance monoidColimitType : Monoid (ColimitType F) where
  one := Quotient.mk _ one
  mul := Quotient.map₂ mul fun x x' rx y y' ry =>
    Setoid.trans (Relation.mul_1 _ _ y rx) (Relation.mul_2 x' _ _ ry)
  one_mul := Quotient.ind fun _ => Quotient.sound <| Relation.one_mul _
  mul_one := Quotient.ind fun _ => Quotient.sound <| Relation.mul_one _
  mul_assoc := Quotient.ind fun _ => Quotient.ind₂ fun _ _ =>
    Quotient.sound <| Relation.mul_assoc _ _ _
set_option linter.uppercaseLean3 false in
#align Mon.colimits.monoid_colimit_type MonCat.Colimits.monoidColimitType

@[simp]
theorem quot_one : Quot.mk Setoid.r one = (1 : ColimitType F) :=
  rfl
set_option linter.uppercaseLean3 false in
#align Mon.colimits.quot_one MonCat.Colimits.quot_one

@[simp]
theorem quot_mul (x y : Prequotient F) : Quot.mk Setoid.r (mul x y) =
    @HMul.hMul (ColimitType F) (ColimitType F) (ColimitType F) _
      (Quot.mk Setoid.r x) (Quot.mk Setoid.r y) :=
  rfl
set_option linter.uppercaseLean3 false in
#align Mon.colimits.quot_mul MonCat.Colimits.quot_mul

/-- The bundled monoid giving the colimit of a diagram. -/
def colimit : MonCat :=
  ⟨ColimitType F, by infer_instance⟩
set_option linter.uppercaseLean3 false in
#align Mon.colimits.colimit MonCat.Colimits.colimit

/-- The function from a given monoid in the diagram to the colimit monoid. -/
def coconeFun (j : J) (x : F.obj j) : ColimitType F :=
  Quot.mk _ (Prequotient.of j x)
set_option linter.uppercaseLean3 false in
#align Mon.colimits.cocone_fun MonCat.Colimits.coconeFun

/-- The monoid homomorphism from a given monoid in the diagram to the colimit monoid. -/
def coconeMorphism (j : J) : F.obj j ⟶ colimit F where
  toFun := coconeFun F j
  map_one' := Quot.sound (Relation.one _)
  map_mul' _ _ := Quot.sound (Relation.mul _ _ _)
set_option linter.uppercaseLean3 false in
#align Mon.colimits.cocone_morphism MonCat.Colimits.coconeMorphism

@[simp]
theorem cocone_naturality {j j' : J} (f : j ⟶ j') :
    F.map f ≫ coconeMorphism F j' = coconeMorphism F j := by
  ext
  apply Quot.sound
  apply Relation.map
set_option linter.uppercaseLean3 false in
#align Mon.colimits.cocone_naturality MonCat.Colimits.cocone_naturality

@[simp]
theorem cocone_naturality_components (j j' : J) (f : j ⟶ j') (x : F.obj j) :
    (coconeMorphism F j') (F.map f x) = (coconeMorphism F j) x := by
  rw [← cocone_naturality F f]
  rfl
set_option linter.uppercaseLean3 false in
#align Mon.colimits.cocone_naturality_components MonCat.Colimits.cocone_naturality_components

/-- The cocone over the proposed colimit monoid. -/
def colimitCocone : Cocone F where
  pt := colimit F
  ι := { app := coconeMorphism F }
set_option linter.uppercaseLean3 false in
#align Mon.colimits.colimit_cocone MonCat.Colimits.colimitCocone

/-- The function from the free monoid on the diagram to the cone point of any other cocone. -/
@[simp]
def descFunLift (s : Cocone F) : Prequotient F → s.pt
  | Prequotient.of j x => (s.ι.app j) x
  | one => 1
  | mul x y => descFunLift _ x * descFunLift _ y
set_option linter.uppercaseLean3 false in
#align Mon.colimits.desc_fun_lift MonCat.Colimits.descFunLift

/-- The function from the colimit monoid to the cone point of any other cocone. -/
def descFun (s : Cocone F) : ColimitType F → s.pt := by
  fapply Quot.lift
  · exact descFunLift F s
  · intro x y r
    induction r with
    | refl x => rfl
    | symm x y _ h => exact h.symm
    | trans x y z _ _ h₁ h₂ => exact h₁.trans h₂
    | map j j' f x => exact s.w_apply f x
    | mul j x y => exact map_mul (s.ι.app j) x y
    | one j => exact map_one (s.ι.app j)
    | mul_1 x x' y _ h => exact congr_arg (· * _) h
    | mul_2 x y y' _ h => exact congr_arg (_ * ·) h
    | mul_assoc x y z => exact mul_assoc _ _ _
    | one_mul x => exact one_mul _
    | mul_one x => exact mul_one _
set_option linter.uppercaseLean3 false in
#align Mon.colimits.desc_fun MonCat.Colimits.descFun

/-- The monoid homomorphism from the colimit monoid to the cone point of any other cocone. -/
def descMorphism (s : Cocone F) : colimit F ⟶ s.pt where
  toFun := descFun F s
  map_one' := rfl
  map_mul' x y := by
    induction x using Quot.inductionOn
    induction y using Quot.inductionOn
    dsimp [descFun]
    rw [← quot_mul]
    simp only [descFunLift]
set_option linter.uppercaseLean3 false in
#align Mon.colimits.desc_morphism MonCat.Colimits.descMorphism

/-- Evidence that the proposed colimit is the colimit. -/
def colimitIsColimit : IsColimit (colimitCocone F) where
  desc s := descMorphism F s
  uniq s m w := by
    ext x
    induction' x using Quot.inductionOn with x
    induction' x with j x x y hx hy
    · change _ = s.ι.app j _
      rw [← w j]
      rfl
    · rw [quot_one, map_one]
      rfl
    · rw [quot_mul, map_mul, hx, hy]
      dsimp [descMorphism, DFunLike.coe, descFun]
      simp only [← quot_mul, descFunLift]
set_option linter.uppercaseLean3 false in
#align Mon.colimits.colimit_is_colimit MonCat.Colimits.colimitIsColimit

instance hasColimits_monCat : HasColimits MonCat where
  has_colimits_of_shape _ _ :=
    { has_colimit := fun F =>
        HasColimit.mk
          { cocone := colimitCocone F
            isColimit := colimitIsColimit F } }
set_option linter.uppercaseLean3 false in
#align Mon.colimits.has_colimits_Mon MonCat.Colimits.hasColimits_monCat

end MonCat.Colimits
