/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module algebra.category.Mon.colimits
! leanprover-community/mathlib commit 70fd9563a21e7b963887c9360bd29b2393e6225a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Category.MonCat.Basic
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.ConcreteCategory.Elementwise

/-!
# The category of monoids has all colimits.

We do this construction knowing nothing about monoids.
In particular, I want to claim that this file could be produced by a python script
that just looks at the output of `#print monoid`:

  -- structure monoid : Type u → Type u
  -- fields:
  -- monoid.mul : Π {α : Type u} [c : monoid α], α → α → α
  -- monoid.mul_assoc : ∀ {α : Type u} [c : monoid α] (a b c_1 : α), a * b * c_1 = a * (b * c_1)
  -- monoid.one : Π (α : Type u) [c : monoid α], α
  -- monoid.one_mul : ∀ {α : Type u} [c : monoid α] (a : α), 1 * a = a
  -- monoid.mul_one : ∀ {α : Type u} [c : monoid α] (a : α), a * 1 = a

and if we'd fed it the output of `#print comm_ring`, this file would instead build
colimits of commutative rings.

A slightly bolder claim is that we could do this with tactics, as well.

Note: `Monoid` and `CommRing` are no longer flat structures in Mathlib4

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
inductive Prequotient-- There's always `of`
  | of : ∀ (j : J) (_ : F.obj j), Prequotient-- Then one generator for each operation
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
  mul := by
    fapply @Quot.lift _ _ (ColimitType F → ColimitType F)
    · intro x
      fapply @Quot.lift
      · intro y
        exact Quot.mk _ (mul x y)
      · intro y y' r
        apply Quot.sound
        exact Relation.mul_2 _ _ _ r
    · intro x x' r
      funext y
      induction y using Quot.inductionOn
      dsimp
      apply Quot.sound
      apply Relation.mul_1 _ _ _ r
  one := Quot.mk _ one
  mul_assoc x y z := by
    induction x using Quot.inductionOn
    induction y using Quot.inductionOn
    induction z using Quot.inductionOn
    dsimp [HMul.hMul]
    apply Quot.sound
    apply Relation.mul_assoc
  one_mul x := by
    induction x using Quot.inductionOn
    dsimp
    apply Quot.sound
    apply Relation.one_mul
  mul_one x := by
    induction x using Quot.inductionOn
    dsimp
    apply Quot.sound
    apply Relation.mul_one
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
    induction' r with _ _ _ _ h _ _ _ _ _ h₁ h₂ _ _ f x _ _ _ _ _ _ _ _ h _ _ _ _ h <;> try simp
    -- symm
    . exact h.symm
    -- trans
    . exact h₁.trans h₂
    -- map
    . exact s.w_apply f x
    -- mul_1
    . rw [h]
    -- mul_2
    . rw [h]
    -- mul_assoc
    . rw [mul_assoc]
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
    . change _ = s.ι.app j _
      rw [← w j]
      rfl
    . rw [quot_one, map_one]
      rfl
    . rw [quot_mul, map_mul, hx, hy]
      dsimp [descMorphism, FunLike.coe, descFun]
      simp only [← quot_mul, descFunLift]
set_option linter.uppercaseLean3 false in
#align Mon.colimits.colimit_is_colimit MonCat.Colimits.colimitIsColimit

instance hasColimits_monCat : HasColimits MonCat
    where has_colimits_of_shape _ _ :=
    { has_colimit := fun F =>
        HasColimit.mk
          { cocone := colimitCocone F
            isColimit := colimitIsColimit F } }
set_option linter.uppercaseLean3 false in
#align Mon.colimits.has_colimits_Mon MonCat.Colimits.hasColimits_monCat

end MonCat.Colimits
