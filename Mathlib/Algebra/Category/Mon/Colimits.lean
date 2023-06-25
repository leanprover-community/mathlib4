/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module algebra.category.Mon.colimits
! leanprover-community/mathlib commit 70fd9563a21e7b963887c9360bd29b2393e6225a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Category.Mon.Basic
import Mathbin.CategoryTheory.Limits.HasLimits
import Mathbin.CategoryTheory.ConcreteCategory.Elementwise

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
-/


universe v

open CategoryTheory

open CategoryTheory.Limits

namespace MonCat.Colimits

/-!
We build the colimit of a diagram in `Mon` by constructing the
free monoid on the disjoint union of all the monoids in the diagram,
then taking the quotient by the monoid laws within each monoid,
and the identifications given by the morphisms in the diagram.
-/


variable {J : Type v} [SmallCategory J] (F : J ⥤ MonCat.{v})

/-- An inductive type representing all monoid expressions (without relations)
on a collection of types indexed by the objects of `J`.
-/
inductive Prequotient-- There's always `of`

  | of : ∀ (j : J) (x : F.obj j), prequotient-- Then one generator for each operation

  | one : prequotient
  | mul : prequotient → prequotient → prequotient
#align Mon.colimits.prequotient MonCat.Colimits.Prequotient

instance : Inhabited (Prequotient F) :=
  ⟨Prequotient.one⟩

open Prequotient

/-- The relation on `prequotient` saying when two expressions are equal
because of the monoid laws, or
because one element is mapped to another by a morphism in the diagram.
-/
inductive Relation : Prequotient F → Prequotient F → Prop-- Make it an equivalence relation:

  | refl : ∀ x, relation x x
  | symm : ∀ (x y) (h : relation x y), relation y x
  |
  trans :
    ∀ (x y z) (h : relation x y) (k : relation y z), relation x z-- There's always a `map` relation

  |
  map :
    ∀ (j j' : J) (f : j ⟶ j') (x : F.obj j),
      relation (of j' ((F.map f) x))
        (of j x)-- Then one relation per operation, describing the interaction with `of`

  | mul : ∀ (j) (x y : F.obj j), relation (of j (x * y)) (mul (of j x) (of j y))
  | one : ∀ j, relation (of j 1) one-- Then one relation per argument of each operation

  | mul_1 : ∀ (x x' y) (r : relation x x'), relation (mul x y) (mul x' y)
  |
  mul_2 : ∀ (x y y') (r : relation y y'), relation (mul x y) (mul x y')-- And one relation per axiom

  | mul_assoc : ∀ x y z, relation (mul (mul x y) z) (mul x (mul y z))
  | one_mul : ∀ x, relation (mul one x) x
  | mul_one : ∀ x, relation (mul x one) x
#align Mon.colimits.relation MonCat.Colimits.Relation

/-- The setoid corresponding to monoid expressions modulo monoid relations and identifications.
-/
def colimitSetoid : Setoid (Prequotient F)
    where
  R := Relation F
  iseqv := ⟨Relation.refl, Relation.symm, Relation.trans⟩
#align Mon.colimits.colimit_setoid MonCat.Colimits.colimitSetoid

attribute [instance] colimit_setoid

/-- The underlying type of the colimit of a diagram in `Mon`.
-/
def ColimitType : Type v :=
  Quotient (colimitSetoid F)
deriving Inhabited
#align Mon.colimits.colimit_type MonCat.Colimits.ColimitType

instance monoidColimitType : Monoid (ColimitType F)
    where
  mul := by
    fapply @Quot.lift _ _ (colimit_type F → colimit_type F)
    · intro x
      fapply @Quot.lift
      · intro y
        exact Quot.mk _ (mul x y)
      · intro y y' r
        apply Quot.sound
        exact relation.mul_2 _ _ _ r
    · intro x x' r
      funext y
      induction y
      dsimp
      apply Quot.sound
      · exact relation.mul_1 _ _ _ r
      · rfl
  one := Quot.mk _ one
  mul_assoc x y z := by
    induction x
    induction y
    induction z
    dsimp
    apply Quot.sound
    apply relation.mul_assoc
    rfl
    rfl
    rfl
  one_mul x := by
    induction x
    dsimp
    apply Quot.sound
    apply relation.one_mul
    rfl
  mul_one x := by
    induction x
    dsimp
    apply Quot.sound
    apply relation.mul_one
    rfl
#align Mon.colimits.monoid_colimit_type MonCat.Colimits.monoidColimitType

@[simp]
theorem quot_one : Quot.mk Setoid.r one = (1 : ColimitType F) :=
  rfl
#align Mon.colimits.quot_one MonCat.Colimits.quot_one

@[simp]
theorem quot_mul (x y) :
    Quot.mk Setoid.r (mul x y) = (Quot.mk Setoid.r x * Quot.mk Setoid.r y : ColimitType F) :=
  rfl
#align Mon.colimits.quot_mul MonCat.Colimits.quot_mul

/-- The bundled monoid giving the colimit of a diagram. -/
def colimit : MonCat :=
  ⟨ColimitType F, by infer_instance⟩
#align Mon.colimits.colimit MonCat.Colimits.colimit

/-- The function from a given monoid in the diagram to the colimit monoid. -/
def coconeFun (j : J) (x : F.obj j) : ColimitType F :=
  Quot.mk _ (of j x)
#align Mon.colimits.cocone_fun MonCat.Colimits.coconeFun

/-- The monoid homomorphism from a given monoid in the diagram to the colimit monoid. -/
def coconeMorphism (j : J) : F.obj j ⟶ colimit F
    where
  toFun := coconeFun F j
  map_one' := Quot.sound (Relation.one _)
  map_mul' x y := Quot.sound (Relation.mul _ _ _)
#align Mon.colimits.cocone_morphism MonCat.Colimits.coconeMorphism

@[simp]
theorem cocone_naturality {j j' : J} (f : j ⟶ j') :
    F.map f ≫ coconeMorphism F j' = coconeMorphism F j :=
  by
  ext
  apply Quot.sound
  apply Relation.Map
#align Mon.colimits.cocone_naturality MonCat.Colimits.cocone_naturality

@[simp]
theorem cocone_naturality_components (j j' : J) (f : j ⟶ j') (x : F.obj j) :
    (coconeMorphism F j') (F.map f x) = (coconeMorphism F j) x := by rw [← cocone_naturality F f];
  rfl
#align Mon.colimits.cocone_naturality_components MonCat.Colimits.cocone_naturality_components

/-- The cocone over the proposed colimit monoid. -/
def colimitCocone : Cocone F where
  pt := colimit F
  ι := { app := coconeMorphism F }
#align Mon.colimits.colimit_cocone MonCat.Colimits.colimitCocone

/-- The function from the free monoid on the diagram to the cone point of any other cocone. -/
@[simp]
def descFunLift (s : Cocone F) : Prequotient F → s.pt
  | of j x => (s.ι.app j) x
  | one => 1
  | mul x y => desc_fun_lift x * desc_fun_lift y
#align Mon.colimits.desc_fun_lift MonCat.Colimits.descFunLift

/-- The function from the colimit monoid to the cone point of any other cocone. -/
def descFun (s : Cocone F) : ColimitType F → s.pt :=
  by
  fapply Quot.lift
  · exact desc_fun_lift F s
  · intro x y r
    induction r <;> try dsimp
    -- refl
    · rfl
    -- symm
    · exact r_ih.symm
    -- trans
    · exact Eq.trans r_ih_h r_ih_k
    -- map
    · simp
    -- mul
    · simp
    -- one
    · simp
    -- mul_1
    · rw [r_ih]
    -- mul_2
    · rw [r_ih]
    -- mul_assoc
    · rw [mul_assoc]
    -- one_mul
    · rw [one_mul]
    -- mul_one
    · rw [mul_one]
#align Mon.colimits.desc_fun MonCat.Colimits.descFun

/-- The monoid homomorphism from the colimit monoid to the cone point of any other cocone. -/
def descMorphism (s : Cocone F) : colimit F ⟶ s.pt
    where
  toFun := descFun F s
  map_one' := rfl
  map_mul' x y := by induction x <;> induction y <;> rfl
#align Mon.colimits.desc_morphism MonCat.Colimits.descMorphism

/-- Evidence that the proposed colimit is the colimit. -/
def colimitIsColimit : IsColimit (colimitCocone F)
    where
  desc s := descMorphism F s
  uniq s m w := by
    ext
    induction x
    induction x
    · have w' :=
        congr_fun (congr_arg (fun f : F.obj x_j ⟶ s.X => (f : F.obj x_j → s.X)) (w x_j)) x_x
      erw [w']
      rfl
    · simp [*]
    · simp [*]
    rfl
#align Mon.colimits.colimit_is_colimit MonCat.Colimits.colimitIsColimit

instance hasColimits_monCat : HasColimits MonCat
    where HasColimitsOfShape J 𝒥 :=
    {
      HasColimit := fun F =>
        has_colimit.mk
          { Cocone := colimit_cocone F
            IsColimit := colimit_is_colimit F } }
#align Mon.colimits.has_colimits_Mon MonCat.Colimits.hasColimits_monCat

end MonCat.Colimits

