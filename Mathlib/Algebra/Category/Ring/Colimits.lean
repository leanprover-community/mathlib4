/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module algebra.category.Ring.colimits
! leanprover-community/mathlib commit 70fd9563a21e7b963887c9360bd29b2393e6225a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Category.Ring.Basic
import Mathbin.CategoryTheory.Limits.HasLimits
import Mathbin.CategoryTheory.ConcreteCategory.Elementwise

/-!
# The category of commutative rings has all colimits.

This file uses a "pre-automated" approach, just as for `Mon/colimits.lean`.
It is a very uniform approach, that conceivably could be synthesised directly
by a tactic that analyses the shape of `comm_ring` and `ring_hom`.
-/


universe u v

open CategoryTheory

open CategoryTheory.Limits

-- [ROBOT VOICE]:
-- You should pretend for now that this file was automatically generated.
-- It follows the same template as colimits in Mon.
/-
`#print comm_ring` says:

structure comm_ring : Type u → Type u
fields:
comm_ring.zero : Π (α : Type u) [c : comm_ring α], α
comm_ring.one : Π (α : Type u) [c : comm_ring α], α
comm_ring.neg : Π {α : Type u} [c : comm_ring α], α → α
comm_ring.add : Π {α : Type u} [c : comm_ring α], α → α → α
comm_ring.mul : Π {α : Type u} [c : comm_ring α], α → α → α

comm_ring.zero_add : ∀ {α : Type u} [c : comm_ring α] (a : α), 0 + a = a
comm_ring.add_zero : ∀ {α : Type u} [c : comm_ring α] (a : α), a + 0 = a
comm_ring.one_mul : ∀ {α : Type u} [c : comm_ring α] (a : α), 1 * a = a
comm_ring.mul_one : ∀ {α : Type u} [c : comm_ring α] (a : α), a * 1 = a
comm_ring.add_left_neg : ∀ {α : Type u} [c : comm_ring α] (a : α), -a + a = 0
comm_ring.add_comm : ∀ {α : Type u} [c : comm_ring α] (a b : α), a + b = b + a
comm_ring.mul_comm : ∀ {α : Type u} [c : comm_ring α] (a b : α), a * b = b * a
comm_ring.add_assoc : ∀ {α : Type u} [c : comm_ring α] (a b c_1 : α), a + b + c_1 = a + (b + c_1)
comm_ring.mul_assoc : ∀ {α : Type u} [c : comm_ring α] (a b c_1 : α), a * b * c_1 = a * (b * c_1)
comm_ring.left_distrib : ∀ {α : Type u} [c : comm_ring α] (a b c_1 : α),
                                                            a * (b + c_1) = a * b + a * c_1
comm_ring.right_distrib : ∀ {α : Type u} [c : comm_ring α] (a b c_1 : α),
                                                            (a + b) * c_1 = a * c_1 + b * c_1
-/
namespace CommRingCat.Colimits

/-!
We build the colimit of a diagram in `CommRing` by constructing the
free commutative ring on the disjoint union of all the commutative rings in the diagram,
then taking the quotient by the commutative ring laws within each commutative ring,
and the identifications given by the morphisms in the diagram.
-/


variable {J : Type v} [SmallCategory J] (F : J ⥤ CommRingCat.{v})

/-- An inductive type representing all commutative ring expressions (without relations)
on a collection of types indexed by the objects of `J`.
-/
inductive Prequotient-- There's always `of`

  | of : ∀ (j : J) (x : F.obj j), prequotient-- Then one generator for each operation

  | zero : prequotient
  | one : prequotient
  | neg : prequotient → prequotient
  | add : prequotient → prequotient → prequotient
  | mul : prequotient → prequotient → prequotient
#align CommRing.colimits.prequotient CommRingCat.Colimits.Prequotient

instance : Inhabited (Prequotient F) :=
  ⟨Prequotient.zero⟩

open Prequotient

/-- The relation on `prequotient` saying when two expressions are equal
because of the commutative ring laws, or
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
      relation (of j' (F.map f x))
        (of j x)-- Then one relation per operation, describing the interaction with `of`

  | zero : ∀ j, relation (of j 0) zero
  | one : ∀ j, relation (of j 1) one
  | neg : ∀ (j) (x : F.obj j), relation (of j (-x)) (neg (of j x))
  | add : ∀ (j) (x y : F.obj j), relation (of j (x + y)) (add (of j x) (of j y))
  |
  mul :
    ∀ (j) (x y : F.obj j),
      relation (of j (x * y))
        (mul (of j x) (of j y))-- Then one relation per argument of each operation

  | neg_1 : ∀ (x x') (r : relation x x'), relation (neg x) (neg x')
  | add_1 : ∀ (x x' y) (r : relation x x'), relation (add x y) (add x' y)
  | add_2 : ∀ (x y y') (r : relation y y'), relation (add x y) (add x y')
  | mul_1 : ∀ (x x' y) (r : relation x x'), relation (mul x y) (mul x' y)
  |
  mul_2 : ∀ (x y y') (r : relation y y'), relation (mul x y) (mul x y')-- And one relation per axiom

  | zero_add : ∀ x, relation (add zero x) x
  | add_zero : ∀ x, relation (add x zero) x
  | one_mul : ∀ x, relation (mul one x) x
  | mul_one : ∀ x, relation (mul x one) x
  | add_left_neg : ∀ x, relation (add (neg x) x) zero
  | add_comm : ∀ x y, relation (add x y) (add y x)
  | mul_comm : ∀ x y, relation (mul x y) (mul y x)
  | add_assoc : ∀ x y z, relation (add (add x y) z) (add x (add y z))
  | mul_assoc : ∀ x y z, relation (mul (mul x y) z) (mul x (mul y z))
  | left_distrib : ∀ x y z, relation (mul x (add y z)) (add (mul x y) (mul x z))
  | right_distrib : ∀ x y z, relation (mul (add x y) z) (add (mul x z) (mul y z))
#align CommRing.colimits.relation CommRingCat.Colimits.Relation

/-- The setoid corresponding to commutative expressions modulo monoid relations and identifications.
-/
def colimitSetoid : Setoid (Prequotient F)
    where
  R := Relation F
  iseqv := ⟨Relation.refl, Relation.symm, Relation.trans⟩
#align CommRing.colimits.colimit_setoid CommRingCat.Colimits.colimitSetoid

attribute [instance] colimit_setoid

/-- The underlying type of the colimit of a diagram in `CommRing`.
-/
def ColimitType : Type v :=
  Quotient (colimitSetoid F)deriving Inhabited
#align CommRing.colimits.colimit_type CommRingCat.Colimits.ColimitType

instance : AddGroup (ColimitType F)
    where
  zero := Quot.mk _ zero
  neg := by
    fapply @Quot.lift
    · intro x
      exact Quot.mk _ (neg x)
    · intro x x' r
      apply Quot.sound
      exact relation.neg_1 _ _ r
  add := by
    fapply @Quot.lift _ _ (colimit_type F → colimit_type F)
    · intro x
      fapply @Quot.lift
      · intro y
        exact Quot.mk _ (add x y)
      · intro y y' r
        apply Quot.sound
        exact relation.add_2 _ _ _ r
    · intro x x' r
      funext y
      induction y
      dsimp
      apply Quot.sound
      · exact relation.add_1 _ _ _ r
      · rfl
  zero_add x := by
    induction x
    dsimp
    apply Quot.sound
    apply relation.zero_add
    rfl
  add_zero x := by
    induction x
    dsimp
    apply Quot.sound
    apply relation.add_zero
    rfl
  add_left_neg x := by
    induction x
    dsimp
    apply Quot.sound
    apply relation.add_left_neg
    rfl
  add_assoc x y z := by
    induction x
    induction y
    induction z
    dsimp
    apply Quot.sound
    apply relation.add_assoc
    rfl
    rfl
    rfl

instance : AddGroupWithOne (ColimitType F) :=
  { ColimitType.addGroup F with one := Quot.mk _ one }

instance : CommRing (ColimitType F) :=
  { ColimitType.addGroupWithOne F with
    one := Quot.mk _ one
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
    one_mul := fun x => by
      induction x
      dsimp
      apply Quot.sound
      apply relation.one_mul
      rfl
    mul_one := fun x => by
      induction x
      dsimp
      apply Quot.sound
      apply relation.mul_one
      rfl
    add_comm := fun x y => by
      induction x
      induction y
      dsimp
      apply Quot.sound
      apply relation.add_comm
      rfl
      rfl
    mul_comm := fun x y => by
      induction x
      induction y
      dsimp
      apply Quot.sound
      apply relation.mul_comm
      rfl
      rfl
    add_assoc := fun x y z => by
      induction x
      induction y
      induction z
      dsimp
      apply Quot.sound
      apply relation.add_assoc
      rfl
      rfl
      rfl
    mul_assoc := fun x y z => by
      induction x
      induction y
      induction z
      dsimp
      apply Quot.sound
      apply relation.mul_assoc
      rfl
      rfl
      rfl
    left_distrib := fun x y z => by
      induction x
      induction y
      induction z
      dsimp
      apply Quot.sound
      apply relation.left_distrib
      rfl
      rfl
      rfl
    right_distrib := fun x y z => by
      induction x
      induction y
      induction z
      dsimp
      apply Quot.sound
      apply relation.right_distrib
      rfl
      rfl
      rfl }

@[simp]
theorem quot_zero : Quot.mk Setoid.r zero = (0 : ColimitType F) :=
  rfl
#align CommRing.colimits.quot_zero CommRingCat.Colimits.quot_zero

@[simp]
theorem quot_one : Quot.mk Setoid.r one = (1 : ColimitType F) :=
  rfl
#align CommRing.colimits.quot_one CommRingCat.Colimits.quot_one

@[simp]
theorem quot_neg (x) : Quot.mk Setoid.r (neg x) = (-Quot.mk Setoid.r x : ColimitType F) :=
  rfl
#align CommRing.colimits.quot_neg CommRingCat.Colimits.quot_neg

@[simp]
theorem quot_add (x y) :
    Quot.mk Setoid.r (add x y) = (Quot.mk Setoid.r x + Quot.mk Setoid.r y : ColimitType F) :=
  rfl
#align CommRing.colimits.quot_add CommRingCat.Colimits.quot_add

@[simp]
theorem quot_mul (x y) :
    Quot.mk Setoid.r (mul x y) = (Quot.mk Setoid.r x * Quot.mk Setoid.r y : ColimitType F) :=
  rfl
#align CommRing.colimits.quot_mul CommRingCat.Colimits.quot_mul

/-- The bundled commutative ring giving the colimit of a diagram. -/
def colimit : CommRingCat :=
  CommRingCat.of (ColimitType F)
#align CommRing.colimits.colimit CommRingCat.Colimits.colimit

/-- The function from a given commutative ring in the diagram to the colimit commutative ring. -/
def coconeFun (j : J) (x : F.obj j) : ColimitType F :=
  Quot.mk _ (of j x)
#align CommRing.colimits.cocone_fun CommRingCat.Colimits.coconeFun

/-- The ring homomorphism from a given commutative ring in the diagram to the colimit commutative
ring. -/
def coconeMorphism (j : J) : F.obj j ⟶ colimit F
    where
  toFun := coconeFun F j
  map_one' := by apply Quot.sound <;> apply relation.one
  map_mul' := by intros <;> apply Quot.sound <;> apply relation.mul
  map_zero' := by apply Quot.sound <;> apply relation.zero
  map_add' := by intros <;> apply Quot.sound <;> apply relation.add
#align CommRing.colimits.cocone_morphism CommRingCat.Colimits.coconeMorphism

@[simp]
theorem cocone_naturality {j j' : J} (f : j ⟶ j') :
    F.map f ≫ coconeMorphism F j' = coconeMorphism F j :=
  by
  ext
  apply Quot.sound
  apply Relation.Map
#align CommRing.colimits.cocone_naturality CommRingCat.Colimits.cocone_naturality

@[simp]
theorem cocone_naturality_components (j j' : J) (f : j ⟶ j') (x : F.obj j) :
    (coconeMorphism F j') (F.map f x) = (coconeMorphism F j) x :=
  by
  rw [← cocone_naturality F f]
  rfl
#align CommRing.colimits.cocone_naturality_components CommRingCat.Colimits.cocone_naturality_components

/-- The cocone over the proposed colimit commutative ring. -/
def colimitCocone : Cocone F where
  pt := colimit F
  ι := { app := coconeMorphism F }
#align CommRing.colimits.colimit_cocone CommRingCat.Colimits.colimitCocone

/-- The function from the free commutative ring on the diagram to the cone point of any other
cocone. -/
@[simp]
def descFunLift (s : Cocone F) : Prequotient F → s.pt
  | of j x => (s.ι.app j) x
  | zero => 0
  | one => 1
  | neg x => -desc_fun_lift x
  | add x y => desc_fun_lift x + desc_fun_lift y
  | mul x y => desc_fun_lift x * desc_fun_lift y
#align CommRing.colimits.desc_fun_lift CommRingCat.Colimits.descFunLift

/-- The function from the colimit commutative ring to the cone point of any other cocone. -/
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
    -- zero
    · simp
    -- one
    · simp
    -- neg
    · simp
    -- add
    · simp
    -- mul
    · simp
    -- neg_1
    · rw [r_ih]
    -- add_1
    · rw [r_ih]
    -- add_2
    · rw [r_ih]
    -- mul_1
    · rw [r_ih]
    -- mul_2
    · rw [r_ih]
    -- zero_add
    · rw [zero_add]
    -- add_zero
    · rw [add_zero]
    -- one_mul
    · rw [one_mul]
    -- mul_one
    · rw [mul_one]
    -- add_left_neg
    · rw [add_left_neg]
    -- add_comm
    · rw [add_comm]
    -- mul_comm
    · rw [mul_comm]
    -- add_assoc
    · rw [add_assoc]
    -- mul_assoc
    · rw [mul_assoc]
    -- left_distrib
    · rw [left_distrib]
    -- right_distrib
    · rw [right_distrib]
#align CommRing.colimits.desc_fun CommRingCat.Colimits.descFun

/-- The ring homomorphism from the colimit commutative ring to the cone point of any other
cocone. -/
def descMorphism (s : Cocone F) : colimit F ⟶ s.pt
    where
  toFun := descFun F s
  map_one' := rfl
  map_zero' := rfl
  map_add' x y := by induction x <;> induction y <;> rfl
  map_mul' x y := by induction x <;> induction y <;> rfl
#align CommRing.colimits.desc_morphism CommRingCat.Colimits.descMorphism

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
    · simp
    · simp
    · simp [*]
    · simp [*]
    · simp [*]
    rfl
#align CommRing.colimits.colimit_is_colimit CommRingCat.Colimits.colimitIsColimit

instance hasColimits_commRingCat : HasColimits CommRingCat
    where HasColimitsOfShape J 𝒥 :=
    {
      HasColimit := fun F =>
        has_colimit.mk
          { Cocone := colimit_cocone F
            IsColimit := colimit_is_colimit F } }
#align CommRing.colimits.has_colimits_CommRing CommRingCat.Colimits.hasColimits_commRingCat

end CommRingCat.Colimits

