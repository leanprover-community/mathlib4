/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module algebra.category.Ring.colimits
! leanprover-community/mathlib commit 70fd9563a21e7b963887c9360bd29b2393e6225a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.ConcreteCategory.Elementwise

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

/-- An inductive type representing all commutative ring expressions (without Relations)
on a collection of types indexed by the objects of `J`.
-/
inductive Prequotient -- There's always `of`
  | of : ∀ (j : J) (_ : F.obj j), Prequotient -- Then one generator for each operation
  | zero : Prequotient
  | one : Prequotient
  | neg : Prequotient → Prequotient
  | add : Prequotient → Prequotient → Prequotient
  | mul : Prequotient → Prequotient → Prequotient
set_option linter.uppercaseLean3 false
#align CommRing.colimits.prequotient CommRingCat.Colimits.Prequotient

instance : Inhabited (Prequotient F) :=
  ⟨Prequotient.zero⟩

open Prequotient

/-- The Relation on `Prequotient` saying when two expressions are equal
because of the commutative ring laws, or
because one element is mapped to another by a morphism in the diagram.
-/
inductive Relation : Prequotient F → Prequotient F → Prop-- Make it an equivalence Relation:
  | refl : ∀ x, Relation x x
  | symm : ∀ (x y) (_ : Relation x y), Relation y x
  | trans : ∀ (x y z) (_ : Relation x y) (_ : Relation y z), Relation x z -- There's always a `map` Relation
  | map : ∀ (j j' : J) (f : j ⟶ j') (x : F.obj j),
      Relation (Prequotient.of j' (F.map f x))
        (Prequotient.of j x)-- Then one Relation per operation, describing the interaction with `of`
  | zero : ∀ j, Relation (Prequotient.of j 0) zero
  | one : ∀ j, Relation (Prequotient.of j 1) one
  | neg : ∀ (j) (x : F.obj j), Relation (Prequotient.of j (-x)) (neg (Prequotient.of j x))
  | add : ∀ (j) (x y : F.obj j), Relation (Prequotient.of j (x + y))
      (add (Prequotient.of j x) (Prequotient.of j y))
  | mul : ∀ (j) (x y : F.obj j),
      Relation (Prequotient.of j (x * y))
        (mul (Prequotient.of j x) (Prequotient.of j y))-- Then one Relation per argument of each operation
  | neg_1 : ∀ (x x') (_ : Relation x x'), Relation (neg x) (neg x')
  | add_1 : ∀ (x x' y) (_ : Relation x x'), Relation (add x y) (add x' y)
  | add_2 : ∀ (x y y') (_ : Relation y y'), Relation (add x y) (add x y')
  | mul_1 : ∀ (x x' y) (_ : Relation x x'), Relation (mul x y) (mul x' y)
  | mul_2 : ∀ (x y y') (_ : Relation y y'), Relation (mul x y) (mul x y')-- And one Relation per axiom
  | zero_add : ∀ x, Relation (add zero x) x
  | add_zero : ∀ x, Relation (add x zero) x
  | one_mul : ∀ x, Relation (mul one x) x
  | mul_one : ∀ x, Relation (mul x one) x
  | add_left_neg : ∀ x, Relation (add (neg x) x) zero
  | add_comm : ∀ x y, Relation (add x y) (add y x)
  | mul_comm : ∀ x y, Relation (mul x y) (mul y x)
  | add_assoc : ∀ x y z, Relation (add (add x y) z) (add x (add y z))
  | mul_assoc : ∀ x y z, Relation (mul (mul x y) z) (mul x (mul y z))
  | left_distrib : ∀ x y z, Relation (mul x (add y z)) (add (mul x y) (mul x z))
  | right_distrib : ∀ x y z, Relation (mul (add x y) z) (add (mul x z) (mul y z))
#align CommRing.colimits.Relation CommRingCat.Colimits.Relation

/-- The setoid corresponding to commutative expressions modulo monoid Relations and identifications.
-/
def colimitSetoid : Setoid (Prequotient F) where
  r := Relation F
  iseqv := ⟨Relation.refl, Relation.symm _ _, Relation.trans _ _ _⟩
#align CommRing.colimits.colimit_setoid CommRingCat.Colimits.colimitSetoid

attribute [instance] colimitSetoid

/-- The underlying type of the colimit of a diagram in `CommRing`.
-/
def ColimitType : Type v :=
  Quotient (colimitSetoid F)
#align CommRing.colimits.colimit_type CommRingCat.Colimits.ColimitType

-- Porting note : failed to derive `Inhabited` instance
instance InhabitedColimitType : Inhabited <| ColimitType F where
  default := Quot.mk _ zero

instance ColimitType.AddGroup : AddGroup (ColimitType F) where
  zero := Quot.mk _ zero
  neg := by
    fapply @Quot.lift
    · intro x
      exact Quot.mk _ (neg x)
    · intro x x' r
      apply Quot.sound
      exact Relation.neg_1 _ _ r
  add := by
    fapply @Quot.lift _ _ (ColimitType F → ColimitType F)
    · intro x
      fapply @Quot.lift
      · intro y
        exact Quot.mk _ (add x y)
      · intro y y' r
        apply Quot.sound
        exact Relation.add_2 _ _ _ r
    · intro x x' r
      funext y
      refine Quot.inductionOn y ?_
      exact fun _ => Quot.sound (Relation.add_1 _ _ _ r)
  zero_add x := Quot.inductionOn x fun _ => Quot.sound (Relation.zero_add _)
  add_zero x := Quot.inductionOn x fun _ => Quot.sound (Relation.add_zero _)
  add_left_neg := Quot.ind fun x => by
    simp only [(. + .)]
    exact Quot.sound (Relation.add_left_neg x)
  add_assoc x y z := by
    refine Quot.induction_on₃ x y z (fun a b c => ?_)
    simp only [(. + .)]
    apply Quot.sound
    apply Relation.add_assoc

instance ColimitType.AddGroupWithOne : AddGroupWithOne (ColimitType F) :=
  { ColimitType.AddGroup F with one := Quot.mk _ one }

-- Porting note : In Lean 4, `Ring` needs a proof of `mul_zero` and `zero_mul`, these are not
-- entirely obvious from `Relation F`. So I first prove that `ColimitType F` is such that
-- `a + b = a + c → b = c`. Then prove that `a * 0 + a * 0 = a * 0 + 0` hence `a * 0 = 0`.
-- In `mathlib3`, `ring` axioms do not include `mul_zero` and `zero_mul`, so this is not necessary.
-- This might not be the best solution. For example, one can add addition axioms to `Relation F`.
instance : IsLeftCancelAdd (ColimitType F) where
  add_left_cancel := fun a b c => Quot.induction_on₃ a b c fun a b c h => by
    simp only [(. + .), Add.add] at h ⊢
    have h1 := Relation.add_2 (neg a) (add a b) (add a c) <| Quotient.exact h
    have h21 : Relation F (add (neg a) (add a b)) (add (add (neg a) a) b) :=
      (Relation.add_assoc (neg a) a b).symm
    have h22 : Relation F (add (add (neg a) a) b) b :=
      Relation.trans _ _ _ (Relation.add_1 _ _ _ (Relation.add_left_neg _)) (Relation.zero_add _)
    have h31 : Relation F (add (neg a) (add a c)) (add (add (neg a) a) c) :=
      (Relation.add_assoc (neg a) a c).symm
    have h32 : Relation F (add (add (neg a) a) c) c :=
      Relation.trans _ _ _ (Relation.add_1 _ _ _ (Relation.add_left_neg _)) (Relation.zero_add _)
    exact Quot.sound (Relation.trans _ _ _
      (Relation.trans _ _ _
        (Relation.trans _ _ _
          (Relation.trans _ _ _ h1 h31) h32).symm h21) h22).symm

instance ColimitType.Mul : Mul (ColimitType.{v} F) where
  mul := Quot.map₂ Prequotient.mul Relation.mul_2 Relation.mul_1

instance ColimitType.LeftDistribClass : LeftDistribClass (ColimitType.{v} F) where
  left_distrib := fun x y z => Quot.induction_on₃ x y z fun x y z => by
    simp only [(. + .), (. * .), Add.add]
    exact Quot.sound (Relation.left_distrib _ _ _)

instance ColimitType.RightDistribClass : RightDistribClass (ColimitType.{v} F) where
  right_distrib := fun x y z => Quot.induction_on₃ x y z fun x y z => by
    simp only [(. + .), (. * .), Add.add]
    exact Quot.sound (Relation.right_distrib _ _ _)

instance : CommRing (ColimitType.{v} F) :=
  { ColimitType.AddGroupWithOne F, ColimitType.Mul F, ColimitType.LeftDistribClass F,
      ColimitType.RightDistribClass F with
    one_mul := fun x => Quot.inductionOn x fun x => Quot.sound <| Relation.one_mul _
    mul_one := fun x => Quot.inductionOn x fun x => Quot.sound <| Relation.mul_one _
    add_comm := fun x y => Quot.induction_on₂ x y fun x y => Quot.sound <| Relation.add_comm _ _
    mul_comm := fun x y => Quot.induction_on₂ x y fun x y => Quot.sound <| Relation.mul_comm _ _
    add_assoc := fun x y z => Quot.induction_on₃ x y z fun x y z => by
      simp only [(. + .), Add.add]
      exact Quot.sound (Relation.add_assoc _ _ _)
    mul_assoc := fun x y z => Quot.induction_on₃ x y z fun x y z => by
      simp only [(. * .)]
      exact Quot.sound (Relation.mul_assoc _ _ _)
    mul_zero := fun a => add_left_cancel (a := a * 0) (b := a * 0) (c := 0) <|
      by simp_rw [add_zero, ←mul_add, zero_add]
    zero_mul := fun a => add_left_cancel (a := 0 * a) (b := 0 * a) (c := 0) <|
      by simp_rw [add_zero, ←add_mul, zero_add] }

@[simp]
theorem quot_zero : Quot.mk Setoid.r zero = (0 : ColimitType F) :=
  rfl
#align CommRing.colimits.quot_zero CommRingCat.Colimits.quot_zero

@[simp]
theorem quot_one : Quot.mk Setoid.r one = (1 : ColimitType F) :=
  rfl
#align CommRing.colimits.quot_one CommRingCat.Colimits.quot_one

@[simp]
theorem quot_neg (x : Prequotient F) :
-- Porting note : Lean can't see `Quot.mk Setoid.r x` is a `ColimitType F` even with type annotation
-- so use `Neg.neg (α := ColimitType F)` to tell Lean negation happens inside `ColimitType F`.
  (Quot.mk Setoid.r (neg x) : ColimitType F) = Neg.neg (α := ColimitType F) (Quot.mk Setoid.r x) :=
  rfl
#align CommRing.colimits.quot_neg CommRingCat.Colimits.quot_neg

-- Porting note : Lean can't see `Quot.mk Setoid.r x` is a `ColimitType F` even with type annotation
-- so use `Add.add (α := ColimitType F)` to tell Lean addition happens inside `ColimitType F`.
@[simp]
theorem quot_add (x y) :
    Quot.mk Setoid.r (add x y) = Add.add (α := ColimitType F) (Quot.mk _ x) (Quot.mk _ y) :=
  rfl
#align CommRing.colimits.quot_add CommRingCat.Colimits.quot_add

-- Porting note : Lean can't see `Quot.mk Setoid.r x` is a `ColimitType F` even with type annotation
-- so use `Mul.mul (α := ColimitType F)` to tell Lean multiplication happens inside `ColimitType F`.
@[simp]
theorem quot_mul (x y) :
    Quot.mk Setoid.r (mul x y) = Mul.mul (α := ColimitType F) (Quot.mk _ x) (Quot.mk _ y) :=
  rfl
#align CommRing.colimits.quot_mul CommRingCat.Colimits.quot_mul

/-- The bundled commutative ring giving the colimit of a diagram. -/
def colimit : CommRingCat :=
  CommRingCat.of (ColimitType F)
#align CommRing.colimits.colimit CommRingCat.Colimits.colimit

/-- The function from a given commutative ring in the diagram to the colimit commutative ring. -/
def coconeFun (j : J) (x : F.obj j) : ColimitType F :=
  Quot.mk _ (Prequotient.of j x)
#align CommRing.colimits.cocone_fun CommRingCat.Colimits.coconeFun

/-- The ring homomorphism from a given commutative ring in the diagram to the colimit commutative
ring. -/
def coconeMorphism (j : J) : F.obj j ⟶ colimit F where
  toFun := coconeFun F j
  map_one' := by apply Quot.sound ; apply Relation.one
  map_mul' := by intros ; apply Quot.sound ; apply Relation.mul
  map_zero' := by apply Quot.sound ; apply Relation.zero
  map_add' := by intros ; apply Quot.sound ; apply Relation.add
#align CommRing.colimits.cocone_morphism CommRingCat.Colimits.coconeMorphism

@[simp]
theorem cocone_naturality {j j' : J} (f : j ⟶ j') :
    F.map f ≫ coconeMorphism F j' = coconeMorphism F j := by
  ext
  apply Quot.sound
  apply Relation.map
#align CommRing.colimits.cocone_naturality CommRingCat.Colimits.cocone_naturality

@[simp]
theorem cocone_naturality_components (j j' : J) (f : j ⟶ j') (x : F.obj j) :
    (coconeMorphism F j') (F.map f x) = (coconeMorphism F j) x := by
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
  | Prequotient.of j x => (s.ι.app j) x
  | zero => 0
  | one => 1
  | neg x => -descFunLift s x
  | add x y => descFunLift s x + descFunLift s y
  | mul x y => descFunLift s x * descFunLift s y
#align CommRing.colimits.desc_fun_lift CommRingCat.Colimits.descFunLift

/-- The function from the colimit commutative ring to the cone point of any other cocone. -/
def descFun (s : Cocone F) : ColimitType F → s.pt := by
  fapply Quot.lift
  · exact descFunLift F s
  · intro x y r
    induction r with
    | refl => rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
    | map j j' f x => exact RingHom.congr_fun (s.ι.naturality f) x
    | zero j => simp
    | one j => simp
    | neg j x => simp
    | add j x y => simp
    | mul j x y => simp
    | neg_1 x x' r ih => dsimp; rw [ih]
    | add_1 x x' y r ih => dsimp; rw [ih]
    | add_2 x y y' r ih => dsimp; rw [ih]
    | mul_1 x x' y r ih => dsimp; rw [ih]
    | mul_2 x y y' r ih => dsimp; rw [ih]
    | zero_add x => dsimp; rw [zero_add]
    | add_zero x => dsimp; rw [add_zero]
    | one_mul x => dsimp; rw [one_mul]
    | mul_one x => dsimp; rw [mul_one]
    | add_left_neg x => dsimp; rw [add_left_neg]
    | add_comm x y => dsimp; rw [add_comm]
    | mul_comm x y => dsimp; rw [mul_comm]
    | add_assoc x y z => dsimp; rw [add_assoc]
    | mul_assoc x y z => dsimp; rw [mul_assoc]
    | left_distrib x y z => dsimp; rw [mul_add]
    | right_distrib x y z => dsimp; rw [add_mul]
#align CommRing.colimits.desc_fun CommRingCat.Colimits.descFun

/-- The ring homomorphism from the colimit commutative ring to the cone point of any other
cocone. -/
def descMorphism (s : Cocone F) : colimit F ⟶ s.pt where
  toFun := descFun F s
  map_one' := rfl
  map_zero' := rfl
  map_add' x y := by
    refine Quot.induction_on₂ x y fun a b => ?_
    dsimp [descFun, (. + .)]
    rw [←quot_add]
    rfl
  map_mul' x y := by exact Quot.induction_on₂ x y fun a b => rfl
#align CommRing.colimits.desc_morphism CommRingCat.Colimits.descMorphism

/-- Evidence that the proposed colimit is the colimit. -/
def colimitIsColimit : IsColimit (colimitCocone F) where
  desc s := descMorphism F s
  uniq s m w := by
    ext x
    refine Quot.inductionOn x ?_
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
