/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# The category of commutative rings has all colimits.

This file uses a "pre-automated" approach, just as for
`Mathlib/Algebra/Category/MonCat/Colimits.lean`.
It is a very uniform approach, that conceivably could be synthesised directly
by a tactic that analyses the shape of `CommRing` and `RingHom`.
-/


universe u v

open CategoryTheory Limits


namespace RingCat.Colimits

/-!
We build the colimit of a diagram in `RingCat` by constructing the
free ring on the disjoint union of all the rings in the diagram,
then taking the quotient by the ring laws within each ring,
and the identifications given by the morphisms in the diagram.
-/


variable {J : Type v} [SmallCategory J] (F : J ⥤ RingCat.{v})

/-- An inductive type representing all ring expressions (without Relations)
on a collection of types indexed by the objects of `J`.
-/
inductive Prequotient
  -- There's always `of`
  | of : ∀ (j : J) (_ : F.obj j), Prequotient
  -- Then one generator for each operation
  | zero : Prequotient
  | one : Prequotient
  | neg : Prequotient → Prequotient
  | add : Prequotient → Prequotient → Prequotient
  | mul : Prequotient → Prequotient → Prequotient

instance : Inhabited (Prequotient F) :=
  ⟨Prequotient.zero⟩

open Prequotient

/-- The Relation on `Prequotient` saying when two expressions are equal
because of the ring laws, or
because one element is mapped to another by a morphism in the diagram.
-/
inductive Relation : Prequotient F → Prequotient F → Prop -- Make it an equivalence Relation:
  | refl : ∀ x, Relation x x
  | symm : ∀ (x y) (_ : Relation x y), Relation y x
  | trans : ∀ (x y z) (_ : Relation x y) (_ : Relation y z), Relation x z
  -- There's always a `map` Relation
  | map : ∀ (j j' : J) (f : j ⟶ j') (x : F.obj j),
      Relation (Prequotient.of j' (F.map f x))
        (Prequotient.of j x)
  -- Then one Relation per operation, describing the interaction with `of`
  | zero : ∀ j, Relation (Prequotient.of j 0) zero
  | one : ∀ j, Relation (Prequotient.of j 1) one
  | neg : ∀ (j) (x : F.obj j), Relation (Prequotient.of j (-x)) (neg (Prequotient.of j x))
  | add : ∀ (j) (x y : F.obj j), Relation (Prequotient.of j (x + y))
      (add (Prequotient.of j x) (Prequotient.of j y))
  | mul : ∀ (j) (x y : F.obj j),
      Relation (Prequotient.of j (x * y))
        (mul (Prequotient.of j x) (Prequotient.of j y))
  -- Then one Relation per argument of each operation
  | neg_1 : ∀ (x x') (_ : Relation x x'), Relation (neg x) (neg x')
  | add_1 : ∀ (x x' y) (_ : Relation x x'), Relation (add x y) (add x' y)
  | add_2 : ∀ (x y y') (_ : Relation y y'), Relation (add x y) (add x y')
  | mul_1 : ∀ (x x' y) (_ : Relation x x'), Relation (mul x y) (mul x' y)
  | mul_2 : ∀ (x y y') (_ : Relation y y'), Relation (mul x y) (mul x y')
  -- And one Relation per axiom
  | zero_add : ∀ x, Relation (add zero x) x
  | add_zero : ∀ x, Relation (add x zero) x
  | one_mul : ∀ x, Relation (mul one x) x
  | mul_one : ∀ x, Relation (mul x one) x
  | neg_add_cancel : ∀ x, Relation (add (neg x) x) zero
  | add_comm : ∀ x y, Relation (add x y) (add y x)
  | add_assoc : ∀ x y z, Relation (add (add x y) z) (add x (add y z))
  | mul_assoc : ∀ x y z, Relation (mul (mul x y) z) (mul x (mul y z))
  | left_distrib : ∀ x y z, Relation (mul x (add y z)) (add (mul x y) (mul x z))
  | right_distrib : ∀ x y z, Relation (mul (add x y) z) (add (mul x z) (mul y z))
  | zero_mul : ∀ x, Relation (mul zero x) zero
  | mul_zero : ∀ x, Relation (mul x zero) zero

/-- The setoid corresponding to commutative expressions modulo monoid Relations and identifications.
-/
def colimitSetoid : Setoid (Prequotient F) where
  r := Relation F
  iseqv := ⟨Relation.refl, Relation.symm _ _, Relation.trans _ _ _⟩

attribute [instance] colimitSetoid

/-- The underlying type of the colimit of a diagram in `CommRingCat`.
-/
def ColimitType : Type v :=
  Quotient (colimitSetoid F)

instance ColimitType.instZero : Zero (ColimitType F) where zero := Quotient.mk _ zero

instance ColimitType.instAdd : Add (ColimitType F) where
  add := Quotient.map₂ add <| fun _x x' rx y _y' ry =>
    Setoid.trans (Relation.add_1 _ _ y rx) (Relation.add_2 x' _ _ ry)

instance ColimitType.instNeg : Neg (ColimitType F) where
  neg := Quotient.map neg Relation.neg_1

instance ColimitType.AddGroup : AddGroup (ColimitType F) where
  neg := Quotient.map neg Relation.neg_1
  zero_add := Quotient.ind <| fun _ => Quotient.sound <| Relation.zero_add _
  add_zero := Quotient.ind <| fun _ => Quotient.sound <| Relation.add_zero _
  neg_add_cancel := Quotient.ind <| fun _ => Quotient.sound <| Relation.neg_add_cancel _
  add_assoc := Quotient.ind <| fun _ => Quotient.ind₂ <| fun _ _ =>
    Quotient.sound <| Relation.add_assoc _ _ _
  nsmul := nsmulRec
  zsmul := zsmulRec

instance InhabitedColimitType : Inhabited <| ColimitType F where
  default := 0

instance ColimitType.AddGroupWithOne : AddGroupWithOne (ColimitType F) :=
  { ColimitType.AddGroup F with one := Quotient.mk _ one }

instance : Ring (ColimitType.{v} F) :=
  { ColimitType.AddGroupWithOne F with
    mul := Quot.map₂ Prequotient.mul Relation.mul_2 Relation.mul_1
    one_mul := fun x => Quot.inductionOn x fun _ => Quot.sound <| Relation.one_mul _
    mul_one := fun x => Quot.inductionOn x fun _ => Quot.sound <| Relation.mul_one _
    add_comm := fun x y => Quot.induction_on₂ x y fun _ _ => Quot.sound <| Relation.add_comm _ _
    mul_assoc := fun x y z => Quot.induction_on₃ x y z fun x y z => by
      simp only [(· * ·)]
      exact Quot.sound (Relation.mul_assoc _ _ _)
    mul_zero := fun x => Quot.inductionOn x fun _ => Quot.sound <| Relation.mul_zero _
    zero_mul := fun x => Quot.inductionOn x fun _ => Quot.sound <| Relation.zero_mul _
    left_distrib := fun x y z => Quot.induction_on₃ x y z fun x y z => by
      simp only [(· + ·), (· * ·), Add.add]
      exact Quot.sound (Relation.left_distrib _ _ _)
    right_distrib := fun x y z => Quot.induction_on₃ x y z fun x y z => by
      simp only [(· + ·), (· * ·), Add.add]
      exact Quot.sound (Relation.right_distrib _ _ _) }

@[simp]
theorem quot_zero : Quot.mk Setoid.r zero = (0 : ColimitType F) :=
  rfl

@[simp]
theorem quot_one : Quot.mk Setoid.r one = (1 : ColimitType F) :=
  rfl

@[simp]
theorem quot_neg (x : Prequotient F) :
    Quot.mk Setoid.r (neg x) = -(show ColimitType F from Quot.mk Setoid.r x) :=
  rfl

@[simp]
theorem quot_add (x y) :
    Quot.mk Setoid.r (add x y) =
      (show ColimitType F from Quot.mk _ x) + (show ColimitType F from Quot.mk _ y) :=
  rfl

@[simp]
theorem quot_mul (x y) :
    Quot.mk Setoid.r (mul x y) =
      (show ColimitType F from Quot.mk _ x) * (show ColimitType F from Quot.mk _ y) :=
  rfl

/-- The bundled ring giving the colimit of a diagram. -/
def colimit : RingCat :=
  RingCat.of (ColimitType F)

/-- The function from a given ring in the diagram to the colimit ring. -/
def coconeFun (j : J) (x : F.obj j) : ColimitType F :=
  Quot.mk _ (Prequotient.of j x)

/-- The ring homomorphism from a given ring in the diagram to the colimit
ring. -/
def coconeMorphism (j : J) : F.obj j ⟶ colimit F := ofHom
  { toFun := coconeFun F j
    map_one' := by apply Quot.sound; apply Relation.one
    map_mul' := by intros; apply Quot.sound; apply Relation.mul
    map_zero' := by apply Quot.sound; apply Relation.zero
    map_add' := by intros; apply Quot.sound; apply Relation.add }

@[simp]
theorem cocone_naturality {j j' : J} (f : j ⟶ j') :
    F.map f ≫ coconeMorphism F j' = coconeMorphism F j := by
  ext
  apply Quot.sound
  apply Relation.map

@[simp]
theorem cocone_naturality_components (j j' : J) (f : j ⟶ j') (x : F.obj j) :
    (coconeMorphism F j') (F.map f x) = (coconeMorphism F j) x := by
  rw [← cocone_naturality F f, comp_apply]

/-- The cocone over the proposed colimit ring. -/
def colimitCocone : Cocone F where
  pt := colimit F
  ι := { app := coconeMorphism F }

/-- The function from the free ring on the diagram to the cone point of any other
cocone. -/
@[simp]
def descFunLift (s : Cocone F) : Prequotient F → s.pt
  | Prequotient.of j x => (s.ι.app j) x
  | zero => 0
  | one => 1
  | neg x => -descFunLift s x
  | add x y => descFunLift s x + descFunLift s y
  | mul x y => descFunLift s x * descFunLift s y

/-- The function from the colimit ring to the cone point of any other cocone. -/
def descFun (s : Cocone F) : ColimitType F → s.pt := by
  fapply Quot.lift
  · exact descFunLift F s
  · intro x y r
    induction r with
    | refl => rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
    | map j j' f x => exact RingHom.congr_fun (congrArg Hom.hom <| s.ι.naturality f) x
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
    | neg_add_cancel x => dsimp; rw [neg_add_cancel]
    | add_comm x y => dsimp; rw [add_comm]
    | add_assoc x y z => dsimp; rw [add_assoc]
    | mul_assoc x y z => dsimp; rw [mul_assoc]
    | left_distrib x y z => dsimp; rw [mul_add]
    | right_distrib x y z => dsimp; rw [add_mul]
    | zero_mul x => dsimp; rw [zero_mul]
    | mul_zero x => dsimp; rw [mul_zero]

/-- The ring homomorphism from the colimit ring to the cone point of any other
cocone. -/
def descMorphism (s : Cocone F) : colimit F ⟶ s.pt := ofHom
  { toFun := descFun F s
    map_one' := rfl
    map_zero' := rfl
    map_add' := fun x y ↦ by
      refine Quot.induction_on₂ x y fun a b => ?_
      dsimp [descFun]
      rw [← quot_add]
      rfl
    map_mul' := fun x y ↦ by exact Quot.induction_on₂ x y fun a b => rfl }

/-- Evidence that the proposed colimit is the colimit. -/
def colimitIsColimit : IsColimit (colimitCocone F) where
  desc s := descMorphism F s
  uniq s m w := hom_ext <| RingHom.ext fun x => by
    refine Quot.inductionOn x ?_
    intro x
    induction x with
    | zero => simp
    | one => simp
    | neg x ih => simp [ih]
    | of j x =>
      exact congr_fun (congr_arg (fun f : F.obj j ⟶ s.pt => (f : F.obj j → s.pt)) (w j)) x
    | add x y ih_x ih_y => simp [ih_x, ih_y]
    | mul x y ih_x ih_y => simp [ih_x, ih_y]

instance hasColimits_ringCat : HasColimits RingCat where
  has_colimits_of_shape _ _ :=
    { has_colimit := fun F =>
        HasColimit.mk
          { cocone := colimitCocone F
            isColimit := colimitIsColimit F } }

end RingCat.Colimits

-- [ROBOT VOICE]:
-- You should pretend for now that this file was automatically generated.
-- It follows the same template as colimits in Mon.
/-
`#print comm_ring` in Lean 3 used to say:

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
We build the colimit of a diagram in `CommRingCat` by constructing the
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

instance : Inhabited (Prequotient F) :=
  ⟨Prequotient.zero⟩

open Prequotient

/-- The Relation on `Prequotient` saying when two expressions are equal
because of the commutative ring laws, or
because one element is mapped to another by a morphism in the diagram.
-/
inductive Relation : Prequotient F → Prequotient F → Prop -- Make it an equivalence Relation:
  | refl : ∀ x, Relation x x
  | symm : ∀ (x y) (_ : Relation x y), Relation y x
  | trans : ∀ (x y z) (_ : Relation x y) (_ : Relation y z), Relation x z
  -- There's always a `map` Relation
  | map : ∀ (j j' : J) (f : j ⟶ j') (x : F.obj j),
      Relation (Prequotient.of j' (F.map f x))
        (Prequotient.of j x)
  -- Then one Relation per operation, describing the interaction with `of`
  | zero : ∀ j, Relation (Prequotient.of j 0) zero
  | one : ∀ j, Relation (Prequotient.of j 1) one
  | neg : ∀ (j) (x : F.obj j), Relation (Prequotient.of j (-x)) (neg (Prequotient.of j x))
  | add : ∀ (j) (x y : F.obj j), Relation (Prequotient.of j (x + y))
      (add (Prequotient.of j x) (Prequotient.of j y))
  | mul : ∀ (j) (x y : F.obj j),
      Relation (Prequotient.of j (x * y))
        (mul (Prequotient.of j x) (Prequotient.of j y))
  -- Then one Relation per argument of each operation
  | neg_1 : ∀ (x x') (_ : Relation x x'), Relation (neg x) (neg x')
  | add_1 : ∀ (x x' y) (_ : Relation x x'), Relation (add x y) (add x' y)
  | add_2 : ∀ (x y y') (_ : Relation y y'), Relation (add x y) (add x y')
  | mul_1 : ∀ (x x' y) (_ : Relation x x'), Relation (mul x y) (mul x' y)
  | mul_2 : ∀ (x y y') (_ : Relation y y'), Relation (mul x y) (mul x y')
  -- And one Relation per axiom
  | zero_add : ∀ x, Relation (add zero x) x
  | add_zero : ∀ x, Relation (add x zero) x
  | one_mul : ∀ x, Relation (mul one x) x
  | mul_one : ∀ x, Relation (mul x one) x
  | neg_add_cancel : ∀ x, Relation (add (neg x) x) zero
  | add_comm : ∀ x y, Relation (add x y) (add y x)
  | mul_comm : ∀ x y, Relation (mul x y) (mul y x)
  | add_assoc : ∀ x y z, Relation (add (add x y) z) (add x (add y z))
  | mul_assoc : ∀ x y z, Relation (mul (mul x y) z) (mul x (mul y z))
  | left_distrib : ∀ x y z, Relation (mul x (add y z)) (add (mul x y) (mul x z))
  | right_distrib : ∀ x y z, Relation (mul (add x y) z) (add (mul x z) (mul y z))
  | zero_mul : ∀ x, Relation (mul zero x) zero
  | mul_zero : ∀ x, Relation (mul x zero) zero

/-- The setoid corresponding to commutative expressions modulo monoid Relations and identifications.
-/
def colimitSetoid : Setoid (Prequotient F) where
  r := Relation F
  iseqv := ⟨Relation.refl, Relation.symm _ _, Relation.trans _ _ _⟩

attribute [instance] colimitSetoid

/-- The underlying type of the colimit of a diagram in `CommRingCat`.
-/
def ColimitType : Type v :=
  Quotient (colimitSetoid F)

instance ColimitType.instZero : Zero (ColimitType F) where zero := Quotient.mk _ zero

instance ColimitType.instAdd : Add (ColimitType F) where
  add := Quotient.map₂ add <| fun _x x' rx y _y' ry =>
    Setoid.trans (Relation.add_1 _ _ y rx) (Relation.add_2 x' _ _ ry)

instance ColimitType.instNeg : Neg (ColimitType F) where
  neg := Quotient.map neg Relation.neg_1

instance ColimitType.AddGroup : AddGroup (ColimitType F) where
  neg := Quotient.map neg Relation.neg_1
  zero_add := Quotient.ind <| fun _ => Quotient.sound <| Relation.zero_add _
  add_zero := Quotient.ind <| fun _ => Quotient.sound <| Relation.add_zero _
  neg_add_cancel := Quotient.ind <| fun _ => Quotient.sound <| Relation.neg_add_cancel _
  add_assoc := Quotient.ind <| fun _ => Quotient.ind₂ <| fun _ _ =>
    Quotient.sound <| Relation.add_assoc _ _ _
  nsmul := nsmulRec
  zsmul := zsmulRec

instance InhabitedColimitType : Inhabited <| ColimitType F where
  default := 0

instance ColimitType.AddGroupWithOne : AddGroupWithOne (ColimitType F) :=
  { ColimitType.AddGroup F with one := Quotient.mk _ one }

instance : CommRing (ColimitType.{v} F) :=
  { ColimitType.AddGroupWithOne F with
    mul := Quot.map₂ Prequotient.mul Relation.mul_2 Relation.mul_1
    one_mul := fun x => Quot.inductionOn x fun _ => Quot.sound <| Relation.one_mul _
    mul_one := fun x => Quot.inductionOn x fun _ => Quot.sound <| Relation.mul_one _
    add_comm := fun x y => Quot.induction_on₂ x y fun _ _ => Quot.sound <| Relation.add_comm _ _
    mul_comm := fun x y => Quot.induction_on₂ x y fun _ _ => Quot.sound <| Relation.mul_comm _ _
    mul_assoc := fun x y z => Quot.induction_on₃ x y z fun x y z => by
      simp only [(· * ·)]
      exact Quot.sound (Relation.mul_assoc _ _ _)
    mul_zero := fun x => Quot.inductionOn x fun _ => Quot.sound <| Relation.mul_zero _
    zero_mul := fun x => Quot.inductionOn x fun _ => Quot.sound <| Relation.zero_mul _
    left_distrib := fun x y z => Quot.induction_on₃ x y z fun x y z => by
      simp only [(· + ·), (· * ·), Add.add]
      exact Quot.sound (Relation.left_distrib _ _ _)
    right_distrib := fun x y z => Quot.induction_on₃ x y z fun x y z => by
      simp only [(· + ·), (· * ·), Add.add]
      exact Quot.sound (Relation.right_distrib _ _ _) }

@[simp]
theorem quot_zero : Quot.mk Setoid.r zero = (0 : ColimitType F) :=
  rfl

@[simp]
theorem quot_one : Quot.mk Setoid.r one = (1 : ColimitType F) :=
  rfl

@[simp]
theorem quot_neg (x : Prequotient F) :
    Quot.mk Setoid.r (neg x) = -(show ColimitType F from Quot.mk Setoid.r x) :=
  rfl

-- Porting note: Lean can't see `Quot.mk Setoid.r x` is a `ColimitType F` even with type annotation
-- unless we use `by exact` to change the elaboration order.
@[simp]
theorem quot_add (x y) :
    Quot.mk Setoid.r (add x y) =
      (show ColimitType F from Quot.mk _ x) + (show ColimitType F from Quot.mk _ y) :=
  rfl

-- Porting note: Lean can't see `Quot.mk Setoid.r x` is a `ColimitType F` even with type annotation
-- unless we use `by exact` to change the elaboration order.
@[simp]
theorem quot_mul (x y) :
    Quot.mk Setoid.r (mul x y) =
      (show ColimitType F from Quot.mk _ x) * (show ColimitType F from Quot.mk _ y) :=
  rfl

/-- The bundled commutative ring giving the colimit of a diagram. -/
def colimit : CommRingCat :=
  CommRingCat.of (ColimitType F)

/-- The function from a given commutative ring in the diagram to the colimit commutative ring. -/
def coconeFun (j : J) (x : F.obj j) : ColimitType F :=
  Quot.mk _ (Prequotient.of j x)

/-- The ring homomorphism from a given commutative ring in the diagram to the colimit commutative
ring. -/
def coconeMorphism (j : J) : F.obj j ⟶ colimit F := ofHom <|
  { toFun := coconeFun F j
    map_one' := by apply Quot.sound; apply Relation.one
    map_mul' := by intros; apply Quot.sound; apply Relation.mul
    map_zero' := by apply Quot.sound; apply Relation.zero
    map_add' := by intros; apply Quot.sound; apply Relation.add }

@[simp]
theorem cocone_naturality {j j' : J} (f : j ⟶ j') :
    F.map f ≫ coconeMorphism F j' = coconeMorphism F j := by
  ext
  apply Quot.sound
  apply Relation.map

@[simp]
theorem cocone_naturality_components (j j' : J) (f : j ⟶ j') (x : F.obj j) :
    (coconeMorphism F j') (F.map f x) = (coconeMorphism F j) x := by
  rw [← cocone_naturality F f, comp_apply]

/-- The cocone over the proposed colimit commutative ring. -/
def colimitCocone : Cocone F where
  pt := colimit F
  ι := { app := coconeMorphism F }

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

/-- The function from the colimit commutative ring to the cone point of any other cocone. -/
def descFun (s : Cocone F) : ColimitType F → s.pt := by
  fapply Quot.lift
  · exact descFunLift F s
  · intro x y r
    induction r with
    | refl => rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
    | map j j' f x => exact RingHom.congr_fun (congrArg Hom.hom <| s.ι.naturality f) x
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
    | neg_add_cancel x => dsimp; rw [neg_add_cancel]
    | add_comm x y => dsimp; rw [add_comm]
    | mul_comm x y => dsimp; rw [mul_comm]
    | add_assoc x y z => dsimp; rw [add_assoc]
    | mul_assoc x y z => dsimp; rw [mul_assoc]
    | left_distrib x y z => dsimp; rw [mul_add]
    | right_distrib x y z => dsimp; rw [add_mul]
    | zero_mul x => dsimp; rw [zero_mul]
    | mul_zero x => dsimp; rw [mul_zero]

/-- The ring homomorphism from the colimit commutative ring to the cone point of any other
cocone. -/
def descMorphism (s : Cocone F) : colimit F ⟶ s.pt := ofHom
  { toFun := descFun F s
    map_one' := rfl
    map_zero' := rfl
    map_add' := fun x y ↦ by
      refine Quot.induction_on₂ x y fun a b => ?_
      dsimp [descFun]
      rw [← quot_add]
      rfl
    map_mul' := fun x y ↦ by exact Quot.induction_on₂ x y fun a b => rfl }

/-- Evidence that the proposed colimit is the colimit. -/
def colimitIsColimit : IsColimit (colimitCocone F) where
  desc := fun s ↦ descMorphism F s
  uniq := fun s m w ↦ hom_ext <| RingHom.ext fun x => by
    refine Quot.inductionOn x ?_
    intro x
    induction x with
    | zero => simp
    | one => simp
    | neg x ih => simp [ih]
    | of j x =>
      exact congr_fun (congr_arg (fun f : F.obj j ⟶ s.pt => (f : F.obj j → s.pt)) (w j)) x
    | add x y ih_x ih_y => simp [ih_x, ih_y]
    | mul x y ih_x ih_y => simp [ih_x, ih_y]

instance hasColimits_commRingCat : HasColimits CommRingCat where
  has_colimits_of_shape _ _ :=
    { has_colimit := fun F =>
        HasColimit.mk
          { cocone := colimitCocone F
            isColimit := colimitIsColimit F } }

end CommRingCat.Colimits
