/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.ConcreteCategory.Elementwise

#align_import algebra.category.Ring.colimits from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# The category of commutative rings has all colimits.

This file uses a "pre-automated" approach, just as for
`Mathlib/Algebra/Category/MonCat/Colimits.lean`.
It is a very uniform approach, that conceivably could be synthesised directly
by a tactic that analyses the shape of `CommRing` and `RingHom`.
-/


universe u v

open CategoryTheory

open CategoryTheory.Limits

-- [ROBOT VOICE]:
-- You should pretend for now that this file was automatically generated.
-- It follows the same template as colimits in Mon.
/-
`#print comm_ring` used to say:

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
set_option linter.uppercaseLean3 false
#align CommRing.colimits.prequotient CommRingCat.Colimits.Prequotient

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
  | add_left_neg : ∀ x, Relation (add (neg x) x) zero
  | add_comm : ∀ x y, Relation (add x y) (add y x)
  | mul_comm : ∀ x y, Relation (mul x y) (mul y x)
  | add_assoc : ∀ x y z, Relation (add (add x y) z) (add x (add y z))
  | mul_assoc : ∀ x y z, Relation (mul (mul x y) z) (mul x (mul y z))
  | left_distrib : ∀ x y z, Relation (mul x (add y z)) (add (mul x y) (mul x z))
  | right_distrib : ∀ x y z, Relation (mul (add x y) z) (add (mul x z) (mul y z))
  | zero_mul : ∀ x, Relation (mul zero x) zero
  | mul_zero : ∀ x, Relation (mul x zero) zero
#align CommRing.colimits.Relation CommRingCat.Colimits.Relation

/-- The setoid corresponding to commutative expressions modulo monoid Relations and identifications.
-/
def colimitSetoid : Setoid (Prequotient F) where
  r := Relation F
  iseqv := ⟨Relation.refl, Relation.symm _ _, Relation.trans _ _ _⟩
#align CommRing.colimits.colimit_setoid CommRingCat.Colimits.colimitSetoid

attribute [instance] colimitSetoid

/-- The underlying type of the colimit of a diagram in `CommRingCat`.
-/
def ColimitType : Type v :=
  Quotient (colimitSetoid F)
#align CommRing.colimits.colimit_type CommRingCat.Colimits.ColimitType

instance ColimitType.AddGroup : AddGroup (ColimitType F) where
  zero := Quotient.mk _ zero
  neg := Quotient.map neg Relation.neg_1
  add := Quotient.map₂ add <| fun x x' rx y y' ry =>
    Setoid.trans (Relation.add_1 _ _ y rx) (Relation.add_2 x' _ _ ry)
  zero_add := Quotient.ind <| fun _ => Quotient.sound <| Relation.zero_add _
  add_zero := Quotient.ind <| fun _ => Quotient.sound <| Relation.add_zero _
  add_left_neg := Quotient.ind <| fun _ => Quotient.sound <| Relation.add_left_neg _
  add_assoc := Quotient.ind <| fun _ => Quotient.ind₂ <| fun _ _ =>
    Quotient.sound <| Relation.add_assoc _ _ _

-- Porting note : failed to derive `Inhabited` instance
instance InhabitedColimitType : Inhabited <| ColimitType F where
  default := 0

instance ColimitType.AddGroupWithOne : AddGroupWithOne (ColimitType F) :=
  { ColimitType.AddGroup F with one := Quotient.mk _ one }

instance : CommRing (ColimitType.{v} F) :=
  { ColimitType.AddGroupWithOne F with
    mul := Quot.map₂ Prequotient.mul Relation.mul_2 Relation.mul_1
    one_mul := fun x => Quot.inductionOn x fun x => Quot.sound <| Relation.one_mul _
    mul_one := fun x => Quot.inductionOn x fun x => Quot.sound <| Relation.mul_one _
    add_comm := fun x y => Quot.induction_on₂ x y fun x y => Quot.sound <| Relation.add_comm _ _
    mul_comm := fun x y => Quot.induction_on₂ x y fun x y => Quot.sound <| Relation.mul_comm _ _
    mul_assoc := fun x y z => Quot.induction_on₃ x y z fun x y z => by
      simp only [(· * ·)]
      -- ⊢ Quot.map₂ mul (_ : ∀ (x y y' : Prequotient F), Relation F y y' → Relation F  …
      exact Quot.sound (Relation.mul_assoc _ _ _)
      -- 🎉 no goals
    mul_zero := fun x => Quot.inductionOn x fun x => Quot.sound <| Relation.mul_zero _
    zero_mul := fun x => Quot.inductionOn x fun x => Quot.sound <| Relation.zero_mul _
      -- ⊢ Quot.map₂ mul (_ : ∀ (x y y' : Prequotient F), Relation F y y' → Relation F  …
    left_distrib := fun x y z => Quot.induction_on₃ x y z fun x y z => by
      -- 🎉 no goals
      simp only [(· + ·), (· * ·), Add.add]
      exact Quot.sound (Relation.left_distrib _ _ _)
      -- ⊢ Quot.map₂ mul (_ : ∀ (x y y' : Prequotient F), Relation F y y' → Relation F  …
    right_distrib := fun x y z => Quot.induction_on₃ x y z fun x y z => by
      -- 🎉 no goals
      simp only [(· + ·), (· * ·), Add.add]
      exact Quot.sound (Relation.right_distrib _ _ _) }

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
  map_one' := by apply Quot.sound; apply Relation.one
                 -- ⊢ Setoid.r (Prequotient.of j 1) one
                                   -- 🎉 no goals
  map_mul' := by intros; apply Quot.sound; apply Relation.mul
                 -- ⊢ OneHom.toFun { toFun := coconeFun F j, map_one' := (_ : Quot.mk Setoid.r (Pr …
                         -- ⊢ Setoid.r (Prequotient.of j (x✝ * y✝)) (mul (Prequotient.of j x✝) (Prequotien …
                                           -- 🎉 no goals
  map_zero' := by apply Quot.sound; apply Relation.zero
                  -- ⊢ Setoid.r (Prequotient.of j 0) zero
                                    -- 🎉 no goals
  map_add' := by intros; apply Quot.sound; apply Relation.add
                 -- ⊢ OneHom.toFun (↑{ toOneHom := { toFun := coconeFun F j, map_one' := (_ : Quot …
                         -- ⊢ Setoid.r (Prequotient.of j (x✝ + y✝)) (add (Prequotient.of j x✝) (Prequotien …
                                           -- 🎉 no goals
#align CommRing.colimits.cocone_morphism CommRingCat.Colimits.coconeMorphism

@[simp]
theorem cocone_naturality {j j' : J} (f : j ⟶ j') :
    F.map f ≫ coconeMorphism F j' = coconeMorphism F j := by
  ext
  -- ⊢ ↑(F.map f ≫ coconeMorphism F j') x✝ = ↑(coconeMorphism F j) x✝
  apply Quot.sound
  -- ⊢ Setoid.r (Prequotient.of j' (↑(F.map f) x✝)) (Prequotient.of j x✝)
  apply Relation.map
  -- 🎉 no goals
#align CommRing.colimits.cocone_naturality CommRingCat.Colimits.cocone_naturality

@[simp]
theorem cocone_naturality_components (j j' : J) (f : j ⟶ j') (x : F.obj j) :
    (coconeMorphism F j') (F.map f x) = (coconeMorphism F j) x := by
  rw [← cocone_naturality F f, comp_apply]
  -- 🎉 no goals
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
  -- ⊢ Prequotient F → ↑s.pt
  · exact descFunLift F s
    -- 🎉 no goals
  · intro x y r
    -- ⊢ descFunLift F s x = descFunLift F s y
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
    | zero_mul x => dsimp; rw [zero_mul]
    | mul_zero x => dsimp; rw [mul_zero]
#align CommRing.colimits.desc_fun CommRingCat.Colimits.descFun

/-- The ring homomorphism from the colimit commutative ring to the cone point of any other
cocone. -/
def descMorphism (s : Cocone F) : colimit F ⟶ s.pt where
  toFun := descFun F s
  map_one' := rfl
  map_zero' := rfl
  map_add' x y := by
    refine Quot.induction_on₂ x y fun a b => ?_
    -- ⊢ OneHom.toFun (↑{ toOneHom := { toFun := descFun F s, map_one' := (_ : descFu …
    dsimp [descFun, (· + ·)]
    -- ⊢ Quot.lift (descFunLift F s) (_ : ∀ (x y : Prequotient F), Setoid.r x y → des …
    rw [←quot_add]
                     -- 🎉 no goals
    -- ⊢ Quot.lift (descFunLift F s) (_ : ∀ (x y : Prequotient F), Setoid.r x y → des …
    rfl
    -- 🎉 no goals
  map_mul' x y := by exact Quot.induction_on₂ x y fun a b => rfl
#align CommRing.colimits.desc_morphism CommRingCat.Colimits.descMorphism

/-- Evidence that the proposed colimit is the colimit. -/
def colimitIsColimit : IsColimit (colimitCocone F) where
  desc s := descMorphism F s
  uniq s m w := RingHom.ext fun x => by
    change (colimitCocone F).pt →+* s.pt at m
    -- ⊢ ↑m x = ↑((fun s => descMorphism F s) s) x
    refine Quot.inductionOn x ?_
    -- ⊢ ∀ (a : Prequotient F), ↑m (Quot.mk Setoid.r a) = ↑((fun s => descMorphism F  …
    intro x
    -- ⊢ ↑m (Quot.mk Setoid.r x) = ↑((fun s => descMorphism F s) s) (Quot.mk Setoid.r …
    induction x with
    | zero => erw [quot_zero, map_zero (f := m), (descMorphism F s).map_zero]
    | one => erw [quot_one, map_one (f := m), (descMorphism F s).map_one]
    | neg x ih => erw [quot_neg, map_neg (f := m), (descMorphism F s).map_neg, ih]
    | of j x =>
      exact congr_fun (congr_arg (fun f : F.obj j ⟶ s.pt => (f : F.obj j → s.pt)) (w j)) x
    | add x y ih_x ih_y => erw [quot_add, map_add (f := m), (descMorphism F s).map_add, ih_x, ih_y]
    | mul x y ih_x ih_y => erw [quot_mul, map_mul (f := m), (descMorphism F s).map_mul, ih_x, ih_y]
#align CommRing.colimits.colimit_is_colimit CommRingCat.Colimits.colimitIsColimit

instance hasColimits_commRingCat : HasColimits CommRingCat where
  has_colimits_of_shape _ _ :=
    { has_colimit := fun F =>
        HasColimit.mk
          { cocone := colimitCocone F
            isColimit := colimitIsColimit F } }
#align CommRing.colimits.has_colimits_CommRing CommRingCat.Colimits.hasColimits_commRingCat

end CommRingCat.Colimits
