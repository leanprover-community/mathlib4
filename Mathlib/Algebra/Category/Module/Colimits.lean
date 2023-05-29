/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module algebra.category.Module.colimits
! leanprover-community/mathlib commit 5a684ce82399d820475609907c6ef8dba5b1b97c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Category.Module.Basic
import Mathbin.CategoryTheory.ConcreteCategory.Elementwise

/-!
# The category of R-modules has all colimits.

This file uses a "pre-automated" approach, just as for `Mon/colimits.lean`.

Note that finite colimits can already be obtained from the instance `abelian (Module R)`.

TODO:
In fact, in `Module R` there is a much nicer model of colimits as quotients
of finitely supported functions, and we really should implement this as well (or instead).
-/


universe u v w

open CategoryTheory

open CategoryTheory.Limits

variable {R : Type u} [Ring R]

-- [ROBOT VOICE]:
-- You should pretend for now that this file was automatically generated.
-- It follows the same template as colimits in Mon.
namespace ModuleCat.Colimits

/-!
We build the colimit of a diagram in `Module` by constructing the
free group on the disjoint union of all the abelian groups in the diagram,
then taking the quotient by the abelian group laws within each abelian group,
and the identifications given by the morphisms in the diagram.
-/


variable {J : Type w} [Category.{v} J] (F : J ⥤ ModuleCat.{max u v w} R)

/-- An inductive type representing all module expressions (without relations)
on a collection of types indexed by the objects of `J`.
-/
inductive Prequotient-- There's always `of`

  | of : ∀ (j : J) (x : F.obj j), prequotient-- Then one generator for each operation

  | zero : prequotient
  | neg : prequotient → prequotient
  | add : prequotient → prequotient → prequotient
  | smul : R → prequotient → prequotient
#align Module.colimits.prequotient ModuleCat.Colimits.Prequotient

instance : Inhabited (Prequotient F) :=
  ⟨Prequotient.zero⟩

open Prequotient

/-- The relation on `prequotient` saying when two expressions are equal
because of the module laws, or
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
  | neg : ∀ (j) (x : F.obj j), relation (of j (-x)) (neg (of j x))
  | add : ∀ (j) (x y : F.obj j), relation (of j (x + y)) (add (of j x) (of j y))
  |
  smul :
    ∀ (j) (s) (x : F.obj j),
      relation (of j (s • x)) (smul s (of j x))-- Then one relation per argument of each operation

  | neg_1 : ∀ (x x') (r : relation x x'), relation (neg x) (neg x')
  | add_1 : ∀ (x x' y) (r : relation x x'), relation (add x y) (add x' y)
  | add_2 : ∀ (x y y') (r : relation y y'), relation (add x y) (add x y')
  |
  smul_1 :
    ∀ (s) (x x') (r : relation x x'), relation (smul s x) (smul s x')-- And one relation per axiom

  | zero_add : ∀ x, relation (add zero x) x
  | add_zero : ∀ x, relation (add x zero) x
  | add_left_neg : ∀ x, relation (add (neg x) x) zero
  | add_comm : ∀ x y, relation (add x y) (add y x)
  | add_assoc : ∀ x y z, relation (add (add x y) z) (add x (add y z))
  | one_smul : ∀ x, relation (smul 1 x) x
  | mul_smul : ∀ s t x, relation (smul (s * t) x) (smul s (smul t x))
  | smul_add : ∀ s x y, relation (smul s (add x y)) (add (smul s x) (smul s y))
  | smul_zero : ∀ s, relation (smul s zero) zero
  | add_smul : ∀ s t x, relation (smul (s + t) x) (add (smul s x) (smul t x))
  | zero_smul : ∀ x, relation (smul 0 x) zero
#align Module.colimits.relation ModuleCat.Colimits.Relation

/-- The setoid corresponding to module expressions modulo module relations and identifications.
-/
def colimitSetoid : Setoid (Prequotient F)
    where
  R := Relation F
  iseqv := ⟨Relation.refl, Relation.symm, Relation.trans⟩
#align Module.colimits.colimit_setoid ModuleCat.Colimits.colimitSetoid

attribute [instance] colimit_setoid

/-- The underlying type of the colimit of a diagram in `Module R`.
-/
def ColimitType : Type max u v w :=
  Quotient (colimitSetoid F)deriving Inhabited
#align Module.colimits.colimit_type ModuleCat.Colimits.ColimitType

instance : AddCommGroup (ColimitType F)
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
  add_comm x y := by
    induction x
    induction y
    dsimp
    apply Quot.sound
    apply relation.add_comm
    rfl
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

instance : Module R (ColimitType F)
    where
  smul s := by
    fapply @Quot.lift
    · intro x
      exact Quot.mk _ (smul s x)
    · intro x x' r
      apply Quot.sound
      exact relation.smul_1 s _ _ r
  one_smul x := by
    induction x
    dsimp
    apply Quot.sound
    apply relation.one_smul
    rfl
  mul_smul s t x := by
    induction x
    dsimp
    apply Quot.sound
    apply relation.mul_smul
    rfl
  smul_add s x y := by
    induction x
    induction y
    dsimp
    apply Quot.sound
    apply relation.smul_add
    rfl
    rfl
  smul_zero s := by apply Quot.sound; apply relation.smul_zero
  add_smul s t x := by
    induction x
    dsimp
    apply Quot.sound
    apply relation.add_smul
    rfl
  zero_smul x := by
    induction x
    dsimp
    apply Quot.sound
    apply relation.zero_smul
    rfl

@[simp]
theorem quot_zero : Quot.mk Setoid.r zero = (0 : ColimitType F) :=
  rfl
#align Module.colimits.quot_zero ModuleCat.Colimits.quot_zero

@[simp]
theorem quot_neg (x) : Quot.mk Setoid.r (neg x) = (-Quot.mk Setoid.r x : ColimitType F) :=
  rfl
#align Module.colimits.quot_neg ModuleCat.Colimits.quot_neg

@[simp]
theorem quot_add (x y) :
    Quot.mk Setoid.r (add x y) = (Quot.mk Setoid.r x + Quot.mk Setoid.r y : ColimitType F) :=
  rfl
#align Module.colimits.quot_add ModuleCat.Colimits.quot_add

@[simp]
theorem quot_smul (s x) : Quot.mk Setoid.r (smul s x) = (s • Quot.mk Setoid.r x : ColimitType F) :=
  rfl
#align Module.colimits.quot_smul ModuleCat.Colimits.quot_smul

/-- The bundled module giving the colimit of a diagram. -/
def colimit : ModuleCat R :=
  ModuleCat.of R (ColimitType F)
#align Module.colimits.colimit ModuleCat.Colimits.colimit

/-- The function from a given module in the diagram to the colimit module. -/
def coconeFun (j : J) (x : F.obj j) : ColimitType F :=
  Quot.mk _ (of j x)
#align Module.colimits.cocone_fun ModuleCat.Colimits.coconeFun

/-- The group homomorphism from a given module in the diagram to the colimit module. -/
def coconeMorphism (j : J) : F.obj j ⟶ colimit F
    where
  toFun := coconeFun F j
  map_smul' := by intros ; apply Quot.sound; apply relation.smul
  map_add' := by intros <;> apply Quot.sound <;> apply relation.add
#align Module.colimits.cocone_morphism ModuleCat.Colimits.coconeMorphism

@[simp]
theorem cocone_naturality {j j' : J} (f : j ⟶ j') :
    F.map f ≫ coconeMorphism F j' = coconeMorphism F j :=
  by
  ext
  apply Quot.sound
  apply Relation.Map
#align Module.colimits.cocone_naturality ModuleCat.Colimits.cocone_naturality

@[simp]
theorem cocone_naturality_components (j j' : J) (f : j ⟶ j') (x : F.obj j) :
    (coconeMorphism F j') (F.map f x) = (coconeMorphism F j) x := by rw [← cocone_naturality F f];
  rfl
#align Module.colimits.cocone_naturality_components ModuleCat.Colimits.cocone_naturality_components

/-- The cocone over the proposed colimit module. -/
def colimitCocone : Cocone F where
  pt := colimit F
  ι := { app := coconeMorphism F }
#align Module.colimits.colimit_cocone ModuleCat.Colimits.colimitCocone

/-- The function from the free module on the diagram to the cone point of any other cocone. -/
@[simp]
def descFunLift (s : Cocone F) : Prequotient F → s.pt
  | of j x => (s.ι.app j) x
  | zero => 0
  | neg x => -desc_fun_lift x
  | add x y => desc_fun_lift x + desc_fun_lift y
  | smul s x => s • desc_fun_lift x
#align Module.colimits.desc_fun_lift ModuleCat.Colimits.descFunLift

/-- The function from the colimit module to the cone point of any other cocone. -/
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
    -- neg
    · simp
    -- add
    · simp
    -- smul,
    · simp
    -- neg_1
    · rw [r_ih]
    -- add_1
    · rw [r_ih]
    -- add_2
    · rw [r_ih]
    -- smul_1
    · rw [r_ih]
    -- zero_add
    · rw [zero_add]
    -- add_zero
    · rw [add_zero]
    -- add_left_neg
    · rw [add_left_neg]
    -- add_comm
    · rw [add_comm]
    -- add_assoc
    · rw [add_assoc]
    -- one_smul
    · rw [one_smul]
    -- mul_smul
    · rw [mul_smul]
    -- smul_add
    · rw [smul_add]
    -- smul_zero
    · rw [smul_zero]
    -- add_smul
    · rw [add_smul]
    -- zero_smul
    · rw [zero_smul]
#align Module.colimits.desc_fun ModuleCat.Colimits.descFun

/-- The group homomorphism from the colimit module to the cone point of any other cocone. -/
def descMorphism (s : Cocone F) : colimit F ⟶ s.pt
    where
  toFun := descFun F s
  map_smul' s x := by induction x <;> rfl
  map_add' x y := by induction x <;> induction y <;> rfl
#align Module.colimits.desc_morphism ModuleCat.Colimits.descMorphism

/-- Evidence that the proposed colimit is the colimit. -/
def colimitCoconeIsColimit : IsColimit (colimitCocone F)
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
    · simp [*]
    · simp [*]
    rfl
#align Module.colimits.colimit_cocone_is_colimit ModuleCat.Colimits.colimitCoconeIsColimit

instance hasColimits_moduleCat : HasColimits (ModuleCat.{max v u} R)
    where HasColimitsOfShape J 𝒥 :=
    {
      HasColimit := fun F =>
        has_colimit.mk
          { Cocone := colimit_cocone F
            IsColimit := colimit_cocone_is_colimit F } }
#align Module.colimits.has_colimits_Module ModuleCat.Colimits.hasColimits_moduleCat

instance hasColimitsOfSize_moduleCat : HasColimitsOfSize.{v} (ModuleCat.{max v u} R) :=
  hasColimitsOfSize_shrink _
#align Module.colimits.has_colimits_of_size_Module ModuleCat.Colimits.hasColimitsOfSize_moduleCat

instance hasColimitsOfSize_zero_moduleCat : HasColimitsOfSize.{0} (ModuleCat.{max v u} R) :=
  @hasColimitsOfSize_shrink.{0} (ModuleCat.{max v u} R) _ ModuleCat.Colimits.hasColimits_moduleCat
#align Module.colimits.has_colimits_of_size_zero_Module ModuleCat.Colimits.hasColimitsOfSize_zero_moduleCat

-- We manually add a `has_colimits` instance with universe parameters swapped, for otherwise
-- the instance is not found by typeclass search.
instance hasColimits_Module' (R : Type u) [Ring R] : HasColimits (ModuleCat.{max u v} R) :=
  ModuleCat.Colimits.hasColimits_moduleCat.{u, v}
#align Module.colimits.has_colimits_Module' ModuleCat.Colimits.hasColimits_Module'

-- We manually add a `has_colimits` instance with equal universe parameters, for otherwise
-- the instance is not found by typeclass search.
instance hasColimits_Module'' (R : Type u) [Ring R] : HasColimits (ModuleCat.{u} R) :=
  ModuleCat.Colimits.hasColimits_moduleCat.{u, u}
#align Module.colimits.has_colimits_Module'' ModuleCat.Colimits.hasColimits_Module''

-- Sanity checks, just to make sure typeclass search can find the instances we want.
example (R : Type u) [Ring R] : HasColimits (ModuleCat.{max v u} R) :=
  inferInstance

example (R : Type u) [Ring R] : HasColimits (ModuleCat.{max u v} R) :=
  inferInstance

example (R : Type u) [Ring R] : HasColimits (ModuleCat.{u} R) :=
  inferInstance

end ModuleCat.Colimits

