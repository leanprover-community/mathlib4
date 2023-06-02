/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module algebra.category.Module.colimits
! leanprover-community/mathlib commit 5a684ce82399d820475609907c6ef8dba5b1b97c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.ConcreteCategory.Elementwise

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
inductive Prequotient
  -- There's always `of`
  | of : ∀ (j : J) (x : F.obj j), Prequotient
  -- Then one generator for each operation
  | zero : Prequotient
  | neg : Prequotient → Prequotient
  | add : Prequotient → Prequotient → Prequotient
  | smul : R → Prequotient → Prequotient
#align Module.colimits.prequotient ModuleCat.Colimits.Prequotient

instance : Inhabited (Prequotient F) :=
  ⟨Prequotient.zero⟩

open Prequotient

/-- The relation on `Prequotient` saying when two expressions are equal
because of the module laws, or
because one element is mapped to another by a morphism in the diagram.
-/
inductive Relation : Prequotient F → Prequotient F → Prop
  -- Make it an equivalence relation:
  | refl : ∀ x, Relation x x
  | symm : ∀ (x y) (h : Relation x y), Relation y x
  | trans : ∀ (x y z) (h : Relation x y) (k : Relation y z), Relation x z
  -- There's always a `map` Relation
  | map : ∀ (j j' : J) (f : j ⟶ j') (x : F.obj j),
    Relation (Prequotient.of j' (F.map f x)) (Prequotient.of j x)
  -- Then one Relation per operation, describing the interaction with `of`
  | zero : ∀ j, Relation (Prequotient.of j 0) zero
  | neg : ∀ (j) (x : F.obj j),
    Relation (Prequotient.of j (-x)) (neg (Prequotient.of j x))
  | add : ∀ (j) (x y : F.obj j),
    Relation (Prequotient.of j (x + y)) (add (Prequotient.of j x) (Prequotient.of j y))
  | smul : ∀ (j) (s) (x : F.obj j),
    Relation (Prequotient.of j (s • x)) (smul s (Prequotient.of j x))
  -- Then one Relation per argument of each operation
  | neg_1 : ∀ (x x') (r : Relation x x'), Relation (neg x) (neg x')
  | add_1 : ∀ (x x' y) (r : Relation x x'), Relation (add x y) (add x' y)
  | add_2 : ∀ (x y y') (r : Relation y y'), Relation (add x y) (add x y')
  | smul_1 : ∀ (s) (x x') (r : Relation x x'), Relation (smul s x) (smul s x')
  -- And one Relation per axiom
  | zero_add : ∀ x, Relation (add zero x) x
  | add_zero : ∀ x, Relation (add x zero) x
  | add_left_neg : ∀ x, Relation (add (neg x) x) zero
  | add_comm : ∀ x y, Relation (add x y) (add y x)
  | add_assoc : ∀ x y z, Relation (add (add x y) z) (add x (add y z))
  | one_smul : ∀ x, Relation (smul 1 x) x
  | mul_smul : ∀ s t x, Relation (smul (s * t) x) (smul s (smul t x))
  | smul_add : ∀ s x y, Relation (smul s (add x y)) (add (smul s x) (smul s y))
  | smul_zero : ∀ s, Relation (smul s zero) zero
  | add_smul : ∀ s t x, Relation (smul (s + t) x) (add (smul s x) (smul t x))
  | zero_smul : ∀ x, Relation (smul 0 x) zero
#align Module.colimits.relation ModuleCat.Colimits.Relation

/-- The setoid corresponding to module expressions modulo module relations and identifications.
-/
def colimitSetoid : Setoid (Prequotient F) where
  r := Relation F
  iseqv := ⟨Relation.refl, Relation.symm _ _, Relation.trans _ _ _⟩
#align Module.colimits.colimit_setoid ModuleCat.Colimits.colimitSetoid

attribute [instance] colimitSetoid

/-- The underlying type of the colimit of a diagram in `Module R`.
-/
def ColimitType : Type max u v w :=
  Quotient (colimitSetoid F)
#align Module.colimits.colimit_type ModuleCat.Colimits.ColimitType

instance : Inhabited (ColimitType F) := ⟨Quot.mk _ <| .zero⟩

instance : AddCommGroup (ColimitType F) where
  zero := Quot.mk _ zero
  neg := Quot.lift (fun t => Quot.mk _ <| neg t) <| fun x x' r => by
    apply Quot.sound
    exact Relation.neg_1 _ _ r
  add := fun x y => Quot.liftOn₂ x y (fun x' y' => Quot.mk _ <| add x' y')
    (by
      intro u v w r
      dsimp
      apply Quot.sound
      exact Relation.add_2 _ _ _ r)
    (by
      intro u v w r
      dsimp
      apply Quot.sound
      exact Relation.add_1 _ _ _ r)
  zero_add x := by
    rcases x
    dsimp
    apply Quot.sound
    apply Relation.zero_add
  add_zero x := by
    rcases x
    dsimp
    apply Quot.sound
    apply Relation.add_zero
  add_left_neg x := by
    rcases x
    dsimp
    apply Quot.sound
    apply Relation.add_left_neg
  add_comm := by
    rintro ⟨x⟩ ⟨y⟩
    apply Quot.sound
    apply Relation.add_comm
  add_assoc := by
    rintro ⟨x⟩ ⟨y⟩ ⟨z⟩
    apply Quot.sound
    apply Relation.add_assoc

instance : Module R (ColimitType F) where
  smul s := by
    fapply @Quot.lift
    · intro x
      exact Quot.mk _ (smul s x)
    · intro x x' r
      apply Quot.sound
      exact Relation.smul_1 s _ _ r
  one_smul x := by
    rcases x
    dsimp
    apply Quot.sound
    apply Relation.one_smul
  mul_smul s t x := by
    rcases x
    dsimp
    apply Quot.sound
    apply Relation.mul_smul
  smul_add s := by
    rintro ⟨x⟩ ⟨y⟩
    dsimp
    apply Quot.sound
    apply Relation.smul_add
  smul_zero s := by apply Quot.sound; apply Relation.smul_zero
  add_smul s t := by
    rintro ⟨x⟩
    dsimp
    apply Quot.sound
    apply Relation.add_smul
  zero_smul := by
    rintro ⟨x⟩
    dsimp
    apply Quot.sound
    apply Relation.zero_smul

@[simp]
theorem quot_zero : Quot.mk Setoid.r zero = (0 : ColimitType F) :=
  rfl
#align Module.colimits.quot_zero ModuleCat.Colimits.quot_zero

def ColimitType.mk {F : J ⥤ ModuleCat R} (x : Prequotient F) : ColimitType F := Quot.mk Setoid.r x

@[simp]
theorem quot_neg (x) : Quot.mk Setoid.r (neg x) = (-ColimitType.mk x : ColimitType F) :=
  rfl
#align Module.colimits.quot_neg ModuleCat.Colimits.quot_neg

@[simp]
theorem quot_add (x y) :
    Quot.mk Setoid.r (add x y) = (ColimitType.mk x + ColimitType.mk y : ColimitType F) :=
  rfl
#align Module.colimits.quot_add ModuleCat.Colimits.quot_add

@[simp]
theorem quot_smul (s x) : Quot.mk Setoid.r (smul s x) = (s • ColimitType.mk x : ColimitType F) :=
  rfl
#align Module.colimits.quot_smul ModuleCat.Colimits.quot_smul

/-- The bundled module giving the colimit of a diagram. -/
def colimit : ModuleCat R :=
  ModuleCat.of R (ColimitType F)
#align Module.colimits.colimit ModuleCat.Colimits.colimit

/-- The function from a given module in the diagram to the colimit module. -/
def coconeFun (j : J) (x : F.obj j) : ColimitType F :=
  Quot.mk _ (Prequotient.of j x)
#align Module.colimits.cocone_fun ModuleCat.Colimits.coconeFun

/-- The group homomorphism from a given module in the diagram to the colimit module. -/
def coconeMorphism (j : J) : F.obj j ⟶ colimit F where
  toFun := coconeFun F j
  map_smul' := by intros <;> apply Quot.sound <;> apply Relation.smul
  map_add' := by intros <;> apply Quot.sound <;> apply Relation.add
#align Module.colimits.cocone_morphism ModuleCat.Colimits.coconeMorphism

@[simp]
theorem cocone_naturality {j j' : J} (f : j ⟶ j') :
    F.map f ≫ coconeMorphism F j' = coconeMorphism F j := by
  ext
  apply Quot.sound
  apply ModuleCat.Colimits.Relation.map
#align Module.colimits.cocone_naturality ModuleCat.Colimits.cocone_naturality

@[simp]
theorem cocone_naturality_components (j j' : J) (f : j ⟶ j') (x : F.obj j) :
    (coconeMorphism F j') (F.map f x) = (coconeMorphism F j) x := by
  rw [← cocone_naturality F f]
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
  | Prequotient.of j x => (s.ι.app j) x
  | zero => 0
  | neg x => -descFunLift _ x
  | add x y => descFunLift _ x + descFunLift _ y
  | smul s x => s • descFunLift _ x
#align Module.colimits.desc_fun_lift ModuleCat.Colimits.descFunLift

/-- The function from the colimit module to the cone point of any other cocone. -/
def descFun (s : Cocone F) : ColimitType F → s.pt := by
  fapply Quot.lift
  · exact descFunLift F s
  · intro x y r
    induction' r with h₁ r_x r_y r_h r_ih r_x r_y r_z r_h r_k r_ih_h r_ih_k r_j r_j' r_f r_x j j x
      j x y j s x u v r r_ih u v w r r_ih u v w r r_ih s u v r r_ih <;> try dsimp
    -- refl
    -- · rfl -- porting note: `dsimp` (above) now closes this
    -- symm
    · exact r_ih.symm
    -- trans
    · exact Eq.trans r_ih_h r_ih_k
    -- map
    · exact s.w_apply r_f r_x -- porting note: `simp` failed
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
def descMorphism (s : Cocone F) : colimit F ⟶ s.pt where
  toFun := descFun F s
  map_smul' s x := by rcases x <;> rfl
  map_add' x y := by rcases x <;> rcases y <;> rfl
#align Module.colimits.desc_morphism ModuleCat.Colimits.descMorphism

/-- Evidence that the proposed colimit is the colimit. -/
def colimitCoconeIsColimit : IsColimit (colimitCocone F) where
  desc s := descMorphism F s
  uniq s m w := by
    ext ⟨⟨x_j, x_x⟩⟩
    · have w' :=
        congr_fun (congr_arg (fun f : F.obj x_j ⟶ s.pt => (f : F.obj x_j → s.pt)) (w x_j)) x_x
      simp only at w'
      erw [w']
      rfl
    · rw [quot_zero, map_zero] -- porting note: was `simp` but `map_zero` won't fire
      rfl
    · sorry -- simp [*]
    · sorry -- simp [*]
    · sorry -- simp [*]
#align Module.colimits.colimit_cocone_is_colimit ModuleCat.Colimits.colimitCoconeIsColimit

instance hasColimits_moduleCat : HasColimits (ModuleCat.{max v u} R)
    where has_colimits_of_shape J 𝒥 :=
    { has_colimit := fun F =>
        HasColimit.mk
          { cocone := colimitCocone F
            isColimit := colimitCoconeIsColimit F } }
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
