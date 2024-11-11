/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Category.Grp.Preadditive
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.ConcreteCategory.Elementwise
import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# The category of additive commutative groups has all colimits.

This file uses a "pre-automated" approach, just as for `Algebra.Category.MonCat.Colimits`.
It is a very uniform approach, that conceivably could be synthesised directly
by a tactic that analyses the shape of `AddCommGroup` and `MonoidHom`.

TODO:
In fact, in `AddCommGrp` there is a much nicer model of colimits as quotients
of finitely supported functions, and we really should implement this as well (or instead).
-/


universe w u v

open CategoryTheory Limits

-- [ROBOT VOICE]:
-- You should pretend for now that this file was automatically generated.
-- It follows the same template as colimits in Mon.
namespace AddCommGrp

variable {J : Type u} [Category.{v} J] (F : J ⥤ AddCommGrp.{max u v w})

namespace Colimits

/-!
We build the colimit of a diagram in `AddCommGrp` by constructing the
free group on the disjoint union of all the abelian groups in the diagram,
then taking the quotient by the abelian group laws within each abelian group,
and the identifications given by the morphisms in the diagram.
-/

/-- An inductive type representing all group expressions (without relations)
on a collection of types indexed by the objects of `J`.
-/
inductive Prequotient
  -- There's always `of`
  | of : ∀ (j : J) (_ : F.obj j), Prequotient
  -- Then one generator for each operation
  | zero : Prequotient
  | neg : Prequotient → Prequotient
  | add : Prequotient → Prequotient → Prequotient

instance : Inhabited (Prequotient.{w} F) :=
  ⟨Prequotient.zero⟩

open Prequotient

/-- The relation on `Prequotient` saying when two expressions are equal
because of the abelian group laws, or
because one element is mapped to another by a morphism in the diagram.
-/
inductive Relation : Prequotient.{w} F → Prequotient.{w} F → Prop
  -- Make it an equivalence relation:
  | refl : ∀ x, Relation x x
  | symm : ∀ (x y) (_ : Relation x y), Relation y x
  | trans : ∀ (x y z) (_ : Relation x y) (_ : Relation y z), Relation x z
  -- There's always a `map` relation
  | map : ∀ (j j' : J) (f : j ⟶ j') (x : F.obj j), Relation (Prequotient.of j' (F.map f x))
      (Prequotient.of j x)
  -- Then one relation per operation, describing the interaction with `of`
  | zero : ∀ j, Relation (Prequotient.of j 0) zero
  | neg : ∀ (j) (x : F.obj j), Relation (Prequotient.of j (-x)) (neg (Prequotient.of j x))
  | add : ∀ (j) (x y : F.obj j), Relation (Prequotient.of j (x + y)) (add (Prequotient.of j x)
      (Prequotient.of j y))
  -- Then one relation per argument of each operation
  | neg_1 : ∀ (x x') (_ : Relation x x'), Relation (neg x) (neg x')
  | add_1 : ∀ (x x' y) (_ : Relation x x'), Relation (add x y) (add x' y)
  | add_2 : ∀ (x y y') (_ : Relation y y'), Relation (add x y) (add x y')
  -- And one relation per axiom
  | zero_add : ∀ x, Relation (add zero x) x
  | add_zero : ∀ x, Relation (add x zero) x
  | neg_add_cancel : ∀ x, Relation (add (neg x) x) zero
  | add_comm : ∀ x y, Relation (add x y) (add y x)
  | add_assoc : ∀ x y z, Relation (add (add x y) z) (add x (add y z))

/--
The setoid corresponding to group expressions modulo abelian group relations and identifications.
-/
def colimitSetoid : Setoid (Prequotient.{w} F) where
  r := Relation F
  iseqv := ⟨Relation.refl, fun r => Relation.symm _ _ r, fun r => Relation.trans _ _ _ r⟩

attribute [instance] colimitSetoid

/-- The underlying type of the colimit of a diagram in `AddCommGrp`.
-/
def ColimitType : Type max u v w :=
  Quotient (colimitSetoid.{w} F)

instance : Zero (ColimitType.{w} F) where
  zero := Quotient.mk _ zero

instance : Neg (ColimitType.{w} F) where
  neg := Quotient.map neg Relation.neg_1

instance : Add (ColimitType.{w} F) where
  add := Quotient.map₂ add <| fun _x x' rx y _y' ry =>
    Setoid.trans (Relation.add_1 _ _ y rx) (Relation.add_2 x' _ _ ry)

instance : AddCommGroup (ColimitType.{w} F) where
  zero_add := Quotient.ind <| fun _ => Quotient.sound <| Relation.zero_add _
  add_zero := Quotient.ind <| fun _ => Quotient.sound <| Relation.add_zero _
  neg_add_cancel := Quotient.ind <| fun _ => Quotient.sound <| Relation.neg_add_cancel _
  add_comm := Quotient.ind₂ <| fun _ _ => Quotient.sound <| Relation.add_comm _ _
  add_assoc := Quotient.ind <| fun _ => Quotient.ind₂ <| fun _ _ =>
    Quotient.sound <| Relation.add_assoc _ _ _
  nsmul := nsmulRec
  zsmul := zsmulRec

instance ColimitTypeInhabited : Inhabited (ColimitType.{w} F) := ⟨0⟩

@[simp]
theorem quot_zero : Quot.mk Setoid.r zero = (0 : ColimitType.{w} F) :=
  rfl

@[simp]
theorem quot_neg (x) :
    -- Porting note: force Lean to treat `ColimitType F` no as `Quot _`
    (by exact Quot.mk Setoid.r (neg x) : ColimitType.{w} F) =
      -(by exact Quot.mk Setoid.r x) :=
  rfl

@[simp]
theorem quot_add (x y) :
    (by exact Quot.mk Setoid.r (add x y) : ColimitType.{w} F) =
      -- Porting note: force Lean to treat `ColimitType F` no as `Quot _`
      (by exact Quot.mk Setoid.r x) + (by exact Quot.mk Setoid.r y) :=
  rfl

/-- The bundled abelian group giving the colimit of a diagram. -/
def colimit : AddCommGrp :=
  AddCommGrp.of (ColimitType.{w} F)

/-- The function from a given abelian group in the diagram to the colimit abelian group. -/
def coconeFun (j : J) (x : F.obj j) : ColimitType.{w} F :=
  Quot.mk _ (Prequotient.of j x)

/-- The group homomorphism from a given abelian group in the diagram to the colimit abelian
group. -/
def coconeMorphism (j : J) : F.obj j ⟶ colimit.{w} F where
  toFun := coconeFun F j
  map_zero' := by apply Quot.sound; apply Relation.zero
  map_add' := by intros; apply Quot.sound; apply Relation.add

@[simp]
theorem cocone_naturality {j j' : J} (f : j ⟶ j') :
    F.map f ≫ coconeMorphism.{w} F j' = coconeMorphism F j := by
  ext
  apply Quot.sound
  apply Relation.map

@[simp]
theorem cocone_naturality_components (j j' : J) (f : j ⟶ j') (x : F.obj j) :
    (coconeMorphism.{w} F j') (F.map f x) = (coconeMorphism F j) x := by
  rw [← cocone_naturality F f]
  rfl

/-- The cocone over the proposed colimit abelian group. -/
def colimitCocone : Cocone F where
  pt := colimit.{w} F
  ι := { app := coconeMorphism F }

/-- The function from the free abelian group on the diagram to the cone point of any other
cocone. -/
@[simp]
def descFunLift (s : Cocone F) : Prequotient.{w} F → s.pt
  | Prequotient.of j x => (s.ι.app j) x
  | zero => 0
  | neg x => -descFunLift s x
  | add x y => descFunLift s x + descFunLift s y

/-- The function from the colimit abelian group to the cone point of any other cocone. -/
def descFun (s : Cocone F) : ColimitType.{w} F → s.pt := by
  fapply Quot.lift
  · exact descFunLift F s
  · intro x y r
    induction r with
    | refl => rfl
    | symm _ _ _ r_ih => exact r_ih.symm
    | trans _ _ _ _ _ r_ih_h r_ih_k => exact Eq.trans r_ih_h r_ih_k
    | map j j' f x => simpa only [descFunLift, Functor.const_obj_obj] using
      DFunLike.congr_fun (s.ι.naturality f) x
    | zero => simp
    | neg => simp
    | add => simp
    | neg_1 _ _ _ r_ih => dsimp; rw [r_ih]
    | add_1 _ _ _ _ r_ih => dsimp; rw [r_ih]
    | add_2 _ _ _ _ r_ih => dsimp; rw [r_ih]
    | zero_add => dsimp; rw [zero_add]
    | add_zero => dsimp; rw [add_zero]
    | neg_add_cancel => dsimp; rw [neg_add_cancel]
    | add_comm => dsimp; rw [add_comm]
    | add_assoc => dsimp; rw [add_assoc]

/-- The group homomorphism from the colimit abelian group to the cone point of any other cocone. -/
def descMorphism (s : Cocone F) : colimit.{w} F ⟶ s.pt where
  toFun := descFun F s
  map_zero' := rfl
  -- Porting note: in `mathlib3`, nothing needs to be done after `induction`
  map_add' x y := Quot.induction_on₂ x y fun _ _ => by dsimp; rw [← quot_add F]; rfl

/-- Evidence that the proposed colimit is the colimit. -/
def colimitCoconeIsColimit : IsColimit (colimitCocone.{w} F) where
  desc s := descMorphism F s
  uniq s m w := DFunLike.ext _ _ fun x => Quot.inductionOn x fun x => by
    change (m : ColimitType F →+ s.pt) _ = (descMorphism F s : ColimitType F →+ s.pt) _
    induction x using Prequotient.recOn with
    | of j x => exact DFunLike.congr_fun (w j) x
    | zero =>
      dsimp only [quot_zero]
      rw [map_zero, map_zero]
    | neg x ih =>
      dsimp only [quot_neg]
      rw [map_neg, map_neg, ih]
    | add x y ihx ihy =>
      simp only [quot_add]
      rw [m.map_add, (descMorphism F s).map_add, ihx, ihy]

end Colimits

lemma hasColimit : HasColimit F := ⟨_, Colimits.colimitCoconeIsColimit.{w} F⟩

variable (J)

lemma hasColimitsOfShape : HasColimitsOfShape J AddCommGrp.{max u v w} where
  has_colimit F := hasColimit.{w} F

lemma hasColimitsOfSize : HasColimitsOfSize.{v, u} AddCommGrp.{max u v w} :=
  ⟨fun _ => hasColimitsOfShape.{w} _⟩

instance hasColimits : HasColimits AddCommGrp.{w} := hasColimitsOfSize.{w}

instance : HasColimitsOfSize.{v, v} (AddCommGrpMax.{u, v}) := hasColimitsOfSize.{u}
instance : HasColimitsOfSize.{u, u} (AddCommGrpMax.{u, v}) := hasColimitsOfSize.{v}
instance : HasColimitsOfSize.{u, v} (AddCommGrpMax.{u, v}) := hasColimitsOfSize.{u}
instance : HasColimitsOfSize.{v, u} (AddCommGrpMax.{u, v}) := hasColimitsOfSize.{u}
instance : HasColimitsOfSize.{0, 0} (AddCommGrp.{u}) := hasColimitsOfSize.{u, 0, 0}

example : HasColimits AddCommGrpMax.{v, u} :=
  inferInstance

example : HasColimits AddCommGrpMax.{u, v} :=
  inferInstance

example : HasColimits AddCommGrp.{u} :=
  inferInstance

end AddCommGrp

namespace AddCommGrp

open QuotientAddGroup

/-- The categorical cokernel of a morphism in `AddCommGrp`
agrees with the usual group-theoretical quotient.
-/
noncomputable def cokernelIsoQuotient {G H : AddCommGrp.{u}} (f : G ⟶ H) :
    cokernel f ≅ AddCommGrp.of (H ⧸ AddMonoidHom.range f) where
  hom := cokernel.desc f (mk' _) <| by
        ext x
        apply Quotient.sound
        apply leftRel_apply.mpr
        fconstructor
        · exact -x
        · simp only [add_zero, AddMonoidHom.map_neg]
  inv :=
    QuotientAddGroup.lift _ (cokernel.π f) <| by
      rintro _ ⟨x, rfl⟩
      exact cokernel.condition_apply f x
  hom_inv_id := by
    refine coequalizer.hom_ext ?_
    simp only [coequalizer_as_cokernel, cokernel.π_desc_assoc, Category.comp_id]
    rfl
  inv_hom_id := by
    ext x
    exact QuotientAddGroup.induction_on x <| cokernel.π_desc_apply f _ _

end AddCommGrp
