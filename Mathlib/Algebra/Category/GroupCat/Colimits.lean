/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Category.GroupCat.Preadditive
import Mathlib.GroupTheory.QuotientGroup
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.CategoryTheory.ConcreteCategory.Elementwise

#align_import algebra.category.Group.colimits from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# The category of additive commutative groups has all colimits.

This file uses a "pre-automated" approach, just as for `Mon/Colimits.lean`.
It is a very uniform approach, that conceivably could be synthesised directly
by a tactic that analyses the shape of `AddCommGroup` and `MonoidHom`.

TODO:
In fact, in `AddCommGroupCat` there is a much nicer model of colimits as quotients
of finitely supported functions, and we really should implement this as well (or instead).
-/

-- porting note: `AddCommGroup` in all the names
set_option linter.uppercaseLean3 false

universe u v

open CategoryTheory

open CategoryTheory.Limits

-- [ROBOT VOICE]:
-- You should pretend for now that this file was automatically generated.
-- It follows the same template as colimits in Mon.
namespace AddCommGroupCat.Colimits

/-!
We build the colimit of a diagram in `AddCommGroupCat` by constructing the
free group on the disjoint union of all the abelian groups in the diagram,
then taking the quotient by the abelian group laws within each abelian group,
and the identifications given by the morphisms in the diagram.
-/


variable {J : Type v} [SmallCategory J] (F : J ⥤ AddCommGroupCat.{v})

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
#align AddCommGroup.colimits.prequotient AddCommGroupCat.Colimits.Prequotient

instance : Inhabited (Prequotient F) :=
  ⟨Prequotient.zero⟩

open Prequotient

/-- The relation on `prequotient` saying when two expressions are equal
because of the abelian group laws, or
because one element is mapped to another by a morphism in the diagram.
-/
inductive Relation : Prequotient F → Prequotient F → Prop
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
  | add_left_neg : ∀ x, Relation (add (neg x) x) zero
  | add_comm : ∀ x y, Relation (add x y) (add y x)
  | add_assoc : ∀ x y z, Relation (add (add x y) z) (add x (add y z))
#align AddCommGroup.colimits.relation AddCommGroupCat.Colimits.Relation

/--
The setoid corresponding to group expressions modulo abelian group relations and identifications.
-/
def colimitSetoid : Setoid (Prequotient F) where
  r := Relation F
  iseqv := ⟨Relation.refl, fun r => Relation.symm _ _ r, fun r => Relation.trans _ _ _ r⟩
#align AddCommGroup.colimits.colimit_setoid AddCommGroupCat.Colimits.colimitSetoid

attribute [instance] colimitSetoid

/-- The underlying type of the colimit of a diagram in `AddCommGroupCat`.
-/
def ColimitType : Type v :=
  Quotient (colimitSetoid F)
#align AddCommGroup.colimits.colimit_type AddCommGroupCat.Colimits.ColimitType

instance : AddCommGroup (ColimitType F) where
  zero := Quotient.mk _ zero
  neg := Quotient.map neg Relation.neg_1
  add := Quotient.map₂ add <| fun x x' rx y y' ry =>
    Setoid.trans (Relation.add_1 _ _ y rx) (Relation.add_2 x' _ _ ry)
  zero_add := Quotient.ind <| fun _ => Quotient.sound <| Relation.zero_add _
  add_zero := Quotient.ind <| fun _ => Quotient.sound <| Relation.add_zero _
  add_left_neg := Quotient.ind <| fun _ => Quotient.sound <| Relation.add_left_neg _
  add_comm := Quotient.ind₂ <| fun _ _ => Quotient.sound <| Relation.add_comm _ _
  add_assoc := Quotient.ind <| fun _ => Quotient.ind₂ <| fun _ _ =>
    Quotient.sound <| Relation.add_assoc _ _ _

instance ColimitTypeInhabited : Inhabited (ColimitType.{v} F) := ⟨0⟩

@[simp]
theorem quot_zero : Quot.mk Setoid.r zero = (0 : ColimitType F) :=
  rfl
#align AddCommGroup.colimits.quot_zero AddCommGroupCat.Colimits.quot_zero

@[simp]
theorem quot_neg (x) : Quot.mk Setoid.r (neg x) =
    -- Porting note : force Lean to treat `ColimitType F` no as `Quot _`
    Neg.neg (α := ColimitType.{v} F) (Quot.mk Setoid.r x : ColimitType.{v} F) :=
  rfl
#align AddCommGroup.colimits.quot_neg AddCommGroupCat.Colimits.quot_neg

@[simp]
theorem quot_add (x y) :
    Quot.mk Setoid.r (add x y) =
    -- Porting note : force Lean to treat `ColimitType F` no as `Quot _`
    Add.add (α := ColimitType.{v} F) (Quot.mk Setoid.r x) (Quot.mk Setoid.r y) :=
  rfl
#align AddCommGroup.colimits.quot_add AddCommGroupCat.Colimits.quot_add

/-- The bundled abelian group giving the colimit of a diagram. -/
def colimit : AddCommGroupCat :=
  AddCommGroupCat.of (ColimitType F)
#align AddCommGroup.colimits.colimit AddCommGroupCat.Colimits.colimit

/-- The function from a given abelian group in the diagram to the colimit abelian group. -/
def coconeFun (j : J) (x : F.obj j) : ColimitType F :=
  Quot.mk _ (Prequotient.of j x)
#align AddCommGroup.colimits.cocone_fun AddCommGroupCat.Colimits.coconeFun

/-- The group homomorphism from a given abelian group in the diagram to the colimit abelian
group. -/
def coconeMorphism (j : J) : F.obj j ⟶ colimit F where
  toFun := coconeFun F j
  map_zero' := by apply Quot.sound; apply Relation.zero
                  -- ⊢ Setoid.r (Prequotient.of j 0) zero
                                    -- 🎉 no goals
  map_add' := by intros; apply Quot.sound; apply Relation.add
                 -- ⊢ ZeroHom.toFun { toFun := coconeFun F j, map_zero' := (_ : Quot.mk Setoid.r ( …
                         -- ⊢ Setoid.r (Prequotient.of j (x✝ + y✝)) (add (Prequotient.of j x✝) (Prequotien …
                                           -- 🎉 no goals
#align AddCommGroup.colimits.cocone_morphism AddCommGroupCat.Colimits.coconeMorphism

@[simp]
theorem cocone_naturality {j j' : J} (f : j ⟶ j') :
    F.map f ≫ coconeMorphism F j' = coconeMorphism F j := by
  ext
  -- ⊢ ↑(F.map f ≫ coconeMorphism F j') x✝ = ↑(coconeMorphism F j) x✝
  apply Quot.sound
  -- ⊢ Setoid.r (Prequotient.of j' (↑(F.map f) x✝)) (Prequotient.of j x✝)
  apply Relation.map
  -- 🎉 no goals
#align AddCommGroup.colimits.cocone_naturality AddCommGroupCat.Colimits.cocone_naturality

@[simp]
theorem cocone_naturality_components (j j' : J) (f : j ⟶ j') (x : F.obj j) :
    (coconeMorphism F j') (F.map f x) = (coconeMorphism F j) x := by
  rw [← cocone_naturality F f]
  -- ⊢ ↑(coconeMorphism F j') (↑(F.map f) x) = ↑(F.map f ≫ coconeMorphism F j') x
  rfl
  -- 🎉 no goals
#align AddCommGroup.colimits.cocone_naturality_components AddCommGroupCat.Colimits.cocone_naturality_components

/-- The cocone over the proposed colimit abelian group. -/
def colimitCocone : Cocone F where
  pt := colimit F
  ι := { app := coconeMorphism F }
#align AddCommGroup.colimits.colimit_cocone AddCommGroupCat.Colimits.colimitCocone

/-- The function from the free abelian group on the diagram to the cone point of any other
cocone. -/
@[simp]
def descFunLift (s : Cocone F) : Prequotient F → s.pt
  | Prequotient.of j x => (s.ι.app j) x
  | zero => 0
  | neg x => -descFunLift s x
  | add x y => descFunLift s x + descFunLift s y
#align AddCommGroup.colimits.desc_fun_lift AddCommGroupCat.Colimits.descFunLift

/-- The function from the colimit abelian group to the cone point of any other cocone. -/
def descFun (s : Cocone F) : ColimitType F → s.pt := by
  fapply Quot.lift
  -- ⊢ Prequotient F → ↑s.pt
  · exact descFunLift F s
    -- 🎉 no goals
  · intro x y r
    -- ⊢ descFunLift F s x = descFunLift F s y
    induction r with
    | refl => rfl
    | symm _ _ _ r_ih => exact r_ih.symm
    | trans _ _ _ _ _ r_ih_h r_ih_k => exact Eq.trans r_ih_h r_ih_k
    | map j j' f x => simpa only [descFunLift, Functor.const_obj_obj] using
      FunLike.congr_fun (s.ι.naturality f) x
    | zero => simp
    | neg => simp
    | add => simp
    | neg_1 _ _ _ r_ih => dsimp; rw [r_ih]
    | add_1 _ _ _ _ r_ih => dsimp; rw [r_ih]
    | add_2 _ _ _ _ r_ih => dsimp; rw [r_ih]
    | zero_add => dsimp; rw [zero_add]
    | add_zero => dsimp; rw [add_zero]
    | add_left_neg => dsimp; rw [add_left_neg]
    | add_comm => dsimp; rw [add_comm]
    | add_assoc => dsimp; rw [add_assoc]
#align AddCommGroup.colimits.desc_fun AddCommGroupCat.Colimits.descFun

/-- The group homomorphism from the colimit abelian group to the cone point of any other cocone. -/
def descMorphism (s : Cocone F) : colimit.{v} F ⟶ s.pt where
  toFun := descFun F s
  map_zero' := rfl
  -- Porting note : in `mathlib3`, nothing needs to be done after `induction`
  map_add' x y := Quot.induction_on₂ x y fun _ _ => by dsimp [(· + ·)]; rw [←quot_add F]; rfl
                                                       -- ⊢ descFun F s (Add.add (Quot.mk Setoid.r x✝¹) (Quot.mk Setoid.r x✝)) = Add.add …
                                                                        -- ⊢ descFun F s (Quot.mk Setoid.r (add x✝¹ x✝)) = Add.add (descFun F s (Quot.mk  …
                                                                                          -- 🎉 no goals
#align AddCommGroup.colimits.desc_morphism AddCommGroupCat.Colimits.descMorphism

/-- Evidence that the proposed colimit is the colimit. -/
def colimitCoconeIsColimit : IsColimit (colimitCocone.{v} F) where
  desc s := descMorphism F s
  uniq s m w := FunLike.ext _ _ <| fun x => Quot.inductionOn x fun x => by
    change (m : ColimitType F →+ s.pt) _ = (descMorphism F s : ColimitType F →+ s.pt) _
    -- ⊢ ↑m (Quot.mk Setoid.r x) = ↑(descMorphism F s) (Quot.mk Setoid.r x)
    induction x using Prequotient.recOn with
    | of j x => exact FunLike.congr_fun (w j) x
    | zero =>
      dsimp only [quot_zero]
      rw [map_zero, map_zero]
    | neg x ih =>
      dsimp only [quot_neg]
      rw [map_neg, map_neg, ih]
    | add x y ihx ihy =>
      simp only [quot_add]
      erw [m.map_add, (descMorphism F s).map_add, ihx, ihy]
#align AddCommGroup.colimits.colimit_cocone_is_colimit AddCommGroupCat.Colimits.colimitCoconeIsColimit

instance hasColimits_addCommGroupCat : HasColimits AddCommGroupCat
    where has_colimits_of_shape {_ _} :=
    { has_colimit := fun F =>
        HasColimit.mk
          { cocone := colimitCocone F
            isColimit := colimitCoconeIsColimit F } }
#align AddCommGroup.colimits.has_colimits_AddCommGroup AddCommGroupCat.Colimits.hasColimits_addCommGroupCat

end AddCommGroupCat.Colimits

namespace AddCommGroupCat

open QuotientAddGroup

/-- The categorical cokernel of a morphism in `AddCommGroupCat`
agrees with the usual group-theoretical quotient.
-/
noncomputable def cokernelIsoQuotient {G H : AddCommGroupCat.{u}} (f : G ⟶ H) :
    cokernel f ≅ AddCommGroupCat.of (H ⧸ AddMonoidHom.range f) where
  hom := cokernel.desc f (mk' _) <| by
        ext x
        -- ⊢ ↑(f ≫ mk' (AddMonoidHom.range f)) x = ↑0 x
        apply Quotient.sound
        -- ⊢ ↑f x ≈ 0
        apply leftRel_apply.mpr
        -- ⊢ -↑f x + 0 ∈ AddMonoidHom.range f
        fconstructor
        -- ⊢ ↑G
        exact -x
        -- ⊢ ↑f (-x) = -↑f x + 0
        simp only [add_zero, AddMonoidHom.map_neg]
        -- 🎉 no goals
  inv :=
    QuotientAddGroup.lift _ (cokernel.π f) <| by
      rintro _ ⟨x, rfl⟩
      -- ⊢ ↑(cokernel.π f) (↑f x) = 0
      exact cokernel.condition_apply f x
      -- 🎉 no goals
  hom_inv_id := by
    refine coequalizer.hom_ext ?_
    -- ⊢ coequalizer.π f 0 ≫ cokernel.desc f (mk' (AddMonoidHom.range f)) (_ : f ≫ mk …
    simp only [coequalizer_as_cokernel, cokernel.π_desc_assoc, Category.comp_id]
    -- ⊢ mk' (AddMonoidHom.range f) ≫ lift (AddMonoidHom.range f) (cokernel.π f) (_ : …
    rfl
    -- 🎉 no goals
  inv_hom_id := by
    ext x
    -- ⊢ ↑(lift (AddMonoidHom.range f) (cokernel.π f) (_ : ∀ (x : ↑H), x ∈ AddMonoidH …
    exact QuotientAddGroup.induction_on x <| cokernel.π_desc_apply f _ _
    -- 🎉 no goals
#align AddCommGroup.cokernel_iso_quotient AddCommGroupCat.cokernelIsoQuotient

end AddCommGroupCat
