/-
Copyright (c) 2025 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.Algebra.Ring.Defs

/-!
# Endomorphism ring (resp. semiring) of a commutative group (resp. monoid) object

Given an additive monoid object `G : AddMon C`, whose underlying structure is commutative, we
show that its endomorphism type `End G` is a semiring. If this object is a group object,
i.e., `G : AddGrp C`, then this semiring is in fact a ring.
-/

@[expose] public noncomputable section

open CategoryTheory

variable {C : Type*} [Category* C] [CartesianMonoidalCategory C]

section EndomorphismSemiring

open AddMonObj CartesianMonoidalCategory

variable {G : AddMon C} {H : AddMon C}

instance [BraidedCategory C] [IsCommAddMonObj G.X] : AddCommMonoid (G ⟶ G) := Hom.addCommMonoid

lemma AddMon.add_hom [BraidedCategory C] [IsCommAddMonObj H.X] (f g : G ⟶ H)
    : (f + g).hom = lift f.hom g.hom ≫ σ := rfl

namespace AddMon.End

/-- Given an `f : End G`, it returns the corrending term of typ `G ⟶ G` -/
def toHom (f : End G) : G ⟶ G := f


open AddMon End

scoped instance : Zero (End G) where
  zero := ((0 : G ⟶ G) : End G)

scoped instance [BraidedCategory C] [IsCommAddMonObj G.X] : Add (End G) where
  add f g :=  by exact (toHom f) + (toHom g)



lemma toHom_eq (f g : End G) : f = g ↔ End.toHom f = End.toHom g := by
  constructor <;> intro h
  · exact AddMon.Hom.ext' (congrArg AddMon.Hom.hom h)
  · exact End.ext h

lemma toHom_add (f g : End G) [BraidedCategory C] [IsCommAddMonObj G.X]
  : toHom (f + g) = toHom f + toHom g := rfl

lemma toHom_zero : toHom (0 : End G) = 0 := rfl

lemma toHom_comp (f g : End G) : toHom (f ≫ g) = (toHom f) ≫ (toHom g) := rfl


/- For a commutaive addtitive monoid object `G`, the endomorphisms `End G` has
an additive commutative monoid structure -/
scoped instance [BraidedCategory C] [IsCommAddMonObj G.X] : AddCommMonoid (End G) where
  add_assoc f g h := by
    simp only [toHom_eq, toHom_add, add_assoc (toHom f) (toHom g) (toHom h)]
  zero_add f := by
    simp only [toHom_eq, toHom_add, toHom_zero]
    exact zero_add (toHom f)
  add_zero f := by
    simp only [toHom_eq, toHom_add, toHom_zero]
    exact add_zero (toHom f)
  nsmul n f := by
    exact n • (toHom f)
  add_comm f g := by
    simp only [toHom_eq, toHom_add]
    exact add_comm (toHom f) (toHom g)

/- For a commutaive addtitive monoid object `G`, the endomorphisms `End G` has
an semiring structure -/
scoped instance [BraidedCategory C] [IsCommAddMonObj G.X] : Semiring (End G) where
  zero_add := zero_add
  add_zero := add_zero
  one_mul := one_mul
  mul_one := mul_one
  zero_mul f := by
    simp only [mul_def, Limits.comp_zero]
  mul_zero f := by
    simp only [mul_def, Limits.zero_comp]
  left_distrib f g h := by
    simp only [mul_def, toHom_eq, toHom_comp, toHom_add, Hom.add_def]
    ext
    simp only [Category.assoc, comp_hom', monMonoidalStruct_tensorObj_X, lift_hom, hom_add,
      IsAddMonHom.add_hom, lift_map_assoc]
  right_distrib f g h := by
    simp only [mul_def, toHom_eq, toHom_comp, toHom_add]
    ext
    simp only [add_hom, comp_hom',
      reassoc_of% (comp_lift (toHom h).hom (toHom f).hom (toHom g).hom).symm]

end AddMon.End

end EndomorphismSemiring

section EndomorphismRing

open AddMonObj CartesianMonoidalCategory

variable {G : AddGrp C} {H : AddGrp C}

lemma AddGrp.add_hom [BraidedCategory C] [IsCommAddMonObj H.X] (f g : G ⟶ H)
    : (f + g).hom = lift f.hom g.hom ≫ σ := rfl

namespace AddGrp.End

/-- Given an `f : End G`, it returns the corrending term of typ `G ⟶ G` -/
def toHom (f : End G) : G ⟶ G := f


open AddGrp End

scoped instance : Zero (End G) where
  zero := ((0 : G ⟶ G) : End G)

scoped instance [BraidedCategory C] [IsCommAddMonObj G.X] : Add (End G) where
  add f g :=  by exact (toHom f) + (toHom g)

lemma toHom_eq (f g : End G) : f = g ↔ End.toHom f = End.toHom g := by
  constructor <;> intro h
  · exact AddGrp.hom_ext_iff.mpr (congrArg AddMon.Hom.hom (congrArg InducedCategory.Hom.hom h))
  · exact End.ext h

lemma toHom_add (f g : End G) [BraidedCategory C] [IsCommAddMonObj G.X]
  : toHom (f + g) = toHom f + toHom g := rfl

lemma toHom_zero : toHom (0 : End G) = 0 := rfl

lemma toHom_comp (f g : End G) : toHom (f ≫ g) = (toHom f) ≫ (toHom g) := rfl



/- For a commutaive addtitive group object `G`, the endomorphisms `End G` has
an additive commutative group structure -/
scoped instance [BraidedCategory C] [IsCommAddMonObj G.X] : AddCommGroup (End G) where
  add_assoc f g h := by
    simp only [toHom_eq, toHom_add, add_assoc (toHom f) (toHom g) (toHom h)]
  zero_add f := by
    simp only [toHom_eq, toHom_add, toHom_zero]
    exact zero_add (toHom f)
  add_zero f := by
    simp only [toHom_eq, toHom_add, toHom_zero]
    exact add_zero (toHom f)
  nsmul n f := by
    exact n • (toHom f)
  neg f := by
    exact (- (toHom f))
  zsmul n f := by
    exact n • (toHom f)
  neg_add_cancel f := by
    rw[toHom_eq, toHom_add]
    have : toHom (- toHom f) = - toHom f := rfl
    rw[this, neg_add_cancel, toHom_zero]
    rfl
  add_comm f g := by
    simp only [toHom_eq, toHom_add]
    exact add_comm (toHom f) (toHom g)

/- For a commutaive addtitive group object `G`, the endomorphisms `End G` has
an ring structure -/
scoped instance [BraidedCategory C] [IsCommAddMonObj G.X] : Ring (End G) where
  zero_add := zero_add
  add_zero := add_zero
  one_mul := one_mul
  mul_one := mul_one
  zero_mul f := by
    simp only [mul_def, Limits.comp_zero]
  mul_zero f := by
    simp only [mul_def, Limits.zero_comp]
  left_distrib f g h := by
    simp only [mul_def, toHom_eq, toHom_comp, toHom_add, Hom.add_def]
    ext
    simp only [Category.assoc, IsAddMonHom.add_hom, lift_map_assoc, comp', lift_hom,
      AddMon.comp_hom', tensorObj_X, AddMon.lift_hom, hom_add]
  right_distrib f g h := by
    simp only [mul_def, toHom_eq, toHom_comp, toHom_add]
    ext
    simp only [add_hom, comp',
      reassoc_of% (comp_lift (toHom h).hom (toHom f).hom (toHom g).hom).symm]
  neg_add_cancel := neg_add_cancel

end AddGrp.End

end EndomorphismRing
