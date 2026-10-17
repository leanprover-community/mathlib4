/-
Copyright (c) 2026 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Endomorphism semiring (resp. ring) of a commutative monoid (resp. group) object

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

namespace AddMon.End

open AddMon End

/-- The zero homomorphism in `End G` for an additive commutative monoid object `G : AddMon C` -/
scoped instance : Zero (End G) where
  zero := .of 0

/-- The addition in `End G` for a additive commutative monoid object `G : AddMon C` -/
scoped instance [BraidedCategory C] [IsCommAddMonObj G.X] : Add (End G) where
  add f g := .of (f.asHom + g.asHom)

lemma add_asHom (f g : End G) [BraidedCategory C] [IsCommAddMonObj G.X] :
  (f + g).asHom = f.asHom + g.asHom := rfl

lemma zero_asHom : (0 : End G).asHom = 0 := rfl

/-- For a commutative addtitive monoid object `G`, the endomorphisms `End G` has
an additive commutative monoid structure -/
scoped instance [BraidedCategory C] [IsCommAddMonObj G.X] : AddCommMonoid (End G) where
  add_assoc f g h := by
    simp only [End.ext_iff, add_asHom, add_assoc f.asHom]
  zero_add f := by
    simp only [End.ext_iff, add_asHom, zero_asHom]
    exact zero_add f.asHom
  add_zero f := by
    simp only [End.ext_iff, add_asHom, zero_asHom]
    exact add_zero f.asHom
  nsmul n f := .of (n • f.asHom)
  add_comm f g := by
    simp only [End.ext_iff, add_asHom]
    exact add_comm f.asHom g.asHom


/-- For a commutative addtitive monoid object `G`, the endomorphisms `End G` has
an semiring structure -/
scoped instance [BraidedCategory C] [IsCommAddMonObj G.X] : Semiring (End G) where
  zero_add := zero_add
  add_zero := add_zero
  one_mul := one_mul
  mul_one := mul_one
  zero_mul f := by
    simp only [End.ext_iff, End.mul_asHom, zero_asHom, Limits.comp_zero]
  mul_zero f := by
    simp only [End.ext_iff, End.mul_asHom, zero_asHom, Limits.zero_comp]
  left_distrib f g h := by
    simp only [End.ext_iff, mul_asHom, add_asHom, Hom.add_def]
    ext
    simp only [Category.assoc, comp_hom', monMonoidalStruct_tensorObj_X, lift_hom, hom_add,
      IsAddMonHom.add_hom, lift_map_assoc]
  right_distrib f g h := by
    simp only [End.ext_iff, mul_asHom, add_asHom]
    ext
    simp only [Hom.add_def, comp_hom', monMonoidalStruct_tensorObj_X, lift_hom, hom_add,
      reassoc_of% (comp_lift h.asHom.hom f.asHom.hom g.asHom.hom).symm]

end AddMon.End

end EndomorphismSemiring

section EndomorphismRing

open AddMonObj CartesianMonoidalCategory

variable {G : AddGrp C} {H : AddGrp C}

namespace AddGrp.End

open AddGrp End

/-- The zero homomorphism in `End G` for an additive commutative group object `G : GrpMon C` -/
scoped instance : Zero (End G) where
  zero := .of 0

/-- The addition in `End G` for a additive commutative group object `G : AddGrp C` -/
scoped instance [BraidedCategory C] [IsCommAddMonObj G.X] : Add (End G) where
  add f g := .of (f.asHom + g.asHom)

lemma add_asHom (f g : End G) [BraidedCategory C] [IsCommAddMonObj G.X] :
  (f + g).asHom = f.asHom + g.asHom := rfl

lemma zero_asHom : (0 : End G).asHom = 0 := rfl

/-- For a commutative addtitive group object `G`, the endomorphisms `End G` has
an additive commutative group structure -/
scoped instance [BraidedCategory C] [IsCommAddMonObj G.X] : AddCommGroup (End G) where
  add_assoc f g h := by
    simp only [End.ext_iff, add_asHom, add_assoc f.asHom]
  zero_add f := by
    simp only [End.ext_iff, add_asHom, zero_asHom]
    exact zero_add f.asHom
  add_zero f := by
    simp only [End.ext_iff, add_asHom, zero_asHom]
    exact add_zero f.asHom
  nsmul n f := .of (n • f.asHom)
  neg f := .of (- f.asHom)
  zsmul n f := .of (n • f.asHom)
  neg_add_cancel f := by
    simp only [End.ext_iff, add_asHom, zero_asHom]
    exact neg_add_cancel f.asHom
  add_comm f g := by
    simp only [End.ext_iff, add_asHom]
    exact add_comm f.asHom g.asHom

/-- For a commutative addtitive group object `G`, the endomorphisms `End G` has
an ring structure -/
scoped instance [BraidedCategory C] [IsCommAddMonObj G.X] : Ring (End G) where
  zero_add := zero_add
  add_zero := add_zero
  one_mul := one_mul
  mul_one := mul_one
  zero_mul f := by
    simp only [End.ext_iff, End.mul_asHom, zero_asHom, Limits.comp_zero]
  mul_zero f := by
    simp only [End.ext_iff, End.mul_asHom, zero_asHom, Limits.zero_comp]
  left_distrib f g h := by
    simp only [End.ext_iff, mul_asHom, add_asHom, Hom.add_def]
    ext
    simp only [Category.assoc, IsAddMonHom.add_hom, lift_map_assoc, comp', lift_hom,
      AddMon.comp_hom', tensorObj_X, AddMon.lift_hom, hom_add]
  right_distrib f g h := by
    simp only [End.ext_iff, mul_asHom, add_asHom]
    have (H : f.asHom.hom = g.asHom.hom) : f.asHom = g.asHom := by
      exact AddGrp.hom_ext_iff.mpr (congrArg AddMon.Hom.hom H)
    ext
    simp only [Hom.add_def, comp', lift_hom, AddMon.comp_hom', tensorObj_X, AddMon.lift_hom,
      hom_add, reassoc_of% (comp_lift h.asHom.hom f.asHom.hom g.asHom.hom).symm,
      AddMon.monMonoidalStruct_tensorObj_X]
  neg_add_cancel := neg_add_cancel

end AddGrp.End

end EndomorphismRing
