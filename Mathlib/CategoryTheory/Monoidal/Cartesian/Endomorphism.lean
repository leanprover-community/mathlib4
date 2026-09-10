/-
Copyright (c) 2025 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.Algebra.Ring.Defs

/-!
# Endomorphism ring (rsp. semiring) of a commutative group (monoid) object

We show that given a monoid object `G : Mon C` whose underlying structure is commutative,
its endomorphism type `G ⟶ G` is a semiring. If this object is a group object, i.e., `G : Grp C`,
then this semiring would in fact be a ring.
-/

@[expose] public section

open CategoryTheory

variable {C : Type*} [Category* C] [CartesianMonoidalCategory C]

section EndomorphismSemiring

open AddMonObj CartesianMonoidalCategory

variable {G : AddMon C} {H : AddMon C}

instance : Mul (G ⟶ G) where
  mul f g := {
    hom := g.hom ≫ f.hom
    isAddMonHom_hom := inferInstance
  }

instance : One (G ⟶ G) where
  one := {
    hom := 𝟙 G.X
    isAddMonHom_hom := by infer_instance
  }

namespace AddMon
lemma add_hom [BraidedCategory C] [IsCommAddMonObj H.X] (f g : G ⟶ H)
    : (f + g).hom = lift f.hom g.hom ≫ σ := rfl

lemma mul_hom (f g : (G ⟶ G)) :
    (f * g).hom = g.hom ≫ f.hom := rfl

lemma one_hom (G₀ : AddMon C) : (1 : G₀ ⟶ G₀).hom = 𝟙 G₀.X := rfl
end AddMon


instance [BraidedCategory C] [IsCommAddMonObj G.X] : AddCommMonoid (G ⟶ G) := Hom.addCommMonoid

open AddMon
instance [BraidedCategory C] [IsCommAddMonObj G.X] : Semiring (G ⟶ G) where
  zero_add := zero_add
  add_zero := add_zero
  mul_assoc f g h := by ext; simp[mul_hom]
  one_mul f := by ext; simp only [mul_hom, one_hom, Category.comp_id]
  mul_one f := by ext; simp only [mul_hom, AddMon.one_hom, Category.id_comp]
  zero_mul f := by ext; simp only [mul_hom, zero_hom, comp_toUnit_assoc]
  mul_zero f := by ext; simp only [zero_hom, mul_hom, Category.assoc, IsAddMonHom.zero_hom]
  left_distrib f g h := by
    ext
    simp only [mul_hom, add_hom, Category.assoc, IsAddMonHom.add_hom, lift_map_assoc]
  right_distrib f g h := by
    ext
    simp only [mul_hom, add_hom, reassoc_of% (comp_lift h.hom f.hom g.hom).symm]

end EndomorphismSemiring

section EndomorphismRing

open CategoryTheory MonoidalCategory AddGrp AddMonObj CartesianMonoidalCategory

variable {D : Type*} [Category* D] [CartesianMonoidalCategory D]
variable {A B : AddGrp D}

instance : Mul (A ⟶ A) where
  mul f g := g ≫ f

instance : One (A ⟶ A) where
  one := 𝟙 A

namespace AddGrp
lemma toAddMonHom (f g : A ⟶ B) : f = g ↔ f.hom = g.hom := by
  constructor <;> intro h
  · exact InducedCategory.hom_ext_iff.mp h
  · exact AddGrp.hom_ext_iff.mpr (congrArg AddMon.Hom.hom h)

lemma mul_hom (f g : A ⟶ A) : (f * g).hom = f.hom * g.hom := by
  ext
  have : (f * g).hom = g.hom ≫ f.hom := rfl
  simp [AddMon.mul_hom, this]

lemma one_hom : (InducedCategory.Hom.hom (1 : A ⟶ A)) = (1 : A.toAddMon ⟶ A.toAddMon) := rfl
end AddGrp

open AddGrp
noncomputable instance [BraidedCategory D] [IsCommAddMonObj A.X] : Ring (A ⟶ A) where
  zero_add := zero_add
  add_zero := add_zero
  mul_assoc f g h := by
    ext; simp only [mul_hom, mul_assoc f.hom g.hom h.hom]
  one_mul f := by
    ext
    simp only [mul_hom, one_hom, one_mul f.hom]
  mul_one f := by
    ext
    simp only [mul_hom, one_hom, mul_one f.hom]
  zero_mul f := by
    simp only [toAddMonHom, mul_hom, zero_hom, zero_mul]
  mul_zero f := by
    simp only [toAddMonHom, mul_hom, zero_hom, mul_zero]
  left_distrib f g h := by
    simp only [toAddMonHom, mul_hom, Hom.hom_add, left_distrib]
  right_distrib f g h := by
    simp only [toAddMonHom, mul_hom, Hom.hom_add, right_distrib]
  neg_add_cancel f := neg_add_cancel f

end EndomorphismRing
