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

@[simp]
lemma add_asHom (f g : End G) [BraidedCategory C] [IsCommAddMonObj G.X] :
  (f + g).asHom = f.asHom + g.asHom := rfl

@[simp]
lemma zero_asHom : (0 : End G).asHom = 0 := rfl

/-- For a commutative addtitive monoid object `G`, the endomorphisms `End G` has
an semiring structure. -/
scoped instance [BraidedCategory C] [IsCommAddMonObj G.X] : Semiring (End G) where
  add_assoc f g h := by
    simp [End.ext_iff, add_assoc f.asHom]
  zero_add f := by
    simp_rw [End.ext_iff]
    exact zero_add f.asHom
  add_zero f := by
    simp_rw [End.ext_iff]
    exact add_zero f.asHom
  nsmul n f := .of (n • f.asHom)
  add_comm f g := by
    simp_rw [End.ext_iff]
    exact add_comm f.asHom g.asHom
  zero_mul f := by
    simp [End.ext_iff]
  mul_zero f := by
    simp [End.ext_iff]
  left_distrib f g h := by
    simp_rw [End.ext_iff]
    ext
    simp [Hom.add_def]
  right_distrib f g h := by
    simp_rw [End.ext_iff]
    ext
    simp [Hom.add_def, reassoc_of% (comp_lift h.asHom.hom f.asHom.hom g.asHom.hom).symm]

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

@[simp]
lemma add_asHom (f g : End G) [BraidedCategory C] [IsCommAddMonObj G.X] :
  (f + g).asHom = f.asHom + g.asHom := rfl

@[simp]
lemma zero_asHom : (0 : End G).asHom = 0 := rfl

/-- For a commutative addtitive group object `G`, the endomorphisms `End G` has
an ring structure. -/
scoped instance [BraidedCategory C] [IsCommAddMonObj G.X] : Ring (End G) where
  add_assoc f g h := by
    simp [End.ext_iff, add_assoc f.asHom]
  zero_add f := by
    simp [End.ext_iff]
    rfl
  add_zero f := by
    simp [End.ext_iff]
    rfl
  nsmul n f := .of (n • f.asHom)
  add_comm f g := by
    simp_rw [End.ext_iff]
    exact add_comm f.asHom g.asHom
  zero_mul f := by
    simp [End.ext_iff]
  mul_zero f := by
    simp [End.ext_iff]
  left_distrib f g h := by
    simp [End.ext_iff, Hom.add_def]
  right_distrib f g h := by
    simp_rw [End.ext_iff]
    have (H : f.asHom.hom = g.asHom.hom) : f.asHom = g.asHom :=
      AddGrp.hom_ext_iff.mpr (congrArg AddMon.Hom.hom H)
    ext
    simp [Hom.add_def, reassoc_of% (comp_lift h.asHom.hom f.asHom.hom g.asHom.hom).symm]
  neg f := .of (- f.asHom)
  zsmul n f := .of (n • f.asHom)
  neg_add_cancel f := by
    simp [End.ext_iff]
    rfl

end AddGrp.End

end EndomorphismRing
