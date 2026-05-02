/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyCofiber
public import Mathlib.Algebra.Homology.Opposite

/-! The homotopy fiber of a morphism of homological complexes

-/

@[expose] public section


open CategoryTheory Category Limits Preadditive Opposite

variable {C : Type*} [Category* C] [Preadditive C]

namespace Homotopy

variable {α : Type*} {c : ComplexShape α}

open HomologicalComplex

-- to be moved
@[simps]
def unop {F G : HomologicalComplex Cᵒᵖ c} {φ₁ φ₂ : F ⟶ G}
    (h : Homotopy φ₁ φ₂) :
      Homotopy ((unopFunctor C c).map φ₁.op) ((unopFunctor C c).map φ₂.op) where
  hom i j := (h.hom j i).unop
  zero i j hij := Quiver.Hom.op_inj (h.zero _ _ hij)
  comm n := Quiver.Hom.op_inj (by
    dsimp
    rw [h.comm n]
    dsimp
    nth_rw 2 [add_comm]
    rfl)

-- to be moved
@[simps]
def op {F G : HomologicalComplex C c} {φ₁ φ₂ : F ⟶ G}
    (h : Homotopy φ₁ φ₂) :
      Homotopy ((opFunctor C c).map φ₁.op) ((opFunctor C c).map φ₂.op) where
  hom i j := (h.hom j i).op
  zero i j hij := Quiver.Hom.unop_inj (h.zero _ _ hij)
  comm n := Quiver.Hom.unop_inj (by
    dsimp
    rw [h.comm n]
    dsimp
    nth_rw 2 [add_comm]
    rfl)

end Homotopy

@[implicit_reducible]
def ComplexShape.decidableRelSymm {α : Type*} (c : ComplexShape α)
    [DecidableRel c.Rel] :
    DecidableRel c.symm.Rel :=
  fun a b ↦ decidable_of_iff (c.Rel b a) Iff.rfl

namespace HomologicalComplex

attribute [local instance] ComplexShape.decidableRelSymm

variable {α : Type*} {c : ComplexShape α} {F G K : HomologicalComplex C c} (φ : F ⟶ G)

variable [DecidableRel c.Rel]

section

/-- A morphism of homological complexes `φ : F ⟶ G` has a homotopy fiber if for all
indices `i` and `j` such that `c.Rel i j`, the binary biproduct `F.X i ⊞ G.X j` exists. -/
class HasHomotopyFiber (φ : F ⟶ G) : Prop where
  hasBinaryBiproduct (φ) (i j : α) (hij : c.Rel i j) : HasBinaryBiproduct (G.X i) (F.X j)

instance [HasBinaryBiproducts C] : HasHomotopyFiber φ where
  hasBinaryBiproduct _ _ _ := inferInstance

variable [HasHomotopyFiber φ] [DecidableRel c.Rel]

instance : HasHomotopyCofiber ((opFunctor C c).map φ.op) where
  hasBinaryBiproduct i j hij := by
    have := HasHomotopyFiber.hasBinaryBiproduct φ j i hij
    dsimp
    infer_instance

noncomputable def homotopyFiber : HomologicalComplex C c :=
  (unopFunctor C c.symm).obj (op (homotopyCofiber ((opFunctor C c).map φ.op)))

end

variable (K)
variable [∀ i, HasBinaryBiproduct (K.X i) (K.X i)]

instance (i : α) : HasBinaryBiproduct (K.op.X i) (K.op.X i) := by
  dsimp; infer_instance

abbrev HasPathObject := HasHomotopyFiber (biprod.desc (𝟙 K) (𝟙 K))

instance [K.HasPathObject] : HasHomotopyCofiber (biprod.lift (𝟙 K.op) (-𝟙 K.op)) where
  hasBinaryBiproduct i j hij := by
    have := HasHomotopyFiber.hasBinaryBiproduct (biprod.desc (𝟙 K) (𝟙 K)) j i hij
    exact hasBinaryBiproduct_of_iso (Iso.refl _ : op (K.X j) ≅ K.op.X j)
      (show op ((K ⊞ K).X i) ≅ (K.op ⊞ K.op).X i by
        refine ((eval _ _ i).mapBiprod K K).op.symm ≪≫ ?_ ≪≫
          ((eval _ _ i).mapBiprod K.op K.op).symm
        dsimp
        sorry)

variable [K.HasPathObject]

noncomputable def pathObject := (unopFunctor C c.symm).obj (op K.op.cylinder)

namespace pathObject

noncomputable def π₀ : K.pathObject ⟶ K :=
  (unopFunctor C c.symm).map (cylinder.ι₀ K.op).op

noncomputable def π₁ : K.pathObject ⟶ K :=
  (unopFunctor C c.symm).map (cylinder.ι₁ K.op).op

noncomputable def ι : K ⟶ K.pathObject :=
  (unopFunctor C c.symm).map (cylinder.π K.op).op

@[reassoc (attr := simp)]
lemma π₀_ι : ι K ≫ π₀ K = 𝟙 K :=
  Quiver.Hom.op_inj ((opFunctor C c).map_injective (cylinder.ι₀_π K.op))

@[reassoc (attr := simp)]
lemma π₁_ι : ι K ≫ π₁ K = 𝟙 K :=
  Quiver.Hom.op_inj ((opFunctor C c).map_injective (cylinder.ι₁_π K.op))

noncomputable def homotopy₀₁ (hc : ∀ (i : α), ∃ j, c.Rel i j) : Homotopy (π₀ K) (π₁ K) :=
  (cylinder.homotopy₀₁ K.op hc).unop

/-- The homotopy equivalence between `K` and `K.pathObject`. -/
noncomputable def homotopyEquiv (hc : ∀ (i : α), ∃ j, c.Rel i j) :
    HomotopyEquiv K K.pathObject where
  hom := ι K
  inv := π₀ K
  homotopyHomInvId := Homotopy.ofEq (by simp)
  homotopyInvHomId := (cylinder.πCompι₀Homotopy K.op hc).unop

section

variable {K} (φ₀ φ₁ : F ⟶ K) (h : Homotopy φ₀ φ₁)

noncomputable def lift : F ⟶ K.pathObject := by
  letI φ : K.op.cylinder ⟶ (opFunctor C c).obj (op F) :=
    cylinder.desc ((opFunctor C c).map φ₀.op)
      ((opFunctor C c).map φ₁.op) h.op
  exact (unopFunctor C c.symm).map φ.op

@[reassoc (attr := simp)]
lemma lift_π₀ : lift φ₀ φ₁ h ≫ π₀ K = φ₀ :=
  Quiver.Hom.op_inj ((opFunctor C c).map_injective (cylinder.ι₀_desc _ _ _))

@[reassoc (attr := simp)]
lemma lift_π₁ : lift φ₀ φ₁ h ≫ π₁ K = φ₁ :=
  Quiver.Hom.op_inj ((opFunctor C c).map_injective (cylinder.ι₁_desc _ _ _))

end

end pathObject

end HomologicalComplex
