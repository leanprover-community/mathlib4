/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyCofiber
public import Mathlib.Algebra.Homology.Opposite
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.CategoryTheory.CategoryStar
import Mathlib.Tactic.CategoryTheory.Reassoc
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
# The homotopy fiber of a morphism of homological complexes

In this file, we construct the homotopy fiber of a morphism `φ : F ⟶ G`
between homological complexes. Moreover, we dualise the definition
of the cylinder (which is a particular case of a homotopy cofiber)
in order to define the path object of a homological complex.

-/

@[expose] public section

open CategoryTheory Category Limits Preadditive Opposite

variable {C : Type*} [Category* C] [Preadditive C]

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

/-- The homotopy fiber of a morphism between homological complexes. -/
noncomputable def homotopyFiber : HomologicalComplex C c :=
  (unopFunctor C c.symm).obj (op (homotopyCofiber ((opFunctor C c).map φ.op)))

end

variable (K) [∀ i, HasBinaryBiproduct (K.X i) (K.X i)]

instance (i : α) : HasBinaryBiproduct (K.op.X i) (K.op.X i) := by
  dsimp; infer_instance

/-- The property that a homological complex `K` has a path object,
i.e. that the morphism `K ⟶ K ⊞ K` induced by `𝟙 K` and `-𝟙 K`
has a homotopy fiber. -/
abbrev HasPathObject := HasHomotopyFiber (biprod.desc (𝟙 K) (-𝟙 K))

instance [K.HasPathObject] :
    HasHomotopyCofiber (biprod.lift (𝟙 K.op) (-𝟙 K.op)) where
  hasBinaryBiproduct i j hij := by
    have := HasHomotopyFiber.hasBinaryBiproduct (biprod.desc (𝟙 K) (-𝟙 K)) j i hij
    exact hasBinaryBiproduct_of_iso (Iso.refl _ : op (K.X j) ≅ K.op.X j)
      (show op ((K ⊞ K).X i) ≅ (K.op ⊞ K.op).X i from
        ((eval _ _ i).mapBiprod K K).op.symm ≪≫ biprod.opIso _ _ ≪≫
          ((eval _ _ i).mapBiprod K.op K.op).symm)

variable [K.HasPathObject]

/-- The path object of a homological complex is defined here by dualizing
the cylinder object of `K.op`. -/
@[no_expose]
noncomputable def pathObject := (unopFunctor C c.symm).obj (op K.op.cylinder)

namespace pathObject

lemma isZero_X (i : α) (h₁ : IsZero (K.X i)) (h₂ : ∀ (j : α), c.Rel j i → IsZero (K.X j)) :
    IsZero (K.pathObject.X i) := by
  apply IsZero.unop
  dsimp [pathObject]
  refine homotopyCofiber.isZero_X _ _ ?_ (fun j hj ↦ IsZero.op (h₂ _ hj))
  exact IsZero.of_iso (by simpa using h₁.op)
    ((eval Cᵒᵖ c.symm i).mapBiprod K.op K.op)

/-- The first projection `K.pathObject ⟶ K`. -/
@[no_expose]
noncomputable def π₀ : K.pathObject ⟶ K :=
  (unopFunctor C c.symm).map (cylinder.ι₀ K.op).op

/-- The second projection `K.pathObject ⟶ K`. -/
@[no_expose]
noncomputable def π₁ : K.pathObject ⟶ K :=
  (unopFunctor C c.symm).map (cylinder.ι₁ K.op).op

/-- The inclusion `K ⟶ K.pathObject`. -/
@[no_expose]
noncomputable def ι : K ⟶ K.pathObject :=
  (unopFunctor C c.symm).map (cylinder.π K.op).op

@[reassoc (attr := simp)]
lemma π₀_ι : ι K ≫ π₀ K = 𝟙 K :=
  Quiver.Hom.op_inj ((opFunctor C c).map_injective (cylinder.ι₀_π K.op))

@[reassoc (attr := simp)]
lemma π₁_ι : ι K ≫ π₁ K = 𝟙 K :=
  Quiver.Hom.op_inj ((opFunctor C c).map_injective (cylinder.ι₁_π K.op))

/-- The homotopy between `π₀ K ≫ ι K` and `𝟙 K.pathObject`. -/
@[no_expose]
noncomputable def π₀CompιHomotopy (hc : ∀ (i : α), ∃ j, c.Rel i j) :
    Homotopy (π₀ K ≫ ι K) (𝟙 K.pathObject) :=
  (cylinder.πCompι₀Homotopy K.op hc).unop

/-- The homotopy equivalence between `K` and `K.pathObject`. -/
@[simps]
noncomputable def homotopyEquiv (hc : ∀ (i : α), ∃ j, c.Rel i j) :
    HomotopyEquiv K K.pathObject where
  hom := ι K
  inv := π₀ K
  homotopyHomInvId := Homotopy.ofEq (by simp)
  homotopyInvHomId := π₀CompιHomotopy K hc

/-- The homotopy between `pathObject.ι₀ K` and `pathObject.ι₁ K`. -/
@[no_expose]
noncomputable def homotopy₀₁ (hc : ∀ (i : α), ∃ j, c.Rel i j) : Homotopy (π₀ K) (π₁ K) :=
  (cylinder.homotopy₀₁ K.op hc).unop

section

variable {K} (φ₀ φ₁ : F ⟶ K) (h : Homotopy φ₀ φ₁)

/-- The morphism `F ⟶ K.pathObject` that is induced by two morphisms `φ₀ φ₁ : F ⟶ K`
and a homotopy `h : Homotopy φ₀ φ₁`. -/
@[no_expose]
noncomputable def lift : F ⟶ K.pathObject :=
  letI φ : K.op.cylinder ⟶ (opFunctor C c).obj (op F) :=
    cylinder.desc ((opFunctor C c).map φ₀.op)
      ((opFunctor C c).map φ₁.op) h.op
  (unopFunctor C c.symm).map φ.op

@[reassoc (attr := simp)]
lemma lift_π₀ : lift φ₀ φ₁ h ≫ π₀ K = φ₀ :=
  Quiver.Hom.op_inj ((opFunctor C c).map_injective (cylinder.ι₀_desc _ _ _))

@[reassoc (attr := simp)]
lemma lift_π₁ : lift φ₀ φ₁ h ≫ π₁ K = φ₁ :=
  Quiver.Hom.op_inj ((opFunctor C c).map_injective (cylinder.ι₁_desc _ _ _))

end

end pathObject

end HomologicalComplex
