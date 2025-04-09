import Mathlib.CategoryTheory.Triangulated.Filtered.TStructure_NoProof
import Mathlib.CategoryTheory.Triangulated.TStructure.Acyclic
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.CategoryTheory.Localization.Triangulated

noncomputable section

open CategoryTheory Preadditive Limits Triangulated CategoryTheory.FilteredTriangulated
  TStructure

open scoped ZeroObject

namespace CategoryTheory

universe u₁ v₁ w₁ t₁ u₂ v₂ w₂ t₂

attribute [local instance] endofunctorMonoidalCategory

variable {C₁ : Type u₁} [Category.{v₁} C₁] [HasShift C₁ (ℤ × ℤ)] [Preadditive C₁] [HasZeroObject C₁]
  [∀ p : ℤ × ℤ, Functor.Additive (shiftFunctor C₁ p)] [Pretriangulated C₁] [FilteredTriangulated C₁]
  [IsTriangulated C₁]

variable {A₁ : Type w₁} [Category.{t₁} A₁] [HasShift A₁ ℤ] [Preadditive A₁] [HasZeroObject A₁]
  [∀ p : ℤ, Functor.Additive (shiftFunctor A₁ p)] [Pretriangulated A₁]
  [IsTriangulated A₁]

variable (L₁ : isFilteredTriangulated_over C₁ A₁) (t₁ : TStructure A₁)
  (tF₁ : TStructure C₁) [t₁.IsCompatible L₁ tF₁]

local instance : t₁.HasHeart := hasHeartFullSubcategory t₁

local instance : tF₁.HasHeart := hasHeartFullSubcategory tF₁

noncomputable local instance : t₁.HasHomology₀ := t₁.hasHomology₀
noncomputable local instance : tF₁.HasHomology₀ := tF₁.hasHomology₀

noncomputable local instance : t₁.homology₀.ShiftSequence ℤ :=
  Functor.ShiftSequence.tautological _ _

noncomputable local instance : tF₁.homology₀.ShiftSequence ℤ :=
  Functor.ShiftSequence.tautological _ _

local instance : L₁.functor.CommShift ℤ := L₁.commShift

local instance : L₁.functor.IsTriangulated := L₁.triangulated

variable {C₂ : Type u₂} [Category.{v₂} C₂] [HasShift C₂ (ℤ × ℤ)] [Preadditive C₂] [HasZeroObject C₂]
  [∀ p : ℤ × ℤ, Functor.Additive (shiftFunctor C₂ p)] [Pretriangulated C₂] [FilteredTriangulated C₂]
  [IsTriangulated C₂]

variable {A₂ : Type w₂} [Category.{t₂} A₂] [HasShift A₂ ℤ] [Preadditive A₂] [HasZeroObject A₂]
  [∀ p : ℤ, Functor.Additive (shiftFunctor A₂ p)] [Pretriangulated A₂]
  [IsTriangulated A₂]

variable (L₂ : isFilteredTriangulated_over C₂ A₂) (t₂ : TStructure A₂)
  (tF₂ : TStructure C₂) [t₂.IsCompatible L₂ tF₂]

local instance : t₂.HasHeart := hasHeartFullSubcategory t₂

local instance : tF₂.HasHeart := hasHeartFullSubcategory tF₂

noncomputable local instance : t₂.HasHomology₀ := t₂.hasHomology₀
noncomputable local instance : tF₂.HasHomology₀ := tF₂.hasHomology₀

noncomputable local instance : t₂.homology₀.ShiftSequence ℤ :=
  Functor.ShiftSequence.tautological _ _

noncomputable local instance : tF₂.homology₀.ShiftSequence ℤ :=
  Functor.ShiftSequence.tautological _ _


variable [t₂.HasHeart] [tF₂.HasHeart] [t₂.HasHomology₀] [tF₂.HasHomology₀]
  [t₂.homology₀.ShiftSequence ℤ] [tF₂.homology₀.ShiftSequence ℤ]

local instance : L₂.functor.CommShift ℤ := L₂.commShift

local instance : L₂.functor.IsTriangulated := L₂.triangulated


namespace Triangulated.Filtered

local instance : HasDerivedCategory t₁.Heart := HasDerivedCategory.standard _

local instance : HasDerivedCategory t₂.Heart := HasDerivedCategory.standard _


-- Proposition A.3.2.
-- The t-structure `t₂` should be nondegenerate.
variable [NonDegenerate t₂]

-- Let `T :A₁ ⥤ A₂` be a triangulated functor.
variable (T : A₁ ⥤ A₂) [T.CommShift ℤ] [T.IsTriangulated]

-- Suppose that: (a) `T` admits an f-lifting `FT`.
variable (FT : T.filteredLifting L₁ L₂)

-- Acyclic complexes of `T`-acyclic objects.
def AcyclicComplexAcyclic : Triangulated.Subcategory
    (HomotopyCategory (AcyclicCategory T t₁ t₂) (ComplexShape.up ℤ)) :=
  (Functor.mapHomotopyCategory (T.AcyclicToHeart t₁ t₂)
  (ComplexShape.up ℤ) ⋙ HomotopyCategory.homologyFunctor
  t₁.Heart (ComplexShape.up ℤ) 0).homologicalKernel

#synth IsTriangulated (AcyclicComplexAcyclic t₁ t₂ T).W.Localization

#synth Abelian t₁.Heart

#check Localization.Construction.lift (Functor.mapHomotopyCategory (T.AcyclicToHeart t₁ t₂)
  (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) (W := (AcyclicComplexAcyclic t₁ t₂ T).W)
  (fun X Y f hf ↦ by )

end Triangulated.Filtered

end CategoryTheory
