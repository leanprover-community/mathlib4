import Mathlib.CategoryTheory.Triangulated.Filtered.TStructure_NoProof
import Mathlib.CategoryTheory.Triangulated.TStructure.Acyclic
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.CategoryTheory.Localization.Triangulated

noncomputable section

open CategoryTheory Preadditive Limits Triangulated CategoryTheory.FilteredTriangulated
  TStructure Pretriangulated

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

-- A complex in the homotopy category of `AcyclicCategory T t₁ t₂` is acyclic if and only
-- if its image in the homotopy category of `t₁.Heart` ia acyclic.

instance : ObjectProperty.IsClosedUnderIsomorphisms (AcyclicComplexAcyclic t₁ t₂ T).P :=
  Functor.instIsClosedUnderIsomorphismsPHomologicalKernel
  (Functor.mapHomotopyCategory (T.AcyclicToHeart t₁ t₂)
  (ComplexShape.up ℤ) ⋙ HomotopyCategory.homologyFunctor
  t₁.Heart (ComplexShape.up ℤ) 0)

lemma AcyclicComplexAcyclic_iff (K : HomotopyCategory (AcyclicCategory T t₁ t₂)
    (ComplexShape.up ℤ)) :
    (AcyclicComplexAcyclic t₁ t₂ T).P K ↔ (HomotopyCategory.subcategoryAcyclic t₁.Heart).P
    (((T.AcyclicToHeart t₁ t₂).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) := sorry

-- A morphism in the homotopy category of `AcyclicCategory T t₁ t₂` has an acyclic
-- cone if and only if then its image in the homotopy category of `t₁.Heart`
-- is a quasi-isomorphism.
lemma AcyclicComplexAcyclic_W {K L : HomotopyCategory (AcyclicCategory T t₁ t₂)
    (ComplexShape.up ℤ)} (f : K ⟶ L) : (AcyclicComplexAcyclic t₁ t₂ T).W f ↔
    HomotopyCategory.quasiIso _ _ (((T.AcyclicToHeart t₁ t₂).mapHomotopyCategory
    (ComplexShape.up ℤ)).map f) := by
  obtain ⟨X, g, h, dT⟩ := distinguished_cocone_triangle f
  erw [Subcategory.mem_W_iff_of_distinguished (AcyclicComplexAcyclic t₁ t₂ T) _ dT]
  rw [AcyclicComplexAcyclic_iff]
  erw [← Subcategory.mem_W_iff_of_distinguished (HomotopyCategory.subcategoryAcyclic t₁.Heart)
    _ (((T.AcyclicToHeart t₁ t₂).mapHomotopyCategory
    (ComplexShape.up ℤ)).map_distinguished _ dT)]
  rw [HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W]
  rfl

-- Condition (b) of Proposition A.3.2.
instance Acyclic_equivalence :
    (Localization.Construction.lift (Functor.mapHomotopyCategory (T.AcyclicToHeart t₁ t₂)
    (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) (W := (AcyclicComplexAcyclic t₁ t₂ T).W)
    (fun _ _ f hf ↦ (Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso t₁.Heart
                    (ComplexShape.up ℤ))) _ ((AcyclicComplexAcyclic_W t₁ t₂ T f).mp hf))
    ).IsEquivalence := sorry

-- First conclusion of Proposition A.3.2:
-- The functor from `HomotopyCategory (AcyclicCategory T t₁ t₂)` to `HomotopyCategory t₂.Heart`
-- induced by `T` sends acyclic complexes to acyclic complexes, hence quasi-isomorphisms to
-- quasi-isomorphisms.

lemma AcyclicComplexAcyclic_image {K : HomotopyCategory (AcyclicCategory T t₁ t₂)
    (ComplexShape.up ℤ)} (hK : (AcyclicComplexAcyclic t₁ t₂ T).P K) :
    (HomotopyCategory.subcategoryAcyclic t₂.Heart).P
    (((T.FromAcyclic t₁ t₂).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) := sorry
-- This follows from the calculations in the file `Acyclic.lean`, modulo boundedness problems.

lemma AcyclicComplexAcyclic_W_image {K L : HomotopyCategory (AcyclicCategory T t₁ t₂)
    (ComplexShape.up ℤ)} {f : K ⟶ L} (hf : (AcyclicComplexAcyclic t₁ t₂ T).W f) :
    HomotopyCategory.quasiIso _ _ (((T.FromAcyclic t₁ t₂).mapHomotopyCategory
    (ComplexShape.up ℤ)).map f) := by
  obtain ⟨X, g, h, dT⟩ := distinguished_cocone_triangle f
  replace hf := (Subcategory.mem_W_iff_of_distinguished (AcyclicComplexAcyclic t₁ t₂ T) _ dT).mp hf
  replace hf := AcyclicComplexAcyclic_image t₁ t₂ T hf
  rw [HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W]
  exact (Subcategory.mem_W_iff_of_distinguished (HomotopyCategory.subcategoryAcyclic t₂.Heart)
    _ (((T.FromAcyclic t₁ t₂).mapHomotopyCategory
    (ComplexShape.up ℤ)).map_distinguished _ dT)).mpr hf

-- By the first conclusion and condition (b), we get a functor from `DerivedCategory t₁.Heart`
-- to `DerivedCategory t₂.Heart`.

def DerivedFunctor : DerivedCategory t₁.Heart ⥤ DerivedCategory t₂.Heart :=
  (Localization.Construction.lift (Functor.mapHomotopyCategory (T.AcyclicToHeart t₁ t₂)
  (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) (W := (AcyclicComplexAcyclic t₁ t₂ T).W)
  (fun _ _ f hf ↦ (Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso t₁.Heart
                    (ComplexShape.up ℤ))) _ ((AcyclicComplexAcyclic_W t₁ t₂ T f).mp hf))).inv ⋙
  (Localization.Construction.lift (Functor.mapHomotopyCategory (T.FromAcyclic t₁ t₂)
  (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) (W := (AcyclicComplexAcyclic t₁ t₂ T).W)
  (fun _ _ _ hf ↦ (Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso t₂.Heart
                    (ComplexShape.up ℤ))) _ (AcyclicComplexAcyclic_W_image t₁ t₂ T hf)))

-- Second statement of Proposition A.3.2: the "commutative" diagram.
-- This is an existence statement.

def DerivedFunctor_comp :
    Realization L₁ t₁ tF₁ ⋙ T ≅ DerivedFunctor t₁ t₂ T ⋙ Realization L₂ t₂ tF₂ := sorry


end Triangulated.Filtered

end CategoryTheory
