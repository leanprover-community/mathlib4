import Mathlib.CategoryTheory.Triangulated.Filtered.TStructure_NoProof
import Mathlib.CategoryTheory.Triangulated.TStructure.Acyclic
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.CategoryTheory.Localization.Triangulated

noncomputable section

open CategoryTheory Preadditive Limits Triangulated CategoryTheory.FilteredTriangulated
  TStructure Pretriangulated Category

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

-- Condition (a) of Proposition A.3.2: `T` admits an f-lifting `FT`.
variable (FT : T.filteredLifting L₁ L₂)

-- We need some more vocabulary to state condition (b).

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
-- cone if and only if its image in the homotopy category of `t₁.Heart`
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

/- Condition (b) of Proposition A.3.2: the "obvious" functor from the homotopy category of
complexes of `T`-acyclic objects in the heart `A₁` to the derived category of the heart of `A₁`
is a localization functor for the class of morphisms with acyclic cone (i.e. quasi-isomorphisms).
-/

variable [(Functor.mapHomotopyCategory (T.AcyclicToHeart t₁ t₂)
    (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).IsLocalization (AcyclicComplexAcyclic t₁ t₂ T).W]

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
  Localization.lift (Functor.mapHomotopyCategory (T.FromAcyclic t₁ t₂)
  (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) (W := (AcyclicComplexAcyclic t₁ t₂ T).W)
  (fun _ _ _ hf ↦ (Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso t₂.Heart
                    (ComplexShape.up ℤ))) _ (AcyclicComplexAcyclic_W_image t₁ t₂ T hf))
  (Functor.mapHomotopyCategory (T.AcyclicToHeart t₁ t₂) (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)

-- Second statement of Proposition A.3.2: the "commutative" diagram.
-- This is an existence statement.
-- To prove this statement, we will use the category of filtered acyclic objects of the
-- heart of `C`, and its equivalent with the category of complexes of acyclic objects.

def FilteredAcyclic : ObjectProperty tF₁.Heart :=
  fun X ↦ ∀ n, AcyclicObject T t₁ t₂ ((t₁.homology n).obj ((Gr L₁ n).obj X.1))

lemma FilteredAcyclic_image (X : (FilteredAcyclic L₁ t₁ tF₁ t₂ T).FullSubcategory) :
    tF₂.heart (FT.functor.obj X.1.1) := sorry

def FilteredAcyclicToHeart : (FilteredAcyclic L₁ t₁ tF₁ t₂ T).FullSubcategory ⥤ tF₂.Heart :=
  ObjectProperty.lift tF₂.heart ((FilteredAcyclic L₁ t₁ tF₁ t₂ T).ι ⋙ tF₁.ιHeart ⋙ FT.functor)
  (FilteredAcyclic_image L₁ t₁ tF₁ L₂ t₂ tF₂ T FT)

def FilteredAcyclicToHeart_comp : FilteredAcyclicToHeart L₁ t₁ tF₁ L₂ t₂ tF₂ T FT ⋙
    tF₂.ιHeart ≅ (FilteredAcyclic L₁ t₁ tF₁ t₂ T).ι ⋙ tF₁.ιHeart ⋙ FT.functor :=
  ObjectProperty.liftCompιIso _ _ _ ≪≫ (Functor.associator _ _ _).symm

abbrev FilteredAcyclicToComplex_deg (n : ℤ) :
    (FilteredAcyclic L₁ t₁ tF₁ t₂ T).FullSubcategory ⥤ (AcyclicObject T t₁ t₂).FullSubcategory :=
  (AcyclicObject T t₁ t₂).lift ((FilteredAcyclic L₁ t₁ tF₁ t₂ T).ι ⋙ tF₁.ιHeart ⋙
  FilteredToComplex_deg L₁ t₁ n) (fun X ↦ X.2 n)

def FilteredAcyclicToComplex_deg_functor_half (n : ℤ) :
    (FilteredAcyclicToComplex_deg L₁ t₁ tF₁ t₂ T n ⋙ T.FromAcyclic t₁ t₂) ⋙ t₂.ιHeart ≅
    (FilteredAcyclic L₁ t₁ tF₁ t₂ T).ι ⋙ tF₁.ιHeart ⋙ FT.functor ⋙ Gr L₂ n ⋙
    shiftFunctor A₂ n := by
  dsimp [FilteredToComplex_deg, FilteredAcyclicToComplex_deg, Functor.FromAcyclic]
  refine Functor.associator _ _ t₂.ιHeart ≪≫ ?_
  refine isoWhiskerLeft _ (ObjectProperty.liftCompιIso t₂.heart _ _) ≪≫ ?_
  refine (Functor.associator _ (AcyclicObject T t₁ t₂).ι (t₁.ιHeart ⋙ T)).symm ≪≫ ?_
  refine isoWhiskerRight (ObjectProperty.liftCompιIso (AcyclicObject T t₁ t₂) _ _)
    (t₁.ιHeart ⋙ T) ≪≫ ?_
  refine isoWhiskerRight ((Functor.associator (FilteredAcyclic L₁ t₁ tF₁ t₂ T).ι tF₁.ιHeart
    (Gr L₁ n ⋙ t₁.homology n)).symm ≪≫ (Functor.associator ((FilteredAcyclic L₁ t₁ tF₁ t₂ T).ι ⋙
    tF₁.ιHeart) (Gr L₁ n) (t₁.homology n)).symm) (t₁.ιHeart ⋙ T) ≪≫ ?_
  refine Functor.associator (((FilteredAcyclic L₁ t₁ tF₁ t₂ T).ι ⋙ tF₁.ιHeart) ⋙ Gr L₁ n)
    (t₁.homology n) (t₁.ιHeart ⋙ T) ≪≫ ?_
  refine isoWhiskerLeft (((FilteredAcyclic L₁ t₁ tF₁ t₂ T).ι ⋙ tF₁.ιHeart) ⋙ Gr L₁ n)
    ((Functor.leftUnitor (t₁.homology n ⋙ t₁.ιHeart ⋙ T)).symm ≪≫
    isoWhiskerRight (shiftEquiv A₁ n).unitIso (t₁.homology n ⋙ t₁.ιHeart ⋙ T) ≪≫
    Functor.associator (shiftFunctor A₁ n) (shiftFunctor A₁ (-n)) _ ≪≫
    isoWhiskerLeft (shiftFunctor A₁ n)
    (Functor.associator (shiftFunctor A₁ (-n)) (t₁.homology n) _).symm ≪≫
    isoWhiskerLeft (shiftFunctor A₁ n) (isoWhiskerRight
    (t₁.homology₀.shiftIso (-n) n 0 (neg_add_cancel _)) (t₁.ιHeart ⋙ T))) ≪≫ ?_
  refine (Functor.associator (((FilteredAcyclic L₁ t₁ tF₁ t₂ T).ι ⋙ tF₁.ιHeart) ⋙ Gr L₁ n)
    (shiftFunctor A₁ n) (t₁.homology₀.shift 0 ⋙ t₁.ιHeart ⋙ T)).symm ≪≫ ?_
  refine isoWhiskerRight (ObjectProperty.liftCompιIso t₁.heart
    ((((FilteredAcyclic L₁ t₁ tF₁ t₂ T).ι ⋙ tF₁.ιHeart) ⋙ Gr L₁ n) ⋙ shiftFunctor A₁ n)
    (fun X ↦ (mem_filtered_heart_iff L₁ t₁ tF₁ X.1.1).mp X.1.2 n)).symm
    (t₁.homology₀.shift 0 ⋙ t₁.ιHeart ⋙ T) ≪≫ ?_
  refine Functor.associator _ t₁.ιHeart (t₁.homology₀.shift 0 ⋙ t₁.ιHeart ⋙ T) ≪≫ ?_
  refine isoWhiskerLeft _ ((Functor.associator t₁.ιHeart (t₁.homology₀.shift 0) _).symm ≪≫
    isoWhiskerRight (t₁.ιHeartHomology_zero) (t₁.ιHeart ⋙ T) ≪≫
    Functor.leftUnitor (t₁.ιHeart ⋙ T)) ≪≫ ?_
  refine (Functor.associator _ t₁.ιHeart T).symm ≪≫  ?_
  refine isoWhiskerRight (ObjectProperty.liftCompιIso t₁.heart
    ((((FilteredAcyclic L₁ t₁ tF₁ t₂ T).ι ⋙ tF₁.ιHeart) ⋙ Gr L₁ n) ⋙ shiftFunctor A₁ n)
    (fun X ↦ (mem_filtered_heart_iff L₁ t₁ tF₁ X.1.1).mp X.1.2 n)) T ≪≫ ?_
  refine Functor.associator (((FilteredAcyclic L₁ t₁ tF₁ t₂ T).ι ⋙ tF₁.ιHeart) ⋙ Gr L₁ n)
    (shiftFunctor A₁ n) T ≪≫ ?_
  refine isoWhiskerLeft (((FilteredAcyclic L₁ t₁ tF₁ t₂ T).ι ⋙ tF₁.ιHeart) ⋙ Gr L₁ n)
    (T.commShiftIso n) ≪≫ ?_
  refine Functor.associator ((FilteredAcyclic L₁ t₁ tF₁ t₂ T).ι ⋙ tF₁.ιHeart) (Gr L₁ n)
    (T ⋙ shiftFunctor A₂ n) ≪≫ ?_
  refine isoWhiskerLeft ((FilteredAcyclic L₁ t₁ tF₁ t₂ T).ι ⋙ tF₁.ιHeart)
    ((Functor.associator (Gr L₁ n) T (shiftFunctor A₂ n)).symm ≪≫
    isoWhiskerRight (lifting_Gr_comm L₁ L₂ FT n).symm (shiftFunctor A₂ n) ≪≫
    Functor.associator FT.functor (Gr L₂ n) (shiftFunctor A₂ n)) ≪≫ ?_
  exact Functor.associator (FilteredAcyclic L₁ t₁ tF₁ t₂ T).ι tF₁.ιHeart
    (FT.functor ⋙ Gr L₂ n ⋙ shiftFunctor A₂ n)

def FilteredAcyclicToComplex_deg_functor (n : ℤ) :
    FilteredAcyclicToComplex_deg L₁ t₁ tF₁ t₂ T n ⋙ T.FromAcyclic t₁ t₂ ≅
    (FilteredAcyclic L₁ t₁ tF₁ t₂ T).ι ⋙ tF₁.ιHeart ⋙ FT.functor ⋙
    FilteredToComplex_deg L₂ t₂ n := by
  refine Functor.fullyFaithfulCancelRight t₂.ιHeart ?_
  refine FilteredAcyclicToComplex_deg_functor_half L₁ t₁ tF₁ L₂ t₂ T FT n ≪≫ ?_
  refine ?_ ≪≫ isoWhiskerRight (isoWhiskerLeft ((FilteredAcyclic L₁ t₁ tF₁ t₂ T).ι ⋙ tF₁.ιHeart ⋙
    FT.functor ⋙ Gr L₂ n) (shiftEquiv A₂ n).unitIso.symm) (t₂.homology n ⋙ t₂.ιHeart)
  refine ?_ ≪≫ isoWhiskerLeft ((FilteredAcyclic L₁ t₁ tF₁ t₂ T).ι ⋙ tF₁.ιHeart ⋙ FT.functor ⋙
    Gr L₂ n) (isoWhiskerLeft (shiftFunctor A₂ n) (Functor.associator (shiftFunctor A₂ (-n))
    (t₂.homology n) (t₂.ιHeart)) ≪≫ (Functor.associator (shiftFunctor A₂ n) (shiftFunctor A₂ (-n))
    (t₂.homology n ⋙ t₂.ιHeart)).symm)
  refine ?_ ≪≫ isoWhiskerLeft ((FilteredAcyclic L₁ t₁ tF₁ t₂ T).ι ⋙ tF₁.ιHeart ⋙ FT.functor ⋙
    Gr L₂ n) (isoWhiskerLeft (shiftFunctor A₂ n) (isoWhiskerRight
    (t₂.homology₀.shiftIso (-n) n 0 (neg_add_cancel _)).symm t₂.ιHeart))
  refine ?_ ≪≫ Functor.associator ((FilteredAcyclic L₁ t₁ tF₁ t₂ T).ι ⋙ tF₁.ιHeart ⋙
    FT.functor ⋙ Gr L₂ n) (shiftFunctor A₂ n) (t₂.homology₀.shift 0 ⋙ t₂.ιHeart)
  refine ?_ ≪≫ Functor.associator (((FilteredAcyclic L₁ t₁ tF₁ t₂ T).ι ⋙ tF₁.ιHeart ⋙
    FT.functor ⋙ Gr L₂ n) ⋙ shiftFunctor A₂ n) (t₂.homology₀.shift 0) t₂.ιHeart
  refine ?_ ≪≫ isoWhiskerRight (isoWhiskerRight (ObjectProperty.liftCompιIso t₂.heart
    (((FilteredAcyclic L₁ t₁ tF₁ t₂ T).ι ⋙ tF₁.ιHeart ⋙ FT.functor ⋙ Gr L₂ n)
    ⋙ shiftFunctor A₂ n)
    (fun X ↦ (mem_filtered_heart_iff L₂ t₂ tF₂ (FT.functor.obj X.1.1)).mp
             (FilteredAcyclic_image L₁ t₁ tF₁ L₂ t₂ tF₂ T FT X) n))
    (t₂.homology₀.shift (0 : ℤ))) t₂.ιHeart
  refine ?_ ≪≫ isoWhiskerRight (Functor.associator _ t₂.ιHeart (t₂.homology₀.shift 0)).symm
    t₂.ιHeart
  refine ?_ ≪≫ isoWhiskerRight (isoWhiskerLeft _ (t₂.ιHeartHomology_zero).symm) t₂.ιHeart
  refine ?_ ≪≫ isoWhiskerRight (Functor.rightUnitor _).symm t₂.ιHeart
  refine ?_ ≪≫ (ObjectProperty.liftCompιIso t₂.heart
    (((FilteredAcyclic L₁ t₁ tF₁ t₂ T).ι ⋙ tF₁.ιHeart ⋙ FT.functor ⋙ Gr L₂ n)
    ⋙ shiftFunctor A₂ n)
    (fun X ↦ (mem_filtered_heart_iff L₂ t₂ tF₂ (FT.functor.obj X.1.1)).mp
             (FilteredAcyclic_image L₁ t₁ tF₁ L₂ t₂ tF₂ T FT X) n)).symm
  exact (Functor.associator (FilteredAcyclic L₁ t₁ tF₁ t₂ T).ι
    (tF₁.ιHeart ⋙ FT.functor ⋙ Gr L₂ n) (shiftFunctor A₂ n)).symm

example (n : ℤ) (X : (FilteredAcyclic L₁ t₁ tF₁ t₂ T).FullSubcategory) :
    (FilteredAcyclicToComplex_deg_functor L₁ t₁ tF₁ L₂ t₂ tF₂ T FT n).hom.app X = 0 := by
  dsimp [FilteredAcyclicToComplex_deg_functor, FilteredAcyclicToComplex_deg_functor_half]
  erw [id_comp, id_comp, Functor.map_id, Functor.map_id, Functor.map_id, Functor.map_id,
    Functor.map_id, Functor.map_id, Functor.map_id, Functor.map_id, id_comp, id_comp, id_comp,
    id_comp, id_comp, id_comp, id_comp, Functor.map_id, id_comp, id_comp, id_comp, id_comp,
    id_comp, id_comp, id_comp, id_comp, id_comp, id_comp, id_comp, id_comp, id_comp, id_comp,
    comp_id, comp_id, comp_id, comp_id, comp_id, comp_id, comp_id, comp_id]
  simp only [assoc]


lemma FilteredAcyclicToComplex_diff_functor (X : (FilteredAcyclic L₁ t₁ tF₁ t₂ T).FullSubcategory)
    (n : ℤ) : (FilteredAcyclicToComplex_deg_functor L₁ t₁ tF₁ L₂ t₂ tF₂ T FT n).hom.app X ≫
    (FilteredToComplex_diff L₂ t₂ n).app (FT.functor.obj X.1.1) =
    (T.FromAcyclic t₁ t₂).map ((FilteredToComplex_diff L₁ t₁ n).app X.1.1) ≫
    (FilteredAcyclicToComplex_deg_functor L₁ t₁ tF₁ L₂ t₂ tF₂ T FT (n + 1)).hom.app X := by
  dsimp [FilteredToComplex_diff]
  sorry


#exit
def FilteredAcyclicToComplexAcyclicObj :
    CochainComplex ((FilteredAcyclic L₁ t₁ tF₁ t₂ T).FullSubcategory ⥤
    (AcyclicObject T t₁ t₂).FullSubcategory) ℤ :=
  CochainComplex.of (FilteredAcyclicToComplex_deg L₁ t₁ tF₁ t₂ T)
    (fun n ↦ {app X := by
                refine (Functor.FullyFaithful.homEquiv
                  (AcyclicObject T t₁ t₂).fullyFaithfulι).symm ?_
                simp only [ObjectProperty.ι_obj, ObjectProperty.lift_obj_obj, Functor.comp_obj]
                exact (FilteredToComplex_diff L₁ t₁ n).app (tF₁.ιHeart.obj X.obj),
              naturality _ _ f := by
                refine (AcyclicObject T t₁ t₂).ι.map_injective ?_
                rw [Functor.map_comp, Functor.FullyFaithful.homEquiv_symm_apply,
                  (AcyclicObject T t₁ t₂).fullyFaithfulι.map_preimage,
                  Functor.map_comp, Functor.FullyFaithful.homEquiv_symm_apply,
                  (AcyclicObject T t₁ t₂).fullyFaithfulι.map_preimage]
                exact (FilteredToComplex_diff L₁ t₁ n).naturality f})
    sorry --(FilteredToComplex_condition L₁ t₁)

def FilteredAcyclicToComplexAcyclic :
    (FilteredAcyclic L₁ t₁ tF₁ t₂ T).FullSubcategory ⥤
    CochainComplex (AcyclicObject T t₁ t₂).FullSubcategory ℤ :=
  (FilteredAcyclicToComplexAcyclicObj L₁ t₁ tF₁ t₂ T).asFunctor

def FilteredAcyclicToComplexAcyclic_compat :
    FilteredAcyclicToComplexAcyclic L₁ t₁ tF₁ t₂ T ⋙
    (AcyclicObject T t₁ t₂).ι.mapHomologicalComplex _ ≅
    (FilteredAcyclic L₁ t₁ tF₁ t₂ T).ι ⋙ tF₁.ιHeart ⋙ FilteredToComplex L₁ t₁ := by
  refine NatIso.ofComponents (fun _ ↦ ?_) (fun _ ↦ ?_)
  · refine HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) (fun _ _ rel ↦ ?_)
    simp only [ComplexShape.up_Rel] at rel
    dsimp [FilteredToComplex, FilteredAcyclicToComplexAcyclic, FilteredAcyclicToComplexAcyclicObj,
      FilteredToComplexObj]
    rw [← rel]
    simp only [CochainComplex.of_d, id_comp, comp_id]
    rfl
  · ext
    dsimp [FilteredToComplex, FilteredAcyclicToComplexAcyclic, FilteredAcyclicToComplexAcyclicObj,
      FilteredToComplexObj]
    simp only [comp_id, id_comp]

instance : (FilteredAcyclicToComplexAcyclic L₁ t₁ tF₁ t₂ T).IsEquivalence := sorry

def FilteredAcyclicToComplexAcyclic_functor :
    FilteredAcyclicToComplexAcyclic L₁ t₁ tF₁ t₂ T ⋙ (T.FromAcyclic t₁ t₂).mapHomologicalComplex _
    ≅ (FilteredAcyclic L₁ t₁ tF₁ t₂ T).ι ⋙ tF₁.ιHeart ⋙ FT.functor
    ⋙ FilteredToComplex L₂ t₂ := by
  refine NatIso.ofComponents (fun X ↦ ?_) ?_
  · refine HomologicalComplex.Hom.isoOfComponents (fun n ↦ (FilteredAcyclicToComplex_deg_functor
      L₁ t₁ tF₁ L₂ t₂ tF₂ T FT n).app X) (fun n m rel ↦ ?_)
    simp only [ComplexShape.up_Rel] at rel
    rw [← rel]
    dsimp [FilteredToComplex, FilteredToComplexObj, FilteredAcyclicToComplexAcyclic,
      FilteredAcyclicToComplexAcyclicObj]
    simp only [CochainComplex.of_d]
    exact FilteredAcyclicToComplex_diff_functor L₁ t₁ tF₁ L₂ t₂ tF₂ T FT X n
  · intro _ _ f
    ext n
    exact (FilteredAcyclicToComplex_deg_functor L₁ t₁ tF₁ L₂ t₂ tF₂ T FT n).hom.naturality f

def DerivedFunctor_comp :
    DerivedFunctor t₁ t₂ T ⋙ Realization L₂ t₂ tF₂ ≅ Realization L₁ t₁ tF₁ ⋙ T := by
  dsimp [DerivedFunctor]
  refine Localization.liftNatIso (Functor.mapHomotopyCategory (T.AcyclicToHeart t₁ t₂)
    (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) (AcyclicComplexAcyclic t₁ t₂ T).W
    ((Functor.mapHomotopyCategory (T.FromAcyclic t₁ t₂)
    (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ⋙ Realization L₂ t₂ tF₂)
    ((Functor.mapHomotopyCategory (T.AcyclicToHeart t₁ t₂)
    (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ⋙ Realization L₁ t₁ tF₁ ⋙ T) _ _ ?_
  have : Localization.Lifting (HomotopyCategory.quotient (AcyclicCategory T t₁ t₂)
      (ComplexShape.up ℤ)) (HomologicalComplex.homotopyEquivalences (AcyclicCategory T t₁ t₂)
      (ComplexShape.up ℤ)) ((T.FromAcyclic t₁ t₂).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      HomotopyCategory.quotient t₂.Heart (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⋙
      Realization L₂ t₂ tF₂) (((T.FromAcyclic t₁ t₂).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh) ⋙ Realization L₂ t₂ tF₂) :=
    {iso' := isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫ (Functor.associator _ _ _).symm ≪≫
             isoWhiskerRight ((T.FromAcyclic t₁ t₂).mapHomotopyCategoryFactors (ComplexShape.up ℤ))
             (DerivedCategory.Qh ⋙ Realization L₂ t₂ tF₂) ≪≫ Functor.associator _ _ _}
  have : Localization.Lifting (HomotopyCategory.quotient (AcyclicCategory T t₁ t₂)
      (ComplexShape.up ℤ)) (HomologicalComplex.homotopyEquivalences (AcyclicCategory T t₁ t₂)
      (ComplexShape.up ℤ)) ((T.AcyclicToHeart t₁ t₂).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      HomotopyCategory.quotient t₁.Heart (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⋙
      Realization L₁ t₁ tF₁ ⋙ T) (((T.AcyclicToHeart t₁ t₂).mapHomotopyCategory (ComplexShape.up ℤ)
      ⋙ DerivedCategory.Qh) ⋙ Realization L₁ t₁ tF₁ ⋙ T) :=
    {iso' := isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫ (Functor.associator _ _ _).symm ≪≫
             isoWhiskerRight ((T.AcyclicToHeart t₁ t₂).mapHomotopyCategoryFactors
             (ComplexShape.up ℤ)) (DerivedCategory.Qh ⋙ Realization L₁ t₁ tF₁ ⋙ T) ≪≫
             Functor.associator _ _ _ }
  refine Localization.liftNatIso (HomotopyCategory.quotient (AcyclicCategory T t₁ t₂)
    (ComplexShape.up ℤ)) (HomologicalComplex.homotopyEquivalences (AcyclicCategory T t₁ t₂)
    (ComplexShape.up ℤ))
    (Functor.mapHomologicalComplex (T.FromAcyclic t₁ t₂) (ComplexShape.up ℤ) ⋙
    HomotopyCategory.quotient t₂.Heart (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⋙
    Realization L₂ t₂ tF₂)
    (Functor.mapHomologicalComplex (T.AcyclicToHeart t₁ t₂) (ComplexShape.up ℤ) ⋙
    HomotopyCategory.quotient t₁.Heart (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⋙
    Realization L₁ t₁ tF₁ ⋙ T)
    _ _ ?_
  refine isoWhiskerLeft _ (Functor.associator _ _ _).symm ≪≫ isoWhiskerLeft _ (isoWhiskerRight
    (DerivedCategory.quotientCompQhIso t₂.Heart) _) ≪≫ ?_ ≪≫ isoWhiskerLeft _ (isoWhiskerRight
    (DerivedCategory.quotientCompQhIso t₁.Heart).symm _) ≪≫
    isoWhiskerLeft _ (Functor.associator _ _ _)
  refine (Functor.leftUnitor _).symm ≪≫ ?_
  refine isoWhiskerRight (FilteredAcyclicToComplexAcyclic L₁ t₁ tF₁ t₂
    T).asEquivalence.counitIso.symm _ ≪≫ ?_
  refine Functor.associator _ _ _ ≪≫ Iso.inverseCompIso ?_
  dsimp
  refine (Functor.associator _ _ _).symm ≪≫ ?_
  refine isoWhiskerRight (FilteredAcyclicToComplexAcyclic_functor L₁ t₁ tF₁ L₂ t₂ tF₂ T FT) _ ≪≫ ?_
  refine isoWhiskerRight ((Functor.associator (FilteredAcyclic L₁ t₁ tF₁ t₂ T).ι tF₁.ιHeart
    (FT.functor ⋙ FilteredToComplex L₂ t₂)).symm ≪≫ (Functor.associator
    ((FilteredAcyclic L₁ t₁ tF₁ t₂ T).ι ⋙ tF₁.ιHeart) FT.functor (FilteredToComplex L₂ t₂)).symm
    ≪≫ isoWhiskerRight (Functor.associator (FilteredAcyclic L₁ t₁ tF₁ t₂ T).ι tF₁.ιHeart
    FT.functor) (FilteredToComplex L₂ t₂) ≪≫
    isoWhiskerRight (FilteredAcyclicToHeart_comp L₁ t₁ tF₁ L₂ t₂ tF₂ T FT).symm
    (FilteredToComplex L₂ t₂) ≪≫ Functor.associator
    (FilteredAcyclicToHeart L₁ t₁ tF₁ L₂ t₂ tF₂ T FT) tF₂.ιHeart (FilteredToComplex L₂ t₂))
    (DerivedCategory.Q ⋙ Realization L₂ t₂ tF₂) ≪≫ ?_
  refine Functor.associator (FilteredAcyclicToHeart L₁ t₁ tF₁ L₂ t₂ tF₂ T FT)
    (tF₂.ιHeart ⋙ FilteredToComplex L₂ t₂) (DerivedCategory.Q ⋙ Realization L₂ t₂ tF₂) ≪≫ ?_
  refine isoWhiskerLeft (FilteredAcyclicToHeart L₁ t₁ tF₁ L₂ t₂ tF₂ T FT)
    (Realization_comp_Q L₂ t₂ tF₂) ≪≫ ?_
  refine (Functor.associator (FilteredAcyclicToHeart L₁ t₁ tF₁ L₂ t₂ tF₂ T FT) tF₂.ιHeart
    (ForgetFiltration L₂)).symm  ≪≫ ?_
  refine isoWhiskerRight (FilteredAcyclicToHeart_comp L₁ t₁ tF₁ L₂ t₂ tF₂ T FT)
    (ForgetFiltration L₂) ≪≫ ?_
  refine ?_ ≪≫ Functor.associator (FilteredAcyclicToComplexAcyclic L₁ t₁ tF₁ t₂ T)
    ((AcyclicObject T t₁ t₂).ι.mapHomologicalComplex (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ Realization L₁ t₁ tF₁ ⋙ T)
  refine ?_ ≪≫ isoWhiskerRight (FilteredAcyclicToComplexAcyclic_compat L₁ t₁ tF₁ t₂ T).symm
    (DerivedCategory.Q ⋙ Realization L₁ t₁ tF₁ ⋙ T)
  refine ?_ ≪≫ (Functor.associator (FilteredAcyclic L₁ t₁ tF₁ t₂ T).ι
    (tF₁.ιHeart ⋙ FilteredToComplex L₁ t₁) (DerivedCategory.Q ⋙ Realization L₁ t₁ tF₁ ⋙ T)).symm
  refine ?_ ≪≫ isoWhiskerLeft (FilteredAcyclic L₁ t₁ tF₁ t₂ T).ι (isoWhiskerRight
    (Realization_comp_Q L₁ t₁ tF₁).symm T ≪≫ isoWhiskerRight
    (Functor.associator (tF₁.ιHeart ⋙ FilteredToComplex L₁ t₁) DerivedCategory.Q
    (Realization L₁ t₁ tF₁)).symm T ≪≫ Functor.associator ((tF₁.ιHeart ⋙ FilteredToComplex L₁ t₁)
    ⋙ DerivedCategory.Q) (Realization L₁ t₁ tF₁) T ≪≫ Functor.associator (tF₁.ιHeart ⋙
    FilteredToComplex L₁ t₁) DerivedCategory.Q (Realization L₁ t₁ tF₁ ⋙ T))
  refine Functor.associator (FilteredAcyclic L₁ t₁ tF₁ t₂ T).ι (tF₁.ιHeart ⋙ FT.functor)
    (ForgetFiltration L₂) ≪≫ ?_
  refine isoWhiskerLeft (FilteredAcyclic L₁ t₁ tF₁ t₂ T).ι ?_
  refine Functor.associator tF₁.ιHeart FT.functor (ForgetFiltration L₂) ≪≫ ?_
    ≪≫ (Functor.associator tF₁.ιHeart (ForgetFiltration L₁) T).symm
  exact isoWhiskerLeft tF₁.ιHeart (lifting_forgetFiltrating_comm L₁ L₂ FT)

end Triangulated.Filtered

end CategoryTheory
