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

abbrev FilteredAcyclicToComplex_aux₁ (X : (FilteredAcyclic L₁ t₁ tF₁ t₂ T).FullSubcategory)
    (n : ℤ) : (AcyclicObject T t₁ t₂).FullSubcategory :=
  ⟨FilteredToComplex_aux₁ L₁ t₁ X.1.1 n, X.2 n⟩

def FilteredAcyclicToComplexObj (X : (FilteredAcyclic L₁ t₁ tF₁ t₂ T).FullSubcategory) :
    CochainComplex (AcyclicObject T t₁ t₂).FullSubcategory ℤ :=
  CochainComplex.of (FilteredAcyclicToComplex_aux₁ L₁ t₁ tF₁ t₂ T X)
    (FilteredToComplex_aux₂ L₁ t₁ X.1.1)
    (FilteredToComplex_aux₃ L₁ t₁ X.1.1)

def FilteredAcyclicToComplexAcyclic :
    (FilteredAcyclic L₁ t₁ tF₁ t₂ T).FullSubcategory ⥤
    CochainComplex (AcyclicObject T t₁ t₂).FullSubcategory ℤ where
  obj X := FilteredAcyclicToComplexObj L₁ t₁ tF₁ t₂ T X
  map f :=
    {
      f := (FilteredToComplexHom L₁ t₁ f).f,
      comm' := (FilteredToComplexHom L₁ t₁ f).comm'
    }
  map_id X := by
    ext
    dsimp [FilteredToComplexHom, FilteredToComplexObj, FilteredToComplex_aux₁, Gr]
    erw [Functor.map_id, Functor.map_id, Functor.map_id, Functor.map_id]
    rfl
  map_comp f g := by
    ext
    dsimp [FilteredToComplexHom, FilteredToComplexObj, FilteredToComplex_aux₁]
    erw [Functor.map_comp, Functor.map_comp, Functor.map_comp, Functor.map_comp]
    rfl

def FilteredAcyclicToComplexAcyclic_compat :
    FilteredAcyclicToComplexAcyclic L₁ t₁ tF₁ t₂ T ⋙
    (AcyclicObject T t₁ t₂).ι.mapHomologicalComplex _ ≅
    (FilteredAcyclic L₁ t₁ tF₁ t₂ T).ι ⋙ tF₁.ιHeart ⋙ FilteredToComplex L₁ t₁ := by
  refine NatIso.ofComponents (fun _ ↦ ?_) (fun _ ↦ ?_)
  · refine HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) (fun _ _ _ ↦ ?_)
    dsimp
    erw [Category.id_comp, Category.comp_id]
    rfl
  · ext
    dsimp
    erw [Category.comp_id, Category.id_comp]
    rfl

instance : (FilteredAcyclicToComplexAcyclic L₁ t₁ tF₁ t₂ T).IsEquivalence := sorry

def FilteredAcyclicToComplexAcyclic_functor :
    FilteredAcyclicToComplexAcyclic L₁ t₁ tF₁ t₂ T ⋙ (T.FromAcyclic t₁ t₂).mapHomologicalComplex _
    ≅ FilteredAcyclicToHeart L₁ t₁ tF₁ L₂ t₂ tF₂ T FT ⋙ tF₂.ιHeart ⋙ FilteredToComplex L₂ t₂ :=
  sorry

#exit

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
  refine Functor.associator _ _ (DerivedCategory.Q ⋙ Realization L₂ t₂ tF₂) ≪≫ ?_
  refine isoWhiskerLeft _ (Realization_comp_Q L₂ t₂ tF₂) ≪≫ ?_
  refine ?_ ≪≫ Functor.associator _ _ _
  refine ?_ ≪≫ isoWhiskerRight (FilteredAcyclicToComplexAcyclic_compat L₁ t₁ tF₁ t₂ T).symm _
  refine (Functor.associator _ _ _).symm ≪≫ ?_
  refine isoWhiskerRight (FilteredAcyclicToHeart_comp L₁ t₁ tF₁ L₂ t₂ tF₂ T FT) _ ≪≫ ?_
  refine Functor.associator _ _ _ ≪≫ ?_ ≪≫
    (Functor.associator (FilteredAcyclic L₁ t₁ tF₁ t₂ T).ι (tF₁.ιHeart ⋙ FilteredToComplex L₁ t₁)
    (DerivedCategory.Q ⋙ Realization L₁ t₁ tF₁ ⋙ T)).symm
  refine isoWhiskerLeft (FilteredAcyclic L₁ t₁ tF₁ t₂ T).ι ?_
  refine ?_ ≪≫ Functor.associator _ _ _ ≪≫ Functor.associator _ _ _
  refine ?_ ≪≫ isoWhiskerRight (Functor.associator _ _ _).symm T
  refine ?_ ≪≫ isoWhiskerRight (Realization_comp_Q L₁ t₁ tF₁).symm T
  refine Functor.associator tF₁.Heart _ _ ≪≫ ?_ ≪≫ (Functor.associator tF₁.Heart _ _).symm
  exact isoWhiskerLeft tF₁.ιHeart (lifting_forgetFiltrating_comm L₁ L₂ FT)

end Triangulated.Filtered

end CategoryTheory
