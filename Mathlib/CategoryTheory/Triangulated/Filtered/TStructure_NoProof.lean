import Mathlib.CategoryTheory.Triangulated.Filtered.Filtered_NoProof
import Mathlib.CategoryTheory.Triangulated.TStructure.TExact
import Mathlib.CategoryTheory.Triangulated.TStructure.Homology
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.ShortComplex.Abelian

noncomputable section

open CategoryTheory Preadditive Limits Triangulated CategoryTheory.FilteredTriangulated

open scoped ZeroObject

namespace CategoryTheory

universe u v u₁ v₁ u₂ v₂ u₃ v₃

attribute [local instance] endofunctorMonoidalCategory

variable {C : Type u} [Category.{v, u} C] [HasShift C (ℤ × ℤ)] [Preadditive C] [HasZeroObject C]
  [∀ p : ℤ × ℤ, Functor.Additive (shiftFunctor C p)] [Pretriangulated C] [FilteredTriangulated C]
  [IsTriangulated C]

variable {A : Type u₁} [Category.{v₁} A] [HasShift A ℤ] [Preadditive A] [HasZeroObject A]
  [∀ p : ℤ, Functor.Additive (shiftFunctor A p)] [Pretriangulated A]
  [IsTriangulated A]

variable (L : isFilteredTriangulated_over C A) (t : TStructure A)

local instance : L.functor.CommShift ℤ := L.commShift

local instance : L.functor.IsTriangulated := L.triangulated

namespace Triangulated.TStructure

-- Definition A.2.1
class IsCompatible (tF : TStructure C) where
  exact_functor : L.functor.TExact t tF
  compat_shift (a b n : ℤ) (h : b + n = a) (X : C) (hX : TStructure.IsLE tF X a) :
      TStructure.IsLE tF ((shiftFunctor₂ C n).obj X) b
-- Here we reformulate the compatibility with shifts to make it easier to use.

-- Proposition A.2.2:
-- Construction of a compatible t-structure on `C` given a t-structure on `A`.
-- Note the ambiguity (we don't know whether the shift applies before or after `Gr`). It doesn't
-- matter because `Gr` commutes with shifts, but in Lean we need to make a choice.
def compatible : TStructure C where
  LE n X := ∀ (i : ℤ), TStructure.IsLE t (((Gr L i).obj X)⟦i⟧) n
  GE n X := ∀ (i : ℤ), TStructure.IsGE t (((Gr L i).obj X)⟦i⟧) n
  LE_closedUnderIsomorphisms n :=
    {of_iso {X Y} e h i := t.isLE_of_iso ((shiftFunctor A i).mapIso ((Gr L i).mapIso e)) n}
  GE_closedUnderIsomorphisms n :=
    {of_iso {X Y} e h i := t.isGE_of_iso ((shiftFunctor A i).mapIso ((Gr L i).mapIso e)) n}
  LE_shift n a n' h X hX i := by
    have : t.IsLE ((shiftFunctor A a).obj ((shiftFunctor A i).obj ((Gr L i).obj X))) n' := by
      exact t.isLE_shift _ n a n' h
    exact t.isLE_of_iso ((shiftFunctor A i).mapIso (((Gr L i).commShiftIso a).app X)
      ≪≫ shiftComm _ a i).symm n'
  GE_shift n a n' h X hX i := by
    have : t.IsGE ((shiftFunctor A a).obj ((shiftFunctor A i).obj ((Gr L i).obj X))) n' := by
      exact t.isGE_shift _ n a n' h
    exact t.isGE_of_iso ((shiftFunctor A i).mapIso (((Gr L i).commShiftIso a).app X)
      ≪≫ shiftComm _ a i).symm n'
  zero' X Y f hX hY := by
    dsimp at hX hY
    sorry -- this one actually takes nontrivial work (the fact that each object of `C` is
          -- a successive extension of its graded pieces)
  LE_zero_le X hX i := t.isLE_of_LE _ 0 1 zero_le_one
  GE_one_le X hX i := t.isGE_of_GE _ 0 1 zero_le_one
  exists_triangle_zero_one := sorry
-- This one also takes a bit of work! (Induction on the length of the filtration, but the
-- induction step will use the uniqueness of the triangle.)

-- Proposition A.2.2:
-- Compatibility of the constructed t-structure on `C`.
instance compatible_is_compatible : t.IsCompatible L (t.compatible L) where
  exact_functor := by
    refine {rightTExact := {objGE := fun X n _ ↦ {ge i := ?_}},
            leftTExact := {objLE := fun X n _ ↦ {le i := ?_}}}
    · dsimp [compatible]
      by_cases h : i = 0
      · have : t.IsGE (((𝟭 A).obj X)⟦i⟧) n := by
          have : t.IsGE ((𝟭 A).obj X) n := by dsimp; infer_instance
          exact t.isGE_of_iso ((shiftFunctorZero' A i h).app X).symm n
        exact t.isGE_of_iso ((shiftFunctor A i).mapIso ((Gr_pure_of_zero L i h).app X)).symm n
      · exact t.isGE_of_isZero _ (Functor.map_isZero (shiftFunctor A i)
          (Gr_pure_zero_of_ne_zero L h X)) n
    · by_cases h : i = 0
      · have : t.IsLE (((𝟭 A).obj X)⟦i⟧) n := by
          have : t.IsLE ((𝟭 A).obj X) n := by dsimp; infer_instance
          exact t.isLE_of_iso ((shiftFunctorZero' A i h).app X).symm n
        exact t.isLE_of_iso ((shiftFunctor A i).mapIso ((Gr_pure_of_zero L i h).app X)).symm n
      · exact t.isLE_of_isZero _ (Functor.map_isZero (shiftFunctor A i)
          (Gr_pure_zero_of_ne_zero L h X)) n
  compat_shift a b n h X hX := by
    refine {le := fun i ↦ ?_}
    dsimp [compatible] at hX ⊢
    have := hX.le (i - n)
    have : t.IsLE ((shiftFunctor A (i - n) ⋙ shiftFunctor A n).obj ((Gr L (i - n)).obj X)) b :=
      t.isLE_shift _ a n b (by rw [add_comm, h])
    exact t.isLE_of_iso ((shiftFunctor A i).mapIso (((Gr_commShift L).iso i n (i - n)
      (by simp)).app X) ≪≫ (shiftFunctorAdd' A (i - n) n i (by simp)).app _).symm b

-- Proposition A.2.2:
-- Uniqueness of the compatible t-structure.
lemma compatible_uniq (tF : TStructure C) [t.IsCompatible L tF] : tF = t.compatible L := sorry

section Realization

-- Theorem A.2.3
-- First we need to construct the functor `H_F : C → CochainComplex t.Heart ℤ`.
-- In the paper, the `n`th degree of `H_F X` is defined as
-- `(t.homology n).obj ((Gr L n).obj X)`. Using `ForgetFiltration_for_Gr`, we can reformulate
-- this as `(t.homology n).obj ((ForgetFiltration L).obj ((truncGELE n n).obj X))`, which
-- is useful to construct the differentials.

variable (tF : TStructure C)

local instance : t.HasHeart := hasHeartFullSubcategory t

local instance : tF.HasHeart := hasHeartFullSubcategory tF

noncomputable local instance : t.HasHomology₀ := t.hasHomology₀
noncomputable local instance : tF.HasHomology₀ := tF.hasHomology₀

noncomputable local instance : t.homology₀.ShiftSequence ℤ :=
  Functor.ShiftSequence.tautological _ _

noncomputable local instance : tF.homology₀.ShiftSequence ℤ :=
  Functor.ShiftSequence.tautological _ _

-- Theorem A.2.3(i):
-- The functor is well-defined.
def FilteredToComplex_aux₁ (X : C) (n : ℤ) : t.Heart :=
  (t.homology n).obj ((ForgetFiltration L).obj
    ((CategoryTheory.truncGELE n n).obj X))

def FilteredToComplex_aux₂ (X : C) (n : ℤ) :
    FilteredToComplex_aux₁ L t X n ⟶ FilteredToComplex_aux₁ L t X (n + 1) :=
  t.homologyδ ((ForgetFiltration L).mapTriangle.obj ((truncGELE_triangle n n (n + 1)
    (le_refl _) (by simp)).obj X)) n (n + 1) rfl

def FilteredToComplex_aux₃ (X : C) (n : ℤ) :
    FilteredToComplex_aux₂ L t X n ≫ FilteredToComplex_aux₂ L t X (n + 1) = 0 := by
-- We don't need the triangle to be distinguished to define the connecting
-- morphism, but we will need it to check that the differentials
-- compose to 0.
  have := (ForgetFiltration L).map_distinguished _ (truncGELE_triangle_distinguished
      n n (n + 1) (le_refl _) (by simp) X)
  sorry

def FilteredToComplexObj (X : C) : CochainComplex t.Heart ℤ :=
  CochainComplex.of (FilteredToComplex_aux₁ L t X)
    (FilteredToComplex_aux₂ L t X) (FilteredToComplex_aux₃ L t X)

def FilteredToComplexHom {X Y : C} (f : X ⟶ Y) :
    FilteredToComplexObj L (t := t) X ⟶ FilteredToComplexObj L (t := t) Y := by
  refine CochainComplex.ofHom (FilteredToComplex_aux₁ L t X)
    (FilteredToComplex_aux₂ L t X) (FilteredToComplex_aux₃ L t X)
    (FilteredToComplex_aux₁ L t Y)
    (FilteredToComplex_aux₂ L t Y) (FilteredToComplex_aux₃ L t Y)
    (fun n ↦ ?_) (fun n ↦ ?_)
  · exact (t.homology n).map ((ForgetFiltration L).map
      ((CategoryTheory.truncGELE n n).map f))
  · dsimp [FilteredToComplex_aux₂]
    sorry

def FilteredToComplex : C ⥤ CochainComplex t.Heart ℤ where
  obj X := FilteredToComplexObj L t X
  map f := FilteredToComplexHom L t f
  map_id X := by
    ext
    dsimp [FilteredToComplexHom, FilteredToComplexObj, FilteredToComplex_aux₁]
    simp
  map_comp f g := by
    ext
    dsimp [FilteredToComplexHom, FilteredToComplexObj, FilteredToComplex_aux₁]
    simp

-- Theorem A.2.3(i):
-- The restriction of `FilteredToComplex` to the heart of `tF` is
-- an equivalence.
instance FilteredToComplex_equivalence [t.IsCompatible L tF] :
    (tF.ιHeart ⋙ FilteredToComplex L t).IsEquivalence := sorry

variable [t.IsCompatible L tF]

-- Theorem A.2.3(i):
-- Indentification of the cohomology functor of `tF`. Again we have
-- an "equality" statement that is actually an "existence of isomorphism"
-- statement, and again the properties of that isomorphism are not clear
-- from the statement.
def HomologyFunctor_iso :
    FilteredToComplex L t ⋙ (tF.ιHeart ⋙ FilteredToComplex L t).inv ≅
    tF.homology 0 := sorry

-- Theorem A.2.3(ii):
-- We want the functor to send quasi-isomorphisms to isomorphisms.
def Realization_aux :
    (HomologicalComplex.quasiIso t.Heart (ComplexShape.up ℤ)).IsInvertedBy
    ((tF.ιHeart ⋙ FilteredToComplex L t).inv ⋙ tF.ιHeart ⋙
    (ForgetFiltration L)) := sorry

local instance : HasDerivedCategory t.Heart :=
  HasDerivedCategory.standard t.Heart

-- Definition A.2.4:
def Realization : DerivedCategory t.Heart ⥤ A :=
  have := MorphismProperty.instIsLocalizationLocalization'Q'
    (HomologicalComplex.quasiIso t.Heart (ComplexShape.up ℤ))
  Localization.lift ((tF.ιHeart ⋙ FilteredToComplex L t).inv ⋙ tF.ιHeart ⋙
    (ForgetFiltration L)) (Realization_aux L t tF)
    (HomologicalComplex.quasiIso t.Heart (ComplexShape.up ℤ)).Q'

end Realization



end Triangulated.TStructure





end CategoryTheory
