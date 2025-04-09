import Mathlib.CategoryTheory.Triangulated.Filtered.Filtered_NoProof
import Mathlib.CategoryTheory.Triangulated.TStructure.TExact
import Mathlib.CategoryTheory.Triangulated.TStructure.Homology
import Mathlib.Algebra.Homology.HomologicalComplex

noncomputable section

open CategoryTheory Preadditive Limits Triangulated CategoryTheory.FilteredTriangulated

open scoped ZeroObject

namespace CategoryTheory

universe u v u₁ v₁ u₂ v₂ u₃ v₃

attribute [local instance] endofunctorMonoidalCategory

variable {C : Type u} [Category.{v, u} C] [HasShift C (ℤ × ℤ)] [Preadditive C] [HasZeroObject C]
  [∀ p : ℤ × ℤ, Functor.Additive (shiftFunctor C p)] [Pretriangulated C] [FilteredTriangulated C]

variable {A : Type u₁} [Category.{v₁} A] [HasShift A ℤ] [Preadditive A] [HasZeroObject A]
  [∀ p : ℤ, Functor.Additive (shiftFunctor A p)] [Pretriangulated A]

variable (L : isFilteredTriangulated_over C A) (t : TStructure A)

local instance : L.functor.CommShift ℤ := L.commShift

local instance : L.functor.IsTriangulated := L.triangulated

namespace Triangulated.TStructure

-- Definition A.2.1
structure IsCompatible (tF : TStructure C) where
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
def compatible_is_compatible : t.IsCompatible L (t.compatible L) where
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
lemma compatible_uniq (tF : TStructure C) (h : t.IsCompatible L tF) : tF = t.compatible L := sorry

section Realization

-- Theorem A.2.3
-- First we need to construct the functor `H_F : C → CochainComplex t.Heart ℤ`.
-- In the paper, the `n`th degree of `H_F X` is defined as
-- `(t.homology n).obj ((Gr L n).obj X)`. Using `ForgetFiltration_for_Gr`, we can reformulate
-- this as `(t.homology n).obj ((ForgetFiltration L).obj ((truncGELE n n).obj X))`, which
-- is useful to construct the differentials.

variable {t}
variable {tF : TStructure C} (comp : t.IsCompatible L tF)

variable [t.HasHeart] [tF.HasHeart] [t.HasHomology₀] [tF.HasHomology₀]
  [t.homology₀.ShiftSequence ℤ] [tF.homology₀.ShiftSequence ℤ]

def H := t.homology 0

def FilteredToComplexObj (X : C) : CochainComplex t.Heart ℤ := by
  refine CochainComplex.of (fun n ↦ (t.homology n).obj ((ForgetFiltration L).obj
    ((CategoryTheory.truncGELE n n).obj X))) (fun n ↦ ?_) ?_
  · dsimp
    have := (truncGELE_triangle n n (n + 1) sorry sorry).obj X
  · sorry

def FilteredToComplex : C ⥤ CochainComplex A ℤ := by sorry

end Realization


end Triangulated.TStructure





end CategoryTheory
