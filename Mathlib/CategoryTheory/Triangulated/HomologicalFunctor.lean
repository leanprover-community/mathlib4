import Mathlib.CategoryTheory.Triangulated.Triangulated
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Abelian.Basic

namespace CategoryTheory

open Category Limits Pretriangulated

variable {C A : Type _} [Category C] [HasZeroObject C]
  [HasShift C ℤ] [Preadditive C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C]
  [Category A] [Abelian A]

namespace Functor

variable (F : C ⥤ A) [F.PreservesZeroMorphisms]

class IsHomological : Prop where
  exact : ∀ (T : Triangle C) (hT : T ∈ distTriang C),
    ((shortComplex_of_dist_triangle T hT).map F).Exact

lemma map_distinguished_exact₂ [F.IsHomological] (T : Triangle C) (hT : T ∈ distTriang C) :
    ((shortComplex_of_dist_triangle T hT).map F).Exact :=
  IsHomological.exact _ hT

end Functor

end CategoryTheory
