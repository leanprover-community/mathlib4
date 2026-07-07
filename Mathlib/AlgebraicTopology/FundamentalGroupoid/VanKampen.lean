module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
public import Mathlib.Topology.Sheaves.SheafCondition.PairwiseIntersections

/-!
# Van Kampen theorem

# References
- May
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace
open scoped FundamentalGroupoid

universe u

variable {X : TopCat.{u}}

noncomputable section

namespace FundamentalGroupoid

def opensToGrpd (X : TopCat.{u}) : Opens X ⥤ Grpd :=
  Opens.toTopCat X ⋙ π

scoped notation "πₒ" => FundamentalGroupoid.opensToGrpd

variable {ι : Type*} {U : ι → Opens X}

variable (U) in
def isColimit_opensToGrpd_mapCocone : IsColimit ((πₒ X).mapCocone (Pairwise.cocone U)) where
  desc c := sorry
  fac := sorry
  uniq := sorry

variable (U) in
instance preservesColimit_opensToGrpd : PreservesColimit (Pairwise.diagram U) (πₒ X) :=
  preservesColimit_of_preserves_colimit_cocone
    (Pairwise.coconeIsColimit U) (isColimit_opensToGrpd_mapCocone U)

/-- The **van Kampen theorem**: the fundamental groupoid functor is a cosheaf. -/
theorem isSheaf_op_opensToGrpd : TopCat.Presheaf.IsSheaf (πₒ X).op := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafPreservesLimitPairwiseIntersections]
  intro ι U
  infer_instance

end FundamentalGroupoid
