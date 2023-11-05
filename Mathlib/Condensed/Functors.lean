import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import Mathlib.Condensed.Abelian
import Mathlib.Condensed.Explicit
import Mathlib.Topology.Category.Yoneda

universe u v

open CategoryTheory Limits ContinuousMap

instance : PreservesFiniteProducts compHausToTop.{u}.op where
  preserves J _ := by
    apply (config := { allowSynthFailures := true }) preservesLimitsOfShapeOp
    exact preservesColimitsOfShapeOfEquiv (Discrete.opposite J).symm _

noncomputable
def TopCat.toCondensed (X : TopCat.{u+1}) : CondensedSet.{u} :=
  @Condensed.ofSheafCompHaus (ContinuousMap.coyoneda.{u, u+1, u, u+1} compHausToTop.{u} X) _ (by
    apply (config := { allowSynthFailures := true }) EqualizerConditionCoyoneda X compHausToTop.{u}
    intro Z B π he
    rw [CompHaus.effectiveEpi_iff_surjective] at he
    apply QuotientMap.of_surjective_continuous he π.continuous )

def topCatToCondensed : TopCat.{u+1} ⥤ CondensedSet.{u} := sorry

def CompHaus.toCondensed (S : CompHaus.{u}) : CondensedSet.{u} := sorry

def compHausToCondensed : CompHaus.{u} ⥤ CondensedSet.{u} := sorry

def Profinite.toCondensed (S : Profinite.{u}) : CondensedSet.{u} := sorry

def profiniteToCondensed : Profinite.{u} ⥤ CondensedSet.{u} := sorry

def Stonean.toCondensed (S : Stonean.{u}) : CondensedSet.{u} := sorry

def stoneanToCondensed : Stonean.{u} ⥤ CondensedSet.{u} := sorry

def Condensed.forget : CondensedAb.{u} ⥤ CondensedSet.{u} := sorry
