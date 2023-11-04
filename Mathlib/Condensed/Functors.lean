import Mathlib.Condensed.Abelian
import Mathlib.Condensed.Explicit
import Mathlib.Topology.Category.Yoneda

universe u v

open CategoryTheory Limits ContinuousMap

noncomputable
def TopCat.toCondensed (X : TopCat.{u+1}) : CondensedSet.{u} := sorry
  -- @ofSheafCompHaus (ContinuousMap.coyoneda.{u, u+1, u, u+1} compHausToTop.{u} X)
  -- (instPreservesFiniteProductsOppositeOppositeTypeTypesCoyoneda.{u, u+1} X.1 compHausToTop) sorry

def topCatToCondensed : TopCat.{u+1} ⥤ CondensedSet.{u} := sorry

def CompHaus.toCondensed (S : CompHaus.{u}) : CondensedSet.{u} := sorry

def compHausToCondensed : CompHaus.{u} ⥤ CondensedSet.{u} := sorry

def Profinite.toCondensed (S : Profinite.{u}) : CondensedSet.{u} := sorry

def profiniteToCondensed : Profinite.{u} ⥤ CondensedSet.{u} := sorry

def Stonean.toCondensed (S : Stonean.{u}) : CondensedSet.{u} := sorry

def stoneanToCondensed : Stonean.{u} ⥤ CondensedSet.{u} := sorry

def Condensed.forget : CondensedAb.{u} ⥤ CondensedSet.{u} := sorry
