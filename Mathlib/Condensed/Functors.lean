import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.Condensed.Abelian
import Mathlib.Condensed.Equivalence

universe u v

open CategoryTheory Limits

instance : PreservesLimits uliftFunctor.{v} := sorry

def Condensed.ulift : Condensed.{u} (Type u) ⥤ CondensedSet.{u} :=
  sheafCompose (coherentTopology CompHaus) uliftFunctor.{u+1}

def CompHaus.toCondensed_aux : CompHaus.{u} ⥤ Condensed (Type u) where
  obj S := {
    val := yoneda.obj S
    cond := by
       rw [isSheaf_iff_isSheaf_of_type]
       exact coherentTopology.isSheaf_yoneda_obj S }
  map f := ⟨yoneda.map f⟩

def CompHaus.toCondensed : CompHaus.{u} ⥤ CondensedSet.{u} := toCondensed_aux ⋙ Condensed.ulift

def Profinite.toCondensed : Profinite.{u} ⥤ CondensedSet.{u} := sorry

def Stonean.toCondensed : Stonean.{u} ⥤ CondensedSet.{u} := sorry
