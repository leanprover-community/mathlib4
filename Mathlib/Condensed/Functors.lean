import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import Mathlib.CategoryTheory.Limits.Preserves.Ulift
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.Condensed.Abelian
import Mathlib.Condensed.Explicit
import Mathlib.Topology.Category.Yoneda

universe u v

open CategoryTheory Limits ContinuousMap

section Universes

-- noncomputable instance : PreservesLimitsOfSize.{u+1} uliftFunctor.{u+1, u} := sorry

def Condensed.ulift : Condensed.{u} (Type u) ⥤ CondensedSet.{u} := by
  refine @sheafCompose _ _ _ _ _ _ (coherentTopology CompHaus) uliftFunctor.{u+1, u} ?_
  intro X S P
  let K := MulticospanIndex.multicospan (GrothendieckTopology.Cover.index S P)
  let I := WalkingMulticospan (GrothendieckTopology.Cover.index S P).fstTo
    (GrothendieckTopology.Cover.index S P).sndTo
  cases' S with S hS
  sorry
  -- We need to preserve a large limit...
  -- TODO: define `sheafCompose` for the coherent topology, where it is enough to preserve a finite
  -- limit. Then the stuff in `CategoryTheory/Preserves/Ulift` applies.

end Universes

section Topology

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

noncomputable
def topCatToCondensed : TopCat.{u+1} ⥤ CondensedSet.{u} where
  obj X := X.toCondensed
  map f := ⟨⟨fun _ g ↦ ContinuousMap.comp f g, by aesop⟩⟩

def CompHaus.toCondensed_aux (S : CompHaus.{u}) : Condensed.{u} (Type u) where
  val := yoneda.obj S
  cond := by
    rw [isSheaf_iff_isSheaf_of_type]
    exact coherentTopology.isSheaf_yoneda_obj S

def compHausToCondensed_aux : CompHaus.{u} ⥤ Condensed.{u} (Type u) where
  obj S := S.toCondensed_aux
  map f := ⟨yoneda.map f⟩

def compHausToCondensed : CompHaus.{u} ⥤ CondensedSet.{u} :=
  compHausToCondensed_aux ⋙ Condensed.ulift

def profiniteToCondensed : Profinite.{u} ⥤ CondensedSet.{u} :=
  profiniteToCompHaus ⋙ compHausToCondensed

def stoneanToCondensed : Stonean.{u} ⥤ CondensedSet.{u} :=
  Stonean.toCompHaus -- TODO: make this naming consistent.
  ⋙ compHausToCondensed

end Topology
