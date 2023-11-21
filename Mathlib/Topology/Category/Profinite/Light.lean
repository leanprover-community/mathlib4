import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.CategoryTheory.Sites.RegularExtensive
import Mathlib.CategoryTheory.Sites.Sheafification

universe u

open CategoryTheory Limits FintypeCat

structure LightProfinite : Type (u+1) where
  diagram : ℕ ⥤ FintypeCat
  cone : Cone (diagram ⋙ toProfinite.{u})
  isLimit : IsLimit cone

namespace LightProfinite

def toProfinite (S : LightProfinite) : Profinite := S.cone.pt

instance : Category LightProfinite := InducedCategory.category toProfinite

instance concreteCategory : ConcreteCategory LightProfinite := InducedCategory.concreteCategory _

@[simps!]
def lightToProfinite : LightProfinite ⥤ Profinite := inducedFunctor _

instance : Faithful lightToProfinite := show Faithful <| inducedFunctor _ from inferInstance

instance : Full lightToProfinite := show Full <| inducedFunctor _ from inferInstance

end LightProfinite

structure LightProfinite' : Type u where
  diagram : ℕ ⥤ FintypeCat.Skeleton.{u}

namespace LightProfinite'

noncomputable section

def toProfinite (S : LightProfinite') : Profinite :=
  limit (S.diagram  ⋙ FintypeCat.Skeleton.equivalence.functor ⋙ FintypeCat.toProfinite.{u})

instance : Category LightProfinite' := InducedCategory.category toProfinite

instance : SmallCategory LightProfinite' := inferInstance

instance concreteCategory : ConcreteCategory LightProfinite' := InducedCategory.concreteCategory _

@[simps!]
def lightToProfinite' : LightProfinite' ⥤ Profinite := inducedFunctor _

instance : Faithful lightToProfinite' := show Faithful <| inducedFunctor _ from inferInstance

instance : Full lightToProfinite' := show Full <| inducedFunctor _ from inferInstance

end

end LightProfinite'

noncomputable section Equivalence

def smallToLight : LightProfinite' ⥤ LightProfinite where
  obj X := ⟨X.diagram ⋙ Skeleton.equivalence.functor, _, limit.isLimit _⟩
  map f := f

instance : Faithful smallToLight := ⟨id⟩

instance : Full smallToLight := ⟨id, fun _ ↦ rfl⟩

instance : EssSurj smallToLight := by
  constructor
  intro Y
  let i : limit (((Y.diagram ⋙ Skeleton.equivalence.inverse) ⋙ Skeleton.equivalence.functor) ⋙
    toProfinite) ≅ Y.cone.pt := (Limits.lim.mapIso (isoWhiskerRight ((Functor.associator _ _ _) ≪≫
    (isoWhiskerLeft Y.diagram Skeleton.equivalence.counitIso)) toProfinite)) ≪≫
    IsLimit.conePointUniqueUpToIso (limit.isLimit _) Y.isLimit
  exact ⟨⟨Y.diagram ⋙ Skeleton.equivalence.inverse⟩, ⟨⟨i.hom, i.inv, i.hom_inv_id, i.inv_hom_id⟩⟩⟩
  -- why can't I just write `i`?

instance : IsEquivalence smallToLight := Equivalence.ofFullyFaithfullyEssSurj _

def LightProfinite.equivSmall : LightProfinite ≌ LightProfinite' := smallToLight.asEquivalence.symm

instance : EssentiallySmall LightProfinite where
  equiv_smallCategory := ⟨LightProfinite', inferInstance, ⟨LightProfinite.equivSmall⟩⟩

end Equivalence

instance : Precoherent LightProfinite := sorry

variable (P : LightProfinite.{0}ᵒᵖ ⥤ Type)

-- #check (coherentTopology LightProfinite.{0}).sheafify P (D := Type)
-- Doesn't work, need a universe bump because `LightProfinite` is large.

instance : Precoherent LightProfinite' := sorry

variable (P : LightProfinite'.{0}ᵒᵖ ⥤ Type)

-- #check (coherentTopology LightProfinite'.{0}).sheafify P (D := Type)
-- Works because `LightProfinite'` is actually small.

-- TODO: provide API to sheafify over essentially small categories
