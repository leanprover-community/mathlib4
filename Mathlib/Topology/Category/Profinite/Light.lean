import Mathlib.Topology.Category.Profinite.Basic

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
