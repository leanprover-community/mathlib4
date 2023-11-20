import Mathlib.Topology.Category.Profinite.Basic

open CategoryTheory Limits FintypeCat

structure LightProfinite where
  diagram : ℕ ⥤ FintypeCat
  cone : Cone (diagram ⋙ toProfinite)
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
