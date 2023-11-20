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

structure LightProfiniteExplicit : Type (u+1) where
  diagram : ℕ ⥤ FintypeCat.{u}

namespace LightProfiniteExplicit

noncomputable section

def toProfinite (S : LightProfiniteExplicit) : Profinite := limit <|
  S.diagram ⋙ FintypeCat.toProfinite

instance : Category LightProfiniteExplicit := InducedCategory.category toProfinite

instance concreteCategory : ConcreteCategory LightProfinite := InducedCategory.concreteCategory _

@[simps!]
def lightToProfinite : LightProfinite ⥤ Profinite := inducedFunctor _

instance : Faithful lightToProfinite := show Faithful <| inducedFunctor _ from inferInstance

instance : Full lightToProfinite := show Full <| inducedFunctor _ from inferInstance

end

end LightProfiniteExplicit

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

def explicitToSmall_aux : LightProfiniteExplicit ⥤ LightProfinite' where
  obj X := ⟨X.diagram ⋙ Skeleton.equivalence.inverse⟩
  map f := sorry
  map_id := sorry
  map_comp := sorry

def lightToSmall_aux : LightProfinite ⥤ LightProfiniteExplicit where
  obj X := ⟨X.diagram⟩
  map {X Y} f := ((IsLimit.conePointUniqueUpToIso X.isLimit (limit.isLimit _)).inv ≫ f ≫
      (IsLimit.conePointUniqueUpToIso Y.isLimit (limit.isLimit _)).hom : _)
  map_id X := by
    simp only [limit.cone_x]
    erw [Category.id_comp]
    simp only [Iso.inv_hom_id]
    rfl
  map_comp {X Y Z} f g := by
    simp only [limit.cone_x]
    change _ = _ ≫ _ ≫ (IsLimit.conePointUniqueUpToIso Y.isLimit (limit.isLimit _)).hom  ≫
      (IsLimit.conePointUniqueUpToIso Y.isLimit (limit.isLimit _)).inv ≫ _ ≫ _
    rw [Iso.hom_inv_id_assoc]
    rfl

def lightToSmall : LightProfinite ⥤ LightProfinite' := lightToSmall_aux ⋙ explicitToSmall_aux

def smallToLight : LightProfinite' ⥤ LightProfinite where
  obj X := ⟨X.diagram ⋙ Skeleton.equivalence.functor, _, limit.isLimit _⟩
  map f := f

def LightProfinite.equivSmall : LightProfinite ≌ LightProfinite' where
  functor := lightToSmall_aux ⋙ explicitToSmall_aux
  inverse := smallToLight
  unitIso := sorry
  counitIso := sorry
  functor_unitIso_comp := sorry

end Equivalence
