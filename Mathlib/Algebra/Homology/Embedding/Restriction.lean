import Mathlib.Algebra.Homology.Embedding.Basic

open CategoryTheory Category Limits ZeroObject

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

namespace HomologicalComplex

variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]

section

variable (K L M : HomologicalComplex C c') (φ : K ⟶ L) (φ' : L ⟶ M)
  (e : c.Embedding c') [e.IsRelIff]

@[simps]
def restriction : HomologicalComplex C c where
  X i := K.X (e.f i)
  d _ _ := K.d _ _
  shape i j hij := K.shape _ _ (by simpa only [← e.rel_iff] using hij)

variable {K L}

@[simps]
def restrictionMap : K.restriction e ⟶ L.restriction e where
  f i := φ.f (e.f i)

variable (K)

@[simp]
lemma restrictionMap_id : restrictionMap (𝟙 K) e = 𝟙 _ := by aesop_cat

@[simp, reassoc]
lemma restrictionMap_comp :
    restrictionMap (φ ≫ φ') e = restrictionMap φ e ≫ restrictionMap φ' e := by aesop_cat

end

end HomologicalComplex

namespace ComplexShape.Embedding

variable (e : Embedding c c') (C : Type*) [Category C] [HasZeroMorphisms C] [HasZeroObject C]

@[simps]
noncomputable def restrictionFunctor [e.IsRelIff] :
    HomologicalComplex C c' ⥤ HomologicalComplex C c where
  obj K := K.restriction e
  map φ := HomologicalComplex.restrictionMap φ e

end ComplexShape.Embedding
