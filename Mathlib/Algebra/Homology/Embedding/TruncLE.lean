import Mathlib.Algebra.Homology.Embedding.TruncGE
import Mathlib.Algebra.Homology.Opposite

open CategoryTheory Limits

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]

namespace HomologicalComplex

variable (K L M : HomologicalComplex C c') (φ : K ⟶ L) (φ' : L ⟶ M)
    (e : c.Embedding c') [e.IsTruncLE]
  [∀ i', K.HasHomology i'] [∀ i', L.HasHomology i'] [∀ i', M.HasHomology i']

noncomputable def truncLE' : HomologicalComplex C c := (K.op.truncGE' e.op).unop

noncomputable def truncLE : HomologicalComplex C c' := (K.op.truncGE e.op).unop

noncomputable def ιTruncLE : K.truncLE e ⟶ K := (unopFunctor _ _).map (K.op.πTruncGE e.op).op

instance (i' : ι') : Mono ((K.ιTruncLE e).f i') :=
  unop_mono_of_epi ((K.op.πTruncGE e.op).f i')

instance : Mono (K.ιTruncLE e) := mono_of_mono_f _ (fun _ => inferInstance)

instance : (K.truncLE e).IsStrictlySupported e where
  isZero i' hi' := ((K.op.truncGE e.op).isZero_X_of_isStrictlySupported e.op i' hi').unop

section

variable {K L M}

noncomputable def truncLE'Map : K.truncLE' e ⟶ L.truncLE' e :=
  (unopFunctor C c.symm).map (truncGE'Map ((opFunctor C c').map φ.op) e.op).op

noncomputable def truncLEMap : K.truncLE e ⟶ L.truncLE e :=
  (unopFunctor C c'.symm).map (truncGEMap ((opFunctor C c').map φ.op) e.op).op

@[simp, reassoc]
lemma truncLE'Map_comp : truncLE'Map (φ ≫ φ') e = truncLE'Map φ e ≫ truncLE'Map φ' e := by
  simp [truncLE'Map]

@[simp, reassoc]
lemma truncLEMap_comp : truncLEMap (φ ≫ φ') e = truncLEMap φ e ≫ truncLEMap φ' e := by
  simp [truncLEMap]

variable (K) in
@[simp]
lemma truncLE'Map_id : truncLE'Map (𝟙 K) e = 𝟙 _ := by
  dsimp [truncLE'Map]
  simp only [CategoryTheory.Functor.map_id, opFunctor_obj, Opposite.unop_op, truncGE'Map_id, op_id]
  erw [CategoryTheory.Functor.map_id]
  rfl

variable (K) in
@[simp]
lemma truncLEMap_id : truncLEMap (𝟙 K) e = 𝟙 _ := by
  dsimp [truncLEMap]
  simp only [CategoryTheory.Functor.map_id, opFunctor_obj, Opposite.unop_op, truncGE'Map_id, op_id]
  erw [truncGEMap_id, CategoryTheory.Functor.map_id]
  rfl

@[reassoc (attr := simp)]
lemma ιTruncLE_naturality :
    truncLEMap φ e ≫ L.ιTruncLE e = K.ιTruncLE e ≫ φ := by
  dsimp [truncLEMap, ιTruncLE]
  rw [← Functor.map_comp, ← op_comp, πTruncGE_naturality, op_comp, Functor.map_comp]
  rfl

end

end HomologicalComplex

namespace ComplexShape.Embedding

variable (e : Embedding c c') [e.IsTruncLE]
    (C : Type*) [Category C] [HasZeroMorphisms C] [HasZeroObject C] [CategoryWithHomology C]

@[simps]
noncomputable def truncLE'Functor :
    HomologicalComplex C c' ⥤ HomologicalComplex C c where
  obj K := K.truncLE' e
  map φ := HomologicalComplex.truncLE'Map φ e

@[simps]
noncomputable def truncLEFunctor :
    HomologicalComplex C c' ⥤ HomologicalComplex C c' where
  obj K := K.truncLE e
  map φ := HomologicalComplex.truncLEMap φ e

@[simps]
noncomputable def ιTruncLENatTrans : e.truncLEFunctor C ⟶ 𝟭 _ where
  app K := K.ιTruncLE e

end ComplexShape.Embedding
