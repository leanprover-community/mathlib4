import Mathlib.Algebra.Homology.Embedding.TruncGEHomology
import Mathlib.Algebra.Homology.Embedding.TruncLE

open CategoryTheory Limits

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]

namespace HomologicalComplex

variable (K : HomologicalComplex C c') (e : c.Embedding c') [e.IsTruncLE]
  [∀ i', K.HasHomology i']

instance (i : ι) : (K.truncLE' e).HasHomology i :=
  (inferInstance : (K.op.truncGE' e.op).unop.HasHomology i)

instance (i' : ι') : (K.truncLE e).HasHomology i' :=
  (inferInstance : (K.op.truncGE e.op).unop.HasHomology i')

lemma quasiIsoAt_ιTruncLE {j : ι} {j' : ι'} (hj' : e.f j = j') :
    QuasiIsoAt (K.ιTruncLE e) j' := by
  rw [← quasiIsoAt_op_iff]
  exact K.op.quasiIsoAt_πTruncGE e.op hj'

instance (j : ι) : QuasiIsoAt (K.ιTruncLE e) (e.f j) :=
  K.quasiIsoAt_ιTruncLE e rfl

end HomologicalComplex
