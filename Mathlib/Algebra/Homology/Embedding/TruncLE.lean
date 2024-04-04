import Mathlib.Algebra.Homology.Embedding.TruncGE
import Mathlib.Algebra.Homology.Opposite

open CategoryTheory Limits

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]

namespace HomologicalComplex

variable (K : HomologicalComplex C c') (e : c.Embedding c') [e.IsTruncLE]
  [∀ i', K.HasHomology i']

noncomputable def truncLE' : HomologicalComplex C c := (K.op.truncGE' e.op).unop

noncomputable def truncLE : HomologicalComplex C c' := (K.op.truncGE e.op).unop

noncomputable def ιTruncLE : K.truncLE e ⟶ K := (unopFunctor _ _).map (K.op.πTruncGE e.op).op

instance (i' : ι') : Mono ((K.ιTruncLE e).f i') :=
  unop_mono_of_epi ((K.op.πTruncGE e.op).f i')



end HomologicalComplex
