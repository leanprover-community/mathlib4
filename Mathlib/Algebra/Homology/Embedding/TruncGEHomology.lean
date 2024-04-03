import Mathlib.Algebra.Homology.Embedding.TruncGE

open CategoryTheory Limits ZeroObject Category

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]

namespace HomologicalComplex

variable (K : HomologicalComplex C c') (e : c.Embedding c') [e.IsTruncGE]
  [∀ i', K.HasHomology i']

namespace truncGE'



end truncGE'

end HomologicalComplex
