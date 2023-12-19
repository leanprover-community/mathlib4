import Mathlib.Algebra.Homology.SpectralSequenceNew.Convergence
import Mathlib.Algebra.Homology.SpectralSequenceNew.SpectralObject
import Mathlib.Algebra.Homology.SpectralSequenceNew.ZTilde

open CategoryTheory Category Limits

variable {C : Type*} [Category C] [Abelian C]

namespace CategoryTheory

namespace Abelian

namespace SpectralObject

variable (X : SpectralObject C ℤt)

namespace ToE₂

def pageX (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) : C := by
  sorry

--  (X.E (pq.1+pq.2-1) (pq.1+pq.2) (pq.1+pq.2+1) (by linarith) (by linarith)).obj
--    (ιℤt.mapArrow₃.obj (Arrow₃.mkOfLE (pq.2-r+2) pq.2 (pq.2+1) (pq.2+r-1)))
def page (r : ℤ) (hr : 2 ≤ r) : HomologicalComplex C (ComplexShape.up' (r, 1 - r)) where
  X := by
    have pif:= X
    sorry
  d := sorry
  shape := sorry
  d_comp_d' := sorry

end ToE₂

noncomputable def toE₂ : E₂CohomologicalSpectralSequence C where
  page' := ToE₂.page X
  iso' := sorry

end SpectralObject

end Abelian

end CategoryTheory
