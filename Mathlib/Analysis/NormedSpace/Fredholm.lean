import Mathlib.Analysis.NormedSpace.CompactOperator
import Mathlib.Analysis.Complex.Basic

variable {E F G : Type _}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]
  (T : E →L[ℂ] F) (S : F →L[ℂ] G)

open FiniteDimensional

def isFredholm : Prop :=
FiniteDimensional ℂ (LinearMap.ker T) ∧ FiniteDimensional ℂ (F ⧸ LinearMap.range T)

namespace isFredholm

protected def comp (hT : isFredholm T) (hS : isFredholm S) : isFredholm (S.comp T) := by
  sorry

noncomputable def index : ℤ :=
(finrank ℂ (LinearMap.ker T) : ℤ) - (finrank ℂ (F ⧸ LinearMap.range T) : ℤ)

lemma index_comp (hT : isFredholm T) (hS : isFredholm S) :
    index (S.comp T) = index T + index S := by
  sorry

end isFredholm

variable (E)

def Fredholm : Submonoid (E →L[ℂ] E) :=
{ carrier := isFredholm,
  one_mem' := sorry,
  mul_mem' := sorry, }

instance : ContinuousMul (E →L[ℂ] E) := by
  constructor
  sorry

instance : ContinuousMul (Fredholm E) := ⟨by continuity⟩

/- TODO (not sure if how easy these are)
  * Index additive on direct sums
  * Relationship to compact operators
-/
