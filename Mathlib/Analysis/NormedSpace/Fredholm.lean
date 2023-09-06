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

example : isFredholm (1 : E →L[ℂ] E) := by
  constructor
  · --rw [LinearMap.mem_ker.mp]
    sorry
  · sorry

protected def comp (hT : isFredholm T) (hS : isFredholm S) : isFredholm (S.comp T) := by
  rw [isFredholm]
  rcases hT with ⟨hTk,hTc⟩
  rcases hS with ⟨hSk,hSc⟩
  constructor
  · sorry
  · sorry

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

namespace myFredholm
variable {E F G : Type _}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]
  (T : E →L[ℂ] F) (S : F →L[ℂ] G)

def finrank_op (A : E →L[ℂ] F) : Prop := FiniteDimensional ℂ (LinearMap.range A)

def eq_upto_finrank_op (A B: E →L[ℂ] F) : Prop := finrank_op (A - B)

@[trans] theorem r_trans (A B C: E →L[ℂ] F)
    (hAB : eq_upto_finrank_op A B) (hBC : eq_upto_finrank_op B C) : eq_upto_finrank_op A C := sorry
infix:50 " =ᶠ " => eq_upto_finrank_op

def quasi_inv (A : E →L[ℂ] F) (B : F →L[ℂ] E) : Prop :=
  1 =ᶠ B ∘L A ∧ 1 =ᶠ A ∘L B

def isFredholm (A : E →L[ℂ] F) : Prop := ∃ (B : F →L[ℂ] E), quasi_inv A B

protected def comp (hT : isFredholm T) (hS : isFredholm S) : isFredholm (S ∘L T) := by
  obtain ⟨T', hTl, hTr⟩ := hT
  obtain ⟨S', hSl, hSr⟩ := hS
  use (T' ∘L S')
  constructor
  · sorry
  · sorry

end myFredholm
