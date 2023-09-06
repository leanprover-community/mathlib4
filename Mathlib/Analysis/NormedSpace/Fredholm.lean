import Mathlib.Analysis.NormedSpace.CompactOperator
import Mathlib.Analysis.Complex.Basic
import Mathlib.SetTheory.Cardinal.Basic

open Cardinal

namespace LinearMap

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

def isFiniteRank (A : V →ₗ[K] W) : Prop :=
  A.rank < ℵ₀

def eqUpToFiniteRank (A B : V →ₗ[K] W) : Prop :=
  isFiniteRank (A - B)

lemma sumFiniteRank (A B : V →ₗ[K] W) (hA : isFiniteRank A) (hB : isFiniteRank B):
    isFiniteRank (A + B) := by
    dsimp only [isFiniteRank]
    calc
      (A + B).rank ≤ A.rank + B.rank := by apply LinearMap.rank_add_le
                 _ < ℵ₀              := by apply add_lt_aleph0 hA hB

@[trans]
theorem eqUpToFiniteRank_trans (A B C : V →ₗ[K] W)
    (hAB : eqUpToFiniteRank A B)
    (hBC : eqUpToFiniteRank B C) : eqUpToFiniteRank A C := by
  dsimp only [eqUpToFiniteRank]
  rw [← sub_add_sub_cancel]
  apply sumFiniteRank (A - B) (B - C) hAB hBC

infix:50 " =ᶠ " => eqUpToFiniteRank

def isQuasiInv (A : V →ₗ[K] W) (B : W →ₗ[K] V) : Prop :=
  1 =ᶠ B ∘ₗ A ∧ 1 =ᶠ A ∘ₗ B

end LinearMap

variable {E F G : Type _}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]
  (T : E →L[ℂ] F) (S : F →L[ℂ] G)

open FiniteDimensional

def isFredholm (A : E →L[ℂ] F) : Prop :=
  ∃ (B : F →L[ℂ] E), LinearMap.isQuasiInv (A : E →ₗ[ℂ] F) B

namespace isFredholm

-- TODO What assumptions are really needed here?
lemma iff_finiteDimensional_ker_coker :
    isFredholm T ↔
    FiniteDimensional ℂ (LinearMap.ker T) ∧ FiniteDimensional ℂ (F ⧸ LinearMap.range T) := by
  sorry

example : isFredholm (1 : E →L[ℂ] E) := by
  constructor
  · --rw [LinearMap.mem_ker.mp]
    sorry
  · sorry

protected def comp (hT : isFredholm T) (hS : isFredholm S) : isFredholm (S.comp T) := by
  obtain ⟨T', hTl, hTr⟩ := hT
  obtain ⟨S', hSl, hSr⟩ := hS
  use (T' ∘L S')
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
