import Mathlib.Analysis.NormedSpace.CompactOperator
import Mathlib.Analysis.Complex.Basic
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Topology.Algebra.Module.LocallyConvex

open Cardinal

namespace LinearMap

variable {K U V W : Type 0} [Field K] [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

def isFiniteRank (A : V →ₗ[K] W) : Prop :=
  rank A < ℵ₀

lemma sumFiniteRank (A B : V →ₗ[K] W) (hA : isFiniteRank A) (hB : isFiniteRank B):
    isFiniteRank (A + B) := by
    dsimp only [isFiniteRank]
    calc
      rank (A + B) ≤ rank A + rank B := by apply rank_add_le
                 _ < ℵ₀              := by show add_lt_aleph0 by assumption

lemma rightCompFiniteRank (A : V →ₗ[K] W) (B : U →ₗ[K] V) (hB : isFiniteRank B):
    isFiniteRank (A ∘ₗ B) := by
  dsimp only [isFiniteRank]
  calc
    rank (A ∘ₗ B) ≤ rank B := by apply rank_comp_le_right
                _ < ℵ₀     := by assumption

lemma leftCompFiniteRank (A : V →ₗ[K] W) (B : U →ₗ[K] V) (hA : isFiniteRank A):
    isFiniteRank (A ∘ₗ B) := by
  dsimp only [isFiniteRank]
  calc
    rank (A ∘ₗ B) ≤ rank A := by apply rank_comp_le_left
                _ < ℵ₀     := by assumption


lemma smulFiniteRank (c : K) (A : V →ₗ[K] W) (hA : isFiniteRank A) : isFiniteRank (c • A) := sorry

theorem zeroFiniteRank : isFiniteRank (0 : V →ₗ[K] W) := by
  dsimp only [isFiniteRank]
  rw [rank_zero]
  exact aleph0_pos

def eqUpToFiniteRank (A B : V →ₗ[K] W) : Prop := isFiniteRank (A - B)
infix:50 " =ᶠ " => eqUpToFiniteRank

@[refl]
theorem eqUpToFiniteRank_refl (A : V →ₗ[K] W) :  A =ᶠ A := by
  dsimp only [eqUpToFiniteRank]
  rw [sub_self]
  exact zeroFiniteRank

@[symm]
theorem eqUpToFiniteRank_symm (A B : V →ₗ[K] W) (h: A =ᶠ B): B =ᶠ A :=
  sorry

@[trans]
theorem eqUpToFiniteRank_trans (A B C : V →ₗ[K] W) (hAB : A =ᶠ B) (hBC : B =ᶠ C) : A =ᶠ C := by
  dsimp only [eqUpToFiniteRank]
  rw [← sub_add_sub_cancel]
  apply sumFiniteRank (A - B) (B - C) hAB hBC

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
