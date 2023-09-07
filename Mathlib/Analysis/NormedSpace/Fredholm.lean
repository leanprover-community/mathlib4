import Mathlib.Analysis.NormedSpace.CompactOperator
import Mathlib.Analysis.Complex.Basic
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Analysis.NormedSpace.Complemented
import Mathlib.FieldTheory.Finiteness

open Cardinal
open Function

namespace LinearMap

variable {K U V W : Type 0} [Field K] [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

def isFiniteRank (A : V →ₗ[K] W) : Prop :=
  rank A < ℵ₀

lemma sumFiniteRank (A B : V →ₗ[K] W) (hA : isFiniteRank A) (hB : isFiniteRank B):
    isFiniteRank (A + B) := by
    dsimp only [isFiniteRank]
    calc
      rank (A + B) ≤ rank A + rank B := by apply rank_add_le
                 _ < ℵ₀              := by apply add_lt_aleph0 <;> assumption

lemma rightCompFiniteRank (A : V →ₗ[K] W) (B : U →ₗ[K] V) (hB : isFiniteRank B) :
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

-- TODO maybe get rid of fixed u
universe u

open FiniteDimensional

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

example (p : Submodule K V) :
    (⊤ : Submodule K p) ≃ₗ[K] p :=
  LinearEquiv.ofTop ⊤ rfl

example (p : Submodule K V) :
    Module.rank K (⊤ : Submodule K p) = Module.rank K p := by
  apply LinearEquiv.rank_eq
  exact LinearEquiv.ofTop ⊤ rfl

/-- The preimage of a finite rank module has finite rank, given that the map has finite rank kernel -/
lemma comap_fin_dim (A B : Type u)
    [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    (R : A →ₗ[ℂ] B) (B' : Submodule ℂ B)
    (hR : FiniteDimensional ℂ (LinearMap.ker R))
    (hB' : FiniteDimensional ℂ B')
    : FiniteDimensional ℂ (Submodule.comap R B') := by
  let A' := Submodule.comap R B'
  let R' := R.domRestrict A'
  set rKer := Module.rank ℂ (LinearMap.ker R')
  set rIm := Module.rank ℂ (LinearMap.range R')
  have hKer : rKer ≤ Module.rank ℂ (LinearMap.ker R) := by
    --have hSubK : (LinearMap.ker R') ≤ (LinearMap.ker R) := by
    --  sorry
    sorry
  have hIm : rIm ≤ Module.rank ℂ B' := by
    have hSubI : (LinearMap.range R') ≤ B' := by
      rw [LinearMap.range_le_iff_comap, Submodule.eq_top_iff']
      aesop
    exact rank_le_of_submodule (LinearMap.range R') B' hSubI
  have hRank : rIm + rKer = Module.rank ℂ A' := rank_range_add_rank_ker R'
  suffices : Module.rank ℂ A' ≤ (Module.rank ℂ B') + (Module.rank ℂ (LinearMap.ker R))
  · have hFin : Module.rank ℂ A' < ℵ₀ := by
      rw [FiniteDimensional, ← IsNoetherian.iff_fg, IsNoetherian.iff_rank_lt_aleph0] at hR
      rw [FiniteDimensional, ← IsNoetherian.iff_fg, IsNoetherian.iff_rank_lt_aleph0] at hB'
      calc Module.rank ℂ A' ≤ (Module.rank ℂ B') + (Module.rank ℂ (LinearMap.ker R)) := this
        _ < ℵ₀ := by apply add_lt_aleph0 <;> assumption
    rw [FiniteDimensional, ← IsNoetherian.iff_fg, IsNoetherian.iff_rank_lt_aleph0]
    apply hFin
  calc Module.rank ℂ A' = rIm + rKer := by rw [hRank]
    _ ≤ rIm + Module.rank ℂ (LinearMap.ker R) := add_le_add_left hKer (rIm)
    _ ≤ Module.rank ℂ B' + (Module.rank ℂ (LinearMap.ker R)) := add_le_add_right hIm (Module.rank ℂ (LinearMap.ker R))

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

example (p : Submodule K V) :
    (⊤ : Submodule K p) ≃ₗ[K] p :=
  LinearEquiv.ofTop ⊤ rfl

example (p : Submodule K V) :
    Module.rank K (⊤ : Submodule K p) = Module.rank K p := by
  apply LinearEquiv.rank_eq
  exact LinearEquiv.ofTop ⊤ rfl


lemma map_fin_codim (A B : Type u)
    [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    (R : A →ₗ[ℂ] B) (A' : Submodule ℂ A)
    (hR : FiniteDimensional ℂ (B ⧸ (LinearMap.range R)) )
    (hA' : FiniteDimensional ℂ (A ⧸ A'))
    : FiniteDimensional ℂ (B ⧸ (Submodule.map R A')) := by
  let B' := Submodule.map R A'
  let hA' : ∀ x : A, x ∈ A' → R x ∈ B' := by
      aesop
  let R' := R.restrict hA'
  have hRank : Module.rank ℂ (B ⧸ B') + Module.rank ℂ B' = Module.rank ℂ B :=
    rank_quotient_add_rank (Submodule.map R A')
  suffices : True
  · sorry
  sorry

-- Stability under composition; proof via the iff_finiteDimensional_ker_coker definition
protected lemma comp (hT : isFredholm T) (hS : isFredholm S)
    : isFredholm (S.comp T) := by
  rw [iff_finiteDimensional_ker_coker]
  rw [iff_finiteDimensional_ker_coker] at hT
  rw [iff_finiteDimensional_ker_coker] at hS
  constructor
  · change FiniteDimensional ℂ (LinearMap.ker ((S : F →ₗ[ℂ] G).comp (T : E →ₗ[ℂ] F) ))
    rw [LinearMap.ker_comp]
    apply comap_fin_dim
    · exact hT.1
    · exact hS.1
  · change FiniteDimensional ℂ (G ⧸ LinearMap.range ((S : F →ₗ[ℂ] G).comp (T : E →ₗ[ℂ] F) ))
    rw [LinearMap.range_comp]
    apply map_fin_codim
    · exact hS.2
    · exact hT.2



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
