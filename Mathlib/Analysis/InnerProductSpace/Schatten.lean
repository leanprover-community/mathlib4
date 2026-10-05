import Mathlib

open scoped ENNReal NNReal InnerProductSpace ContinuousLinearMap

noncomputable section



namespace ContinuousLinearMap

section Trace

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- The trace of an operator on `E`. -/
def traceOfBasis (A : E →L[𝕜] E) {ι : Type*} (b : HilbertBasis ι 𝕜 E) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal (RCLike.re ⟪b i, A (b i)⟫_𝕜)

theorem traceOfBasis_eq {A : E →L[𝕜] E} (hA : 0 ≤ A) {ι : Type*} (b b' : HilbertBasis ι 𝕜 E) :
    traceOfBasis A b = traceOfBasis A b' := by
  sorry

/-- The trace of an operator on `E`. -/
def trace (A : E →L[𝕜] E) : ℝ≥0∞ := traceOfBasis A
  (Classical.choose (Classical.choose_spec (exists_hilbertBasis 𝕜 E)))

variable {A B : E →L[𝕜] E}

@[simp]
theorem trace_zero : trace (0 : E →L[𝕜] E) = 0 := by simp [trace, traceOfBasis]

@[simp]
theorem trace_add (hA : 0 ≤ A) (hB : 0 ≤ B) : trace (A + B) = trace A + trace B := by
  unfold trace traceOfBasis
  simp_rw [add_apply, inner_add_right, map_add, ← ENNReal.tsum_add]
  refine tsum_congr fun i ↦ ?_
  refine ENNReal.ofReal_add ?_ ?_
  · simpa only [sub_zero] using hA.re_inner_nonneg_right _
  · simpa only [sub_zero] using hB.re_inner_nonneg_right _

end Trace

section

variable (p : ℝ≥0∞) (q : ℝ) {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def modulus (T : E →L[ℂ] F) : E →L[ℂ] E := CFC.sqrt (T.adjoint ∘L T)

@[simp]
theorem modulus_zero : modulus (0 : E →L[ℂ] F) = 0 := by simp [modulus]
@[simp]
theorem modulus_neg (T : E →L[ℂ] F) : modulus (-T) = modulus T := by simp [modulus]
@[simp]
theorem modulus_nonneg (T : E →L[ℂ] F) : 0 ≤ modulus T := by simp [modulus]

def eSpNorm' (T : E →L[ℂ] F) : ℝ≥0∞ := (CFC.nnrpow T.modulus q.toNNReal).trace ^ (1 / q)

@[simp]
theorem eSpNorm'_apply (T : E →L[ℂ] F) :
    eSpNorm' q T = (CFC.nnrpow T.modulus q.toNNReal).trace ^ (1 / q) :=
  rfl

def eSpNorm (T : E →L[ℂ] F) : ℝ≥0∞ :=
  if p = 0 then 0 else
    if p = ∞ then ‖T‖ₑ else
      eSpNorm' p.toReal T

@[simp]
theorem eSpNorm_apply (T : E →L[ℂ] F) :
    eSpNorm p T = if p = 0 then 0 else
    if p = ∞ then ‖T‖ₑ else
      eSpNorm' p.toReal T :=
  rfl

def spNorm (T : E →L[ℂ] F) : ℝ := (eSpNorm p T).toReal

def MemSp (T : E →L[ℂ] F) : Prop := eSpNorm p T < ∞

set_option linter.unusedVariables false in
def Sp (p : ℝ≥0∞) (E F : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] : Type _ :=
  E →L[ℂ] F

end

namespace Sp

variable (p : ℝ≥0∞) (q : ℝ) {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

instance : FunLike (Sp p E F) E F := inferInstanceAs (FunLike (E →L[ℂ] F) E F)
instance : ContinuousLinearMapClass (Sp p E F) ℂ E F :=
  inferInstanceAs (ContinuousLinearMapClass (E →L[ℂ] F) ℂ E F)
instance : AddCommGroup (Sp p E F) := inferInstanceAs (AddCommGroup (E →L[ℂ] F))
instance : Module ℂ (Sp p E F) := inferInstanceAs (Module ℂ (E →L[ℂ] F))

def toCLM : (Sp p E F) ≃ₗ[ℂ] (E →L[ℂ] F) := LinearEquiv.refl _ _
def ofCLM : (E →L[ℂ] F) ≃ₗ[ℂ] (Sp p E F) := LinearEquiv.refl _ _

instance : ENorm (Sp p E F) where
  enorm T := eSpNorm p (toCLM p T)

@[simp]
theorem enorm_def (T : Sp p E F) : ‖T‖ₑ = eSpNorm p (toCLM p T) := rfl

@[simp]
theorem enorm_zero : ‖(0 : Sp p E F)‖ₑ = 0 := by
  simp
  rintro hn0 hnt
  exact ENNReal.toReal_pos hn0 hnt

theorem enorm_add_le [Fact (1 ≤ p)] (T T' : Sp p E F) : ‖T + T'‖ₑ ≤ ‖T‖ₑ + ‖T'‖ₑ := by
  simp
  by_cases h : p = ∞
  · simp [h]
    exact ESeminormedAddMonoid.enorm_add_le ((toCLM p) T) ((toCLM p) T')
  · have hp : p ≠ 0 := sorry
    simp [h, hp]
    sorry

theorem enorm_eq_zero (T : Sp p E F) : ‖T‖ₑ = 0 ↔ T = 0 := by
  constructor
  · sorry
  · rintro hT
    rw [hT, enorm_zero]

instance [Fact (1 ≤ p)] : EMetricSpace (Sp p E F) where
  edist f g := ‖f - g‖ₑ
  edist_self f := by
    rw [sub_self, enorm_zero]
  edist_comm f g:= by
    simp [eSpNorm, enorm_sub_rev, ← modulus_neg (toCLM p f - toCLM p g)]
  edist_triangle f g h := by
    simpa using enorm_add_le p (f-g) (g-h)
  eq_of_edist_eq_zero hfg := by
    rw [← sub_eq_zero]
    exact (enorm_eq_zero p _).mp hfg

instance [Fact (1 ≤ p)] : ENormedAddMonoid (Sp p E F) where
  continuous_enorm := by
    refine continuous_of_le_add_edist 1 ENNReal.one_ne_top fun f g => ?_
    have := enorm_add_le p g (f - g)
    rw [add_sub_cancel g f] at this
    rw [one_mul]
    exact this
  enorm_zero := enorm_zero p
  enorm_add_le := enorm_add_le p
  enorm_eq_zero := enorm_eq_zero p

end Sp

namespace MemSp

end MemSp

end ContinuousLinearMap
