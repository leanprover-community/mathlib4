import Mathlib

open scoped ENNReal NNReal InnerProductSpace ContinuousLinearMap

noncomputable section



namespace ContinuousLinearMap

section Trace

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

open scoped ComplexConjugate ENNReal

/-- The trace of an operator on `E`. -/
def traceOfBasis (A : E →L[ℂ] E) {ι : Type*} (b : HilbertBasis ι ℂ E) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal (RCLike.re ⟪b i, A (b i)⟫_ℂ)

theorem traceOfBasis_eq {A : E →L[ℂ] E} (hA : 0 ≤ A) {ι : Type*} (b b' : HilbertBasis ι ℂ E) :
    traceOfBasis A b = traceOfBasis A b' := by
  unfold traceOfBasis
  set S := CFC.sqrt A with hSdef
  have hS : S.adjoint * S = A := by
    simp [hSdef, CFC.sqrt_mul_sqrt_self A hA, (CFC.sqrt_nonneg A).isSelfAdjoint.adjoint_eq]
  simp_rw [← hS, mul_apply_eq_comp, ContinuousLinearMap.adjoint_inner_right]
  simp_rw +singlePass [← HilbertBasis.tsum_inner_mul_inner b' (S (b _)),
    ← inner_conj_symm (S (b _)), ← HilbertBasis.tsum_inner_mul_inner b (S (b' _)),
    ← inner_conj_symm (S (b' _)), RCLike.conj_mul, ← RCLike.ofReal_pow]
  simp_rw [← RCLike.ofReal_tsum]
  simp only [Complex.coe_algebraMap, RCLike.re_to_complex, Complex.ofReal_re]
  have h : ∀ (c : HilbertBasis ι ℂ E) (x : E),
      ENNReal.ofReal (∑' a, ‖⟪c a, x⟫_ℂ‖ ^ 2) = ∑' a, ENNReal.ofReal (‖⟪c a, x⟫_ℂ‖ ^ 2) :=
    fun c x => ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity)
      (c.orthonormal.inner_products_summable x)
  simp_rw [h b, h b']
  rw [ENNReal.tsum_comm]
  simp_rw [← LinearMap.IsSymmetric.apply_clm (T := S)
    (CFC.sqrt_nonneg A).isSelfAdjoint.isSymmetric (b' _) (b _), norm_inner_symm (S (b' _)) (b _)]

/-- The trace of an operator on `E`. -/
def trace (A : E →L[ℂ] E) : ℝ≥0∞ := traceOfBasis A
  (Classical.choose (Classical.choose_spec (exists_hilbertBasis ℂ E)))

variable {A B : E →L[ℂ] E}

@[simp]
theorem trace_zero : trace (0 : E →L[ℂ] E) = 0 := by simp [trace, traceOfBasis]

@[simp]
theorem trace_add (hA : 0 ≤ A) (hB : 0 ≤ B) : trace (A + B) = trace A + trace B := by
  unfold trace traceOfBasis
  simp_rw [add_apply, inner_add_right, map_add, ← ENNReal.tsum_add]
  refine tsum_congr fun i ↦ ?_
  refine ENNReal.ofReal_add ?_ ?_
  · simpa only [sub_zero] using hA.re_inner_nonneg_right _
  · simpa only [sub_zero] using hB.re_inner_nonneg_right _

theorem trace_eq_zero (hA : 0 ≤ A) : trace A = 0 ↔ A = 0 := by
  constructor
  · rintro h
    unfold trace traceOfBasis at h
    set b := Classical.choose (Classical.choose_spec (exists_hilbertBasis ℂ E))
    set S := CFC.sqrt A with hSdef
    have hS : S.adjoint * S = A := by
      simp [hSdef, CFC.sqrt_mul_sqrt_self A hA, (CFC.sqrt_nonneg A).isSelfAdjoint.adjoint_eq]
    simp_rw [ENNReal.tsum_eq_zero, ← hS, mul_apply_eq_comp,
      ContinuousLinearMap.adjoint_inner_right, ENNReal.ofReal_eq_zero, re_inner_self_nonpos] at h
    rw [← hS]
    apply ContinuousLinearMap.ext_on (Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span)
    rintro _ ⟨i, rfl⟩
    simp [h i]
  · rintro h
    simp [h]

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

theorem modulus_eq_zero (T : E →L[ℂ] F) : modulus T = 0 ↔ T = 0 := by
  constructor
  · rintro h
    simp [modulus] at h
    rw [CFC.sqrt_eq_zero_iff (adjoint T ∘SL T)
      (nonneg_iff_isPositive.mpr (ContinuousLinearMap.isPositive_adjoint_comp_self T))] at h
    exact adjoint_comp_self_eq_zero_iff.mp h
  · rintro h
    simp [h]

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

theorem enorm_eq_zero [Fact (0 < p)] (T : Sp p E F) : ‖T‖ₑ = 0 ↔ T = 0 := by
  constructor
  · rintro hT
    have hp : ¬p = 0 := by sorry
    simp [enorm, hp] at hT
    by_cases hp : p = ∞
    · simp [hp] at hT
      exact hT
    · have hp' : 0 < p.toReal := sorry
      have hp'' : ¬ p.toReal < 0 := sorry
      have hp''' : p.toNNReal ≠ 0 := sorry
      simp [hp, hp', hp'', trace_eq_zero] at hT
      rw [← CFC.nnrpow_inv_eq 0 ((toCLM p) T).modulus hp''' (le_refl 0) (modulus_nonneg _)] at hT
      simp at hT
      have : (toCLM p T).modulus = 0 := Eq.symm hT
      have : (toCLM p T) = 0 := by exact (modulus_eq_zero ((toCLM p) T)).mp this
      exact this
  · rintro hT
    rw [hT, enorm_zero]

local instance [Fact (1 ≤ p)] : Fact (0 < p) := sorry

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
