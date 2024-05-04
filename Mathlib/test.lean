import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

variable {E : Type*} [NormedAddCommGroup E]  [NormedSpace ℝ E]

lemma l₁ (f : E → ℝ) (z a b : E) :
    fderiv ℝ (fderiv ℝ f) z a b = iteratedFDeriv ℝ 2 f z ![a, b] := by
  -- should we have a simp lemma for the next line?
  have I : Fin.tail ![a, b] 0 = b := rfl
  -- next line should not be needed, but is because of synthPending issue
  let A (n : ℕ) : NormedAddCommGroup (E →L[ℝ]
      ContinuousMultilinearMap ℝ (fun (_ : Fin n) ↦ E) ℝ) := by infer_instance
  simp only [iteratedFDeriv_succ_eq_comp_left, Nat.succ_eq_add_one, Nat.reduceAdd,
    Function.comp_apply,
    (continuousMultilinearCurryLeftEquiv ℝ (fun (_ : Fin 1) ↦ E) ℝ).comp_fderiv
      -- next line shouldn't be needed, but Lean is confused without it
      -- without any help (i.e., just using LinearIsometryEquiv.comp_fderiv), nothing is simplified.
      (f := fderiv ℝ (iteratedFDeriv ℝ 0 f)),
    continuousMultilinearCurryLeftEquiv_apply, Fin.isValue, Matrix.cons_val_zero,
    ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_coe, I]
  simp [iteratedFDeriv_zero_eq_comp, fderiv_continuousLinearEquiv_comp,
    LinearIsometryEquiv.comp_fderiv']

lemma l₂' {f : E → ℝ} (hf : ContDiff ℝ 2 f) (z a b : E) :
    fderiv ℝ (fderiv ℝ f) z b a = fderiv ℝ (fun w ↦ fderiv ℝ f w a) z b := by
  rw [fderiv_clm_apply]
  · simp
  · exact (contDiff_succ_iff_fderiv.1 hf).2.differentiable le_rfl z
  · simp

lemma l₂ {f : E → ℝ} (hf : ContDiff ℝ 2 f) (z a b : E) :
    fderiv ℝ (fderiv ℝ f) z a b = fderiv ℝ (fun w ↦ fderiv ℝ f w a) z b := by
  rw [← l₂' hf z a b]
  apply second_derivative_symmetric (f := f) (f' := fderiv ℝ f) (x := z)
  · intro y
    exact (hf.differentiable one_le_two y).hasFDerivAt
  · exact ((contDiff_succ_iff_fderiv.1 hf).2.differentiable le_rfl z).hasFDerivAt
