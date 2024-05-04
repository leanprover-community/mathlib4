import Mathlib

variable {E : Type*} [NormedAddCommGroup E]  [NormedSpace ℝ E]

lemma l₁ (f : E → ℝ) (z a b : E) :
    (fderiv ℝ (fun w => fderiv ℝ f w) z) a b = iteratedFDeriv ℝ 2 f z ![a, b] := by
  have I : Fin.tail ![a, b] 0 = b := rfl
  let A (n : ℕ) : NormedAddCommGroup (E →L[ℝ]
      ContinuousMultilinearMap ℝ (fun (i : Fin n) ↦ E) ℝ) := by infer_instance
  simp only [iteratedFDeriv_succ_eq_comp_left, Nat.succ_eq_add_one, Nat.reduceAdd,
    Function.comp_apply,
    (continuousMultilinearCurryLeftEquiv ℝ (fun (_ : Fin 1) ↦ E) ℝ).comp_fderiv (f :=
      fderiv ℝ (iteratedFDeriv ℝ 0 f)),
    continuousMultilinearCurryLeftEquiv_apply, Fin.isValue, Matrix.cons_val_zero,
    ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_coe, I]
  simp only [iteratedFDeriv_zero_eq_comp,
    (continuousMultilinearCurryFin0 ℝ E ℝ).symm.comp_fderiv' (f := f),
    fderiv_continuousLinearEquiv_comp,
    ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe, Function.comp_apply]
  rfl

lemma l₂ (f : ℝ × ℝ → ℝ) (h : ContDiff ℝ 2 f) :
  ∀ z a b : ℝ × ℝ, (fderiv ℝ (fun w => fderiv ℝ f w) z) a b = (fderiv ℝ (fun w ↦ (fderiv ℝ f w) a) z) b := by
  sorry
