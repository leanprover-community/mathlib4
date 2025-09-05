import Mathlib.Analysis.RCLike.Basic


/-- The real part in an `RCLike` field, as a continuous linear map. -/
noncomputable def reCLM : StrongDual ℝ K :=
  reLm.mkContinuous 1 fun x => by
    rw [one_mul]
    exact abs_re_le_norm x

@[simp, rclike_simps, norm_cast]
theorem reCLM_coe : ((reCLM : StrongDual ℝ K) : K →ₗ[ℝ] ℝ) = reLm :=
  rfl

@[simp, rclike_simps]
theorem reCLM_apply : ((reCLM : StrongDual ℝ K) : K → ℝ) = re :=
  rfl

@[continuity, fun_prop]
theorem continuous_re : Continuous (re : K → ℝ) :=
  reCLM.continuous

/-- The imaginary part in an `RCLike` field, as a continuous linear map. -/
noncomputable def imCLM : StrongDual ℝ K :=
  imLm.mkContinuous 1 fun x => by
    rw [one_mul]
    exact abs_im_le_norm x

@[simp, rclike_simps, norm_cast]
theorem imCLM_coe : ((imCLM : StrongDual ℝ K) : K →ₗ[ℝ] ℝ) = imLm :=
  rfl

@[simp, rclike_simps]
theorem imCLM_apply : ((imCLM : StrongDual ℝ K) : K → ℝ) = im :=
  rfl

@[continuity, fun_prop]
theorem continuous_im : Continuous (im : K → ℝ) :=
  imCLM.continuous

/-- Conjugate as a linear isometry -/
noncomputable def conjLIE : K ≃ₗᵢ[ℝ] K :=
  ⟨conjAe.toLinearEquiv, norm_conj⟩

@[simp, rclike_simps]
theorem conjLIE_apply : (conjLIE : K → K) = conj :=
  rfl

/-- Conjugate as a continuous linear equivalence -/
noncomputable def conjCLE : K ≃L[ℝ] K :=
  @conjLIE K _

@[simp, rclike_simps]
theorem conjCLE_coe : (@conjCLE K _).toLinearEquiv = conjAe.toLinearEquiv :=
  rfl

@[simp, rclike_simps]
theorem conjCLE_apply : (conjCLE : K → K) = conj :=
  rfl

instance (priority := 100) : ContinuousStar K :=
  ⟨conjLIE.continuous⟩

@[continuity, fun_prop]
theorem continuous_conj : Continuous (conj : K → K) :=
  continuous_star

/-- The ℝ → K coercion, as a linear isometry -/
noncomputable def ofRealLI : ℝ →ₗᵢ[ℝ] K where
  toLinearMap := ofRealAm.toLinearMap
  norm_map' := norm_ofReal

@[simp, rclike_simps]
theorem ofRealLI_apply : (ofRealLI : ℝ → K) = ofReal :=
  rfl

/-- The `ℝ → K` coercion, as a continuous linear map -/
noncomputable def ofRealCLM : ℝ →L[ℝ] K :=
  ofRealLI.toContinuousLinearMap

@[simp, rclike_simps]
theorem ofRealCLM_coe : (@ofRealCLM K _ : ℝ →ₗ[ℝ] K) = ofRealAm.toLinearMap :=
  rfl

@[simp, rclike_simps]
theorem ofRealCLM_apply : (ofRealCLM : ℝ → K) = ofReal :=
  rfl

@[continuity, fun_prop]
theorem continuous_ofReal : Continuous (ofReal : ℝ → K) :=
  ofRealLI.continuous

@[continuity]
theorem continuous_normSq : Continuous (normSq : K → ℝ) :=
  (continuous_re.mul continuous_re).add (continuous_im.mul continuous_im)

theorem lipschitzWith_ofReal : LipschitzWith 1 (ofReal : ℝ → K) :=
  ofRealLI.lipschitz

lemma lipschitzWith_re : LipschitzWith 1 (re (K := K)) := by
  intro x y
  simp only [ENNReal.coe_one, one_mul, edist_eq_enorm_sub]
  calc ‖re x - re y‖ₑ
  _ = ‖re (x - y)‖ₑ := by rw [ AddMonoidHom.map_sub re x y]
  _ ≤ ‖x - y‖ₑ := by rw [enorm_le_iff_norm_le]; exact norm_re_le_norm (x - y)

lemma lipschitzWith_im : LipschitzWith 1 (im (K := K)) := by
  intro x y
  simp only [ENNReal.coe_one, one_mul, edist_eq_enorm_sub]
  calc ‖im x - im y‖ₑ
  _ = ‖im (x - y)‖ₑ := by rw [ AddMonoidHom.map_sub im x y]
  _ ≤ ‖x - y‖ₑ := by rw [enorm_le_iff_norm_le]; exact norm_im_le_norm (x - y)
