import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Data.Real.Sign
import Mathlib.LinearAlgebra.Dimension.Finrank

open Real NNReal Set Filter Topology FiniteDimensional MeasureTheory Module Submodule LinearMap

variable {E : Type*}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

section OfTopLeSpan

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
variable {s t : Set V}

namespace Basis

noncomputable instance [Module.Finite K V] (hs : LinearIndependent K ((↑) : s → V)) (hst : s ⊆ t) :
    Fintype (hs.extend hst) := by
  refine Classical.choice (Cardinal.lt_aleph0_iff_fintype.1 ?_)
  refine lt_of_le_of_lt (LinearIndependent.cardinal_le_rank' (hs.linearIndependent_extend hst)) ?_
  exact rank_lt_aleph0 K V

end Basis

end OfTopLeSpan

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem span_eq_top_of_ne_zero {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [IsReflexive R M]
    {s : Set (M →ₗ[R] R)} [Free R ((M →ₗ[R] R) ⧸ (span R s))]
    (h : ∀ z : M, z ≠ 0 → ∃ f ∈ s, f z ≠ 0) :
    ⊤ ≤ span R s := by
  by_contra hn
  replace hn := (ne_of_not_le hn).symm.lt_top
  rcases exists_dual_map_eq_bot_of_lt_top hn inferInstance with ⟨φ, φne, hφ⟩
  let φs := (Module.evalEquiv R M).symm φ
  have : ∀ f ∈ s, f φs = 0 := by
    intro f hf
    rw [← mem_bot R, ← hφ, Submodule.mem_map]
    exact ⟨f, Submodule.subset_span hf, (apply_evalEquiv_symm_apply R M f φ).symm⟩
  have φsn : φs ≠ 0 := by simp [φne, φs]
  rcases h φs φsn with ⟨x, xs, hx⟩
  exact hx <| this x xs

theorem hasFDerivAt_norm_smul {x : E} {t : ℝ} (ht : t ≠ 0)
    {f : E →L[ℝ] ℝ} (hx : HasFDerivAt (‖·‖) f x) :
    HasFDerivAt (‖·‖) ((SignType.sign t : ℝ) • f) (t • x) := by
  replace hx := (hx.hasFDerivAtFilter le_rfl).isLittleO
  constructor
  rw [Asymptotics.isLittleO_iff] at *
  intro c hc
  have := hx hc
  rw [eventually_iff, ← smul_mem_nhds_smul_iff₀ ht] at this
  filter_upwards [this]
  rintro - ⟨ε, hε, rfl⟩
  simp only
  rw [norm_smul, norm_smul, ← smul_sub, _root_.map_smul, ← ContinuousLinearMap.smul_apply,
    smul_smul, self_mul_sign, ContinuousLinearMap.smul_apply, ← norm_eq_abs, smul_eq_mul,
    ← mul_sub, ← mul_sub, norm_mul, norm_norm, norm_smul, ← mul_assoc, mul_comm c, mul_assoc,
    _root_.mul_le_mul_left]
  · exact hε
  · exact norm_pos_iff.2 ht

theorem differentiableAt_norm_smul {x : E} {t : ℝ} (ht : t ≠ 0) :
    DifferentiableAt ℝ (‖·‖) x ↔ DifferentiableAt ℝ (‖·‖) (t • x) where
  mp hd := (hasFDerivAt_norm_smul ht hd.hasFDerivAt).differentiableAt
  mpr hd := by
    convert (hasFDerivAt_norm_smul (inv_ne_zero ht) hd.hasFDerivAt).differentiableAt
    rw [smul_smul, inv_mul_cancel₀ ht, one_smul]

theorem not_differentiableAt_norm_zero (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Nontrivial E] :
    ¬DifferentiableAt ℝ (‖·‖) (0 : E) := by
  obtain ⟨x, hx⟩ := NormedSpace.exists_lt_norm ℝ E 0
  intro h
  have : DifferentiableAt ℝ (fun t : ℝ ↦ ‖t • x‖) 0 := DifferentiableAt.comp _ (by simpa) (by simp)
  have : DifferentiableAt ℝ (|·|) (0 : ℝ) := by
    simp_rw [norm_smul, norm_eq_abs] at this
    have aux : abs = fun t ↦ (1 / ‖x‖) * (|t| * ‖x‖) := by
      ext t
      field_simp
    rw [aux]
    exact this.const_mul _
  exact not_differentiableAt_abs_zero this

theorem differentiableAt_norm_of_smul {x : E} {t : ℝ} (h : DifferentiableAt ℝ (‖·‖) (t • x)) :
    DifferentiableAt ℝ (‖·‖) x := by
  rcases eq_or_ne t 0 with rfl | ht
  · by_cases hE : Nontrivial E
    · rw [zero_smul] at h
      exact not_differentiableAt_norm_zero E h |>.elim
    · rw [not_nontrivial_iff_subsingleton] at hE
      exact (hasFDerivAt_of_subsingleton _ _).differentiableAt
  · exact differentiableAt_norm_smul ht |>.2 h

theorem fderiv_norm_self {x : E} (h : DifferentiableAt ℝ (‖·‖) x) :
    fderiv ℝ (‖·‖) x x = ‖x‖ := by
  rw [← h.lineDeriv_eq_fderiv, lineDeriv]
  have this (t : ℝ) : ‖x + t • x‖ = |1 + t| * ‖x‖ := by
    rw [← norm_eq_abs, ← norm_smul, add_smul, one_smul]
  simp_rw [this]
  rw [deriv_mul_const]
  · conv_lhs => enter [1, 1]; change abs ∘ (fun t ↦ 1 + t)
    rw [deriv.comp, deriv_abs, deriv_const_add]
    · simp
    · exact differentiableAt_abs (by norm_num)
    · exact differentiableAt_id.const_add _
  · exact (differentiableAt_abs (by norm_num)).comp _ (differentiableAt_id.const_add _)

theorem fderiv_norm_smul (x : E) (t : ℝ) :
    fderiv ℝ (‖·‖) (t • x) = (SignType.sign t : ℝ) • (fderiv ℝ (‖·‖) x) := by
  by_cases hE : Nontrivial E
  · by_cases hd : DifferentiableAt ℝ (‖·‖) x
    · rcases eq_or_ne t 0 with rfl | ht
      · simp only [zero_smul, _root_.sign_zero, SignType.coe_zero]
        exact fderiv_zero_of_not_differentiableAt <| not_differentiableAt_norm_zero E
      · rw [(hasFDerivAt_norm_smul ht hd.hasFDerivAt).fderiv]
    · rw [fderiv_zero_of_not_differentiableAt hd, fderiv_zero_of_not_differentiableAt]
      · simp
      · exact mt differentiableAt_norm_of_smul hd
  · rw [not_nontrivial_iff_subsingleton] at hE
    simp_rw [(hasFDerivAt_of_subsingleton _ _).fderiv, smul_zero]

theorem fderiv_norm_smul_pos {x : E} {t : ℝ} (ht : 0 < t) :
    fderiv ℝ (‖·‖) (t • x) = fderiv ℝ (‖·‖) x := by
  simp [fderiv_norm_smul, ht]

theorem fderiv_norm_smul_neg {x : E} {t : ℝ} (ht : t < 0) :
    fderiv ℝ (‖·‖) (t • x) = -fderiv ℝ (‖·‖) x := by
  simp [fderiv_norm_smul, ht]

theorem norm_fderiv_norm [Nontrivial E] {x : E} (h : DifferentiableAt ℝ (‖·‖) x) :
    ‖fderiv ℝ (‖·‖) x‖ = 1 := by
  have : x ≠ 0 := by
    refine fun hx ↦ not_differentiableAt_norm_zero E ?_
    rwa [← hx]
  apply le_antisymm
  · rw [show (1 : ℝ) = ↑(1 : ℝ≥0) by rfl]
    exact norm_fderiv_le_of_lipschitz ℝ lipschitzWith_one_norm
  · apply le_of_mul_le_mul_right _ (norm_pos_iff.2 this)
    calc
      1 * ‖x‖ = fderiv ℝ (‖·‖) x x := by rw [one_mul, fderiv_norm_self h]
      _ ≤ ‖fderiv ℝ (‖·‖) x x‖ := le_norm_self _
      _ ≤ ‖fderiv ℝ (‖·‖) x‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _

theorem le_opNorm_of {f : E →L[ℝ] F} {x : E} {C : ℝ} (hx : x ≠ 0) (h : C * ‖x‖ ≤ ‖f x‖) :
    C ≤ ‖f‖ := by
  rw [← _root_.mul_le_mul_right (norm_pos_iff.2 hx)]
  exact h.trans (ContinuousLinearMap.le_opNorm _ _)

theorem le_opNorm_of' {f : E →L[ℝ] F} {x : E} {C : ℝ} (hx : ‖x‖ = 1) (h : C ≤ ‖f x‖) :
    C ≤ ‖f‖ := by
  apply le_opNorm_of (norm_ne_zero_iff.1 (hx ▸ (by norm_num : (1 : ℝ) ≠ 0)))
  rwa [hx, mul_one]

theorem le_opNorm_of'' {f : E →L[ℝ] F} {x : E} {C : ℝ} (hx : x ≠ 0) (nx : ‖x‖ ≤ 1) (h : C ≤ ‖f x‖) :
    C ≤ ‖f‖ := by
  obtain hC | hC := le_total C 0
  · exact hC.trans (norm_nonneg _)
  · exact le_opNorm_of hx (le_trans (mul_le_of_le_one_right hC nx) h)

section LowerSemicontinuous

open WeakDual ContinuousLinearMap in
theorem lowerSemicontinuous_norm :
    LowerSemicontinuous (fun f : WeakDual ℝ E ↦ ‖toNormedDual f‖) := by
  intro f r hrf
  obtain hr | hr := lt_or_le r 0
  · exact Eventually.of_forall fun _ ↦ lt_of_lt_of_le hr (norm_nonneg _)
  · obtain ⟨x, nx, hx⟩ := exists_lt_apply_of_lt_opNorm f hrf
    wlog hfx : 0 ≤ f x
    · apply this f r hrf hr (-x)
      · rwa [norm_neg]
      · rwa [map_neg, norm_neg]
      · rw [map_neg]
        linarith
    · let U : Set (WeakDual ℝ E) := (fun (f : WeakDual ℝ E) ↦ f x) ⁻¹' Ioi r
      have : U ∈ 𝓝 f := by
        apply (isOpen_Ioi.preimage (eval_continuous x)).mem_nhds
        rw [norm_of_nonneg hfx] at hx
        simpa
      apply eventually_of_mem this
      intro g hg
      rw [← not_le, (opNorm_le_iff hr).not]
      push_neg
      use x
      apply lt_of_le_of_lt (b := r)
      · nth_rw 2 [← mul_one r]
        exact mul_le_mul_of_nonneg_left nx.le hr
      · exact lt_of_lt_of_le hg (le_abs_self _)

end LowerSemicontinuous
