import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Real.Sign

open Real NNReal Set Filter Topology FiniteDimensional MeasureTheory Module Submodule

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem dense_of_ae {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    {μ : Measure X} [μ.IsOpenPosMeasure]
    {p : X → Prop} (hp : ∀ᵐ x ∂μ, p x) : Dense {x | p x} := by
  rw [dense_iff_closure_eq, closure_eq_compl_interior_compl, compl_univ_iff]
  exact μ.interior_eq_empty_of_null hp

theorem basis_of_span [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} (hs : span ℝ s = ⊤) :
    ∃ b : Basis (Fin (finrank ℝ E)) ℝ E, range b ⊆ s := by
  let u := (linearIndependent_empty ℝ E).extend (empty_subset s)
  let v : u → E := Subtype.val
  have liv : LinearIndependent ℝ v :=
    (linearIndependent_empty ℝ E).linearIndependent_extend (empty_subset s)
  have sv : ⊤ ≤ span ℝ (range v) := by
    rw [Subtype.range_val_subtype, ← hs, span_le]
    exact (linearIndependent_empty ℝ E).subset_span_extend (empty_subset s)
  let w := Basis.mk liv sv
  use w.reindex (w.indexEquiv (finBasis ℝ E))
  rw [w.range_reindex, show range w = range v by simp [v, w], Subtype.range_val_subtype]
  exact (linearIndependent_empty ℝ E).extend_subset (empty_subset s)

noncomputable def BasisOfSpan [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} (hs : span ℝ s = ⊤) :
    Basis (Fin (finrank ℝ E)) ℝ E := (basis_of_span hs).choose

theorem basisOfSpan_subset [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} (hs : span ℝ s = ⊤) :
    range (BasisOfSpan hs) ⊆ s := (basis_of_span hs).choose_spec

theorem span_eq_top_of_ne_zero [IsReflexive ℝ E] {s : Set (E →ₗ[ℝ] ℝ)}
    (h : ∀ z : E, z ≠ 0 → ∃ f ∈ s, f z ≠ 0) :
    span ℝ s = ⊤ := by
  by_contra! hn
  rcases exists_dual_map_eq_bot_of_lt_top hn.lt_top inferInstance with ⟨φ, φne, hφ⟩
  let φs := (Module.evalEquiv ℝ E).symm φ
  have : ∀ f ∈ s, f φs = 0 := by
    intro f hf
    rw [← mem_bot ℝ, ← hφ, Submodule.mem_map]
    exact ⟨f, Submodule.subset_span hf, (apply_evalEquiv_symm_apply ℝ E f φ).symm⟩
  have φsn : φs ≠ 0 := by simp [φne, φs]
  rcases h φs φsn with ⟨x, xs, hx⟩
  exact hx <| this x xs

theorem hasFDerivAt_norm_smul {x : E} {t : ℝ} (ht : t ≠ 0)
    {f : E →L[ℝ] ℝ} (hx : HasFDerivAt (‖·‖) f x) :
    HasFDerivAt (‖·‖) ((SignType.sign t : ℝ) • f) (t • x) := by
  unfold HasFDerivAt at *
  have hx := hx.isLittleO
  constructor
  rw [Asymptotics.isLittleO_iff] at *
  intro c hc
  have := hx hc
  rw [eventually_iff, ← set_smul_mem_nhds_smul_iff ht] at this
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
    rw [smul_smul, inv_mul_cancel ht, one_smul]

theorem not_differentiableAt_norm_zero (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Nontrivial E] :
    ¬DifferentiableAt ℝ (‖·‖) (0 : E) := by
  rcases NormedSpace.exists_lt_norm ℝ E 0 with ⟨x, hx⟩
  intro h
  have : DifferentiableAt ℝ (fun t : ℝ ↦ ‖t • x‖) 0 := by
    apply DifferentiableAt.comp
    · simpa
    · simp
  have : DifferentiableAt ℝ (|·|) (0 : ℝ) := by
    simp_rw [norm_smul, norm_eq_abs] at this
    have aux : abs = fun t ↦ (1 / ‖x‖) * (|t| * ‖x‖) := by
      ext t
      rw [mul_comm, mul_assoc, mul_one_div_cancel hx.ne.symm, mul_one]
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

theorem deriv_abs (x : ℝ) : deriv (|·|) x = SignType.sign x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [EventuallyEq.deriv_eq (f := fun x ↦ -x)]
    · simp [hx]
    · rw [EventuallyEq, eventually_iff_exists_mem]
      exact ⟨Iic 0, Iic_mem_nhds hx, by simp [hx]⟩
  · rw [deriv_zero_of_not_differentiableAt not_differentiableAt_abs_zero]
    simp
  · rw [EventuallyEq.deriv_eq (f := id)]
    · simp [hx]
    · rw [EventuallyEq, eventually_iff_exists_mem]
      exact ⟨Ici 0, Ici_mem_nhds hx, by simp [hx]⟩

theorem hasDerivAt_abs {x : ℝ} (hx : x ≠ 0) : HasDerivAt abs (SignType.sign x : ℝ) x := by
  convert (differentiableAt_of_deriv_ne_zero ?_).hasDerivAt
  · rw [deriv_abs]
  · rcases hx.lt_or_lt with hx | hx
    all_goals rw [deriv_abs]; simp [hx]

theorem differentiableAt_abs {x : ℝ} (hx : x ≠ 0) : DifferentiableAt ℝ abs x :=
  (hasDerivAt_abs hx).differentiableAt

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
