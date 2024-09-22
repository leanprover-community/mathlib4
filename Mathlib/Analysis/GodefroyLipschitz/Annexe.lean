import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Real.Sign

open Real NNReal Set Filter Topology FiniteDimensional MeasureTheory Module Submodule LinearMap

variable {E : Type*}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem dense_of_ae {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    {μ : Measure X} [μ.IsOpenPosMeasure]
    {p : X → Prop} (hp : ∀ᵐ x ∂μ, p x) : Dense {x | p x} := by
  rw [dense_iff_closure_eq, closure_eq_compl_interior_compl, compl_univ_iff]
  exact μ.interior_eq_empty_of_null hp

section tkt

theorem mem_span_dual {𝕜 E : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E] [FiniteDimensional 𝕜 E]
    {n : ℕ} {L : Fin n → E →ₗ[𝕜] 𝕜} {K : E →ₗ[𝕜] 𝕜}
    (h : ⨅ i, ker (L i) ≤ ker K) : K ∈ span 𝕜 (range L) := by
  by_contra hK
  rcases exists_dual_map_eq_bot_of_nmem hK inferInstance with ⟨φ, φne, hφ⟩
  let φs := (Module.evalEquiv 𝕜 E).symm φ
  have : K φs = 0 := by
    refine h <| (Submodule.mem_iInf _).2 fun i ↦ (mem_bot 𝕜).1 ?_
    rw [← hφ, Submodule.mem_map]
    exact ⟨L i, Submodule.subset_span ⟨i, rfl⟩, (apply_evalEquiv_symm_apply 𝕜 E _ φ).symm⟩
  simp only [apply_evalEquiv_symm_apply, φs, φne] at this

theorem mem_span_dual' {𝕜 E : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]
    {n : ℕ} {L : Fin n → E →ₗ[𝕜] 𝕜} {K : E →ₗ[𝕜] 𝕜}
    (h : ⨅ i, ker (L i) ≤ ker K) : K ∈ span 𝕜 (range L) := by
  let φ : E →ₗ[𝕜] Fin n → 𝕜 := LinearMap.pi L
  let p := ⨅ i, ker (L i)
  have p_eq : p = ker φ := (ker_pi L).symm
  let ψ : (E ⧸ p) →ₗ[𝕜] Fin n → 𝕜 := p.liftQ φ p_eq.le
  have _ : FiniteDimensional 𝕜 (E ⧸ p) := of_injective ψ (ker_eq_bot.1 (ker_liftQ_eq_bot' p φ p_eq))
  let L' i : (E ⧸ p) →ₗ[𝕜] 𝕜 := p.liftQ (L i) (iInf_le _ i)
  let K' : (E ⧸ p) →ₗ[𝕜] 𝕜 := p.liftQ K h
  have : ⨅ i, ker (L' i) ≤ ker K' := by
    have : LinearMap.pi L' = ψ := by
      ext x i
      simp [L', ψ, φ]
    simp_rw [← ker_pi, this, ψ, ker_liftQ_eq_bot' p φ p_eq]
    exact bot_le
  obtain ⟨c, hK'⟩ := (mem_span_range_iff_exists_fun 𝕜).1 (mem_span_dual this)
  refine (mem_span_range_iff_exists_fun 𝕜).2 ⟨c, ?_⟩
  conv_lhs => enter [2]; intro i; rw [← p.liftQ_mkQ (L i) (iInf_le _ i)]
  rw [← p.liftQ_mkQ K h]
  ext x
  convert LinearMap.congr_fun hK' (p.mkQ x)
  simp only [coeFn_sum, Finset.sum_apply, smul_apply, coe_comp, Function.comp_apply, smul_eq_mul]

end tkt

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

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem span_eq_top_of_ne_zero {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [IsReflexive R M]
    {s : Set (M →ₗ[R] R)} [Free R ((M →ₗ[R] R) ⧸ (span R s))]
    (h : ∀ z : M, z ≠ 0 → ∃ f ∈ s, f z ≠ 0) :
    span R s = ⊤ := by
  by_contra! hn
  rcases exists_dual_map_eq_bot_of_lt_top hn.lt_top inferInstance with ⟨φ, φne, hφ⟩
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
  unfold HasFDerivAt at *
  have hx := hx.isLittleO
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

noncomputable def CoeffSpan {x : E} (nx : x ≠ 0) : span ℝ {x} →ₗ[ℝ] ℝ where
  toFun y := (mem_span_singleton.1 y.2).choose
  map_add' y z := by
    have h1 := (mem_span_singleton.1 y.2).choose_spec
    have h2 := (mem_span_singleton.1 z.2).choose_spec
    have h3 : (mem_span_singleton.1 (y + z).2).choose • x = y + z :=
      (mem_span_singleton.1 (y + z).2).choose_spec
    rw [← h1, ← h2, ← add_smul] at h3
    exact smul_left_injective ℝ nx h3
  map_smul' t y := by
    have h1 := (mem_span_singleton.1 y.2).choose_spec
    have h2 : (mem_span_singleton.1 (t • y).2).choose • x = t • y :=
      (mem_span_singleton.1 (t • y).2).choose_spec
    rw [← h1, smul_smul] at h2
    exact smul_left_injective ℝ nx h2

theorem coeffSpan_smul {x : E} (nx : x ≠ 0) (y : span ℝ {x}) : (CoeffSpan nx y) • x = y :=
  (mem_span_singleton.1 y.2).choose_spec

theorem coeffSpan_self {x : E} (nx : x ≠ 0) :
    CoeffSpan nx ⟨x, mem_span_singleton_self x⟩ = 1 := by
  have hx : x ∈ span ℝ {x} := mem_span_singleton_self x
  have : (CoeffSpan nx ⟨x, hx⟩) • x = x := coeffSpan_smul nx _
  apply smul_left_injective ℝ nx
  simp [this]

theorem exists_eq_norm (x : E) (nx : x ≠ 0) : ∃ f : E →L[ℝ] ℝ, ‖f‖ = 1 ∧ f x = ‖x‖ := by
  let g' : span ℝ {x} →ₗ[ℝ] ℝ :=
    { toFun := fun y ↦ (CoeffSpan nx y) * ‖x‖
      map_add' := fun y z ↦ by simp [add_mul]
      map_smul' := fun t y ↦ by simp [mul_assoc] }
  let g := LinearMap.toContinuousLinearMap g'
  have ng y : ‖g y‖ = ‖y‖ := by
    change ‖(CoeffSpan nx y) * ‖x‖‖ = ‖y‖
    rw [← norm_coe y, ← coeffSpan_smul nx y, norm_smul, norm_mul, norm_norm]
  rcases Real.exists_extension_norm_eq (span ℝ {x}) g with ⟨f, hf, nf⟩
  have hx : x ∈ span ℝ {x} := mem_span_singleton_self x
  refine ⟨f, ?_, ?_⟩
  · rw [nf]
    apply le_antisymm
    · refine g.opNorm_le_bound (by norm_num) (fun y ↦ ?_)
      simp [ng]
    · apply le_of_mul_le_mul_right _ (norm_pos_iff.2 nx)
      rw [one_mul, show ‖x‖ = ‖(⟨x, hx⟩ : span ℝ {x})‖ by rfl]
      nth_rw 1 [← ng ⟨x, hx⟩]
      exact g.le_opNorm _
  · change f (⟨x, hx⟩ : span ℝ {x}) = ‖(⟨x, hx⟩ : span ℝ {x})‖
    rw [hf]
    change (CoeffSpan nx ⟨x, hx⟩) * ‖x‖ = ‖x‖
    rw [coeffSpan_self, one_mul]
