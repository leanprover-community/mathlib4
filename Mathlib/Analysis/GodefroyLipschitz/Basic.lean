import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.LinearAlgebra.Dimension.Finrank

open Real NNReal Set Filter Topology FiniteDimensional MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem dense_of_ae {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    {μ : Measure X} [μ.IsOpenPosMeasure]
    {p : X → Prop} (hp : ∀ᵐ x ∂μ, p x) : Dense {x | p x} := by
  rw [dense_iff_closure_eq, closure_eq_compl_interior_compl, compl_univ_iff]
  exact μ.interior_eq_empty_of_null hp

theorem test [FiniteDimensional ℝ E]
    (h : ∀ z : E, z ≠ 0 → ∃ x : E, DifferentiableAt ℝ (‖·‖) x ∧ fderiv ℝ (‖·‖) x z ≠ 0) :
    ∃ b : Basis (Fin (finrank ℝ (Module.Dual ℝ E))) ℝ (Module.Dual ℝ E),
      ∀ i, ∃ y : E, DifferentiableAt ℝ (‖·‖) y ∧ b i = fderiv ℝ (‖·‖) y := by
  let S := {f : E→ₗ[ℝ] ℝ | ∃ x : E, DifferentiableAt ℝ (‖·‖) x ∧ f = fderiv ℝ (‖·‖) x}
  have : Submodule.span ℝ S = ⊤ := by
    by_contra! hn
    have hlt := hn.lt_top
    rcases Submodule.exists_dual_map_eq_bot_of_lt_top hlt inferInstance with ⟨f, fne, hf⟩
    let fs := (Module.evalEquiv ℝ E).symm f
    have : ∀ x : E, DifferentiableAt ℝ (‖·‖) x → fderiv ℝ (‖·‖) x fs = 0 := by
      intro x hx
      rw [← Submodule.mem_bot ℝ, ← hf, Submodule.mem_map]
      use fderiv ℝ (‖·‖) x
      refine ⟨Submodule.subset_span ⟨x, hx, rfl⟩, ?_⟩
      simp only [fs]
      convert (Module.apply_evalEquiv_symm_apply ℝ E (fderiv ℝ (‖·‖) x) f).symm
    have fsn : fs ≠ 0 := by
      simp only [ne_eq, AddEquivClass.map_eq_zero_iff, fne, not_false_eq_true, fs]
    rcases h fs fsn with ⟨x, dx, hx⟩
    exact hx <| this x dx
  let u := LinearIndependent.extend (linearIndependent_empty ℝ (Module.Dual ℝ E)) (empty_subset S)
  have liu := LinearIndependent.linearIndependent_extend
    (linearIndependent_empty ℝ (Module.Dual ℝ E)) (empty_subset S)
  have spu : ⊤ ≤ Submodule.span ℝ u := by
    have aux := (linearIndependent_empty ℝ (Module.Dual ℝ E)).subset_span_extend (empty_subset S)
    rw [← Submodule.span_le, this] at aux
    exact aux
  have hu : ∀ b ∈ u, ∃ y : E, DifferentiableAt ℝ (‖·‖) y ∧ b = fderiv ℝ (‖·‖) y := by
    intro b hb
    have := (linearIndependent_empty ℝ (Module.Dual ℝ E)).extend_subset (empty_subset S)
    rcases this hb with ⟨x, dx, rfl⟩
    exact ⟨x, dx, rfl⟩
  let v : {x // x ∈ u} → Module.Dual ℝ E := Subtype.val
  have rv : range v = u := Subtype.range_val_subtype
  have spv : ⊤ ≤ Submodule.span ℝ (range v) := by rwa [rv]
  let x := Basis.mk liu spv
  let w := FiniteDimensional.finBasis ℝ (Module.Dual ℝ E)
  let e := Basis.indexEquiv x w
  let b := x.reindex e
  use b
  intro i
  have aux1 : range b = range x := x.range_reindex e
  have aux2 : range x = range v := by
    simp [x, v]
  have omg : b i ∈ u := by
    rw [← rv, ← aux2, ← aux1]
    exact ⟨i, rfl⟩
  exact hu _ omg

theorem lol (f : E → ℝ) (x y : E) (h : DifferentiableAt ℝ f x) :
    fderiv ℝ f x y = deriv (fun t : ℝ ↦ f (x + t • y)) 0 := by
  conv_rhs => enter [1]; change f ∘ (fun t ↦ x + t • y)
  rw [fderiv.comp_deriv, zero_smul, add_zero, deriv_const_add, deriv_smul_const, deriv_id'']
  · simp
  · exact differentiableAt_id
  · simpa
  · simp

theorem logique {x : E} {t : ℝ} (ht : t ≠ 0) {f : E →L[ℝ] ℝ} (hx : HasFDerivAt (‖·‖) f x) :
    HasFDerivAt (‖·‖) ((|t| / t) • f) (t • x) := by
  unfold HasFDerivAt at *
  have := hx.isLittleO
  constructor
  rw [Asymptotics.isLittleO_iff] at this
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have := this hc
  rw [eventually_iff, ← set_smul_mem_nhds_smul_iff ht] at this
  filter_upwards [this]
  rintro - ⟨ε, hε, rfl⟩
  simp only
  rw [norm_smul, norm_smul, ← smul_sub, _root_.map_smul, ← ContinuousLinearMap.smul_apply,
    smul_smul, mul_div_cancel₀ _ ht, ContinuousLinearMap.smul_apply, ← norm_eq_abs, smul_eq_mul,
    ← mul_sub, ← mul_sub, norm_mul, norm_norm, norm_smul, ← mul_assoc, mul_comm c, mul_assoc,
    mul_le_mul_left]
  · exact hε
  · exact norm_pos_iff.2 ht

theorem differentiableAt_norm_smul {x : E} {t : ℝ} (ht : t ≠ 0) :
    DifferentiableAt ℝ (‖·‖) x ↔ DifferentiableAt ℝ (‖·‖) (t • x) where
  mp hd := (logique ht hd.hasFDerivAt).differentiableAt
  mpr hd := by
    convert (logique (inv_ne_zero ht) hd.hasFDerivAt).differentiableAt
    rw [smul_smul, inv_mul_cancel ht, one_smul]

theorem fderiv_norm {x : E} (h : DifferentiableAt ℝ (‖·‖) x) :
    fderiv ℝ (‖·‖) x x = ‖x‖ := by
  rw [lol _ _ _ h]
  have this (t : ℝ) (ht : t ≥ -1) : ‖x + t • x‖ = (1 + t) * ‖x‖ := by
    calc
      ‖x + t • x‖ = ‖(1 + t) • x‖ := by
        rw [add_smul, one_smul]
      _ = |1 + t| * ‖x‖ := by
        rw [← norm_eq_abs, norm_smul]
      _ = (1 + t) * ‖x‖ := by
        rw [abs_eq_self.2]
        linarith
  rw [← derivWithin_of_mem_nhds (s := Ici (-1)), derivWithin_congr (f := fun t ↦ (1 + t) * ‖x‖),
    derivWithin_of_mem_nhds]
  · rw [deriv_mul_const, deriv_const_add]
    simp
    apply DifferentiableAt.const_add
    exact differentiableAt_id
  · exact Ici_mem_nhds (by norm_num)
  · intro t ht
    apply this
    simpa
  · simp
  · exact Ici_mem_nhds (by norm_num)

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
    have mdr : (fun t : ℝ ↦ |t|) = fun t : ℝ ↦ (1 / ‖x‖) * |t| * ‖x‖ := by
      ext t
      rw [mul_assoc, mul_comm, mul_assoc, mul_one_div_cancel, mul_one]
      exact hx.ne.symm
    rw [mdr]
    simp_rw [mul_assoc]
    apply DifferentiableAt.const_mul
    exact this
  exact not_differentiableAt_abs_zero this

theorem fderiv_norm_smul (x : E) (t : ℝ) :
    fderiv ℝ (‖·‖) (t • x) = (|t| / t) • (fderiv ℝ (‖·‖) x) := by
  by_cases Nontrivial E
  · by_cases hd : DifferentiableAt ℝ (‖·‖) x
    · rcases eq_or_ne t 0 with rfl | ht
      · simp only [zero_smul, abs_zero, div_zero]
        rw [fderiv_zero_of_not_differentiableAt]
        exact not_differentiableAt_norm_zero E
      · rw [(logique ht hd.hasFDerivAt).fderiv]
    · rw [fderiv_zero_of_not_differentiableAt hd, smul_zero, fderiv_zero_of_not_differentiableAt]
      rcases eq_or_ne t 0 with rfl | ht
      · convert not_differentiableAt_norm_zero E
        exact zero_smul _ _
      · exact (differentiableAt_norm_smul ht).not.1 hd
  · rw [not_nontrivial_iff_subsingleton] at *
    rw [(hasFDerivAt_of_subsingleton _ _).fderiv, (hasFDerivAt_of_subsingleton _ _).fderiv]
    simp

theorem norm_fderiv_norm {x : E} (h : DifferentiableAt ℝ (‖·‖) x) :
    ‖fderiv ℝ (‖·‖) x‖ = 1 := by
  have : x ≠ 0 := by
    intro hx
    apply not_differentiableAt_norm_zero E
    convert h
    exact hx.symm
  apply le_antisymm
  · rw [show (1 : ℝ) = ↑(1 : ℝ≥0) by rfl]
    apply norm_fderiv_le_of_lipschitz
    exact lipschitzWith_one_norm
  · apply le_of_mul_le_mul_right (a := ‖x‖)
    rw [one_mul]
    calc
      ‖x‖ = fderiv ℝ (‖·‖) x x := (fderiv_norm h).symm
      _ ≤ ‖fderiv ℝ (‖·‖) x x‖ := le_norm_self _
      _ ≤ ‖fderiv ℝ (‖·‖) x‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
    exact norm_pos_iff.2 this


theorem unique1 [FiniteDimensional ℝ E] {x : E} (hx : ‖x‖ = 1) (h : DifferentiableAt ℝ (‖·‖) x)
    (φ : E → ℝ) (hφ : LipschitzWith 1 φ) (φ_eq : ∀ t : ℝ, φ (t • x) = t) :
    φ = fderiv ℝ (‖·‖) x := by
  ext y
  have this t (ht : t ≠ 0) : 1 = |t * (φ y) - t * (φ (((φ y) + 1 / t) • x))| := by
    rw [φ_eq, mul_add, ← sub_sub, sub_self, mul_one_div_cancel ht]
    simp
  have this (t : ℝ) : 1 ≤ ‖x - t • (y - (φ y) • x)‖ := by
    rcases eq_or_ne t 0 with rfl | ht
    · rw [zero_smul, sub_zero, hx]
    · calc
        1 = |t * (φ y) - t * (φ (((φ y) + 1 / t) • x))| := this t ht
        _ = |t| * |φ y - φ (((φ y) + 1 / t) • x)| := by
          rw [← abs_mul]
          congr
          ring
        _ ≤ |t| * ‖y - (φ y + 1 / t) • x‖ := by
          rw [mul_le_mul_left]
          convert hφ.dist_le_mul y ((φ y + 1 / t) • x) using 1
          · simp [dist_eq_norm]
          · exact abs_pos.2 ht
        _ = ‖x - t • (y - (φ y) • x)‖ := by
          rw [← norm_eq_abs, ← norm_smul, ← norm_neg, smul_sub, smul_smul, mul_add,
            mul_one_div_cancel ht, add_smul, one_smul, mul_smul, smul_sub]
          congr 1
          abel
  have : IsLocalMin (fun t : ℝ ↦ ‖x - t • (y - (φ y) • x)‖) 0 := by
    simp [IsLocalMin, IsMinFilter, hx, this]
  have aux := this.deriv_eq_zero
  have : deriv (fun t : ℝ ↦ ‖x - t • (y - (φ y) • x)‖) 0 = - fderiv ℝ (‖·‖) x (y - (φ y) • x) := by
    conv_lhs => enter [1]; change ((‖·‖) ∘ (fun t : ℝ ↦ x - t • (y - (φ y) • x)))
    rw [fderiv.comp_deriv]
    · rw [deriv_const_sub, deriv_smul_const]
      simp
      exact differentiableAt_id
    · simpa
    · simp
  rw [aux, map_sub, _root_.map_smul, fderiv_norm h, hx] at this
  simp only [smul_eq_mul, mul_one, neg_sub] at this
  exact sub_eq_zero.1 this.symm

theorem tendsto_differentiable
    (x : ℕ → E) (hd : ∀ n, DifferentiableAt ℝ (‖·‖) (x n))
    (z : E) (ht : Tendsto x atTop (𝓝 z)) :
    Tendsto (fun n ↦ fderiv ℝ (‖·‖) (x n) z) atTop (𝓝 ‖z‖) := by
  have aux1 : Tendsto (fun n ↦ fderiv ℝ (‖·‖) (x n) (x n)) atTop (𝓝 ‖z‖) := by
    simp_rw [fun n ↦ fderiv_norm (hd n)]
    exact (continuous_norm.tendsto z).comp ht
  apply tendsto_of_tendsto_of_dist aux1
  simp_rw [dist_eq_norm, ← map_sub]
  apply squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ContinuousLinearMap.le_opNorm _ _)
  simp_rw [fun n ↦ norm_fderiv_norm (hd n), one_mul]
  exact tendsto_iff_norm_sub_tendsto_zero.1 ht

theorem exists_inverse (h : finrank ℝ E = 1) (φ : E → F) (hφ : Isometry φ) :
    ∃ (f : F →L[ℝ] E), ‖f‖ = 1 ∧ ∀ x : E, f (φ x) = x := by sorry

theorem exists_inverse' [FiniteDimensional ℝ E] (φ : E → F) (hφ : Isometry φ) :
    ∃ (f : F →L[ℝ] E), ‖f‖ = 1 ∧ f ∘ φ = id := by
  have main (x : E) (nx : ‖x‖ = 1) :
      ∃ f : F →L[ℝ] ℝ, ‖f‖ = 1 ∧ ∀ t : ℝ, f (φ (t • x)) = t := by
    apply exists_inverse
    · exact finrank_self ℝ
    · apply Isometry.of_dist_eq
      intro x₁ x₂
      rw [hφ.dist_eq, dist_eq_norm, ← sub_smul, norm_smul, nx, mul_one, dist_eq_norm]
  have aux2 : Dense {x : E | DifferentiableAt ℝ (‖·‖) x} := by
    let _ : MeasurableSpace E := borel E
    have _ : BorelSpace E := ⟨rfl⟩
    let w := FiniteDimensional.finBasis ℝ E
    let μ := w.addHaar
    have := lipschitzWith_one_norm.ae_differentiableAt (μ := μ)
    exact dense_of_ae this
  have aux3 (z : E) : z ≠ 0 → ∃ x', DifferentiableAt ℝ (‖·‖) x' ∧ fderiv ℝ (‖·‖) x' z ≠ 0 := by
    intro hz
    have : z ∈ closure {x : E | DifferentiableAt ℝ (‖·‖) x} := by
      rw [dense_iff_closure_eq.1 aux2]; trivial
    obtain ⟨u, hu, htu⟩ := mem_closure_iff_seq_limit.1 this
    have := tendsto_differentiable u hu z htu
    have := this.eventually_ne (norm_ne_zero_iff.2 hz)
    rw [eventually_atTop] at this
    rcases this with ⟨N, hN⟩
    use u N, hu N, hN N (le_refl N)
  rcases test aux3 with ⟨b, hb⟩
  have hb i : ∃ y : E, ‖y‖ = 1 ∧ DifferentiableAt ℝ (‖·‖) y ∧ b i = fderiv ℝ (‖·‖) y := by
    rcases hb i with ⟨y, dy, hy⟩
    have bin := b.ne_zero i
    have yn : y ≠ 0 := by
      intro hyn
      rw [hyn, fderiv_zero_of_not_differentiableAt] at hy
      exact bin hy
      exact not_differentiableAt_norm_zero E
    use (1 / ‖y‖) • y
    constructor
    · rw [norm_smul, norm_div, norm_one, norm_norm, one_div_mul_cancel]
      exact norm_ne_zero_iff.2 yn
    · constructor
      · apply (differentiableAt_norm_smul _).1
        · exact dy
        · exact one_div_ne_zero (norm_ne_zero_iff.2 yn)
      · rw [fderiv_norm_smul, abs_div, abs_one, abs_norm, div_self, one_smul, hy]
        apply one_div_ne_zero
        exact norm_ne_zero_iff.2 yn
  choose y ny dy hy using hb
  let c := (b.dualBasis).map (Module.evalEquiv ℝ E).symm
  have mdr i j : b i (c j) = if i = j then 1 else 0 := by
    calc
      (b i) (c j)
        = Module.evalEquiv ℝ E (c j) (b i) := rfl
      _ = Module.evalEquiv ℝ E ((Module.evalEquiv ℝ E).symm (b.dualBasis j)) (b i) := rfl
      _ = b.dualBasis j (b i) := by
        rw [(Module.evalEquiv ℝ E).apply_symm_apply]
      _ = if i = j then 1 else 0 := b.dualBasis_apply_self j i
  choose f nf hf using fun i ↦ main (y i) (ny i)
  let T : F →L[ℝ] E :=
    { toFun := fun y ↦ ∑ i, (f i y) • (c i)
      map_add' := by
        intro y z
        simp_rw [map_add, add_smul]
        rw [Finset.sum_add_distrib]
      map_smul' := by
        intro m y
        simp_rw [_root_.map_smul, smul_eq_mul, ← smul_smul]
        rw [← Finset.smul_sum]
        rfl }
  use T
  constructor
  · sorry
  · have best i x : f i (φ x) = b i x := by
      have : LipschitzWith 1 ((f i) ∘ φ) := by
        convert (f i).lipschitz.comp hφ.lipschitz
        rw [← norm_toNNReal, nf i, mul_one, toNNReal_one]
      have aux1 := unique1 (ny i) (dy i) ((f i) ∘ φ) this (hf i)
      have := congrFun aux1 x
      convert this
      ext x
      have := LinearMap.congr_fun (hy i) x
      convert this
    let g : E →ₗ[ℝ] E :=
      { toFun := fun y ↦ ∑ i, (b i y) • (c i)
        map_add' := by
          intro y z
          simp_rw [map_add, add_smul]
          rw [Finset.sum_add_distrib]
        map_smul' := by
          intro m y
          simp_rw [_root_.map_smul, smul_eq_mul, ← smul_smul]
          rw [← Finset.smul_sum]
          rfl }
    have : g = LinearMap.id := by
      apply c.ext
      intro i
      simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.id_coe, id_eq, g]
      simp_rw [mdr, ite_smul, one_smul, zero_smul]
      rw [Fintype.sum_ite_eq']
    ext x
    convert LinearMap.congr_fun this x
    ext x
    simp only [ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply, T,
      g]
    simp_rw [best]
