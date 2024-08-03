import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.LinearAlgebra.Dimension.Finrank

open Real NNReal Set Filter Topology FiniteDimensional MeasureTheory Module Submodule

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem dense_of_ae {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    {μ : Measure X} [μ.IsOpenPosMeasure]
    {p : X → Prop} (hp : ∀ᵐ x ∂μ, p x) : Dense {x | p x} := by
  rw [dense_iff_closure_eq, closure_eq_compl_interior_compl, compl_univ_iff]
  exact μ.interior_eq_empty_of_null hp

theorem basis_of_span [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} (hn : finrank ℝ E = n)
    {s : Set E} (hs : span ℝ s = ⊤) :
    ∃ b : Basis (Fin n) ℝ E, range b ⊆ s := by
  let u := (linearIndependent_empty ℝ E).extend (empty_subset s)
  let v : u → E := Subtype.val
  have liv := (linearIndependent_empty ℝ E).linearIndependent_extend (empty_subset s)
  have sv : ⊤ ≤ span ℝ (range v) := by
    rw [Subtype.range_val_subtype, ← hs, span_le]
    exact (linearIndependent_empty ℝ E).subset_span_extend (empty_subset s)
  let w := Basis.mk liv sv
  use w.reindex (w.indexEquiv (finBasisOfFinrankEq ℝ E hn))
  rw [w.range_reindex, show range w = range v by simp [v, w], Subtype.range_val_subtype]
  exact (linearIndependent_empty ℝ E).extend_subset (empty_subset s)

theorem test [FiniteDimensional ℝ E] {n : ℕ} (hn : finrank ℝ (E →ₗ[ℝ] ℝ) = n)
    (h : ∀ z : E, z ≠ 0 → ∃ x : E, DifferentiableAt ℝ (‖·‖) x ∧ fderiv ℝ (‖·‖) x z ≠ 0) :
    ∃ b : Basis (Fin n) ℝ (E →ₗ[ℝ] ℝ),
      ∀ i, ∃ y : E, DifferentiableAt ℝ (‖·‖) y ∧ b i = fderiv ℝ (‖·‖) y := by
  let S := {f : E→ₗ[ℝ] ℝ | ∃ x : E, DifferentiableAt ℝ (‖·‖) x ∧ f = fderiv ℝ (‖·‖) x}
  have : span ℝ S = ⊤ := by
    by_contra! hn
    rcases exists_dual_map_eq_bot_of_lt_top hn.lt_top inferInstance with ⟨f, fne, hf⟩
    let fs := (Module.evalEquiv ℝ E).symm f
    have : ∀ x : E, DifferentiableAt ℝ (‖·‖) x → fderiv ℝ (‖·‖) x fs = 0 := by
      intro x dx
      rw [← mem_bot ℝ, ← hf, Submodule.mem_map]
      exact ⟨fderiv ℝ (‖·‖) x, Submodule.subset_span ⟨x, dx, rfl⟩,
        (apply_evalEquiv_symm_apply ℝ E (fderiv ℝ (‖·‖) x) f).symm⟩
    have fsn : fs ≠ 0 := by simp [fne, fs]
    rcases h fs fsn with ⟨x, dx, hx⟩
    exact hx <| this x dx
  rcases basis_of_span hn this with ⟨b, hb⟩
  exact ⟨b, fun i ↦ hb ⟨i, rfl⟩⟩

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
    smul_smul, mul_div_cancel₀ _ ht, ContinuousLinearMap.smul_apply, ← norm_eq_abs, smul_eq_mul,
    ← mul_sub, ← mul_sub, norm_mul, norm_norm, norm_smul, ← mul_assoc, mul_comm c, mul_assoc,
    _root_.mul_le_mul_left]
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

theorem fderiv_norm_smul_pos {x : E} {t : ℝ} (ht : t > 0) :
    fderiv ℝ (‖·‖) (t • x) = fderiv ℝ (‖·‖) x := by
  rw [fderiv_norm_smul, abs_of_pos ht, div_self ht.ne.symm, one_smul]

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
          rw [_root_.mul_le_mul_left]
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
    {x : ℕ → E} (hd : ∀ n, DifferentiableAt ℝ (‖·‖) (x n))
    {z : E} (ht : Tendsto x atTop (𝓝 z)) :
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

theorem norm_normalize {x : E} (hx : x ≠ 0) : ‖(1 / ‖x‖) • x‖ = 1 := by
  rw [norm_smul, norm_div, norm_one, norm_norm, one_div_mul_cancel (norm_ne_zero_iff.2 hx)]

theorem dense_seq {X : Type*} [TopologicalSpace X] [FrechetUrysohnSpace X]
    {s : Set X} (hs : Dense s) (x : X) :
    ∃ u : ℕ → X, (∀ n, u n ∈ s) ∧ Tendsto u atTop (𝓝 x) := by
  rw [← mem_closure_iff_seq_limit, dense_iff_closure_eq.1 hs]; trivial

theorem exists_inverse' [FiniteDimensional ℝ E] {n : ℕ} (hn : finrank ℝ (E →ₗ[ℝ] ℝ) = n)
    (φ : E → F) (hφ : Isometry φ) (φz : φ 0 = 0)
    (hlol : Dense (X := F) (Submodule.span ℝ (range φ))) :
    ∃ (f : F →L[ℝ] E), ‖f‖ = 1 ∧ f ∘ φ = id := by
  have main (x : E) (nx : ‖x‖ = 1) : ∃ f : F →L[ℝ] ℝ, ‖f‖ = 1 ∧ ∀ t : ℝ, f (φ (t • x)) = t := by
    apply exists_inverse
    · exact finrank_self ℝ
    · apply Isometry.of_dist_eq
      intro x₁ x₂
      rw [hφ.dist_eq, dist_eq_norm, ← sub_smul, norm_smul, nx, mul_one, dist_eq_norm]
  choose! f nf hf using main
  have aux2 : Dense {x : E | DifferentiableAt ℝ (‖·‖) x} := by
    let _ : MeasurableSpace E := borel E
    have _ : BorelSpace E := ⟨rfl⟩
    let w := FiniteDimensional.finBasis ℝ E
    exact dense_of_ae (lipschitzWith_one_norm.ae_differentiableAt (μ := w.addHaar))
  have aux3 (z : E) (hz : z ≠ 0) : ∃ x', DifferentiableAt ℝ (‖·‖) x' ∧ fderiv ℝ (‖·‖) x' z ≠ 0 := by
    obtain ⟨u, hu, htu⟩ := dense_seq aux2 z
    have := tendsto_differentiable hu htu
    have := this.eventually_ne (norm_ne_zero_iff.2 hz)
    rw [eventually_atTop] at this
    rcases this with ⟨N, hN⟩
    exact ⟨u N, hu N, hN N (le_refl N)⟩
  rcases test hn aux3 with ⟨b, hb⟩
  have hb i : ∃ y : E, ‖y‖ = 1 ∧ DifferentiableAt ℝ (‖·‖) y ∧ b i = fderiv ℝ (‖·‖) y := by
    rcases hb i with ⟨y, dy, hy⟩
    have bin := b.ne_zero i
    have yn : y ≠ 0 := by
      intro hyn
      rw [hyn, fderiv_zero_of_not_differentiableAt] at hy
      exact bin hy
      exact not_differentiableAt_norm_zero E
    refine ⟨(1 / ‖y‖) • y, norm_normalize yn,
      (differentiableAt_norm_smul (one_div_ne_zero (norm_ne_zero_iff.2 yn))).1 dy, ?_⟩
    rw [fderiv_norm_smul_pos, hy]
    exact one_div_pos.2 <| norm_pos_iff.2 yn
  choose y ny dy hy using hb
  let c := (b.dualBasis).map (Module.evalEquiv ℝ E).symm
  have mdr i j : b i (c j) = if i = j then 1 else 0 := by
    calc
      (b i) (c j)
        = Module.evalEquiv ℝ E ((Module.evalEquiv ℝ E).symm (b.dualBasis j)) (b i) := rfl
      _ = b.dualBasis j (b i) := by
        rw [(Module.evalEquiv ℝ E).apply_symm_apply]
      _ = if i = j then 1 else 0 := b.dualBasis_apply_self j i
  let T : F →L[ℝ] E :=
    { toFun := fun z ↦ ∑ i, (f (y i) z) • (c i)
      map_add' := by
        intro z w
        simp_rw [map_add, add_smul]
        rw [Finset.sum_add_distrib]
      map_smul' := by
        intro m z
        simp_rw [_root_.map_smul, smul_eq_mul, ← smul_smul]
        rw [← Finset.smul_sum]
        rfl
      cont := continuous_finset_sum (@Finset.univ (Fin n) _) fun _ ↦ by fun_prop }
  use T
  have Tφ x : T (φ x) = x := by
    have this i : LipschitzWith 1 ((f (y i)) ∘ φ) := by
      convert (f (y i)).lipschitz.comp hφ.lipschitz
      rw [← norm_toNNReal, nf _ (ny i), mul_one, toNNReal_one]
    have aux1 i x : f (y i) (φ x) = fderiv ℝ (‖·‖) (y i) x :=
      congrFun (unique1 (ny i) (dy i) ((f (y i)) ∘ φ) (this i) (hf _ (ny i))) x
    have aux2 i x : f (y i) (φ x) = b i x := by
      rw [aux1]
      exact (LinearMap.congr_fun (hy i) x).symm
    simp only [ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk, aux2, T]
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
    exact LinearMap.congr_fun this x
  constructor
  · apply le_antisymm
    · have prim : ∀ x : E, ‖x‖ = 1 → DifferentiableAt ℝ (‖·‖) x → f x = (fderiv ℝ (‖·‖) x) ∘ T := by
        intro x nx dx
        apply Continuous.ext_on hlol
        · exact (f x).continuous
        · exact (ContinuousLinearMap.continuous _).comp T.continuous
        · intro y hy
          change f x y = ((fderiv ℝ (‖·‖) x).comp T) y
          apply LinearMap.eqOn_span (R := ℝ) _ hy
          rintro - ⟨z, rfl⟩
          have : LipschitzWith 1 ((f x) ∘ φ) := by
            convert (f x).lipschitz.comp hφ.lipschitz
            rw [← norm_toNNReal, nf x nx, mul_one, toNNReal_one]
          have aux1 := unique1 nx dx ((f x) ∘ φ) this (hf x nx)
          simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
          rw [Tφ]
          exact congrFun aux1 z
      apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
      intro y
      obtain ⟨u, hu, htu⟩ := dense_seq aux2 (T y)
      have := tendsto_differentiable hu htu
      have unez n : u n ≠ 0 := by
        intro h
        have := h ▸ hu n
        exact not_differentiableAt_norm_zero E this
      have obv n : 1 / ‖u n‖ > 0 := one_div_pos.2 <| norm_pos_iff.2 <| unez n
      have mdr n : fderiv ℝ (‖·‖) (u n) = fderiv ℝ (‖·‖) ((1 / ‖u n‖) • (u n)) :=
        (fderiv_norm_smul_pos (obv n)).symm
      simp_rw [mdr] at this
      apply le_of_tendsto this
      apply eventually_of_forall
      intro n
      have : fderiv ℝ (‖·‖) ((1 / ‖u n‖) • (u n)) (T y) = f ((1 / ‖u n‖) • (u n)) y := by
        have putain : DifferentiableAt ℝ (‖·‖) ((1 / ‖u n‖) • (u n)) :=
          (differentiableAt_norm_smul (obv n).ne.symm).1 (hu n)
        exact congrFun (prim _ (norm_normalize (unez n)) putain).symm y
      rw [this]
      calc
        f ((1 / ‖u n‖) • (u n)) y ≤ ‖f ((1 / ‖u n‖) • (u n)) y‖ := by
          rw [norm_eq_abs]
          exact le_abs_self _
        _ ≤ ‖f ((1 / ‖u n‖) • (u n))‖ * ‖y‖ := ContinuousLinearMap.le_opNorm _ y
        _ = 1 * ‖y‖ := by rw [nf _ (norm_normalize (unez n))]
    · have nφ := hφ.norm_map_of_map_zero φz
      rcases NormedSpace.exists_lt_norm ℝ E 0 with ⟨x, hx⟩
      apply le_of_mul_le_mul_right _ hx
      nth_rw 1 [← Tφ x]
      rw [← nφ x, one_mul]
      exact T.le_opNorm _
  · ext x
    exact Tφ x
