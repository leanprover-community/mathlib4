import Mathlib.Analysis.GodefroyLipschitz.Annexe

open Real NNReal Set Filter Topology FiniteDimensional MeasureTheory Module Submodule

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem unique1 [FiniteDimensional ℝ E] {x : E} (nx : ‖x‖ = 1) (hx : DifferentiableAt ℝ (‖·‖) x)
    (φ : E → ℝ) (hφ : LipschitzWith 1 φ) (φ_eq : ∀ t : ℝ, φ (t • x) = t) :
    φ = fderiv ℝ (‖·‖) x := by
  ext y
  have this t (ht : t ≠ 0) : 1 = |t * (φ y) - t * (φ (((φ y) + 1 / t) • x))| := by
    rw [φ_eq, mul_add, ← sub_sub, sub_self, mul_one_div_cancel ht]
    simp
  have this (t : ℝ) : 1 ≤ ‖x - t • (y - (φ y) • x)‖ := by
    rcases eq_or_ne t 0 with rfl | ht
    · rw [zero_smul, sub_zero, nx]
    · calc
        1 = |t| * |φ y - φ (((φ y) + 1 / t) • x)| := by
          nth_rw 1 [this t ht, ← abs_mul, mul_sub]
        _ ≤ |t| * ‖y - (φ y + 1 / t) • x‖ := by
          rw [_root_.mul_le_mul_left (abs_pos.2 ht), ← norm_eq_abs]
          convert hφ.norm_sub_le _ _
          simp
        _ = ‖x - t • (y - (φ y) • x)‖ := by
          rw [← norm_eq_abs, ← norm_smul, ← norm_neg, smul_sub, smul_smul, mul_add,
            mul_one_div_cancel ht, add_smul, one_smul, mul_smul, smul_sub]
          congr 1
          abel
  have : IsLocalMin (fun t : ℝ ↦ ‖x - t • (y - (φ y) • x)‖) 0 := by
    simp [IsLocalMin, IsMinFilter, nx, this]
  have aux := this.deriv_eq_zero
  have : deriv (fun t : ℝ ↦ ‖x - t • (y - (φ y) • x)‖) 0 = - fderiv ℝ (‖·‖) x (y - (φ y) • x) := by
    conv_lhs => enter [1]; change ((‖·‖) ∘ (fun t : ℝ ↦ x - t • (y - (φ y) • x)))
    rw [fderiv.comp_deriv]
    · rw [deriv_const_sub, deriv_smul_const]
      simp
      exact differentiableAt_id
    · simpa
    · simp
  rw [aux, map_sub, _root_.map_smul, fderiv_norm_self hx, nx] at this
  simp only [smul_eq_mul, mul_one, neg_sub] at this
  exact sub_eq_zero.1 this.symm

theorem tendsto_differentiable [Nontrivial E]
    {x : ℕ → E} (hd : ∀ n, DifferentiableAt ℝ (‖·‖) (x n))
    {z : E} (ht : Tendsto x atTop (𝓝 z)) :
    Tendsto (fun n ↦ fderiv ℝ (‖·‖) (x n) z) atTop (𝓝 ‖z‖) := by
  have aux1 : Tendsto (fun n ↦ fderiv ℝ (‖·‖) (x n) (x n)) atTop (𝓝 ‖z‖) := by
    simp_rw [fun n ↦ fderiv_norm_self (hd n)]
    exact (continuous_norm.tendsto z).comp ht
  apply tendsto_of_tendsto_of_dist aux1
  simp_rw [dist_eq_norm, ← map_sub]
  apply squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ContinuousLinearMap.le_opNorm _ _)
  simp_rw [fun n ↦ norm_fderiv_norm (hd n), one_mul]
  exact tendsto_iff_norm_sub_tendsto_zero.1 ht

theorem aux (a b c : ℝ) (ha : |a| ≤ c) (hb : |b| ≤ c) (h : a - b = 2 * c) :
    a = c ∧ b = -c := by
  have ha : a ≤ c := (abs_le.1 ha).2
  have hb : -c ≤ b := (abs_le.1 hb).1
  by_contra this
  rw [Classical.not_and_iff_or_not_not] at this
  rcases this with ha' | hb'
  · have ha : a < c := lt_of_le_of_ne ha ha'
    linarith
  · change b ≠ -c at hb'
    have hb : -c < b := lt_of_le_of_ne hb hb'.symm
    linarith

theorem Isometry.map_norm_sub {φ : E → F} (hφ : Isometry φ) (x y : E) :
    ‖φ x - φ y‖ = ‖x - y‖ := by
  rw [← dist_eq_norm, hφ.dist_eq, dist_eq_norm]

theorem exists_inverse (φ : ℝ → F) (hφ : Isometry φ) (φz : φ 0 = 0) :
    ∃ (f : F →L[ℝ] ℝ), ‖f‖ = 1 ∧ ∀ t : ℝ, f (φ t) = t := by
  have this (k : ℕ) (hk : 1 ≤ k) :
      ∃ f : F →L[ℝ] ℝ, ‖f‖ = 1 ∧ ∀ t : ℝ, t ∈ Icc (-k : ℝ) k → f (φ t) = t := by
    obtain ⟨f, nf, hf⟩ : ∃ f : F →L[ℝ] ℝ, ‖f‖ = 1 ∧ f ((φ k) - (φ (-k))) = 2 * k := by
      have nk : ‖(φ k) - (φ (-k))‖ = 2 * k := by
        rw [hφ.map_norm_sub, norm_eq_abs, sub_neg_eq_add, two_mul, abs_eq_self.2 (by positivity)]
      have hnk : (φ k) - (φ (-k)) ≠ 0 := by
        rw [← norm_pos_iff, nk]
        positivity
      obtain ⟨f, nf, hfk⟩ := exists_eq_norm _ hnk
      use f, nf
      rw [hfk, nk]
    refine ⟨f, nf, fun t tmem ↦ ?_⟩
    have ⟨h1, h2⟩ : f (φ k) = k ∧ f (φ (-k)) = -k := by
      apply aux
      · rw [← norm_eq_abs]
        convert f.le_opNorm (φ k)
        rw [nf, one_mul, hφ.norm_map_of_map_zero φz, norm_eq_abs, abs_eq_self.2 (by positivity)]
      · rw [← norm_eq_abs]
        convert f.le_opNorm (φ (-k))
        rw [nf, one_mul, hφ.norm_map_of_map_zero φz, norm_eq_abs, abs_eq_neg_self.2 (by simp),
          neg_neg]
      · rw [← map_sub, hf]
    rcases le_total t 0 with ht | ht
    · have : f ((φ t) - (φ (-k))) = t - (-k) := by
        apply le_antisymm
        · apply le_trans <| le_abs_self _
          rw [← norm_eq_abs]
          apply le_trans <| f.le_opNorm _
          rw [nf, one_mul, hφ.map_norm_sub, norm_eq_abs, abs_eq_self.2]
          linarith [mem_Icc.1 tmem |>.1]
        · have : |f (φ t)| ≤ -t := by
            rw [← norm_eq_abs]
            convert f.le_opNorm (φ t) using 1
            rw [nf, hφ.norm_map_of_map_zero φz, one_mul, norm_eq_abs, abs_eq_neg_self.2 ht]
          rw [map_sub, h2]
          linarith [abs_le.1 this |>.1]
      simpa [map_sub, h2] using this
    · have : f ((φ k) - (φ t)) = k - t := by
        apply le_antisymm
        · apply le_trans <| le_abs_self _
          rw [← norm_eq_abs]
          apply le_trans <| f.le_opNorm _
          rw [nf, one_mul, hφ.map_norm_sub, norm_eq_abs, abs_eq_self.2]
          linarith [mem_Icc.1 tmem |>.2]
        · have : |f (φ t)| ≤ t := by
            rw [← norm_eq_abs]
            convert f.le_opNorm (φ t) using 1
            rw [nf, hφ.norm_map_of_map_zero φz, one_mul, norm_eq_abs, abs_eq_self.2 ht]
          rw [map_sub, h1]
          linarith [abs_le.1 this |>.2]
      simpa [map_sub, h1] using this
  choose! f nf hf using this
  obtain ⟨g, ψ, hψ, hg⟩ : ∃ (g : F →L[ℝ] ℝ) (ψ : ℕ → ℕ), StrictMono ψ ∧
      ∀ y, Tendsto (fun n ↦ f (ψ n) y) atTop (𝓝 (g y)) := by sorry
  refine ⟨g, le_antisymm (g.opNorm_le_bound (by norm_num) fun y ↦ ?_) ?_, fun t ↦ ?_⟩
  · apply le_of_tendsto ((continuous_norm.tendsto _).comp (hg y))
    rw [eventually_atTop]
    exact ⟨1, fun c hc ↦ nf (ψ c) (hc.trans (hψ.id_le c)) ▸ (f (ψ c)).le_opNorm _⟩
  · have : ∀ n ≥ 1, ‖f (ψ n) (φ 1)‖ = 1 := by
      intro n hn
      rw [hf (ψ n) (hn.trans (hψ.id_le n)), norm_one]
      rw [mem_Icc]
      constructor
      · linarith
      · norm_cast
        exact hn.trans <| hψ.id_le n
    have : 1 = ‖g (φ 1)‖ := by
      have aux1 : Tendsto (fun n ↦ ‖f (ψ n) (φ 1)‖) atTop (𝓝 1) := by
        apply tendsto_const_nhds.congr'
        rw [EventuallyEq, eventually_atTop]
        exact ⟨1, fun n hn ↦ (this n hn).symm⟩
      have aux2 := (continuous_norm.tendsto _).comp <| hg (φ 1)
      exact tendsto_nhds_unique aux1 aux2
    rw [this]
    apply g.unit_le_opNorm
    rw [hφ.norm_map_of_map_zero φz, norm_one]
  · rcases eq_or_ne t 0 with rfl | ht
    · rw [φz, _root_.map_zero]
    · have aux1 : Tendsto (fun n ↦ f (ψ n) (φ t)) atTop (𝓝 t) := by
        apply tendsto_const_nhds.congr'
        rw [EventuallyEq, eventually_atTop]
        use ⌈|t|⌉₊
        intro b hb
        have : t ∈ Icc (-(ψ b) : ℝ) (ψ b) := by
          rw [mem_Icc]
          exact abs_le.1 (Nat.ceil_le.1 (hb.trans (hψ.id_le b)))
        refine (hf _ ?_ _ this).symm
        apply le_trans _ (hψ.id_le b)
        apply le_trans _ hb
        rw [Nat.one_le_ceil_iff]
        positivity
      have aux2 := hg (φ t)
      exact tendsto_nhds_unique aux2 aux1

theorem norm_normalize {x : E} (hx : x ≠ 0) : ‖(1 / ‖x‖) • x‖ = 1 := by
  rw [norm_smul, norm_div, norm_one, norm_norm, one_div_mul_cancel (norm_ne_zero_iff.2 hx)]

theorem dense_seq {X : Type*} [TopologicalSpace X] [FrechetUrysohnSpace X]
    {s : Set X} (hs : Dense s) (x : X) :
    ∃ u : ℕ → X, (∀ n, u n ∈ s) ∧ Tendsto u atTop (𝓝 x) := by
  rw [← mem_closure_iff_seq_limit, dense_iff_closure_eq.1 hs]; trivial

theorem exists_inverse' [FiniteDimensional ℝ E] [Nontrivial E]
    (φ : E → F) (hφ : Isometry φ) (φz : φ 0 = 0)
    (hlol : Dense (X := F) (Submodule.span ℝ (range φ))) :
    ∃ (f : F →L[ℝ] E), ‖f‖ = 1 ∧ f ∘ φ = id := by
  have main (x : E) (nx : ‖x‖ = 1) : ∃ f : F →L[ℝ] ℝ, ‖f‖ = 1 ∧ ∀ t : ℝ, f (φ (t • x)) = t := by
    apply exists_inverse
    · apply Isometry.of_dist_eq
      intro x₁ x₂
      rw [hφ.dist_eq, dist_eq_norm, ← sub_smul, norm_smul, nx, mul_one, dist_eq_norm]
    · simpa using φz
  choose! f nf hf using main
  have aux2 : Dense {x : E | DifferentiableAt ℝ (‖·‖) x} := by
    let _ : MeasurableSpace E := borel E
    have _ : BorelSpace E := ⟨rfl⟩
    let w := FiniteDimensional.finBasis ℝ E
    exact dense_of_ae (lipschitzWith_one_norm.ae_differentiableAt (μ := w.addHaar))
  let s := {f : E →ₗ[ℝ] ℝ | ∃ x' : E, DifferentiableAt ℝ (‖·‖) x' ∧ f = fderiv ℝ (‖·‖) x'}
  have aux3 (z : E) (hz : z ≠ 0) : ∃ f ∈ s, f z ≠ 0 := by
    obtain ⟨u, hu, htu⟩ := dense_seq aux2 z
    have := (tendsto_differentiable hu htu).eventually_ne (norm_ne_zero_iff.2 hz)
    rcases eventually_atTop.1 this with ⟨N, hN⟩
    exact ⟨fderiv ℝ (‖·‖) (u N), ⟨u N, hu N, rfl⟩, hN N (le_refl N)⟩
  let b := BasisOfSpan (span_eq_top_of_ne_zero aux3)
  have hb i : ∃ y : E, ‖y‖ = 1 ∧ DifferentiableAt ℝ (‖·‖) y ∧ b i = fderiv ℝ (‖·‖) y := by
    obtain ⟨y, dy, hy⟩ : ∃ y : E, DifferentiableAt ℝ (‖·‖) y ∧ b i = fderiv ℝ (‖·‖) y :=
      basisOfSpan_subset (span_eq_top_of_ne_zero aux3) ⟨i, rfl⟩
    have yn : y ≠ 0 := by
      intro hyn
      rw [hyn, fderiv_zero_of_not_differentiableAt <| not_differentiableAt_norm_zero E] at hy
      exact b.ne_zero i hy
    refine ⟨(1 / ‖y‖) • y, norm_normalize yn,
      (differentiableAt_norm_smul (one_div_ne_zero (norm_ne_zero_iff.2 yn))).1 dy, ?_⟩
    rw [fderiv_norm_smul_pos (one_div_pos.2 <| norm_pos_iff.2 yn), hy]
  choose y ny dy hy using hb
  let c := (b.dualBasis).map (Module.evalEquiv ℝ E).symm
  have mdr i j : b i (c j) = if i = j then 1 else 0 := by
    calc
      (b i) (c j) = Module.evalEquiv ℝ E ((Module.evalEquiv ℝ E).symm (b.dualBasis j)) (b i) := rfl
      _ = b.dualBasis j (b i) := by rw [(Module.evalEquiv ℝ E).apply_symm_apply]
      _ = if i = j then 1 else 0 := b.dualBasis_apply_self j i
  let T : F →L[ℝ] E :=
    { toFun := fun z ↦ ∑ i, (f (y i) z) • (c i)
      map_add' := fun _ ↦ by simp [Finset.sum_add_distrib, add_smul]
      map_smul' := fun _ ↦ by simp [Finset.smul_sum, smul_smul]
      cont := continuous_finset_sum (@Finset.univ (Fin _) _) fun _ ↦ by fun_prop }
  use T
  have lipfφ {x : E} (nx : ‖x‖ = 1) : LipschitzWith 1 ((f x) ∘ φ) := by
    convert (f x).lipschitz.comp hφ.lipschitz
    rw [← norm_toNNReal, nf x nx, mul_one, toNNReal_one]
  have fφ_eq {x : E} (nx : ‖x‖ = 1) (hx : DifferentiableAt ℝ (‖·‖) x) :=
    unique1 nx hx ((f x) ∘ φ) (lipfφ nx) (hf x nx)
  have Tφ x : T (φ x) = x := by
    have aux2 i x : f (y i) (φ x) = b i x := by
      convert congrFun (fφ_eq (ny i) (dy i)) x using 1
      exact DFunLike.congr_fun (hy i) x
    simp only [ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk, aux2, T]
    let g : E →ₗ[ℝ] E :=
      { toFun := fun y ↦ ∑ i, (b i y) • (c i)
        map_add' := fun _ ↦ by simp [Finset.sum_add_distrib, add_smul]
        map_smul' := fun _ ↦ by simp [Finset.smul_sum, smul_smul] }
    have : g = LinearMap.id := c.ext fun i ↦ by simp [g, mdr]
    exact DFunLike.congr_fun this x
  constructor
  · apply le_antisymm
    · have prim {x : E} (nx : ‖x‖ = 1) (hx : DifferentiableAt ℝ (‖·‖) x) :
          f x = (fderiv ℝ (‖·‖) x).comp T := by
        apply ContinuousLinearMap.ext_on hlol
        rintro - ⟨y, rfl⟩
        simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, Tφ]
        exact congrFun (fφ_eq nx hx) y
      refine T.opNorm_le_bound (by norm_num) fun y ↦ ?_
      obtain ⟨u, hu, htu⟩ := dense_seq aux2 (T y)
      have := tendsto_differentiable hu htu
      have unez n : u n ≠ 0 := fun h ↦ not_differentiableAt_norm_zero E (h ▸ hu n)
      have obv n : 1 / ‖u n‖ > 0 := one_div_pos.2 <| norm_pos_iff.2 <| unez n
      simp_rw [← fun n ↦ fderiv_norm_smul_pos (x := u n) (obv n)] at this
      refine le_of_tendsto this <| eventually_of_forall fun n ↦ ?_
      have : fderiv ℝ (‖·‖) ((1 / ‖u n‖) • (u n)) (T y) = f ((1 / ‖u n‖) • (u n)) y :=
        DFunLike.congr_fun (prim (norm_normalize (unez n))
          ((differentiableAt_norm_smul (obv n).ne.symm).1 (hu n))).symm y
      rw [this]
      calc
        f ((1 / ‖u n‖) • (u n)) y ≤ ‖f ((1 / ‖u n‖) • (u n)) y‖ := norm_eq_abs _ ▸ le_abs_self _
        _ ≤ ‖f ((1 / ‖u n‖) • (u n))‖ * ‖y‖ := ContinuousLinearMap.le_opNorm _ y
        _ = 1 * ‖y‖ := by rw [nf _ (norm_normalize (unez n))]
    · rcases NormedSpace.exists_lt_norm ℝ E 0 with ⟨x, hx⟩
      apply le_of_mul_le_mul_right _ hx
      nth_rw 1 [← Tφ x]
      rw [← hφ.norm_map_of_map_zero φz x, one_mul]
      exact T.le_opNorm _
  · ext x
    exact Tφ x

theorem isup_fin :
    univ = ⋃ (F : Submodule ℝ E) (_ : FiniteDimensional ℝ F), (F : Set E) := by
  ext x
  simp only [mem_univ, mem_iUnion, SetLike.mem_coe, exists_prop, true_iff]
  refine ⟨span ℝ {x}, ?_, ?_⟩
  · exact Finite.span_singleton ℝ x
  apply subset_span
  exact mem_singleton _

theorem Dense.denseInducing_val {X : Type*} [TopologicalSpace X] {s : Set X} (hs : Dense s) :
    DenseInducing (@Subtype.val X s) := ⟨inducing_subtype_val, hs.denseRange_val⟩

theorem uniformInducing_val {X : Type*} [UniformSpace X] (s : Set X) :
    UniformInducing (@Subtype.val X s) := ⟨uniformity_setCoe⟩

theorem exists_inverse'' [CompleteSpace E] [Nontrivial E]
    (φ : E → F) (hφ : Isometry φ) (φz : φ 0 = 0)
    (hlol : Dense (X := F) (Submodule.span ℝ (range φ))) :
    ∃ (f : F →L[ℝ] E), ‖f‖ = 1 ∧ f ∘ φ = id := by
  let A : Submodule ℝ E → Submodule ℝ F := fun p ↦ span ℝ (φ '' p)
  have mA : Monotone A := fun p q hpq ↦ span_mono (image_mono hpq)
  let ψ : (p : Submodule ℝ E) → p → A p := fun p x ↦ ⟨φ x, subset_span ⟨x.1, x.2, rfl⟩⟩
  have hψ p : Isometry (ψ p) := Isometry.of_dist_eq fun x y ↦ hφ.dist_eq _ _
  have ψz p : ψ p 0 = 0 := by simp [ψ, φz]
  have fini (p : Submodule ℝ E) (hp : FiniteDimensional ℝ p) :
      ∃ T : A p →L[ℝ] p, (∀ y, ‖T y‖ ≤ 1 * ‖y‖) ∧ ∀ y : p, T (ψ p y) = y := by
    by_cases np : Nontrivial p
    · have : Dense (X := A p) (span ℝ (range (ψ p))) := by
        convert dense_univ
        ext x
        simp only [SetLike.mem_coe, mem_univ, iff_true]
        rcases mem_span_set'.1 x.2 with ⟨n, f, g, hx⟩
        rw [mem_span_set']
        have this i : ⟨g i, subset_span (g i).2⟩ ∈ range (ψ p) := by
          rcases (g i).2 with ⟨y, hy, h⟩
          use ⟨y, hy⟩
          rw [← Subtype.val_inj]
          simpa
        use n, f, fun i ↦ ⟨⟨g i, subset_span (g i).2⟩, this i⟩
        rw [← Subtype.val_inj, ← hx]
        simp
      rcases exists_inverse' (ψ p) (hψ p) (ψz p) this with ⟨T, nT, hT⟩
      exact ⟨T, fun y ↦ nT ▸ T.le_opNorm y, fun y ↦ congrFun hT y⟩
    · refine ⟨0, by simp, ?_⟩
      rw [not_nontrivial_iff_subsingleton] at np
      exact fun _ ↦ Subsingleton.allEq _ _
  choose! T nT hT using fini
  have eq {p q : Submodule ℝ E} (hp : FiniteDimensional ℝ p) (hq : FiniteDimensional ℝ q)
      (hpq : p ≤ q) :
      ∀ y : A p, (T p y).1 =
        (T q (Submodule.inclusion (mA hpq) y)).1 := by
    have : p.subtype ∘ₗ (T p) = q.subtype ∘ₗ (T q) ∘ₗ (Submodule.inclusion (mA hpq)) := by
      have : span ℝ (range (ψ p)) = ⊤ := by
        ext x
        simp only [Submodule.mem_top, iff_true]
        rcases mem_span_set'.1 x.2 with ⟨n, f, g, hx⟩
        rw [mem_span_set']
        have this i : ⟨g i, subset_span (g i).2⟩ ∈ range (ψ p) := by
          rcases (g i).2 with ⟨y, hy, h⟩
          use ⟨y, hy⟩
          rw [← Subtype.val_inj]
          simpa
        use n, f, fun i ↦ ⟨⟨g i, subset_span (g i).2⟩, this i⟩
        rw [← Subtype.val_inj, ← hx]
        simp
      apply LinearMap.ext_on_range this
      intro x
      simp only [LinearMap.coe_comp, coeSubtype, ContinuousLinearMap.coe_coe, Function.comp_apply]
      have : Submodule.inclusion (mA hpq) (ψ p x) = ψ q (Submodule.inclusion hpq x) := rfl
      rw [hT p hp, this, hT q hq]
      rfl
    exact fun y ↦ congrFun (congrArg DFunLike.coe this) y
  let Q : Set F := ⋃ (p : Submodule ℝ E) (_ : FiniteDimensional ℝ p), A p
  let g : span ℝ Q → E := fun y ↦
    let n := (mem_span_set'.1 y.2).choose
    let c : Fin n → ℝ := (mem_span_set'.1 y.2).choose_spec.choose
    let x : Fin n → Q := (mem_span_set'.1 y.2).choose_spec.choose_spec.choose
    let p := fun i ↦ (mem_iUnion₂.1 (x i).2).choose
    have hx := fun i ↦ (mem_iUnion₂.1 (x i).2).choose_spec.choose_spec
    ∑ i : Fin n, c i • (T (p i) ⟨(x i).1, hx i⟩)
  have Teg (p : Submodule ℝ E) (hp : FiniteDimensional ℝ p) (x : span ℝ Q)
      (hx : x.1 ∈ A p) : (T p ⟨x, hx⟩).1 = g x := by
    let nx := (mem_span_set'.1 x.2).choose
    let cx : Fin nx → ℝ := (mem_span_set'.1 x.2).choose_spec.choose
    let xx : Fin nx → Q := (mem_span_set'.1 x.2).choose_spec.choose_spec.choose
    have xe : ∑ i, cx i • (xx i).1 = x :=
      (mem_span_set'.1 x.2).choose_spec.choose_spec.choose_spec
    let px := fun i ↦ (mem_iUnion₂.1 (xx i).2).choose
    have hpx i : FiniteDimensional ℝ (px i) := (mem_iUnion₂.1 (xx i).2).choose_spec.choose
    have hxx : ∀ i, (xx i).1 ∈ A (px i) :=
      fun i ↦ (mem_iUnion₂.1 (xx i).2).choose_spec.choose_spec
    change (T p ⟨x, hx⟩).1 = ∑ i, cx i • (T (px i) ⟨(xx i).1, hxx i⟩).1
    have this i : px i ≤ p ⊔ ⨆ j, px j := by
      apply le_sup_of_le_right
      apply le_iSup _ i
    simp_rw [fun i ↦ eq (hpx i) _ (this i) ⟨(xx i), hxx i⟩]
    rw [eq hp inferInstance (le_sup_left (b := ⨆ j, px j)) ⟨x, hx⟩]
    simp_rw [← coe_smul, ← Submodule.coe_sum, ← _root_.map_smul, ← map_sum]
    congr
    rw [← Subtype.val_inj]
    simp_rw [Submodule.coe_sum, Submodule.coe_inclusion, coe_smul]
    rw [xe]
  have imp {n : ℕ} {p : Fin n → Submodule ℝ E} {x : Fin n → Q} (hx : ∀ i, (x i).1 ∈ A (p i)) i :
      (x i).1 ∈ A (⨆ i, p i) := by
    have : ⨆ i, A (p i) ≤ A (⨆ i, p i) := by
      simp only [A]
      rw [iSup_span, ← image_iUnion]
      apply span_mono
      apply image_mono
      simp only [iUnion_subset_iff, SetLike.coe_subset_coe]
      exact fun i ↦ le_iSup p i
    apply this
    apply le_iSup (A ∘ p) i
    exact hx i
  have imp (x : span ℝ Q) : ∃ (p : Submodule ℝ E), FiniteDimensional ℝ p ∧ x.1 ∈ A p := by
    let nx := (mem_span_set'.1 x.2).choose
    let cx : Fin nx → ℝ := (mem_span_set'.1 x.2).choose_spec.choose
    let xx : Fin nx → Q := (mem_span_set'.1 x.2).choose_spec.choose_spec.choose
    have xe : ∑ i, cx i • (xx i).1 = x :=
      (mem_span_set'.1 x.2).choose_spec.choose_spec.choose_spec
    let px := fun i ↦ (mem_iUnion₂.1 (xx i).2).choose
    have hpx i : FiniteDimensional ℝ (px i) := (mem_iUnion₂.1 (xx i).2).choose_spec.choose
    have hxx : ∀ i, (xx i).1 ∈ A (px i) :=
      fun i ↦ (mem_iUnion₂.1 (xx i).2).choose_spec.choose_spec
    use ⨆ i, px i, inferInstance
    rw [← xe]
    convert (∑ i, cx i • (⟨(xx i).1, imp hxx i⟩ : ( A (⨆ i, (px i)) : Submodule ℝ F))).2
    simp_rw [Submodule.coe_sum, coe_smul]
  have gadd x y : g (x + y) = g x + g y := by
    rcases imp x with ⟨p, hp, hx⟩
    rcases imp y with ⟨q, hq, hy⟩
    have : (A p) ⊔ (A q) ≤ A (p ⊔ q) := by
      apply sup_le
      · exact mA le_sup_left
      · exact mA le_sup_right
    have hx : x.1 ∈ A (p ⊔ q) := this <| le_sup_left (b := A q) hx
    have hy : y.1 ∈ A (p ⊔ q) := this <| le_sup_right (a := A p) hy
    have hxy : x.1 + y.1 ∈ A (p ⊔ q) := by
      exact ((⟨x.1, hx⟩ : A (p ⊔ q)) + ⟨y.1, hy⟩).2
    rw [← Teg (p ⊔ q) inferInstance x hx, ← Teg (p ⊔ q) inferInstance y hy,
      ← Teg (p ⊔ q) inferInstance (x + y) hxy, ← coe_add, ← map_add]
    rfl
  have gsmul (c : ℝ) x : g (c • x) = c • (g x) := by
    rcases imp x with ⟨p, hp, hx⟩
    have hcx : c • x.1 ∈ A p := (c • ⟨x.1, hx⟩ : A p).2
    rw [← Teg p hp x hx, ← Teg p hp (c • x) hcx, ← coe_smul, ← _root_.map_smul]
    rfl
  have ng x : ‖g x‖ ≤ 1 * ‖x‖ := by
    rcases imp x with ⟨p, hp, hx⟩
    rw [← Teg p hp x hx]
    exact nT p hp _

  have dQ : Dense (span ℝ Q : Set F) := by
    simp only [Q, A]
    rw [span_iUnion₂]
    simp_rw [span_span]
    rw [← span_iUnion₂, ← image_iUnion₂, ← isup_fin, image_univ]
    exact hlol
  have dQ := dQ.denseRange_val
  have ui := uniformInducing_val (span ℝ Q : Set F)
  have cg : UniformContinuous g := by
    apply LipschitzWith.uniformContinuous (K := 1)
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, sub_eq_add_neg, ← neg_one_smul ℝ, ← gsmul, ← gadd, dist_eq_norm,
      neg_one_smul ℝ, ← sub_eq_add_neg]
    exact ng _
  let h := (ui.denseInducing dQ).extend g
  have ch : Continuous h :=
    (ui.denseInducing dQ).continuous_extend (uniformly_extend_exists ui dQ cg)
  have merde : ∀ x : F, ∃ u : ℕ → span ℝ Q, Tendsto (Subtype.val ∘ u) atTop (𝓝 x) := by
    intro x
    rcases dense_seq dQ x with ⟨u, hu1, hu2⟩
    let v : ℕ → span ℝ Q := fun n ↦ (hu1 n).choose
    have : u = Subtype.val ∘ v := by
      ext n
      simp only [SetLike.coe_sort_coe, Function.comp_apply, v]
      exact (hu1 n).choose_spec.symm
    use v
    rwa [← this]
  have hadd x y : h (x + y) = h x + h y := by
    rcases merde x with ⟨ux, hux⟩
    rcases merde y with ⟨uy, huy⟩
    have ptn1 : Tendsto (fun n ↦ g (ux n) + g (uy n)) atTop (𝓝 (h x + h y)) := by
      apply Tendsto.add
      · apply ((ch.tendsto x).comp hux).congr
        exact fun n ↦ (ui.denseInducing dQ).extend_eq cg.continuous (ux n)
      · apply ((ch.tendsto y).comp huy).congr
        exact fun n ↦ (ui.denseInducing dQ).extend_eq cg.continuous (uy n)
    have ptn2 : Tendsto (fun n ↦ g (ux n) + g (uy n)) atTop (𝓝 (h (x + y))) := by
      simp_rw [← gadd]
      apply ((ch.tendsto _).comp (hux.add huy)).congr
      exact fun n ↦ (ui.denseInducing dQ).extend_eq cg.continuous (ux n + uy n)
    exact tendsto_nhds_unique ptn2 ptn1
  have hsmul (c : ℝ) x : h (c • x) = c • (h x) := by
    rcases merde x with ⟨ux, hux⟩
    have ptn1 : Tendsto (fun n ↦ c • (g (ux n))) atTop (𝓝 (h (c • x))) := by
      simp_rw [← gsmul]
      apply ((ch.tendsto _).comp (hux.const_smul c)).congr
      exact fun n ↦ (ui.denseInducing dQ).extend_eq cg.continuous (c • (ux n))
    have ptn2 : Tendsto (fun n ↦ c • (g (ux n))) atTop (𝓝 (c • (h x))) := by
      apply Tendsto.const_smul
      apply ((ch.tendsto x).comp hux).congr
      exact fun n ↦ (ui.denseInducing dQ).extend_eq cg.continuous (ux n)
    exact tendsto_nhds_unique ptn1 ptn2
  have hnorm x : ‖h x‖ ≤ 1 * ‖x‖ := by
    rcases merde x with ⟨ux, hux⟩
    have ptn1 : Tendsto (fun n ↦ ‖g (ux n)‖) atTop (𝓝 (‖h x‖)) := by
      apply ((continuous_norm.tendsto _).comp <| (ch.tendsto x).comp hux).congr
      intro n
      simp only [Function.comp_apply]
      congr
      exact (ui.denseInducing dQ).extend_eq cg.continuous (ux n)
    apply le_of_tendsto_of_tendsto' ptn1 (((continuous_norm.tendsto _).comp hux).const_mul 1)
    exact fun _ ↦ ng _
  let h' : F →ₗ[ℝ] E :=
    { toFun := h
      map_add' := hadd
      map_smul' := hsmul }
  let H := h'.mkContinuous 1 hnorm
  use H
  have this x : H (φ x) = x := by
    have : x ∈ ⋃ (F : Submodule ℝ E) (_ : FiniteDimensional ℝ F), (F : Set E) := by
      rw [← isup_fin]; trivial
    rcases mem_iUnion₂.1 this with ⟨p, hp, hx⟩
    have ptn : φ x ∈ A p := by
      exact subset_span ⟨x, hx, rfl⟩
    have ptn' : φ x ∈ span ℝ Q := subset_span <| mem_iUnion₂.2 ⟨p, hp, ptn⟩
    have ob : (T p ⟨φ x, ptn⟩).1 = g ⟨φ x, ptn'⟩ := by
      exact Teg p hp ⟨φ x, ptn'⟩ ptn
    have merde : H (φ x) = g ⟨φ x, ptn'⟩ := by
      change h (⟨φ x, ptn'⟩ : span ℝ Q) = g ⟨φ x, ptn'⟩
      exact (ui.denseInducing dQ).extend_eq cg.continuous _
    rw [merde, ← ob]
    exact Subtype.val_inj.2 <| hT p hp ⟨x, hx⟩
  constructor
  · apply le_antisymm
    · exact H.opNorm_le_bound (by norm_num) hnorm
    · rcases NormedSpace.exists_lt_norm ℝ E 0 with ⟨x, hx⟩
      rw [← _root_.mul_le_mul_right hx, one_mul]
      nth_rw 1 [← this x]
      rw [← hφ.norm_map_of_map_zero φz x]
      exact H.le_opNorm _
  · ext x
    exact this x
