import Mathlib.Analysis.GodefroyLipschitz.Annexe
import Mathlib.MeasureTheory.Measure.OpenPos

open Real NNReal Set Filter Topology FiniteDimensional Metric Module Submodule
open WeakDual

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem unique1 [FiniteDimensional ℝ E] {x : E} (nx : ‖x‖ = 1) (hx : DifferentiableAt ℝ (‖·‖) x)
    {φ : E → ℝ} (hφ : LipschitzWith 1 φ) (φ_eq : ∀ t : ℝ, φ (t • x) = t) :
    φ = fderiv ℝ (‖·‖) x := by
  ext y
  have this t (ht : t ≠ 0) : 1 = |t * (φ y) - t * (φ (((φ y) + 1 / t) • x))| := by
    simp [φ_eq, mul_comm, mul_add, ht]
  have this (t : ℝ) : 1 ≤ ‖x - t • (y - (φ y) • x)‖ := by
    rcases eq_or_ne t 0 with rfl | ht
    · rw [zero_smul, sub_zero, nx]
    · calc
        1 ≤ |t| * ‖y - (φ y + 1 / t) • x‖ := by
          nth_rw 1 [this t ht, ← mul_sub, abs_mul, ← norm_eq_abs (_ - _)]
          rw [_root_.mul_le_mul_left (abs_pos.2 ht)]
          simpa using hφ.norm_sub_le _ _
        _ = ‖x - t • (y - (φ y) • x)‖ := by
          rw [← norm_eq_abs, ← norm_smul, ← norm_neg, smul_sub, smul_smul]
          congr
          field_simp
          module
  have min : IsLocalMin (fun t : ℝ ↦ ‖x - t • (y - (φ y) • x)‖) 0 := by
    simp [IsLocalMin, IsMinFilter, nx, this]
  have : deriv (fun t : ℝ ↦ ‖x - t • (y - (φ y) • x)‖) 0 = - fderiv ℝ (‖·‖) x (y - (φ y) • x) := by
    conv_lhs => enter [1]; change ((‖·‖) ∘ (fun t : ℝ ↦ x - t • (y - (φ y) • x)))
    rw [fderiv.comp_deriv]
    · rw [deriv_const_sub, deriv_smul_const] <;> simp
    · simpa
    · simp
  rw [min.deriv_eq_zero, map_sub, _root_.map_smul, fderiv_norm_self hx, nx] at this
  simp only [smul_eq_mul, mul_one, neg_sub] at this
  exact sub_eq_zero.1 this.symm

theorem Filter.Tendsto.fderiv_norm_tendsto_norm {ι : Type*} {ℱ : Filter ι}
    {x : ι → E} (hd : ∀ i, DifferentiableAt ℝ (‖·‖) (x i))
    {z : E} (ht : Tendsto x ℱ (𝓝 z)) :
    Tendsto (fun n ↦ fderiv ℝ (‖·‖) (x n) z) ℱ (𝓝 ‖z‖) := by
  obtain hE | _ := subsingleton_or_nontrivial E
  · rw [subsingleton_iff.1 hE z 0]
    simpa using tendsto_const_nhds
  · have aux1 : Tendsto (fun n ↦ fderiv ℝ (‖·‖) (x n) (x n)) ℱ (𝓝 ‖z‖) := by
      simp_rw [fun n ↦ fderiv_norm_self (hd n)]
      exact (continuous_norm.tendsto z).comp ht
    apply tendsto_of_tendsto_of_dist aux1
    simp_rw [dist_eq_norm, ← map_sub]
    apply squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ContinuousLinearMap.le_opNorm _ _)
    simp_rw [fun n ↦ norm_fderiv_norm (hd n), one_mul]
    exact tendsto_iff_norm_sub_tendsto_zero.1 ht

private lemma eq_of_abs_le_sub_eq {a b c : ℝ} (ha : |a| ≤ c) (hb : |b| ≤ c) (h : a - b = 2 * c) :
    a = c ∧ b = -c := by
  by_contra this
  obtain ha' | hb' := Classical.not_and_iff_or_not_not.1 this
  · linarith [(abs_le.1 hb).1, lt_of_le_of_ne (abs_le.1 ha).2 ha']
  · linarith [(abs_le.1 ha).2, lt_of_le_of_ne (abs_le.1 hb).1 (ne_eq .. ▸ hb').symm]

variable {E F : Type*} [NormedAddGroup E] [NormedAddGroup F] in
theorem Isometry.map_norm_sub {φ : E → F} (hφ : Isometry φ) (x y : E) :
    ‖φ x - φ y‖ = ‖x - y‖ := by
  rw [← dist_eq_norm, hφ.dist_eq, dist_eq_norm]

open ContinuousLinearMap in
private lemma jsp {f : F →L[ℝ] ℝ} {a b : ℝ} {φ : ℝ → F} (hφ : Isometry φ) (φz : φ 0 = 0)
    (nf : ‖f‖ = 1) (hfa : f (φ a) = a) (hb : b ∈ Icc 0 a) : f (φ b) = b := by
  apply le_antisymm
  · refine le_trans (le_norm_self _) ?_
    convert f.le_opNorm _ using 1
    rw [nf, hφ.norm_map_of_map_zero φz, one_mul, norm_of_nonneg hb.1]
  · nth_rw 1 [← neg_le_neg_iff, ← add_le_add_iff_left a, ← hfa]
    simp_rw [← sub_eq_add_neg, ← map_sub]
    refine le_trans (le_norm_self _) ?_
    convert f.le_opNorm _ using 1
    rw [hφ.map_norm_sub, nf, one_mul, norm_of_nonneg (by linarith [hb.2])]

open ContinuousLinearMap in
private lemma jsp2 {f : F →L[ℝ] ℝ} {a b : ℝ} {φ : ℝ → F} (hφ : Isometry φ) (φz : φ 0 = 0)
    (nf : ‖f‖ = 1) (hfa : f (φ a) = a) (hb : b ∈ Icc a 0) : f (φ b) = b := by
  apply le_antisymm
  · rw [← sub_add_cancel (f (φ b)) (f (φ a)), ← map_sub, ← le_sub_iff_add_le, hfa]
    refine le_trans (le_norm_self _) ?_
    convert f.le_opNorm _ using 1
    rw [hφ.map_norm_sub, nf, one_mul, norm_of_nonneg (by linarith [hb.1])]
  · rw [← neg_le_neg_iff]
    refine le_trans (le_norm_self _) (norm_neg (f _) ▸ ?_)
    convert f.le_opNorm _ using 1
    rw [nf, hφ.norm_map_of_map_zero φz, one_mul, norm_of_nonpos hb.2]

open ContinuousLinearMap in
theorem exists_inverse {φ : ℝ → F} (hφ : Isometry φ) (φz : φ 0 = 0) :
    ∃ (f : F →L[ℝ] ℝ), ‖f‖ = 1 ∧ ∀ t : ℝ, f (φ t) = t := by
  have _ : Nontrivial F := by
    refine nontrivial_iff.2 ⟨φ 1, 0, ?_⟩
    rw [← norm_ne_zero_iff, hφ.norm_map_of_map_zero φz, norm_one]
    norm_num
  have (k : ℕ) :
      ∃ f : WeakDual ℝ F, ‖toNormedDual f‖ = 1 ∧ ∀ s : ℝ, s ∈ Icc (-k : ℝ) k → f (φ s) = s := by
    obtain ⟨f, nf, hf⟩ : ∃ f : F →L[ℝ] ℝ, ‖f‖ = 1 ∧ f ((φ k) - (φ (-k))) = 2 * k := by
      have nk : ‖(φ k) - (φ (-k))‖ = 2 * k := by
        rw [hφ.map_norm_sub, norm_eq_abs, sub_neg_eq_add, two_mul, abs_eq_self.2 (by positivity)]
      obtain ⟨f, nf, hfk⟩ := exists_dual_vector'  ℝ ((φ k) - (φ (-k)))
      simp only [RCLike.ofReal_real_eq_id, id_eq] at hfk
      exact ⟨f, nf, by rw [hfk, nk]⟩
    refine ⟨f, nf, fun s ⟨hs1, hs2⟩ ↦ ?_⟩
    have ⟨h1, h2⟩ : f (φ k) = k ∧ f (φ (-k)) = -k := by
      refine eq_of_abs_le_sub_eq ?_ ?_ (by rw [← map_sub, hf])
      · rw [← norm_eq_abs]
        convert f.le_opNorm (φ k)
        rw [nf, one_mul, hφ.norm_map_of_map_zero φz, norm_of_nonneg (by positivity)]
      · rw [← norm_eq_abs]
        convert f.le_opNorm (φ (-k))
        rw [nf, one_mul, hφ.norm_map_of_map_zero φz, norm_of_nonpos (by simp), neg_neg]
    obtain hs | hs := le_total s 0
    · exact jsp2 hφ φz nf h2 ⟨hs1, hs⟩
    · exact jsp hφ φz nf h1 ⟨hs, hs2⟩
  choose! f nf hf using this
  obtain ⟨g, hg⟩ : ∃ g : WeakDual ℝ F, MapClusterPt g atTop f := by
    have aux : atTop.map f ≤ 𝓟 (toNormedDual ⁻¹' closedBall 0 1) := by
      rw [le_principal_iff, ← eventually_mem_set, eventually_map]
      exact Eventually.of_forall fun n ↦ by simp [-coe_toNormedDual, nf]
    obtain ⟨g, -, hg⟩ := (WeakDual.isCompact_closedBall _ _ _).exists_clusterPt aux
    exact ⟨g, hg⟩
  have (t : ℝ) : g (φ t) = t := by
    have := hg.tendsto_comp ((eval_continuous (φ t)).tendsto g)
    obtain ⟨ψ, hψ, h⟩ := TopologicalSpace.FirstCountableTopology.tendsto_subseq this
    have : Tendsto (fun n ↦ f (ψ n) (φ t)) atTop (𝓝 t) := by
      refine tendsto_atTop_of_eventually_const (i₀ := Nat.ceil |t|) fun i hi ↦ hf _ _ ?_
      replace hi : Nat.ceil |t| ≤ ψ i := hi.trans hψ.le_apply
      rw [mem_Icc]
      rwa [Nat.ceil_le, abs_le] at hi
    exact tendsto_nhds_unique h this
  refine ⟨toNormedDual g, ?_, this⟩
  apply le_antisymm
  · refine opNorm_le_of_unit_norm (by norm_num) fun x hx ↦ le_of_forall_lt
      fun c (hc : c < |g x|) ↦ ?_
    wlog hgx : 0 ≤ g x generalizing x
    · exact this (-x) (by rwa [norm_neg]) (by rwa [map_neg, abs_neg]) (by rw [map_neg]; linarith)
    rw [abs_of_nonneg hgx] at hc
    rw [mapClusterPt_iff] at hg
    let s := (fun (f : WeakDual ℝ F) ↦ f x) ⁻¹' (Ioi c)
    specialize hg s ((isOpen_Ioi.preimage (eval_continuous x)).mem_nhds hc)
    rw [frequently_atTop] at hg
    obtain ⟨b, -, hfb⟩ := hg 0
    obtain hc | hc := lt_or_le c 0
    · linarith
    · simp_rw [s, mem_preimage, mem_Ioi] at hfb
      have : f b x ≤ 1 := by
        rw [← norm_of_nonneg (r := f b x) (by linarith), ← nf b, ← mul_one ‖toNormedDual _‖, ← hx]
        exact le_opNorm _ _
      linarith
  · apply le_opNorm_of' (x := φ 1)
    · rw [hφ.norm_map_of_map_zero φz, norm_one]
    · rw [toNormedDual_apply, this, norm_one]

theorem norm_normalize {x : E} (hx : x ≠ 0) : ‖(1 / ‖x‖) • x‖ = 1 := by
  rw [norm_smul, norm_div, norm_one, norm_norm, one_div_mul_cancel (norm_ne_zero_iff.2 hx)]

theorem dense_seq {X : Type*} [TopologicalSpace X] [FrechetUrysohnSpace X]
    {s : Set X} (hs : Dense s) (x : X) :
    ∃ u : ℕ → X, (∀ n, u n ∈ s) ∧ Tendsto u atTop (𝓝 x) := by
  rw [← mem_closure_iff_seq_limit, dense_iff_closure_eq.1 hs]; trivial

theorem ne_zero_of_differentiableAt_norm [Nontrivial E]
    {x : E} (h : DifferentiableAt ℝ (‖·‖) x) : x ≠ 0 :=
  fun hx ↦ (not_differentiableAt_norm_zero E (hx ▸ h)).elim

theorem exists_inverse' [FiniteDimensional ℝ E] [Nontrivial E]
    {φ : E → F} (hφ : Isometry φ) (φz : φ 0 = 0)
    (hdφ : Dense (span ℝ (range φ) : Set F)) :
    ∃ (f : F →L[ℝ] E), ‖f‖ = 1 ∧ f ∘ φ = id := by
  have main (x : E) (nx : ‖x‖ = 1) : ∃ f : F →L[ℝ] ℝ, ‖f‖ = 1 ∧ ∀ t : ℝ, f (φ (t • x)) = t := by
    refine exists_inverse (Isometry.of_dist_eq fun x₁ x₂ ↦ ?_) (by simpa)
    rw [hφ.dist_eq, dist_eq_norm, ← sub_smul, norm_smul, nx, mul_one, dist_eq_norm]
  choose! f nf hf using main
  have dense_diff : Dense {x : E | DifferentiableAt ℝ (‖·‖) x} :=
    dense_differentiableAt_norm
  let s : Set (E →ₗ[ℝ] ℝ) := {fderiv ℝ (‖·‖) x' | (x' : E) (_ : DifferentiableAt ℝ (‖·‖) x')}
  have aux3 (z : E) (hz : z ≠ 0) : ∃ f ∈ s, f z ≠ 0 := by
    obtain ⟨u, hu, htu⟩ := dense_seq dense_diff z
    have := (htu.fderiv_norm_tendsto_norm hu).eventually_ne (norm_ne_zero_iff.2 hz)
    rcases eventually_atTop.1 this with ⟨N, hN⟩
    exact ⟨fderiv ℝ (‖·‖) (u N), ⟨u N, hu N, rfl⟩, hN N le_rfl⟩
  let b := (Basis.ofSpan (span_eq_top_of_ne_zero (s := s) aux3))
  have hb i : ∃ y : E, ‖y‖ = 1 ∧ DifferentiableAt ℝ (‖·‖) y ∧ b i = fderiv ℝ (‖·‖) y := by
    obtain ⟨y, dy, hy⟩ := Basis.ofSpan_subset (span_eq_top_of_ne_zero aux3) ⟨i, rfl⟩
    have yn : y ≠ 0 := ne_zero_of_differentiableAt_norm dy
    refine ⟨(1 / ‖y‖) • y, norm_normalize yn,
      (differentiableAt_norm_smul (one_div_ne_zero (norm_ne_zero_iff.2 yn))).1 dy, ?_⟩
    rw [fderiv_norm_smul_pos (one_div_pos.2 <| norm_pos_iff.2 yn), hy]
  choose y ny dy hy using hb
  classical
  let c := (b.dualBasis).map (evalEquiv ℝ E).symm
  have b_map_c i j : b i (c j) = if i = j then 1 else 0 := by
    simp only [Basis.map_apply, apply_evalEquiv_symm_apply, Basis.dualBasis_apply_self, b, c]
  let T : F →L[ℝ] E :=
    { toFun := fun z ↦ ∑ i, (f (y i) z) • (c i)
      map_add' := fun _ ↦ by simp [Finset.sum_add_distrib, add_smul]
      map_smul' := fun _ ↦ by simp [Finset.smul_sum, smul_smul]
      cont := continuous_finset_sum (@Finset.univ _ _) fun _ ↦ by fun_prop }
  use T
  have lipfφ {x : E} (nx : ‖x‖ = 1) : LipschitzWith 1 ((f x) ∘ φ) := by
    convert (f x).lipschitz.comp hφ.lipschitz
    rw [← norm_toNNReal, nf x nx, mul_one, toNNReal_one]
  have fφ_eq {x : E} (nx : ‖x‖ = 1) (hx : DifferentiableAt ℝ (‖·‖) x) :=
    unique1 nx hx (lipfφ nx) (hf x nx)
  have Tφ x : T (φ x) = x := by
    have aux2 i x : f (y i) (φ x) = b i x := by
      convert congrFun (fφ_eq (ny i) (dy i)) x using 1
      exact DFunLike.congr_fun (hy i) x
    simp only [ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk, aux2, T]
    let g : E →ₗ[ℝ] E :=
      { toFun := fun y ↦ ∑ i, (b i y) • (c i)
        map_add' := fun _ ↦ by simp [Finset.sum_add_distrib, add_smul]
        map_smul' := fun _ ↦ by simp [Finset.smul_sum, smul_smul] }
    have : g = LinearMap.id := c.ext fun i ↦ by simp [g, b_map_c]
    exact DFunLike.congr_fun this x
  constructor
  · apply le_antisymm
    · have prim {x : E} (nx : ‖x‖ = 1) (hx : DifferentiableAt ℝ (‖·‖) x) :
          f x = (fderiv ℝ (‖·‖) x).comp T := by
        apply ContinuousLinearMap.ext_on hdφ
        rintro - ⟨y, rfl⟩
        simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, Tφ]
        exact congrFun (fφ_eq nx hx) y
      refine T.opNorm_le_bound (by norm_num) fun y ↦ ?_
      obtain ⟨u, hu, htu⟩ := dense_seq dense_diff (T y)
      have := htu.fderiv_norm_tendsto_norm hu
      have unez n : u n ≠ 0 := fun h ↦ not_differentiableAt_norm_zero E (h ▸ hu n)
      have obv n : 1 / ‖u n‖ > 0 := one_div_pos.2 <| norm_pos_iff.2 <| unez n
      simp_rw [← fun n ↦ fderiv_norm_smul_pos (x := u n) (obv n)] at this
      refine le_of_tendsto' this fun n ↦ ?_
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
  exact ⟨span ℝ {x}, Finite.span_singleton ℝ x, subset_span <| mem_singleton _⟩

theorem Dense.isDenseInducing_val {X : Type*} [TopologicalSpace X] {s : Set X} (hs : Dense s) :
    IsDenseInducing (@Subtype.val X s) := ⟨inducing_subtype_val, hs.denseRange_val⟩

theorem uniformInducing_val {X : Type*} [UniformSpace X] (s : Set X) :
    IsUniformInducing (@Subtype.val X s) := ⟨uniformity_setCoe⟩

theorem exists_inverse'' [CompleteSpace E] [Nontrivial E]
    (φ : E → F) (hφ : Isometry φ) (φz : φ 0 = 0)
    (hdφ : Dense (Submodule.span ℝ (range φ) : Set F)) :
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
        simp [Submodule.coe_sum]
      rcases exists_inverse' (hψ p) (ψz p) this with ⟨T, nT, hT⟩
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
        simp [Submodule.coe_sum]
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
    exact hdφ
  have dQ := dQ.denseRange_val
  have ui := uniformInducing_val (span ℝ Q : Set F)
  have cg : UniformContinuous g := by
    apply LipschitzWith.uniformContinuous (K := 1)
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, sub_eq_add_neg, ← neg_one_smul ℝ, ← gsmul, ← gadd, dist_eq_norm,
      neg_one_smul ℝ, ← sub_eq_add_neg]
    exact ng _
  let h := (ui.isDenseInducing dQ).extend g
  have ch : Continuous h :=
    (ui.isDenseInducing dQ).continuous_extend (uniformly_extend_exists ui dQ cg)
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
        exact fun n ↦ (ui.isDenseInducing dQ).extend_eq cg.continuous (ux n)
      · apply ((ch.tendsto y).comp huy).congr
        exact fun n ↦ (ui.isDenseInducing dQ).extend_eq cg.continuous (uy n)
    have ptn2 : Tendsto (fun n ↦ g (ux n) + g (uy n)) atTop (𝓝 (h (x + y))) := by
      simp_rw [← gadd]
      apply ((ch.tendsto _).comp (hux.add huy)).congr
      exact fun n ↦ (ui.isDenseInducing dQ).extend_eq cg.continuous (ux n + uy n)
    exact tendsto_nhds_unique ptn2 ptn1
  have hsmul (c : ℝ) x : h (c • x) = c • (h x) := by
    rcases merde x with ⟨ux, hux⟩
    have ptn1 : Tendsto (fun n ↦ c • (g (ux n))) atTop (𝓝 (h (c • x))) := by
      simp_rw [← gsmul]
      apply ((ch.tendsto _).comp (hux.const_smul c)).congr
      exact fun n ↦ (ui.isDenseInducing dQ).extend_eq cg.continuous (c • (ux n))
    have ptn2 : Tendsto (fun n ↦ c • (g (ux n))) atTop (𝓝 (c • (h x))) := by
      apply Tendsto.const_smul
      apply ((ch.tendsto x).comp hux).congr
      exact fun n ↦ (ui.isDenseInducing dQ).extend_eq cg.continuous (ux n)
    exact tendsto_nhds_unique ptn1 ptn2
  have hnorm x : ‖h x‖ ≤ 1 * ‖x‖ := by
    rcases merde x with ⟨ux, hux⟩
    have ptn1 : Tendsto (fun n ↦ ‖g (ux n)‖) atTop (𝓝 (‖h x‖)) := by
      apply ((continuous_norm.tendsto _).comp <| (ch.tendsto x).comp hux).congr
      intro n
      simp only [Function.comp_apply]
      congr
      exact (ui.isDenseInducing dQ).extend_eq cg.continuous (ux n)
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
      exact (ui.isDenseInducing dQ).extend_eq cg.continuous _
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

-- theorem test {α β : Type*} [TopologicalSpace α] [ConditionallyCompleteLinearOrder β]
--     {f : α → β} {ℱ : Filter α} (hf : LowerSemicontinuous f) {b : β} {a : α}
--     (hℱ : @MapClusterPt _ (Preorder.topology β) _ b (𝓝 a) f) :
--     b ≤ limsup f (𝓝 a) := by
--   let _ := Preorder.topology β
--   refine (le_limsup_iff).2 ?_
