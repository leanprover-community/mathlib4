import Mathlib.KolmogorovExtension4.meilleure_composition
import Mathlib.KolmogorovExtension4.Projective
import Mathlib.Probability.Kernel.MeasureCompProd
import Mathlib.KolmogorovExtension4.DependsOn
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.KolmogorovExtension4.KolmogorovExtension
import Mathlib.Data.PNat.Interval
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Constructions.Prod.Integral
import Mathlib.Probability.Process.Filtration

open MeasureTheory ProbabilityTheory Finset ENNReal Filter Topology Function MeasurableSpace

variable {X : ℕ → Type*} [Nonempty (X 0)] [∀ n, MeasurableSpace (X n)]
variable (κ : (k : ℕ) → kernel ((i : Iic k) → X i) (X (k + 1)))
variable [∀ k, IsMarkovKernel (κ k)]

/-- To check that a measure `ν` is the projective limit of a projective family of measures indexed
by `Finset ℕ`, it is enough to check on intervals of the form `Iic n`, where `n` is larger than
a given integer. -/
theorem isProjectiveLimit_nat_iff' (μ : (I : Finset ℕ) → Measure ((i : I) → X i))
    (hμ : IsProjectiveMeasureFamily μ) (ν : Measure ((n : ℕ) → X n)) (a : ℕ) :
    IsProjectiveLimit ν μ ↔ ∀ n ≥ a, ν.map (proj n) = μ (Iic n) := by
  refine ⟨fun h n _ ↦ h (Iic n), fun h I ↦ ?_⟩
  conv_lhs =>
    enter [1]
    change (projection (I.sub_Iic.trans (Iic_subset_Iic.2 (le_max_left (I.sup id) a)))) ∘
       (proj (max (I.sup id) a))
  rw [← Measure.map_map (measurable_projection _) (meas_proj _),
    h (max (I.sup id) a) (le_max_right _ _), hμ (Iic (max (I.sup id) a)) I]
  exact I.sub_Iic.trans (Iic_subset_Iic.2 (le_max_left (I.sup id) a))

/-- To check that a measure `ν` is the projective limit of a projective family of measures indexed
by `Finset ℕ`, it is enough to check on intervals of the form `Iic n`. -/
theorem isProjectiveLimit_nat_iff (μ : (I : Finset ℕ) → Measure ((i : I) → X i))
    (hμ : IsProjectiveMeasureFamily μ) (ν : Measure ((n : ℕ) → X n)) :
    IsProjectiveLimit ν μ ↔ ∀ n, ν.map (proj n) = μ (Iic n) := by
  rw [isProjectiveLimit_nat_iff' _ hμ _ 0]
  simp

/-- Given a family of measures `μ : (n : ℕ) → Measure ((i : Iic n) → X i)`, we can define a family
of measures indexed by `Finset ℕ` by projecting the measures. -/
noncomputable def induced_family (μ : (n : ℕ) → Measure ((i : Iic n) → X i)) :
    (S : Finset ℕ) → Measure ((k : S) → X k) :=
  fun S ↦ (μ (S.sup id)).map
    (fun x (i : S) ↦ x ⟨i.1, mem_Iic.2 (le_sup (f := id) i.2)⟩)

private lemma Iic_pi_eq {a b : ℕ} (h : a = b) :
    ((i : Iic a) → X i) = ((i : Iic b) → X i) := by cases h; rfl

private lemma measure_cast {a b : ℕ} (h : a = b) (μ : (n : ℕ) → Measure ((i : Iic n) → X i)) :
    (μ a).map (cast (Iic_pi_eq h)) = μ b := by
  subst h
  exact Measure.map_id

private lemma cast_pi {s t : Set ℕ} (h : s = t) (h' : ((i : s) → X i) = ((i : t) → X i))
    (x : (i : s) → X i) (i : t) :
    cast h' x i = x ⟨i.1, h.symm ▸ i.2⟩ := by
  subst h
  rfl

/-- Given a family of measures `μ : (n : ℕ) → Measure ((i : Iic n) → X i)`, the induced family
equals `μ` over the intervals `Iic n`. -/
theorem induced_family_Iic (μ : (n : ℕ) → Measure ((i : Iic n) → X i)) (n : ℕ) :
    induced_family μ (Iic n) = μ n := by
  rw [induced_family, ← measure_cast (sup_Iic n) μ]
  congr with x i
  rw [cast_pi _ (Iic_pi_eq (sup_Iic n)) x i]
  rw [sup_Iic n]

/-- Given a family of measures `μ : (n : ℕ) → Measure ((i : Iic n) → X i)`, the induced family
will be projective only if `μ` is projective, in the sense that if `a ≤ b`, then projecting
`μ b` gives `μ a`. -/
theorem isProjectiveMeasureFamily_induced_family (μ : (n : ℕ) → Measure ((i : Iic n) → X i))
    (h : ∀ a b : ℕ, ∀ hab : a ≤ b, (μ b).map (projection (Iic_subset_Iic.2 hab)) = μ a) :
    IsProjectiveMeasureFamily (induced_family μ) := by
  intro I J hJI
  have sls : J.sup id ≤ I.sup id := sup_mono hJI
  simp only [induced_family]
  rw [Measure.map_map, projection_comp_projection hJI I.sub_Iic,
    ← projection_comp_projection J.sub_Iic (Iic_subset_Iic.2 sls), ← Measure.map_map,
    h (J.sup id) (I.sup id) sls] <;> exact measurable_projection _
  exact measurable_projection hJI
  exact measurable_projection I.sub_Iic

theorem partialKernel_proj_apply {n : ℕ} (x : (i : Iic n) → X i) (a b : ℕ) (hab : a ≤ b) :
    (partialKernel κ n b x).map (projection (Iic_subset_Iic.2 hab)) = partialKernel κ n a x := by
  rw [← partialKernel_proj _ _ hab, kernel.map_apply]

/-- Given a family of kernels `κ : (n : ℕ) → kernel ((i : Iic n) → X i) (X (n + 1))`, and the
trajectory up to time `n` we can construct an additive content over cylinders. It corresponds
to composing the kernels by starting at time `n + 1`. -/
noncomputable def ionescuContent {n : ℕ} (x : (i : Iic n) → X i) : AddContent (cylinders X) :=
  kolContent (isProjectiveMeasureFamily_induced_family _ (partialKernel_proj_apply κ x))

private lemma heq_measurableSpace_Iic_pi {a b : ℕ} (h : a = b) :
    HEq (inferInstance : MeasurableSpace ((i : Iic a) → X i))
    (inferInstance : MeasurableSpace ((i : Iic b) → X i)) := by cases h; rfl

/-- The `ionescuContent κ x` of a cylinder indexed by first coordinates is given by
`partialKernel`. -/
theorem ionescuContent_cylinder {a b : ℕ} (x : (i : Iic a) → X i) {S : Set ((i : Iic b) → X i)}
    (mS : MeasurableSet S) :
    ionescuContent κ x (cylinder _ S) = partialKernel κ a b x S := by
  rw [ionescuContent, kolContent_congr _ (by rw [mem_cylinders]; exact ⟨Iic b, S, mS, rfl⟩) rfl mS,
    induced_family_Iic]

/-- This function computes the integral of a function `f` against `partialKernel`,
and allows to view it as a function depending on all the variables. -/
noncomputable def lmarginal_partialKernel (a b : ℕ) (f : ((n : ℕ) → X n) → ℝ≥0∞)
    (x : (n : ℕ) → X n) : ℝ≥0∞ :=
  ∫⁻ z : (i : Iic b) → X i, f (updateFinset x _ z) ∂(partialKernel κ a b (proj a x))

/-- If `a < b`, then integrating `f` against the `partialKernel κ a b` is the same as integrating
  against `kerNat a b`. -/
theorem lmarginal_partialKernel_lt {a b : ℕ} (hab : a < b) {f : ((n : ℕ) → X n) → ℝ≥0∞}
    (mf : Measurable f) (x : (n : ℕ) → X n) :
    lmarginal_partialKernel κ a b f x =
      ∫⁻ y : (i : Ioc a b) → X i, f (updateFinset x _ y) ∂kerNat κ a b (proj a x) := by
  rw [lmarginal_partialKernel, partialKernel, dif_pos hab, kernel.lintegral_map,
    kernel.lintegral_prod, kernel.lintegral_deterministic']
  · congrm ∫⁻ _, f (fun i ↦ ?_) ∂_
    simp only [updateFinset, mem_Iic, el, id_eq, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, mem_Ioc]
    split_ifs <;> try rfl
    · omega
    · omega
    · omega
  · apply Measurable.lintegral_prod_right'
      (f := fun p ↦ f (updateFinset x (Iic b) (el a b hab.le p)))
    exact mf.comp <| measurable_updateFinset.comp (el a b hab.le).measurable
  · exact mf.comp <| measurable_updateFinset.comp (el a b hab.le).measurable
  · exact mf.comp measurable_updateFinset

/-- If `b ≤ a`, then integrating `f` against the `partialKernel κ a b` does nothing. -/
theorem lmarginal_partialKernel_le {a b : ℕ} (hba : b ≤ a)
    {f : ((n : ℕ) → X n) → ℝ≥0∞} (mf : Measurable f) : lmarginal_partialKernel κ a b f = f := by
  ext x
  rw [lmarginal_partialKernel, partialKernel, dif_neg (not_lt.2 hba),
    kernel.lintegral_deterministic']
  · congr with i
    by_cases hi : i ∈ Iic b <;> simp [updateFinset, hi]
  · exact mf.comp measurable_updateFinset

/-- The `ionescuContent` of a cylinder is equal to the integral of its indicator function. -/
theorem ionescuContent_eq_lmarginal_partialKernel {N : ℕ} {S : Set ((i : Iic N) → X i)}
    (mS : MeasurableSet S) (x : (n : ℕ) → X n) (n : ℕ) :
    ionescuContent κ (proj n x) (cylinder _ S) =
    lmarginal_partialKernel κ n N ((cylinder _ S).indicator 1) x := by
  rw [ionescuContent_cylinder _ _ mS, ← lintegral_indicator_one mS, lmarginal_partialKernel]
  congr with y
  apply indicator_const_eq
  rw [mem_cylinder]
  congrm ?_ ∈ S
  ext i
  simp [updateFinset, i.2]

theorem lmarginal_partialKernel_mono (a b : ℕ) {f g : ((n : ℕ) → X n) → ℝ≥0∞} (hfg : f ≤ g)
    (x : (n : ℕ) → X n) : lmarginal_partialKernel κ a b f x ≤ lmarginal_partialKernel κ a b g x :=
  lintegral_mono fun _ ↦ hfg _

theorem measurable_lmarginal_partialKernel (a b : ℕ) {f : ((n : ℕ) → X n) → ℝ≥0∞}
    (hf : Measurable f) : Measurable (lmarginal_partialKernel κ a b f) := by
  unfold lmarginal_partialKernel
  let g : ((i : Iic b) → X i) × ((n : ℕ) → X n) → ℝ≥0∞ :=
    fun c ↦ f (updateFinset c.2 _ c.1)
  let η : kernel ((n : ℕ) → X n) ((i : Iic b) → X i) :=
    kernel.comap (partialKernel κ a b) (fun x i ↦ x i) (measurable_proj _)
  change Measurable fun x ↦ ∫⁻ z : (i : Iic b) → X i, g (z, x) ∂η x
  refine Measurable.lintegral_kernel_prod_left' <| hf.comp ?_
  simp only [updateFinset, measurable_pi_iff]
  intro i
  by_cases h : i ∈ Iic b <;> simp [h]
  · exact (measurable_pi_apply _).comp <| measurable_fst
  · exact measurable_snd.eval

theorem DependsOn.lmarginal_partialKernel_eq {a b : ℕ} (c : ℕ) {f : ((n : ℕ) → X n) → ℝ≥0∞}
    (mf : Measurable f) (hf : DependsOn f (Iic a)) (hab : a ≤ b) :
    lmarginal_partialKernel κ b c f = f := by
  rcases le_or_lt c b with hcb | hbc
  · exact lmarginal_partialKernel_le κ hcb mf
  · ext x
    have := isMarkovKernel_kerNat κ hbc
    rw [lmarginal_partialKernel_lt κ hbc mf, ← mul_one (f x),
      ← measure_univ (μ := kerNat κ b c (proj b x)), ← lintegral_const]
    refine lintegral_congr fun y ↦ hf fun i hi ↦ ?_
    simp only [updateFinset, mem_Iic, el, id_eq, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk,
      dite_eq_right_iff, dite_eq_left_iff, not_le]
    intro h
    rw [mem_Ioc] at h
    rw [mem_coe, mem_Iic] at hi
    omega

theorem dependsOn_lmarginal_partialKernel (a : ℕ) {b : ℕ} {f : ((n : ℕ) → X n) → ℝ≥0∞}
    (hf : DependsOn f (Iic b)) (mf : Measurable f) :
    DependsOn (lmarginal_partialKernel κ a b f) (Iic a) := by
  intro x y hxy
  rcases le_or_lt b a with hba | hab
  · rw [lmarginal_partialKernel_le κ hba mf]
    exact hf fun i hi ↦ hxy i (Iic_subset_Iic.2 hba hi)
  · rw [lmarginal_partialKernel_lt _ hab mf, lmarginal_partialKernel_lt _ hab mf]
    congrm ∫⁻ z : _, ?_ ∂kerNat κ a b (fun i ↦ ?_)
    · exact hxy i.1 i.2
    · refine dependsOn_updateFinset hf _ _ ?_
      rwa [← coe_sdiff, Iic_sdiff_Ioc_same hab.le]

theorem lmarginal_partialKernel_self {a b c : ℕ} (hab : a < b) (hbc : b < c)
    {f : ((n : ℕ) → X n) → ℝ≥0∞} (hf : Measurable f) :
    lmarginal_partialKernel κ a b (lmarginal_partialKernel κ b c f) =
      lmarginal_partialKernel κ a c f := by
  ext x
  rw [lmarginal_partialKernel_lt _ (hab.trans hbc) hf, lmarginal_partialKernel_lt _ hab]
  simp_rw [lmarginal_partialKernel_lt _ hbc hf]
  rw [← compProd_kerNat _ hab hbc, compProd_eq _ _  hab hbc, kernel.map_apply,
    lintegral_map _ (er ..).measurable, kernel.lintegral_compProd]
  · congrm ∫⁻ _, ∫⁻ _, f fun i ↦ ?_ ∂(?_) ∂_
    · rw [split_eq_comap, kernel.comap_apply]
      congr with i
      simp only [el, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, proj, updateFinset, mem_Ioc]
      split_ifs with h1 h2 h3 <;> try rfl
      · omega
      · have := mem_Iic.1 i.2
        omega
    · simp only [updateFinset, mem_Ioc, er, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk]
      split_ifs <;> try omega
      rfl; rfl; rfl
  · exact hf.comp <| measurable_updateFinset.comp (er ..).measurable
  · exact hf.comp <| measurable_updateFinset
  · exact measurable_lmarginal_partialKernel _ _ _ hf

theorem update_updateFinset_eq (x z : (n : ℕ) → X n) {m : ℕ} :
    update (updateFinset x (Iic m) (proj m z)) (m + 1) (z (m + 1)) =
    updateFinset x (Iic (m + 1)) (proj (m + 1) z) := by
  ext i
  simp only [update, updateFinset, mem_Iic, dite_eq_ite]
  split_ifs with h1 h2 h3 h4 h5 <;> try omega
  cases h1; rfl; rfl; rfl

/-- This is an auxiliary result for `ionescuContent_tendsto_zero`. Consider `f` a sequence of bounded measurable
functions such that `f n` depends only on the first coordinates up to `N n`.
Assume that when integrating `f n` against `partialKernel (k + 1) (N n)`,
one gets a non-increasing sequence of functions wich converges to `l`.
Assume then that there exists `ε` and `y : (n : Iic k) → X n` such that
when integrating `f n` against `partialKernel k (N n)`, you get something at least
`ε` for all. Then there exists `z` such that this remains true when integrating
`f` against `partialKernel (k + 1) (N n) (update y (k + 1) z)`. -/
theorem le_lmarginal_partialKernel_succ {f : ℕ → ((n : ℕ) → X n) → ℝ≥0∞} {N : ℕ → ℕ}
    (hcte : ∀ n, DependsOn (f n) (Iic (N n))) (mf : ∀ n, Measurable (f n))
    {bound : ℝ≥0∞} (fin_bound : bound ≠ ∞) (le_bound : ∀ n x, f n x ≤ bound) {k : ℕ}
    (anti : ∀ x, Antitone (fun n ↦ lmarginal_partialKernel κ (k + 1) (N n) (f n) x))
    {l : ((n : ℕ) → X n) → ℝ≥0∞}
    (htendsto : ∀ x, Tendsto (fun n ↦ lmarginal_partialKernel κ (k + 1) (N n) (f n) x)
      atTop (𝓝 (l x)))
    (ε : ℝ≥0∞) (y : (n : Iic k) → X n)
    (hpos : ∀ x n, ε ≤ lmarginal_partialKernel κ k (N n) (f n) (updateFinset x _ y)) :
    ∃ z, ∀ x n, ε ≤ lmarginal_partialKernel κ (k + 1) (N n) (f n)
      (Function.update (updateFinset x _ y) (k + 1) z) := by
  have _ n : Nonempty (X n) := by
    refine Nat.case_strong_induction_on (p := fun n ↦ Nonempty (X n)) _ inferInstance
      fun n hind ↦ ?_
    have : Nonempty ((i : Iic n) → X i) :=
      Nonempty.intro fun i ↦ @Classical.ofNonempty _ (hind i.1 (mem_Iic.1 i.2))
    exact ProbabilityMeasure.nonempty ⟨κ n Classical.ofNonempty, inferInstance⟩
  let F : ℕ → ((n : ℕ) → X n) → ℝ≥0∞ := fun n ↦ lmarginal_partialKernel κ (k + 1) (N n) (f n)
  -- `Fₙ` converges to `l` by hypothesis.
  have tendstoF x : Tendsto (F · x) atTop (𝓝 (l x)) := htendsto x
  -- Integrating `fₙ` between time `k` and `Nₙ` is the same as integrating
  -- `Fₙ` between time `k` and time `k + 1` variable.
  have f_eq x n : lmarginal_partialKernel κ k (N n) (f n) x =
    lmarginal_partialKernel κ k (k + 1) (F n) x := by
    simp_rw [F]
    rcases lt_trichotomy (k + 1) (N n) with h | h | h
    · rw [← lmarginal_partialKernel_self κ k.lt_succ_self h (mf n)]
    · rw [← h, lmarginal_partialKernel_le _ (le_refl (k + 1)) (mf n)]
    · rw [lmarginal_partialKernel_le _ (by omega) (mf n),
        (hcte n).lmarginal_partialKernel_eq _ _ (mf n) (by omega),
        (hcte n).lmarginal_partialKernel_eq _ _ (mf n) (by omega)]
  -- `F` is also a bounded sequence.
  have F_le n x : F n x ≤ bound := by
    simp_rw [F, lmarginal_partialKernel]
    rw [← mul_one bound, ← measure_univ (μ := partialKernel κ (k + 1) (N n) (proj (k + 1) x)),
        ← lintegral_const]
    exact lintegral_mono fun _ ↦ le_bound _ _
  -- By dominated convergence, the integral of `fₙ` between time `k` and time `N n` converges
  -- to the integral of `l` between time `k` and time `k + 1`.
  have tendsto_int x : Tendsto (fun n ↦ lmarginal_partialKernel κ k (N n) (f n) x) atTop
      (𝓝 (lmarginal_partialKernel κ k (k + 1) l x)) := by
    simp_rw [f_eq, lmarginal_partialKernel]
    exact tendsto_lintegral_of_dominated_convergence (fun _ ↦ bound)
      (fun n ↦ (measurable_lmarginal_partialKernel _ _ _ (mf n)).comp measurable_updateFinset)
      (fun n ↦ eventually_of_forall <| fun y ↦ F_le n _)
      (by simp [fin_bound]) (eventually_of_forall (fun _ ↦ tendstoF _))
  -- By hypothesis, we have `ε ≤ lmarginal_partialKernel κ k (k + 1) (F n) (updateFinset x _ y)`,
  -- so this is also true for `l`.
  have ε_le_lint x : ε ≤ lmarginal_partialKernel κ k (k + 1) l (updateFinset x _ y) :=
    ge_of_tendsto (tendsto_int _) (by simp [hpos])
  let x_ : (n : ℕ) → X n := Classical.ofNonempty
  -- We now have that the integral of `l` with respect to a probability measure is greater than `ε`,
  -- therefore there exists `x'` such that `ε ≤ l(y, x')`.
  obtain ⟨x', hx'⟩ : ∃ x', ε ≤ l (Function.update (updateFinset x_ _ y) (k + 1) x') := by
    have aux : ∫⁻ (a : X (k + 1)),
        l (update (updateFinset x_ _ y) (k + 1) a) ∂(κ k y) ≠ ∞ := by
      apply ne_top_of_le_ne_top fin_bound
      rw [← mul_one bound, ← measure_univ (μ := κ k y), ← lintegral_const]
      exact lintegral_mono <| fun y ↦ le_of_tendsto' (tendstoF _) <| fun _ ↦ F_le _ _
    rcases exists_lintegral_le aux with ⟨x', hx'⟩
    refine ⟨x', ?_⟩
    calc
      ε ≤ ∫⁻ (z : X (k + 1)),
          l (update (updateFinset x_ _ y) (k + 1) z) ∂(κ k y) := by
          convert ε_le_lint x_
          rw [lmarginal_partialKernel_lt _ k.lt_succ_self, kerNat_succ, kernel.map_apply,
            lintegral_map_equiv]
          · congrm ∫⁻ z, (l fun i ↦ ?_) ∂κ k (fun i ↦ ?_)
            · simp [i.2, updateFinset]
            · simp [update, updateFinset, e]
          · refine ENNReal.measurable_of_tendsto ?_ (tendsto_pi_nhds.2 htendsto)
            exact fun n ↦ measurable_lmarginal_partialKernel _ _ _ (mf n)
      _ ≤ l (update (updateFinset x_ _ y) (k + 1) x') := hx'
  refine ⟨x', fun x n ↦ ?_⟩
  -- As `F` is a non-increasing sequence, we have `ε ≤ Fₙ(y, x')` for any `n`.
  have := le_trans hx' ((anti _).le_of_tendsto (tendstoF _) n)
  -- This part below is just to say that this is true for any `x : (i : ι) → X i`,
  -- as `Fₙ` technically depends on all the variables, but really depends only on the first `k + 1`.
  convert this using 1
  refine dependsOn_lmarginal_partialKernel _ _ (hcte n) (mf n) fun i hi ↦ ?_
  simp only [update, updateFinset]
  split_ifs with h1 h2 <;> try rfl
  rw [mem_coe, mem_Iic] at *
  omega

/-- The cylinders of a product space indexed by `ℕ` can be seen as depending on the first
corrdinates. -/
theorem cylinders_nat :
    cylinders X = ⋃ (N) (S) (_ : MeasurableSet S), {cylinder (Iic N) S} := by
  ext s
  simp only [mem_cylinders, exists_prop, Set.mem_iUnion, mem_singleton]
  refine ⟨?_, fun ⟨N, S, mS, s_eq⟩ ↦ ⟨Iic N, S, mS, s_eq⟩⟩
  rintro ⟨t, S, mS, rfl⟩
  refine ⟨t.sup id, projection t.sub_Iic ⁻¹' S, measurable_projection _ mS, ?_⟩
  unfold cylinder
  rw [← Set.preimage_comp]
  rfl

/-- This function takes a trajectory up to time `p` and a way of building the next step of the
trajectory and returns a whole trajectory whose first steps correspond
to the initial ones provided. -/
def iterate_induction {p : ℕ} (x₀ : (i : Iic p) → X i) (ind : (k : ℕ) → ((n : Iic k) → X n) → X (k + 1)) :
    (k : ℕ) → X k := fun k ↦ by
  cases k with
  | zero => exact x₀ ⟨0, mem_Iic.2 <| zero_le p⟩
  | succ q =>
    exact if hq : q + 1 ≤ p
      then x₀ ⟨q + 1, mem_Iic.2 hq⟩
      else ind q (fun i ↦ iterate_induction x₀ ind i)
  decreasing_by
    have := mem_Iic.1 i.2
    rename_i h
    rw [← Nat.lt_succ, Nat.succ_eq_add_one, ← h] at this
    exact this

theorem iterate_induction_le {p : ℕ} (x₀ : (i : Iic p) → X i)
    (ind : (k : ℕ) → ((n : Iic k) → X n) → X (k + 1)) (k : Iic p) :
    iterate_induction x₀ ind k = x₀ k := by
  rcases k with ⟨i, hi⟩
  cases i with
  | zero =>
    rw [iterate_induction, Nat.casesAuxOn_zero]
  | succ j =>
    rw [iterate_induction, Nat.casesAuxOn_succ]
    simp [mem_Iic.1 hi]

/-- The indicator of a cylinder only depends on the variables whose the cylinder depends on. -/
theorem dependsOn_cylinder_indicator {ι : Type*} {α : ι → Type*} {I : Finset ι}
    (S : Set ((i : I) → α i)) :
    DependsOn ((cylinder I S).indicator (1 : ((i : ι) → α i) → ℝ≥0∞)) I :=
  fun x y hxy ↦ indicator_const_eq _ (by simp [hxy])

theorem proj_updateFinset {n : ℕ} (x : (n : ℕ) → X n) (y : (i : Iic n) → X i) :
    proj n (updateFinset x _ y) = y := by
  ext i
  simp [proj, updateFinset, mem_Iic.1 i.2]

/-- This is the key theorem to prove the existence of the `ionescuTulceaKernel`:
the `ionescuContent` of a decresaing sequence of cylinders with empty intersection converges to `0`.
This implies the $\sigma$-additivity of `ionescuContent`
(see `sigma_additive_addContent_of_tendsto_zero`), which allows to extend it to the
$\sigma$-algebra by Carathéodory's theorem. -/
theorem ionescuContent_tendsto_zero (A : ℕ → Set ((n : ℕ) → X n))
    (A_mem : ∀ n, A n ∈ cylinders X) (A_anti : Antitone A) (A_inter : ⋂ n, A n = ∅)
    {p : ℕ} (x₀ : (i : Iic p) → X i) :
    Tendsto (fun n ↦ ionescuContent κ x₀ (A n)) atTop (𝓝 0) := by
  have _ n : Nonempty (X n) := by
    refine Nat.case_strong_induction_on (p := fun n ↦ Nonempty (X n)) _ inferInstance
      fun n hind ↦ ?_
    have : Nonempty ((i : Iic n) → X i) :=
      Nonempty.intro fun i ↦ @Classical.ofNonempty _ (hind i.1 (mem_Iic.1 i.2))
    exact ProbabilityMeasure.nonempty ⟨κ n Classical.ofNonempty, inferInstance⟩
  -- `Aₙ` is a cylinder, it can be written `cylinder (Iic (N n)) Sₙ`.
  have A_cyl n : ∃ N S, MeasurableSet S ∧ A n = cylinder (Iic N) S := by
    simpa [cylinders_nat] using A_mem n
  choose N S mS A_eq using A_cyl
  -- We write `χₙ` for the indicator function of `Aₙ`.
  let χ n := (A n).indicator (1 : ((n : ℕ) → X n) → ℝ≥0∞)
  -- `χₙ` is measurable.
  have mχ n : Measurable (χ n) := by
    simp_rw [χ, A_eq]
    exact (measurable_indicator_const_iff 1).2 <| measurableSet_cylinder _ _ (mS n)
  -- `χₙ` only depends on the first coordinates.
  have χ_dep n : DependsOn (χ n) (Iic (N n)) := by
    simp_rw [χ, A_eq]
    exact dependsOn_cylinder_indicator _
  -- Therefore its integral against `partialKernel κ k (N n)` is constant.
  have lma_const x y n :
      lmarginal_partialKernel κ p (N n) (χ n) (updateFinset x _ x₀) =
      lmarginal_partialKernel κ p (N n) (χ n) (updateFinset y _ x₀) := by
    apply dependsOn_lmarginal_partialKernel κ p (χ_dep n) (mχ n)
    intro i hi
    rw [mem_coe, mem_Iic] at hi
    simp [updateFinset, hi]
  -- As `(Aₙ)` is non-increasing, so is `(χₙ)`.
  have χ_anti : Antitone χ := by
    intro m n hmn y
    apply Set.indicator_le
    exact fun a ha ↦ by simp [χ, A_anti hmn ha]
  -- Integrating `χₙ` further than the last coordinate it depends on does nothing.
  -- This is used to then show that the integral of `χₙ` from time `k` is non-increasing.
  have lma_inv k M n (h : N n ≤ M) :
      lmarginal_partialKernel κ k M (χ n) = lmarginal_partialKernel κ k (N n) (χ n) := by
    refine Nat.le_induction rfl ?_ M h
    intro K hK hind
    rw [← hind]
    rcases lt_trichotomy k K with hkK | hkK | hkK
    · rw [← lmarginal_partialKernel_self κ hkK K.lt_succ_self (mχ n),
        (χ_dep n).lmarginal_partialKernel_eq _ _ (mχ n) hK]
    · rw [hkK, (χ_dep n).lmarginal_partialKernel_eq _ _ (mχ n) hK,
        (χ_dep n).lmarginal_partialKernel_eq _ _ (mχ n) hK]
    · rw [lmarginal_partialKernel_le _ hkK.le (mχ n),
        lmarginal_partialKernel_le _ (Nat.succ_le.2 hkK) (mχ n)]
  -- the integral of `χₙ` from time `k` is non-increasing.
  have anti_lma k x : Antitone fun n ↦ lmarginal_partialKernel κ k (N n) (χ n) x := by
    intro m n hmn
    simp only
    rw [← lma_inv k ((N n).max (N m)) n (le_max_left _ _),
      ← lma_inv k ((N n).max (N m)) m (le_max_right _ _)]
    exact lmarginal_partialKernel_mono _ _ _ (χ_anti hmn) _
  -- Therefore it converges to some function `lₖ`.
  have this k x : ∃ l,
      Tendsto (fun n ↦ lmarginal_partialKernel κ k (N n) (χ n) x) atTop (𝓝 l) := by
    rcases tendsto_of_antitone <| anti_lma k x with h | h
    · rw [OrderBot.atBot_eq] at h
      exact ⟨0, h.mono_right <| pure_le_nhds 0⟩
    · exact h
  choose l hl using this
  -- `lₚ` is constant because it is the limit of constant functions: we call it `ε`.
  have l_const x y : l p (updateFinset x _ x₀) = l p (updateFinset y _ x₀) := by
    have := hl p (updateFinset x _ x₀)
    simp_rw [lma_const x y] at this
    exact tendsto_nhds_unique this (hl p _)
  obtain ⟨ε, hε⟩ : ∃ ε, ∀ x, l p (updateFinset x _ x₀) = ε :=
      ⟨l p (updateFinset Classical.ofNonempty _ x₀), fun x ↦ l_const _ _⟩
  -- As the sequence is decreasing, `ε ≤ ∫ χₙ`.
  have hpos x n : ε ≤ lmarginal_partialKernel κ p (N n) (χ n) (updateFinset x _ x₀) :=
    hε x ▸ ((anti_lma p _).le_of_tendsto (hl p _)) n
  -- Also, the indicators are bounded by `1`.
  have χ_le n x : χ n x ≤ 1 := by
    apply Set.indicator_le
    simp
  -- We have all the conditions to apply ``. This allows us to recursively
  -- build a sequence `z` with the following property: for any `k ≥ p` and `n`,
  -- integrating `χ n` from time `k` to time `N n` with the trajectory up to `k` being equal to `z`
  -- gives something greater than `ε`.
  choose! ind hind using
    fun k y h ↦ le_lmarginal_partialKernel_succ κ χ_dep mχ (by norm_num : (1 : ℝ≥0∞) ≠ ∞)
      χ_le (anti_lma (k + 1)) (hl (k + 1)) ε y h
  let z := iterate_induction x₀ ind
  have imp k (hk : p ≤ k) : ∀ x n,
      ε ≤ lmarginal_partialKernel κ k (N n) (χ n) (updateFinset x (Iic k) (fun i ↦ z i)) := by
    refine Nat.le_induction ?_ ?_ k hk
    · intro x n
      convert hpos x n with i
      simp_rw [z]
      apply iterate_induction_le
    · intro k hn h x n
      rw [← update_updateFinset_eq]
      convert hind k (fun i ↦ z i.1) h x n
      simp_rw [z]
      rw [iterate_induction, Nat.casesAuxOn_succ]
      simp [Nat.lt_succ.2 hn]
  -- We now want to prove that the integral of `χₙ`, which is equal to the `ionescuContent`
  -- of `Aₙ`, converges to `0`.
  have aux x n : ionescuContent κ x₀ (A n) =
      lmarginal_partialKernel κ p (N n) (χ n) (updateFinset x _ x₀) := by
    simp_rw [χ, A_eq]
    nth_rw 1 [← proj_updateFinset x x₀]
    exact ionescuContent_eq_lmarginal_partialKernel κ (mS n) (updateFinset x _ x₀) p
  simp_rw [aux Classical.ofNonempty]
  convert hl p (updateFinset Classical.ofNonempty _ x₀)
  rw [hε]
  by_contra!
  -- Which means that we want to prove that `ε = 0`. But if `ε > 0`, then for any `n`,
  -- choosing `k > Nₙ` we get `ε ≤ χₙ(z₀, ..., z_{Nₙ})` and therefore `z ∈ Aₙ`.
  -- This contradicts the fact that `(Aₙ)` has an empty intersection.
  have ε_pos : 0 < ε := this.symm.bot_lt
  have mem n : z ∈ A n := by
    have : χ n z = lmarginal_partialKernel κ (max p (N n)) (N n) (χ n)
        (updateFinset z (Iic (N n)) (fun i ↦ z i)) := by
      rw [lmarginal_partialKernel_le _ (le_max_right _ _) (mχ n)]
      congr with i
      simp [updateFinset]
    have : 0 < χ n (z) := by
      rw [this]
      convert lt_of_lt_of_le ε_pos (imp _ (le_max_left _ _) z n) using 2
      ext i
      simp [updateFinset]
    exact Set.mem_of_indicator_ne_zero (ne_of_lt this).symm
  exact (A_inter ▸ Set.mem_iInter.2 mem).elim

/-- The `ionescuContent` is sigma-subadditive. -/
theorem ionescuContent_sigma_subadditive {p : ℕ} (x₀ : (i : Iic p) → X i)
    ⦃f : ℕ → Set ((n : ℕ) → X n)⦄
    (hf : ∀ n, f n ∈ cylinders X)
    (hf_Union : (⋃ n, f n) ∈ cylinders X) :
    ionescuContent κ x₀ (⋃ n, f n) ≤ ∑' n, ionescuContent κ x₀ (f n) := by
  have _ n : Nonempty (X n) := by
    refine Nat.case_strong_induction_on (p := fun n ↦ Nonempty (X n)) _ inferInstance
      fun n hind ↦ ?_
    have : Nonempty ((i : Iic n) → X i) :=
      Nonempty.intro fun i ↦ @Classical.ofNonempty _ (hind i.1 (mem_Iic.1 i.2))
    exact ProbabilityMeasure.nonempty
      ⟨κ n Classical.ofNonempty, inferInstance⟩
  refine (ionescuContent κ x₀).sigma_subadditive_of_sigma_additive
    setRing_cylinders (fun f hf hf_Union hf' ↦ ?_) f hf hf_Union
  refine sigma_additive_addContent_of_tendsto_zero setRing_cylinders
    (ionescuContent κ x₀) (fun h ↦ ?_) ?_ hf hf_Union hf'
  · rename_i s
    obtain ⟨N, S, mS, s_eq⟩ : ∃ N S, MeasurableSet S ∧ s = cylinder (Iic N) S := by
      simpa [cylinders_nat] using h
    let x_ : (n : ℕ) → X n := Classical.ofNonempty
    classical
    rw [s_eq, ← proj_updateFinset x_ x₀,
      ionescuContent_eq_lmarginal_partialKernel κ mS (updateFinset x_ _ x₀)]
    refine ne_of_lt (lt_of_le_of_lt ?_ (by norm_num : (1 : ℝ≥0∞) < ∞))
    nth_rw 2 [← mul_one 1,
      ← measure_univ (μ := partialKernel κ p N (fun i ↦ updateFinset x_ _ x₀ i))]
    rw [lmarginal_partialKernel, ← lintegral_const]
    exact lintegral_mono <| Set.indicator_le (by simp)
  · exact fun s hs anti_s inter_s ↦ ionescuContent_tendsto_zero κ s hs anti_s inter_s x₀

/-- This function is the kernel given by the Ionescu-Tulcea theorem. -/
noncomputable def ionescuTulceaFun (p : ℕ) (x₀ : (i : Iic p) → X i) :
    Measure ((n : ℕ) → X n) :=
  Measure.ofAddContent setSemiringCylinders generateFrom_cylinders
    (ionescuContent κ x₀) (ionescuContent_sigma_subadditive κ x₀)

theorem isProbabilityMeasure_ionescuTulceaFun (p : ℕ) (x₀ : (i : Iic p) → X i) :
    IsProbabilityMeasure (ionescuTulceaFun κ p x₀) := by
  constructor
  rw [← cylinder_univ (Iic 0), ionescuTulceaFun, Measure.ofAddContent_eq, ionescuContent_cylinder]
  · simp
  · exact MeasurableSet.univ
  · rw [mem_cylinders]
    exact ⟨Iic 0, Set.univ, MeasurableSet.univ, rfl⟩

theorem isProjectiveLimit_ionescuTulceaFun (p : ℕ) (x₀ : (i : Iic p) → X i) :
    IsProjectiveLimit (ionescuTulceaFun κ p x₀)
      (induced_family (fun n ↦ partialKernel κ p n x₀)) := by
  rw [isProjectiveLimit_nat_iff]
  · intro n
    ext s ms
    rw [Measure.map_apply (meas_proj n) ms]
    have h_mem : (proj n) ⁻¹' s ∈ cylinders X := by
      rw [mem_cylinders]; exact ⟨Iic n, s, ms, rfl⟩
    rw [ionescuTulceaFun, Measure.ofAddContent_eq _ _ _ _ h_mem, ionescuContent,
      kolContent_congr _ h_mem rfl ms]
  · exact (isProjectiveMeasureFamily_induced_family _ (partialKernel_proj_apply κ x₀))

theorem measurable_ionescuTulceaFun (p : ℕ) : Measurable (ionescuTulceaFun κ p) := by
  apply Measure.measurable_of_measurable_coe
  refine MeasurableSpace.induction_on_inter
    (C := fun t ↦ Measurable (fun x₀ ↦ ionescuTulceaFun κ p x₀ t))
    (s := cylinders X) generateFrom_cylinders.symm isPiSystem_cylinders
    (by simp) (fun t ht ↦ ?cylinder) (fun t mt ht ↦ ?compl) (fun f disf mf hf ↦ ?union)
  · obtain ⟨N, S, mS, t_eq⟩ : ∃ N S, MeasurableSet S ∧ t = cylinder (Iic N) S := by
      simpa [cylinders_nat] using ht
    simp_rw [ionescuTulceaFun, Measure.ofAddContent_eq _ _ _ _ ht, ionescuContent,
      kolContent_congr _ ht t_eq mS]
    simp only [induced_family]
    refine Measure.measurable_measure.1 ?_ _ mS
    refine (Measure.measurable_map _ ?_).comp (kernel.measurable _)
    exact measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)
  · have := isProbabilityMeasure_ionescuTulceaFun κ p
    simp_rw [measure_compl mt (measure_ne_top _ _), measure_univ]
    exact Measurable.const_sub ht _
  · simp_rw [measure_iUnion disf mf]
    exact Measurable.ennreal_tsum hf

noncomputable def ionescuTulceaKernel (p : ℕ) : kernel ((i : Iic p) → X i) ((n : ℕ) → X n) :=
  { val := ionescuTulceaFun κ p
    property := measurable_ionescuTulceaFun κ p }

theorem ionescuTulceaKernel_apply (p : ℕ) (x₀ : (i : Iic p) → X i) :
    ionescuTulceaKernel κ p x₀ = ionescuTulceaFun κ p x₀ := rfl

instance (p : ℕ) : IsMarkovKernel (ionescuTulceaKernel κ p) :=
  IsMarkovKernel.mk fun _ ↦ isProbabilityMeasure_ionescuTulceaFun ..

theorem ionescuTulceaKernel_proj (a b : ℕ) :
    kernel.map (ionescuTulceaKernel κ a) (proj b) (meas_proj b) = partialKernel κ a b := by
  ext1 x₀
  rw [kernel.map_apply, ionescuTulceaKernel_apply, isProjectiveLimit_ionescuTulceaFun,
    induced_family_Iic]

theorem eq_ionescuTulceaKernel {a : ℕ} (η : kernel ((i : Iic a) → X i) ((n : ℕ) → X n))
    (hη : ∀ b, kernel.map η (proj b) (meas_proj b) = partialKernel κ a b) :
    η = ionescuTulceaKernel κ a := by
  ext1 x₀
  have _ I : IsFiniteMeasure (induced_family (fun n ↦ partialKernel κ a n x₀) I) := by
    rw [induced_family]
    infer_instance
  refine isProjectiveLimit_unique ?_ (isProjectiveLimit_ionescuTulceaFun _ _ _)
  rw [isProjectiveLimit_nat_iff]
  · intro n
    rw [induced_family_Iic, ← kernel.map_apply _ (meas_proj n), hη n]
  · exact (isProjectiveMeasureFamily_induced_family _ (partialKernel_proj_apply κ x₀))

theorem partialKernel_comp_ionescuTulceaKernel {a b : ℕ} (hab : a ≤ b) :
    (ionescuTulceaKernel κ b) ∘ₖ (partialKernel κ a b) = ionescuTulceaKernel κ a := by
  refine eq_ionescuTulceaKernel _ _ fun n ↦ ?_
  ext x₀ s ms
  rw [kernel.map_apply' _ _ _ ms, kernel.comp_apply' _ _ _ (meas_proj n ms)]
  simp_rw [← Measure.map_apply (meas_proj n) ms,
    ← kernel.map_apply (ionescuTulceaKernel κ b) (meas_proj n), ionescuTulceaKernel_proj κ b n]
  rw [← kernel.comp_apply' _ _ _ ms, partialKernel_comp _ n hab]


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {Y Z T U : Type*} [MeasurableSpace Y] [MeasurableSpace Z] [MeasurableSpace T]
variable [MeasurableSpace U]

abbrev m : MeasurableSpace ((n : ℕ) → X n) := inferInstance
abbrev m' : (n : ℕ) → MeasurableSpace ((i : Iic n) → X i) := inferInstance

def ℱ : Filtration ℕ (m (X := X)) where
  seq n := (m' n).comap (proj n)
  mono' i j hij := by
    simp only
    conv_lhs => enter [1]; change (projection (Iic_subset_Iic.2 hij)) ∘ (proj j)
    rw [← comap_comp]
    exact MeasurableSpace.comap_mono (measurable_projection _).comap_le
  le' n := (meas_proj n).comap_le

theorem MeasureTheory.Filtration.condexp_condexp {X ι : Type*} [Preorder ι] [MeasurableSpace X]
    (f : X → E) {μ : Measure X}
    (ℱ : @Filtration X ι _ inferInstance)
    {i j : ι} (hij : i ≤ j) [SigmaFinite (μ.trim (ℱ.le j))] :
    μ[μ[f|ℱ j]|ℱ i] =ᵐ[μ] μ[f|ℱ i] := condexp_condexp_of_le (ℱ.mono hij) (ℱ.le j)

theorem dependsOn_proj (n : ℕ) : DependsOn (@proj X n) (Iic n) := by
  intro x y hxy
  ext i
  exact hxy i.1 (mem_coe.1 i.2)

theorem measurable_dependsOn {n : ℕ} {f : ((n : ℕ) → X n) → E}
    (mf : @StronglyMeasurable _ _ _ (ℱ n) f) : DependsOn f (Iic n) := by
  intro x y hxy
  let _ : MeasurableSpace E := borel E
  have : BorelSpace E := BorelSpace.mk rfl
  have : @MeasurableSet _ (ℱ n) (f ⁻¹' {f x}) :=
    (measurableSet_singleton (f x)).preimage mf.measurable
  rcases this with ⟨s, -, hs⟩
  have : x ∈ proj n ⁻¹' s := by simp [hs]
  have : y ∈ proj n ⁻¹' s := by
    rw [Set.mem_preimage] at *
    convert this using 1
    ext i
    exact (hxy i.1 (mem_coe.1 i.2)).symm
  rw [hs] at this
  exact (by simpa using this : f y = f x).symm

theorem Set.indicator_const_smul_apply' {α R M : Type*} [Zero R] [Zero M] [SMulWithZero R M]
    (s : Set α) (r : R) (f : α → M) (a : α) :
    s.indicator (r • f) a = (s.indicator (fun _ ↦ r : α → R) a) • (f a) := by
  by_cases h : a ∈ s <;> simp [h]

theorem Set.indicator_one_smul_apply {α M β : Type*} [Zero β] [MonoidWithZero M]
    [MulActionWithZero M β] (f : α → β) (s : Set α) (a : α) :
    s.indicator f a = (s.indicator (fun _ ↦ 1 : α → M) a) • (f a) := by
  by_cases h : a ∈ s <;> simp [h]

theorem kernel.integral_prod (κ : kernel Y Z) [IsFiniteKernel κ]
    (η : kernel Y T) [IsFiniteKernel η] {f : (Z × T) → E}
    (y : Y) (hf : Integrable f ((κ ×ₖ η) y)) :
    ∫ p, f p ∂(κ ×ₖ η) y = ∫ z, ∫ t, f (z, t) ∂η y ∂κ y := by
  rw [kernel.prod_apply, MeasureTheory.integral_prod]
  convert hf
  rw [kernel.prod_apply]

theorem kernel.integral_comp (η : kernel Z T) [IsFiniteKernel η]
    (κ : kernel Y Z) [IsFiniteKernel κ]
    (y : Y) {g : T → E} (hg1 : Integrable g ((η ∘ₖ κ) y)) :
    ∫ t, g t ∂(η ∘ₖ κ) y = ∫ z, ∫ t, g t ∂η z ∂κ y := by
  rw [kernel.comp_eq_snd_compProd, kernel.snd_apply, integral_map,
    ProbabilityTheory.integral_compProd]
  · simp_rw [kernel.prodMkLeft_apply η]
  · apply Integrable.comp_measurable
    · convert hg1
      rw [kernel.comp_eq_snd_compProd, kernel.snd_apply]
    · exact measurable_snd
  · exact measurable_snd.aemeasurable
  · convert hg1.aestronglyMeasurable
    rw [kernel.comp_eq_snd_compProd, kernel.snd_apply]

def el' (n : ℕ) : (((i : Iic n) → X i) × ((i : Set.Ioi n) → X i)) ≃ᵐ ((n : ℕ) → X n) :=
  { toFun := fun p i ↦ if hi : i ≤ n
      then p.1 ⟨i, mem_Iic.2 hi⟩
      else p.2 ⟨i, Set.mem_Ioi.2 (not_le.1 hi)⟩
    invFun := fun x ↦ (fun i ↦ x i, fun i ↦ x i)
    left_inv := fun p ↦ by
      ext i
      · simp [mem_Iic.1 i.2]
      · simp [not_le.2 <| Set.mem_Ioi.1 i.2]
    right_inv := fun x ↦ by simp
    measurable_toFun := by
      refine measurable_pi_lambda _ (fun i ↦ ?_)
      by_cases hi : i ≤ n
      · simp only [Equiv.coe_fn_mk, hi, ↓reduceDite]
        exact measurable_fst.eval
      · simp only [Equiv.coe_fn_mk, hi, ↓reduceDite]
        exact measurable_snd.eval
    measurable_invFun := Measurable.prod_mk (measurable_proj _) (measurable_proj _) }

theorem projel' (n : ℕ) (x : (i : Iic n) → X i) (y : (i : Set.Ioi n) → X i) :
    proj n ((el' (X := X) n) (x, y)) = x := by
  ext i
  simp [el', proj, mem_Iic.1 i.2]

theorem noyau_proj {a b : ℕ} (hab : a ≤ b) :
    kernel.map (ionescuTulceaKernel κ b) (@proj X a) (meas_proj a) =
    kernel.deterministic
      (fun (x : (i : Iic b) → X i) (i : Iic a) ↦ x ⟨i.1, Iic_subset_Iic.2 hab i.2⟩)
      (measurable_proj₂' ..) := by
  rw [ionescuTulceaKernel_proj, partialKernel, dif_neg (not_lt.2 hab)]

theorem integral_map_equiv' (e : Y ≃ᵐ Z) (f : Z → E) (μ : Measure Z) :
    ∫ y, f (e y) ∂Measure.map e.symm μ = ∫ z, f z ∂μ := by
  simp_rw [integral_map_equiv e.symm, e.apply_symm_apply]

/-- This theorem shows that `ionescuTulceaKernel κ n` is, up to an equivalence, the product of
a determinstic kernel with another kernel. This is an intermediate result to compute integrals
with respect to this kernel. -/
theorem ionescu_eq (n : ℕ) :
    ionescuTulceaKernel κ n =
    kernel.map
      (kernel.deterministic (@id ((i : Iic n) → X i)) measurable_id ×ₖ
        kernel.map (ionescuTulceaKernel κ n)
          (fun x i ↦ x i : ((n : ℕ) → X n) → (i : Set.Ioi n) → X i) (measurable_proj _))
      (el' n) (el' n).measurable := by
  ext1 x
  rw [ionescuTulceaKernel_apply]
  have _ I : IsFiniteMeasure (induced_family (fun k ↦ partialKernel κ n k x) I) := by
    rw [induced_family]
    infer_instance
  refine isProjectiveLimit_unique (isProjectiveLimit_ionescuTulceaFun _ _ _) ?_
  rw [isProjectiveLimit_nat_iff' _ (isProjectiveMeasureFamily_induced_family _ (partialKernel_proj_apply κ x)) _ (n + 1)]
  intro k hk
  have hk' : n ≤ k := n.le_succ.trans hk
  rw [induced_family_Iic]
  ext s ms
  rw [← kernel.map_apply _ (meas_proj k), kernel.map_map, kernel.map_apply' _ _ _ ms,
    kernel.deterministic_prod_apply', kernel.map_apply']
  · have : (proj k) ∘ (el' n) ∘ (Prod.mk x) ∘
        (fun x i ↦ x i : ((n : ℕ) → X n) → (i : Set.Ioi n) → X i) =
        (fun y (i : Iic k) ↦ if hi : i.1 ≤ n then x ⟨i.1, mem_Iic.2 hi⟩ else y i) ∘ (proj k) := by
      ext x i
      by_cases hi : i.1 ≤ n <;> simp [proj, hi, el']
    have aux t : {c : (i : Set.Ioi n) → X i | (id x, c) ∈ t} = Prod.mk x ⁻¹' t := rfl
    have hyp : Measurable
        (fun (y : (i : Iic k) → X i) (i : Iic k) ↦
        if hi : i.1 ≤ n then x ⟨i.1, mem_Iic.2 hi⟩ else y i) := by
      refine measurable_pi_lambda _ (fun i ↦ ?_)
      by_cases hi : i.1 ≤ n <;> simp [hi]
      exact measurable_pi_apply _
    rw [aux, ← Set.preimage_comp, ← Set.preimage_comp, comp.assoc, this,
      ← kernel.map_apply' _ _ _ ms, ← kernel.map_map _ (meas_proj k) hyp, ionescuTulceaKernel_proj,
      kernel.map_apply' _ _ _ ms, partialKernel_lt κ (Nat.succ_le.1 hk),
      kernel.map_apply' _ _ _ (hyp ms), kernel.deterministic_prod_apply',
      kernel.map_apply' _ _ _ ms, kernel.deterministic_prod_apply']
    · congr with y
      simp only [id_eq, el, Nat.succ_eq_add_one, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk,
        Set.mem_preimage, Set.mem_setOf_eq]
      congrm (fun i ↦ ?_) ∈ s
      by_cases hi : i.1 ≤ n <;> simp [hi]
    · exact (el n k hk').measurable ms
    · exact (el n k hk').measurable <| hyp ms
  · exact measurable_prod_mk_left ((el' n).measurable <| (meas_proj k) ms)
  · exact (el' n).measurable <| (meas_proj k) ms

theorem kernel.integrable_comp (η : kernel Z T) [IsSFiniteKernel η]
    (κ : kernel Y Z) [IsSFiniteKernel κ] (y : Y)
    {f : T → E} (hf : AEStronglyMeasurable f ((η ∘ₖ κ) y)) :
    Integrable f ((η ∘ₖ κ) y) ↔
    (∀ᵐ z ∂κ y, Integrable f (η z)) ∧ (Integrable (fun z ↦ ∫ t, ‖f t‖ ∂η z) (κ y)) := by
  rw [kernel.comp_eq_snd_compProd, kernel.snd] at *
  rw [kernel.map_apply, integrable_map_measure, ProbabilityTheory.integrable_compProd_iff]
  · rfl
  · exact hf.comp_measurable measurable_snd
  · exact hf
  · exact measurable_snd.aemeasurable

theorem victoire {a b : ℕ} (hab : a ≤ b) : (partialKernel κ a b) ⊗ₖ
    (kernel.comap (ionescuTulceaKernel κ b) Prod.snd measurable_snd) =
    kernel.map (ionescuTulceaKernel κ a) (fun x ↦ (proj b x, x))
      ((meas_proj b).prod_mk measurable_id) := by
  ext x s ms
  have hyp := (meas_proj (X := X) b).prod_mk measurable_id
  rw [kernel.compProd_apply _ _ _ ms, kernel.map_apply' _ _ _ ms, ← partialKernel_comp_ionescuTulceaKernel κ hab,
    kernel.comp_apply']
  · congr with y
    rw [kernel.comap_apply, ionescu_eq, kernel.map_apply', kernel.prod_apply',
      kernel.map_apply', kernel.prod_apply', kernel.lintegral_deterministic',
      kernel.lintegral_deterministic']
    · congr with z
      simp [projel' b]
    · exact measurable_measure_prod_mk_left ((el' b).measurable <| hyp ms)
    · exact measurable_measure_prod_mk_left ((el' b).measurable <| measurable_prod_mk_left ms)
    · exact (el' b).measurable <| hyp ms
    · exact hyp ms
    · exact (el' b).measurable (measurable_prod_mk_left ms)
    · exact measurable_prod_mk_left ms
  · exact hyp ms

theorem measurable_updateFinset' {ι : Type*} [DecidableEq ι] {I : Finset ι}
    {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    {y : (i : I) → X i} : Measurable (fun x ↦ updateFinset x I y) := by
  refine measurable_pi_lambda _ (fun i ↦ ?_)
  by_cases hi : i ∈ I <;> simp only [updateFinset, hi, ↓reduceDite, measurable_const]
  exact measurable_pi_apply _

theorem integral_ionescu {n : ℕ} (x₀ : (i : Iic n) → X i) {f : ((n : ℕ) → X n) → E}
    (mf : StronglyMeasurable f)
    (i_f : Integrable f (ionescuTulceaKernel κ n x₀)) :
    ∫ x, f x ∂ionescuTulceaKernel κ n x₀ =
      ∫ x, f (updateFinset x _ x₀) ∂ionescuTulceaKernel κ n x₀ := by
  rw [ionescu_eq, kernel.map_apply, integral_map, kernel.integral_prod,
    kernel.integral_deterministic', integral_map, kernel.integral_prod,
    kernel.integral_deterministic']
  · congrm ∫ x, f fun i ↦ ?_ ∂_
    by_cases hi : i ≤ n <;> simp [updateFinset, el', hi]
  · exact (mf.comp_measurable
      (measurable_updateFinset'.comp (el' n).measurable)).integral_prod_right'
  · change Integrable (f ∘ (fun x ↦ updateFinset x _ x₀) ∘ (el' n)) _
    rw [← integrable_map_measure]
    · convert i_f
      ext s ms
      nth_rw 2 [ionescu_eq]
      rw [Measure.map_apply, kernel.map_apply', kernel.prod_apply', kernel.prod_apply',
        kernel.lintegral_deterministic', kernel.lintegral_deterministic']
      · congr with x
        simp only [id_eq, Set.mem_preimage, comp_apply, Set.mem_setOf_eq]
        congrm (fun i ↦ ?_) ∈ s
        by_cases hi : i ≤ n <;> simp [el', hi, updateFinset]
      · exact measurable_measure_prod_mk_left ((el' n).measurable ms)
      · exact measurable_measure_prod_mk_left (measurable_updateFinset'.comp (el' n).measurable ms)
      · exact (el' n).measurable ms
      · exact measurable_updateFinset'.comp (el' n).measurable ms
      · exact ms
      · exact measurable_updateFinset'.comp (el' n).measurable
      · exact ms
    · exact mf.aestronglyMeasurable
    · exact (measurable_updateFinset'.comp (el' n).measurable).aemeasurable
  · exact (el' n).measurable.aemeasurable
  · exact (mf.comp_measurable measurable_updateFinset').aestronglyMeasurable
  · exact (mf.comp_measurable (el' n).measurable).integral_prod_right'
  · rwa [ionescu_eq, kernel.map_apply, integrable_map_measure] at i_f
    · exact mf.aestronglyMeasurable
    · exact (el' n).measurable.aemeasurable
  · exact (el' n).measurable.aemeasurable
  · exact mf.aestronglyMeasurable

theorem partialKernel_comp_ionescuTulceaKernel_apply {a b : ℕ} (hab : a ≤ b)
    (f : ((i : Iic b) → X i) → ((n : ℕ) → X n) → E)
    (hf : StronglyMeasurable f.uncurry)
    (x₀ : (i : Iic a) → X i)
    (i_f : Integrable (fun x ↦ f (proj b x) x) (ionescuTulceaKernel κ a x₀)) :
    ∫ x, f (proj b x) x ∂ionescuTulceaKernel κ a x₀ =
    ∫ x, ∫ y, f x y ∂ionescuTulceaKernel κ b x ∂partialKernel κ a b x₀ := by
  rw [← partialKernel_comp_ionescuTulceaKernel κ hab, kernel.integral_comp]
  have i_f' := i_f
  rw [← partialKernel_comp_ionescuTulceaKernel κ hab, kernel.integrable_comp] at i_f'
  change Integrable (f.uncurry ∘ (fun x ↦ (proj b x, x))) _ at i_f
  rw [← integrable_map_measure, ← kernel.map_apply, ← victoire _ hab] at i_f
  rcases (ProbabilityTheory.integrable_compProd_iff hf.aestronglyMeasurable).1 i_f with ⟨i_f1, -⟩
  · apply integral_congr_ae
    filter_upwards [i_f1, i_f'.1]
    intro x hx1 hx2
    rw [ionescu_eq, kernel.map_apply, integral_map, kernel.prod_apply, integral_prod,
      kernel.integral_deterministic', integral_map, integral_prod,
      kernel.integral_deterministic']
    · congr with y
      rw [projel']
      rfl
    · apply StronglyMeasurable.integral_prod_right'
        (f := fun p ↦ f x (el' b p))
      exact hf.of_uncurry_left.comp_measurable (el' b).measurable
    · conv => enter [1]; change (fun y ↦ f x y) ∘ (el' b)
      rw [← integrable_map_equiv (el' b) (fun y ↦ f x y), ← kernel.prod_apply, ← kernel.map_apply,
        ← ionescu_eq]
      exact hx1
    · exact (el' b).measurable.aemeasurable
    · exact hf.of_uncurry_left.aestronglyMeasurable
    · apply StronglyMeasurable.integral_prod_right'
        (f := fun p ↦ f (proj b ((el' b) p)) (el' b p))
      apply hf.comp_measurable (g := fun p ↦ (proj b ((el' b) p), el' b p))
      exact Measurable.prod_mk ((meas_proj b).comp (el' b).measurable) (el' b).measurable
    · conv => enter [1]; change f.uncurry ∘ (fun x ↦ (proj b x, x)) ∘ (el' b)
      rw [← comp.assoc, ← integrable_map_equiv (el' b), ← kernel.prod_apply, ← kernel.map_apply,
        ← ionescu_eq]
      exact hx2
    · exact (el' b).measurable.aemeasurable
    · refine (hf.comp_measurable (g := fun p ↦ (proj b p, p)) ?_).aestronglyMeasurable
      exact Measurable.prod_mk (meas_proj b) measurable_id
  · exact hf.aestronglyMeasurable
  · exact ((meas_proj b).prod_mk measurable_id).aemeasurable
  · exact (hf.comp_measurable <| (meas_proj b).prod_mk measurable_id).aestronglyMeasurable
  · rwa [partialKernel_comp_ionescuTulceaKernel _ hab]

theorem integrable_ionescu {a b : ℕ} (hab : a ≤ b) {f : ((n : ℕ) → X n) → E}
    (x₀ : (i : Iic a) → X i)
    (i_f : Integrable f (ionescuTulceaKernel κ a x₀)) :
    ∀ᵐ x ∂ionescuTulceaKernel κ a x₀, Integrable f (ionescuTulceaKernel κ b (proj b x)) := by
  rw [← partialKernel_comp_ionescuTulceaKernel _ hab, kernel.integrable_comp] at i_f
  · apply ae_of_ae_map (p := fun x ↦ Integrable f (ionescuTulceaKernel κ b x))
    · exact (meas_proj b).aemeasurable
    · convert i_f.1
      rw [← ionescuTulceaKernel_proj, kernel.map_apply]
  · exact i_f.aestronglyMeasurable

theorem condexp_ionescu
    {a b : ℕ} (hab : a ≤ b) (x₀ : (i : Iic a) → X i) {f : ((n : ℕ) → X n) → E}
    (i_f : Integrable f (ionescuTulceaKernel κ a x₀)) (mf : StronglyMeasurable f) :
    ((ionescuTulceaKernel κ a) x₀)[f|ℱ b] =ᵐ[ionescuTulceaKernel κ a x₀]
      fun x ↦ ∫ y, f y ∂ionescuTulceaKernel κ b (proj b x) := by
  refine (ae_eq_condexp_of_forall_setIntegral_eq _ i_f ?_ ?_ ?_).symm
  · intro s ms hs
    apply Integrable.integrableOn
    conv => enter [1]; change (fun x ↦ ∫ y, f y ∂ionescuTulceaKernel κ b x) ∘ (proj b)
    rw [← partialKernel_comp_ionescuTulceaKernel κ hab, kernel.integrable_comp] at i_f
    · rw [← integrable_map_measure, ← kernel.map_apply, ionescuTulceaKernel_proj, ← integrable_norm_iff]
      · apply i_f.2.mono'
        · apply AEStronglyMeasurable.norm
          exact (mf.comp_measurable measurable_snd).integral_kernel_prod_right'.aestronglyMeasurable
        · refine eventually_of_forall fun x ↦ ?_
          rw [norm_norm]
          exact norm_integral_le_integral_norm _
      · exact (mf.comp_measurable measurable_snd).integral_kernel_prod_right'.aestronglyMeasurable
      · exact (mf.comp_measurable measurable_snd).integral_kernel_prod_right'.aestronglyMeasurable
      · exact (meas_proj b).aemeasurable
    · exact mf.aestronglyMeasurable
  · intro s ms hs
    rcases ms with ⟨t, mt, rfl⟩
    rw [← integral_indicator]
    · have this x : ((proj b) ⁻¹' t).indicator
          (fun x ↦ ∫ y, f y ∂ionescuTulceaKernel κ b (proj b x)) x =
          t.indicator (fun x ↦ ∫ y, f y ∂ionescuTulceaKernel κ b x) ((proj b) x) :=
        Set.indicator_comp_right (proj b) (g := fun x ↦ ∫ y, f y ∂ionescuTulceaKernel κ b x)
      simp_rw [this]
      rw [← integral_map, ← kernel.map_apply, ionescuTulceaKernel_proj κ,]
      simp_rw [Set.indicator_one_smul_apply (M := ℝ)
        (fun x ↦ ∫ y, f y ∂ionescuTulceaKernel κ b x), ← integral_smul]
      · rw [← partialKernel_comp_ionescuTulceaKernel_apply _ hab, ← integral_indicator]
        · congr with x
          by_cases h : proj b x ∈ t <;> simp [h]
        · exact meas_proj b mt
        · rw [uncurry_def]
          apply StronglyMeasurable.smul
          · exact (stronglyMeasurable_const.indicator mt).comp_measurable measurable_fst
          · exact mf.comp_measurable measurable_snd
        · simp_rw [← Set.indicator_comp_right, comp, ← Set.indicator_one_smul_apply]
          exact i_f.indicator (meas_proj b mt)
      · exact (meas_proj b).aemeasurable
      · refine (StronglyMeasurable.indicator ?_ mt).aestronglyMeasurable
        exact (mf.comp_measurable measurable_snd).integral_kernel_prod_right'
    · exact meas_proj b mt
  · conv => enter [2]; change (fun x ↦ ∫ y, f y ∂ionescuTulceaKernel κ b x) ∘ (proj b)
    apply AEStronglyMeasurable.comp_ae_measurable'
    · exact (mf.comp_measurable measurable_snd).integral_kernel_prod_right'.aestronglyMeasurable
    · exact (meas_proj b).aemeasurable

theorem condexp_ionescu' {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) (x₀ : (i : Iic a) → X i)
    {f : ((n : ℕ) → X n) → E} :
    (ionescuTulceaKernel κ a x₀)[f|ℱ b] =ᵐ[ionescuTulceaKernel κ a x₀]
      fun x ↦ ∫ y, ((ionescuTulceaKernel κ a x₀)[f|ℱ c]) (updateFinset x _ y)
        ∂partialKernel κ b c (proj b x) := by
  have i_cf : Integrable ((ionescuTulceaKernel κ a x₀)[f|ℱ c])
      (ionescuTulceaKernel κ a x₀) := integrable_condexp
  have mcf : StronglyMeasurable ((ionescuTulceaKernel κ a x₀)[f|ℱ c]) :=
    stronglyMeasurable_condexp.mono (ℱ.le c)
  filter_upwards [ℱ.condexp_condexp f hbc, condexp_ionescu κ hab x₀ i_cf mcf]
  intro x h1 h2
  rw [← h1, h2, ← ionescuTulceaKernel_proj, kernel.map_apply, integral_map]
  · congr with y
    apply measurable_dependsOn stronglyMeasurable_condexp
    simp [updateFinset, proj]
    exact fun i hi ↦ (if_pos hi).symm
  · exact (meas_proj c).aemeasurable
  · exact ((stronglyMeasurable_condexp.mono (ℱ.le c)).comp_measurable
      measurable_updateFinset).aestronglyMeasurable
