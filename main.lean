import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.KolmogorovExtension4.Projective
import Mathlib.KolmogorovExtension4.KolmogorovExtension
import Mathlib.Topology.Defs.Filter
-- import Mathlib.KolmogorovExtension4.section_file
import Mathlib.KolmogorovExtension4.DependsOn
import Mathlib.MeasureTheory.Integral.Marginal
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

open Set MeasureTheory Filter Topology ENNReal Finset symmDiff BigOperators

variable {ι : Type*} {α : ι → Type*}

/--  -/
theorem preimage_proj (I J : Finset ι) [∀ i : ι, Decidable (i ∈ I)]
    (hIJ : I ⊆ J) (s : (i : I) → Set (α i)) :
    (fun t : (∀ j : J, α j) ↦ fun i : I ↦ t ⟨i, hIJ i.2⟩) ⁻¹' (univ.pi s) =
    (@Set.univ J).pi (fun j ↦ if h : j.1 ∈ I then s ⟨j.1, h⟩ else univ) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Subtype.forall]
  refine ⟨fun h i hi ↦ ?_, fun h i i_mem ↦ by simpa [i_mem] using h i (hIJ i_mem)⟩
  split_ifs with i_mem
  · simp [i_mem, h i i_mem]
  · simp [i_mem]

variable {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
variable (μ : (i : ι) → Measure (X i)) [hμ : ∀ i, IsProbabilityMeasure (μ i)]

/-- Consider a family of probability measures. You can take their products for any fimite
subfamily. This gives a projective family of measures, see `IsProjectiveMeasureFamily`. -/
theorem isProjectiveMeasureFamily_pi :
    IsProjectiveMeasureFamily (fun I : Finset ι ↦ (Measure.pi (fun i : I ↦ μ i))) := by
  classical
  intro I J hJI
  refine Measure.pi_eq (fun s ms ↦ ?_)
  rw [Measure.map_apply (measurable_proj₂' (α := X) I J hJI) (MeasurableSet.univ_pi ms),
    preimage_proj J I hJI, Measure.pi_pi]
  have h1 : (@Finset.univ I _).prod (fun i ↦ (μ i) (if hi : i.1 ∈ J then s ⟨i.1, hi⟩ else univ)) =
      (@Finset.univ I.toSet _).prod
      (fun i ↦ (fun j ↦ (μ j) (if hj : j ∈ J then s ⟨j, hj⟩ else univ)) i) :=
    Finset.prod_congr rfl (by simp)
  have h2 : (@Finset.univ J _).prod (fun i ↦ (μ i) (s i)) =
      (@Finset.univ J.toSet _).prod
      (fun i ↦ (fun j ↦ (μ j) (if hj : j ∈ J then s ⟨j, hj⟩ else univ)) i) :=
    Finset.prod_congr rfl (by simp)
  rw [h1, h2, Finset.prod_set_coe
      (f := fun i ↦ (fun j ↦ (μ j) (if hj : j ∈ J then s ⟨j, hj⟩ else univ)) i),
    Finset.prod_set_coe
      (f := fun i ↦ (fun j ↦ (μ j) (if hj : j ∈ J then s ⟨j, hj⟩ else univ)) i),
    Finset.toFinset_coe, Finset.toFinset_coe,
    Finset.prod_subset hJI (fun _ h h' ↦ by simp [h, h'])]

/-- The indicator function of a cylinder only depends on the coordinates used
to build this cylinder. -/
theorem dependsOn_cylinder_indicator (I : Finset ι) (S : Set ((i : I) → X i)) :
    DependsOn ((cylinder I S).indicator (1 : ((i : ι) → X i) → ℝ≥0∞)) I := by
  intro x y hxy
  have : x ∈ cylinder I S ↔ y ∈ cylinder I S := by simp [hxy]
  by_cases h : x ∈ cylinder I S
  · simp [h, this.1 h]
  · simp [h, this.not.1 h]

/-- The `kolContent` of `cylinder I S` can be computed by integrating the indicator of
`cylinder I S` over the variables indexed by `I`. -/
theorem kolContent_eq_lmarginal [DecidableEq ι] [∀ (S : Finset ι) i, Decidable (i ∈ S)]
    (I : Finset ι) {S : Set ((i : I) → X i)} (mS : MeasurableSet S) (x : (i : ι) → X i) :
    kolContent (isProjectiveMeasureFamily_pi μ) (cylinder I S) =
    (∫⋯∫⁻_I, (cylinder I S).indicator 1 ∂μ) x := by
  rw [kolContent_congr (isProjectiveMeasureFamily_pi μ)
      (by rw [mem_cylinders]; exact ⟨I, S, mS, rfl⟩) rfl mS,
    ← lintegral_indicator_one₀ mS.nullMeasurableSet]
  refine lintegral_congr <| fun x ↦ ?_
  by_cases hx : x ∈ S <;> simp [hx, Function.updateFinset]

theorem Finset.Icc_eq_left_union (h : k ≤ N) : Finset.Icc k N = {k} ∪ (Finset.Icc (k + 1) N) := by
  ext x
  simp only [mem_Icc, mem_union, mem_singleton]
  refine ⟨fun ⟨h1, h2⟩ ↦ ?_, ?_⟩
  · by_cases hxk : x = k
    · exact Or.inl hxk
    · exact Or.inr ⟨Nat.succ_le_of_lt <| Nat.lt_of_le_of_ne h1 (fun h ↦ hxk h.symm), h2⟩
  · rintro (h1 | ⟨h2, h3⟩)
    · exact ⟨h1 ▸ le_refl _, h1 ▸ h⟩
    · exact ⟨Nat.le_of_succ_le h2, h3⟩

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]

/-- Any cylinder index by natural integers can be seen as depending on the first coordinates. -/
theorem cylinders_nat :
    cylinders X = ⋃ (N) (S) (_ : MeasurableSet S), {cylinder (Icc 0 N) S} := by
  ext s
  simp only [mem_cylinders, exists_prop, mem_iUnion, mem_singleton_iff]
  constructor
  · rintro ⟨t, S, mS, rfl⟩
    refine ⟨t.sup id, (fun (f : ((n : Finset.Icc 0 (t.sup id)) → X n)) (k : t) ↦
      f ⟨k.1, Finset.mem_Icc.2 ⟨Nat.zero_le k.1, Finset.le_sup (f := id) k.2⟩⟩) ⁻¹' S,
      by measurability, ?_⟩
    dsimp only [cylinder]
    rw [← preimage_comp]
    rfl
  · rintro ⟨N, S, mS, rfl⟩
    exact ⟨Finset.Icc 0 N, S, mS, rfl⟩

variable (μ : (n : ℕ) → Measure (X n)) [hμ : ∀ n, IsProbabilityMeasure (μ n)]

/-- Auxiliary result for `firstLemma`: Consider $f$ is a sequence of bounded measurable functions
which only depend on the first coordinates. Assume that when integrating $f_n$
over all the variables except the first $k + 1$ one gets a non-increasing sequence of functions
wich converges to $l$. Assume then that there exists $\epsilon$ and $y_0, ..., y_{k-1}$ such that
when integrating $f_n (y_0, ..., y_{k-1}, \cdot)$ you get something at least $\epsilon$ for all
$n$.
Then there exists $z$ such that this remains true when integrating
$f_n (y_0, ..., y_{k-1}, z, \cdot)$. -/
theorem auxiliaire (f : ℕ → (∀ n, X n) → ℝ≥0∞) (N : ℕ → ℕ)
    (hcte : ∀ n, DependsOn (f n) (Finset.Icc 0 (N n))) (mf : ∀ n, Measurable (f n))
    (bound : ℝ≥0∞) (fin_bound : bound ≠ ∞) (le_bound : ∀ n x, f n x ≤ bound) (k : ℕ)
    (anti : ∀ x, Antitone (fun n ↦ (∫⋯∫⁻_Finset.Icc (k + 1) (N n), f n ∂μ) x))
    (l : ((n : ℕ) → X n) → ℝ≥0∞)
    (htendsto : ∀ x, Tendsto (fun n ↦ (∫⋯∫⁻_Finset.Icc (k + 1) (N n), f n ∂μ) x) atTop (𝓝 (l x)))
    (ε : ℝ≥0∞)
    (y : (n : Finset.Ico 0 k) → X n)
    (hpos : ∀ x, ∀ n,
    ε ≤ (∫⋯∫⁻_Finset.Icc k (N n), f n ∂μ) (Function.updateFinset x (Finset.Ico 0 k) y)) :
    ∃ z, ∀ x n, ε ≤ (∫⋯∫⁻_Finset.Icc (k + 1) (N n), f n ∂μ)
    (Function.update (Function.updateFinset x (Finset.Ico 0 k) y) k z) := by
  -- The measurable spaces are not empty.
  have : ∀ n, Nonempty (X n) := by
    have := fun n ↦ ProbabilityMeasure.nonempty ⟨μ n, hμ n⟩;
    infer_instance
  -- Shorter name for integrating over all the variables except the first `k + 1`.
  let F : ℕ → (∀ n, X n) → ℝ≥0∞ := fun n ↦ (∫⋯∫⁻_Finset.Icc (k + 1) (N n), f n ∂μ)
  -- `Fₙ` converges to `l` by hypothesis.
  have tendstoF x : Tendsto (F · x) atTop (𝓝 (l x)) := htendsto x
  -- Integrating `fₙ` over all the variables except the first `k` is the same as integrating
  -- `Fₙ` over the `k`-th variable.
  have f_eq x n : (∫⋯∫⁻_Finset.Icc k (N n), f n ∂μ) x = (∫⋯∫⁻_{k}, F n ∂μ) x := by
    by_cases h : k ≤ N n
    · rw [Finset.Icc_eq_left_union h, lmarginal_union _ _ (mf n) (by simp)]
    · have : ¬k + 1 ≤ N n := fun h' ↦ h <| le_trans k.le_succ h'
      simp only [F]
      rw [Finset.Icc_eq_empty h, Finset.Icc_eq_empty this,
        lmarginal_eq_of_disjoint (hcte n) (by simp),
        lmarginal_eq_of_disjoint (hcte n) (by simp [h])]
  -- `F` is also a bounded sequence.
  have F_le n x : F n x ≤ bound := by
    rw [← lmarginal_const (μ := μ) (s := Finset.Icc (k + 1) (N n)) bound x]
    apply lmarginal_mono <| le_bound n
  -- By dominated convergence, the integral of `fₙ` with respect to all the variable except
  -- the `k` first converges to the integral of `l`.
  have tendsto_int x : Tendsto (fun n ↦ (∫⋯∫⁻_Finset.Icc k (N n), f n ∂μ) x) atTop
      (𝓝 ((∫⋯∫⁻_{k}, l ∂μ) x)) := by
    simp_rw [f_eq, lmarginal_singleton]
    exact tendsto_lintegral_of_dominated_convergence (fun _ ↦ bound)
      (fun n ↦ ((mf n).lmarginal μ).comp <| measurable_update ..)
      (fun n ↦ eventually_of_forall <| fun y ↦ F_le n _)
      (by simp [fin_bound])
      (eventually_of_forall (fun _ ↦ tendstoF _))
  -- By hypothesis, we have `ε ≤ ∫ F(y, xₖ) ∂μₖ`, so this is also true for `l`.
  have ε_le_lint x : ε ≤ (∫⋯∫⁻_{k}, l ∂μ) (Function.updateFinset x _ y) :=
    ge_of_tendsto (tendsto_int _) (by simp [hpos])
  -- Same statement but with a true integral.
  have this x : ε ≤ ∫⁻ xₐ : X k, l (Function.update (Function.updateFinset x _ y) k xₐ) ∂μ k := by
    simpa [lmarginal_singleton] using ε_le_lint x
  -- Previous results were stated for constant `lmarginal`s, but in order to get an element we
  -- have to specialize them to some element (any of them as the integral is constant).
  let x_ : (n : ℕ) → X n := Classical.ofNonempty
  -- We now have that the integral of `l` with respect to a probability measure is greater than `ε`,
  -- therefore there exists `x'` such that `ε ≤ l(y, x')`.
  obtain ⟨x', hx'⟩ : ∃ x', ε ≤ l (Function.update (Function.updateFinset x_ _ y) k x') := by
    simp_rw [lmarginal_singleton] at ε_le_lint
    have aux : ∫⁻ (a : X k), l (Function.update (Function.updateFinset x_ _ y) k a) ∂μ k ≠ ⊤ := by
      apply ne_top_of_le_ne_top fin_bound
      rw [← mul_one bound, ← measure_univ (μ := μ k), ← lintegral_const]
      exact lintegral_mono <| fun y ↦ le_of_tendsto' (tendstoF _) <| fun _ ↦ F_le _ _
    rcases exists_lintegral_le aux with ⟨x', hx'⟩
    exact ⟨x', le_trans (this _) hx'⟩
  refine ⟨x', fun x n ↦ ?_⟩
  -- As `F` is a non-increasing sequence, we have `ε ≤ Fₙ(y, x')` for any `n`.
  have := le_trans hx' ((anti _).le_of_tendsto (tendstoF _) n)
  -- This part below is just to say that this is true for any `x : (i : ι) → X i`,
  -- as `Fₙ` technically depends on all the variables, but really depends only on the first `k + 1`.
  have aux : F n (Function.update (Function.updateFinset x_ (Finset.Ico 0 k) y) k x') =
      F n (Function.update (Function.updateFinset x (Finset.Ico 0 k) y) k x') := by
    simp only [F]
    have := dependsOn_lmarginal (μ := μ) (hcte n) (Finset.Icc (k + 1) (N n))
    rw [← coe_sdiff] at this
    have := dependsOn_updateFinset (dependsOn_update this k x') (Finset.Ico 0 k) y
    have aux : (Finset.Icc 0 (N n) \ Finset.Icc (k + 1) (N n)).erase k \ Finset.Ico 0 k = ∅ := by
      ext i
      simp only [Nat.Ico_zero_eq_range, mem_sdiff, mem_erase, ne_eq, Finset.mem_Icc, zero_le,
        true_and, not_and, not_le, Finset.mem_range, not_lt, Finset.not_mem_empty, iff_false,
        and_imp]
      intro h1 h2 h3
      refine lt_iff_le_and_ne.2 ⟨?_, h1⟩
      by_contra!
      rw [← Nat.succ_le] at this
      exact (lt_iff_not_le.1 (h3 this)) h2
    rw [← coe_sdiff, aux, coe_empty] at this
    apply dependsOn_empty this
  simp only [F] at aux
  rw [aux] at this
  exact this

/-- An auxiliary definition to prove `firstLemma`: If for any $k$, given $(x_0, ..., x_{k-1})$
one can construct $x_k = \text{ind}(x_0, .., x_{k-1})$, then one can construct a sequence $(x_k)$
such that for all $k$, $x_k = \text{ind}(x_0, .., x_{k-1})$. -/
def key (ind : (k : ℕ) → ((i : Finset.Ico 0 k) → X i) → X k) : (k : ℕ) → X k := fun k ↦ by
  use ind k (fun i ↦ key ind i)
  decreasing_by
  exact (Finset.mem_Ico.1 i.2).2

/-- This is the key theorem to prove the existence of the product measure: the `kolContent` of
a decresaing sequence of cylinders with empty intersection converges to $0$, in the case where
the measurable spaces are indexed by $\mathbb{N}$. This implies the $\sigma$-additivity of
`kolContent` (see `sigma_additive_addContent_of_tendsto_zero`),
which allows to extend it to the $\sigma$-algebra by Carathéodory's theorem. -/
theorem firstLemma (A : ℕ → Set ((n : ℕ) → X n)) (A_mem : ∀ n, A n ∈ cylinders X)
    (A_anti : Antitone A) (A_inter : ⋂ n, A n = ∅) :
    Tendsto (fun n ↦ kolContent (isProjectiveMeasureFamily_pi μ) (A n)) atTop (𝓝 0) := by
  -- The measurable spaces are not empty.
  have : ∀ n, Nonempty (X n) := by
    have := fun n ↦ ProbabilityMeasure.nonempty ⟨μ n, hμ n⟩;
    infer_instance
  -- `Aₙ` is a cylinder, it can be writtent `cylinder sₙ Sₙ`.
  have A_cyl n : ∃ N S, MeasurableSet S ∧ A n = cylinder (Finset.Icc 0 N) S := by
    simpa [cylinders_nat] using A_mem n
  choose N S mS A_eq using A_cyl
  set μ_proj := isProjectiveMeasureFamily_pi μ
  -- We write `χₙ` for the indicator function of `Aₙ`.
  let χ n := (A n).indicator (1 : (∀ n, X n) → ℝ≥0∞)
  -- `χₙ` is measurable.
  have mχ n : Measurable (χ n) := by
    simp_rw [χ, A_eq]
    exact (measurable_indicator_const_iff 1).2 <| measurableSet_cylinder _ _ (mS n)
  -- `χₙ` only depends on the first coordinates.
  have χ_dep n : DependsOn (χ n) (Finset.Icc 0 (N n)) := by
    simp_rw [χ, A_eq]
    exact dependsOn_cylinder_indicator _ _
  -- Therefore its integral is constant.
  have lma_const x y n : (∫⋯∫⁻_Finset.Icc 0 (N n), χ n ∂μ) x =
      (∫⋯∫⁻_Finset.Icc 0 (N n), χ n ∂μ) y := by
    apply dependsOn_lmarginal (μ := μ) (χ_dep n) (Finset.Icc 0 (N n))
    simp
  -- As `(Aₙ)` is non-increasing, so is `(χₙ)`.
  have χ_anti : Antitone χ := by
    intro m n hmn y
    apply indicator_le
    exact fun a ha ↦ by simp [χ, A_anti hmn ha]
  -- Integrating `χₙ` further than the last coordinate it depends on does nothing.
  -- This is used to then show that the integral of `χₙ` over all the variables except the first
  -- `k` ones is non-increasing.
  have lma_inv k M n (h : N n ≤ M) :
      ∫⋯∫⁻_Finset.Icc k M, χ n ∂μ = ∫⋯∫⁻_Finset.Icc k (N n), χ n ∂μ := by
    apply lmarginal_eq_of_disjoint_diff (mχ n) (χ_dep n) (Finset.Icc_subset_Icc_right h)
    rw [← coe_sdiff, Finset.disjoint_coe, Finset.disjoint_iff_inter_eq_empty]
    ext i
    simp only [Finset.mem_inter, Finset.mem_Icc, zero_le, true_and, mem_sdiff, not_and, not_le,
      Finset.not_mem_empty, iff_false, Classical.not_imp, not_lt, and_imp]
    exact fun h1 h2 _ ↦ ⟨h2, h1⟩
  -- the integral of `χₙ` over all the variables except the first `k` ones is non-increasing.
  have anti_lma k x : Antitone fun n ↦ (∫⋯∫⁻_Finset.Icc k (N n), χ n ∂μ) x := by
    intro m n hmn
    simp only
    rw [← lma_inv k ((N n).max (N m)) n (le_max_left _ _),
      ← lma_inv k ((N n).max (N m)) m (le_max_right _ _)]
    exact lmarginal_mono (χ_anti hmn) x
  -- Therefore it converges to some function `lₖ`.
  have this k x : ∃ l, Tendsto (fun n ↦ (∫⋯∫⁻_Finset.Icc k (N n), χ n ∂μ) x) atTop (𝓝 l) := by
    rcases tendsto_of_antitone <| anti_lma k x with h | h
    · rw [OrderBot.atBot_eq] at h
      exact ⟨0, h.mono_right <| pure_le_nhds 0⟩
    · exact h
  choose l hl using this
  -- `l₀` is constant because it is the limit of constant functions: we call it `ε`.
  have l_const x y : l 0 x = l 0 y := by
    have := hl 0 x
    simp_rw [lma_const x y] at this
    exact tendsto_nhds_unique this (hl 0 _)
  obtain ⟨ε, hε⟩ : ∃ ε, ∀ x, l 0 x = ε := ⟨l 0 Classical.ofNonempty, fun x ↦ l_const ..⟩
  -- As the sequence is decreasing, `ε ≤ ∫ χₙ`.
  have hpos x n : ε ≤ (∫⋯∫⁻_Finset.Icc 0 (N n), χ n ∂μ) x :=
    hε x ▸ ((anti_lma 0 _).le_of_tendsto (hl 0 _)) n
  -- Also, the indicators are bounded by `1`.
  have χ_le n x : χ n x ≤ 1 := by
    apply Set.indicator_le
    simp
  -- We have all the conditions to apply àuxiliaire. This allows us to recursively
  -- build a sequence `(zₙ)` with the following crucial property: for any `k` and `n`,
  -- `ε ≤ ∫ χₙ(z₀, ..., z_{k-1}) ∂(μₖ ⊗ ... ⊗ μ_{Nₙ})`.
  choose! ind hind using
    fun k y h ↦ auxiliaire μ χ N χ_dep mχ 1 (by norm_num) χ_le k (anti_lma (k + 1))
      (l (k + 1)) (hl (k + 1)) ε y h
  let z := key ind
  have crucial : ∀ k x n, ε ≤ (∫⋯∫⁻_Finset.Icc k (N n), χ n ∂μ)
      (Function.updateFinset x (Finset.Ico 0 k) (fun i ↦ z i)) := by
    intro k
    induction k with
    | zero =>
      intro x n
      rw [Finset.Ico_self 0, Function.updateFinset_empty]
      exact hpos x n
    | succ m hm =>
      intro x n
      have : Function.updateFinset x (Finset.Ico 0 (m + 1)) (fun i ↦ z i) =
          Function.update (Function.updateFinset x (Finset.Ico 0 m) (fun i ↦ z i))
          m (z m) := by
        ext i
        simp [Function.updateFinset, Function.update]
        split_ifs with h1 h2 h3 h4 h5
        · subst h2
          rfl
        · rfl
        · rw [Nat.lt_succ] at h1
          exact (not_or.2 ⟨h2, h3⟩ <| le_iff_eq_or_lt.1 h1).elim
        · rw [h4] at h1
          exfalso
          linarith
        · exact (h1 <| lt_trans h5 m.lt_succ_self).elim
        · rfl
      rw [this]
      convert hind m (fun i ↦ z i) hm x n
      cases m with | zero | succ _ => rfl
  -- We now want to prove that the integral of `χₙ` converges to `0`.
  have concl x n : kolContent μ_proj (A n) = (∫⋯∫⁻_Finset.Icc 0 (N n), χ n ∂μ) x := by
    simp_rw [χ, A_eq]
    exact kolContent_eq_lmarginal μ (Finset.Icc 0 (N n)) (mS n) x
  simp_rw [concl Classical.ofNonempty]
  convert hl 0 Classical.ofNonempty
  rw [hε]
  by_contra!
  -- Which means that we want to prove that `ε = 0`. But if `ε > 0`, then for any `n`,
  -- choosing `k > Nₙ` we get `ε ≤ χₙ(z₀, ..., z_{Nₙ})` and therefore `(z n) ∈ Aₙ`.
  -- This contradicts the fact that `(Aₙ)` has an empty intersection.
  have ε_pos : 0 < ε := this.symm.bot_lt
  have incr : ∀ n, z ∈ A n := by
    intro n
    have : χ n (z) = (∫⋯∫⁻_Finset.Icc (N n + 1) (N n), χ n ∂μ)
        (Function.updateFinset (z) (Finset.Ico 0 (N n + 1)) (fun i ↦ z i)) := by
      rw [Finset.Icc_eq_empty (by simp), lmarginal_empty]
      congr
      ext i
      by_cases h : i ∈ Finset.Ico 0 (N n + 1) <;> simp [Function.updateFinset, h]
    have : 0 < χ n (z) := by
      rw [this]
      exact lt_of_lt_of_le ε_pos (crucial (N n + 1) (z) n)
    exact mem_of_indicator_ne_zero (ne_of_lt this).symm
  exact (A_inter ▸ mem_iInter.2 incr).elim

variable {X : ι → Type*} [hX : ∀ i, MeasurableSpace (X i)]
variable (μ : (i : ι) → Measure (X i)) [hμ : ∀ i, IsProbabilityMeasure (μ i)]

lemma omg (s : Set ι) (x : (i : s) → X i) (i j : s) (h : i = j) (h' : X i = X j) :
    cast h' (x i) = x j := by
  subst h
  rfl

lemma omg' (α β : Type _) (h : α = β) (a : α) (s : Set α) (h' : Set α = Set β) :
    (cast h a ∈ cast h' s) = (a ∈ s) := by
  subst h
  rfl

/-- This theorem is used to prove the existence of the product measure: the `kolContent` of
a decresaing sequence of cylinders with empty intersection converges to $0$, in the case where
the measurable spaces are indexed by a countable type. This implies the $\sigma$-additivity of
`kolContent` (see `sigma_additive_addContent_of_tendsto_zero`),
which allows to extend it to the $\sigma$-algebra by Carathéodory's theorem. -/
theorem secondLemma
    (φ : ℕ ≃ ι) (A : ℕ → Set ((i : ι) → X i)) (A_mem : ∀ n, A n ∈ cylinders X)
    (A_anti : Antitone A) (A_inter : ⋂ n, A n = ∅) :
    Tendsto (fun n ↦ kolContent (isProjectiveMeasureFamily_pi μ) (A n)) atTop (𝓝 0) := by
  have : ∀ i, Nonempty (X i) := by
    have := fun i ↦ ProbabilityMeasure.nonempty ⟨μ i, hμ i⟩;
    infer_instance
  set μ_proj := isProjectiveMeasureFamily_pi μ
  let μ_proj' := isProjectiveMeasureFamily_pi (fun k : ℕ ↦ μ (φ k))
  have A_cyl n : ∃ s S, MeasurableSet S ∧ A n = cylinder s S := by
    simpa only [mem_cylinders, exists_prop] using A_mem n
  choose s S mS A_eq using A_cyl
  -- The goal of the proof is to apply the same result when the index set is `ℕ`. To do so we
  -- have to pull back the sets `sₙ` and `Sₙ` using equivalences.
  let t n := (s n).preimage φ (φ.injective.injOn _)
  have h i : X (φ (φ.symm i)) = X i := congrArg X (φ.apply_symm_apply i)
  have e n i (h : i ∈ s n) : φ.symm i ∈ t n := by simpa [t] using h
  have e' n k (h : k ∈ t n) : φ k ∈ s n := by simpa [t] using h
  -- The function `f` does the link between families indexed by `ℕ` and those indexed by `ι`.
  -- Here we have to use `cast` because otherwhise we land in `X (φ (φ.symm i))`, which is not
  -- definitionally equal to X i.
  let f : ((k : ℕ) → X (φ k)) → (i : ι) → X i := fun x i ↦ cast (h i) (x (φ.symm i))
  -- `aux n` is an equivalence between `sₙ` ans `tₙ`, it will be used to link the two.
  let aux n : s n ≃ t n :=
    { toFun := fun i ↦ ⟨φ.symm i, e n i.1 i.2⟩
      invFun := fun k ↦ ⟨φ k, e' n k.1 k.2⟩
      left_inv := by simp [Function.LeftInverse]
      right_inv := by simp [Function.RightInverse, Function.LeftInverse] }
  -- `gₙ` is the equivalent of `f` for families indexed by `tₙ` and `sₙ`.
  let g n : ((k : t n) → X (φ k)) → (i : s n) → X i :=
    fun x i ↦ cast (h i) (x (aux n i))
  -- Transfering from `ℕ` to `ι` and then projecting on `sₙ` is the same as first
  -- projecting on `uₙ` and then transfering to `ι`.
  have test n : (fun (x : (i : ι) → X i) (i : s n) ↦ x i) ∘ f =
      (g n) ∘ (fun (x : (k : ℕ) → X (φ k)) (k : t n) ↦ x k) := by
    ext x
    simp [f, g, aux]
  -- Now fe define `Bₙ` and `Tₙ` as follows. `Bₙ` is a cylinder.
  let B n := f ⁻¹' (A n)
  let T n := (g n) ⁻¹' (S n)
  have B_eq n : B n = cylinder (t n) (T n) := by
    simp_rw [B, A_eq, cylinder, ← preimage_comp, test n]
    rfl
  -- `gₙ` is measurable. We have to play with `Heq` to prove measurability of `cast`.
  have mg n : Measurable (g n) := by
    simp only [g]
    refine measurable_pi_lambda _ (fun i ↦ ?_)
    have : (fun c : (k : t n) → X (φ k) ↦ cast (h i) (c (aux n i))) =
        ((fun a ↦ cast (h i) a) ∘ (fun x ↦ x (aux n i))) := by
      ext x
      simp
    rw [this]
    apply Measurable.comp
    · have aux1 : HEq (hX i) (hX (φ (φ.symm i))) := by
        rw [← cast_eq_iff_heq (e := by simp [h i])]
        exact @omg ι (fun i ↦ MeasurableSpace (X i)) (s n) (fun i ↦ hX i)
          i ⟨φ (φ.symm i), by simp [i.2]⟩ (by simp) _
      let f := MeasurableEquiv.cast (h i).symm aux1
      have aux2 : (fun a : X (φ (φ.symm i)) ↦ cast (h i) a) = f.symm := by
        ext a
        simp [f, MeasurableEquiv.cast]
      rw [aux2]
      exact f.measurable_invFun
    · exact @measurable_pi_apply (t n) (fun k ↦ X (φ k)) _ _
  -- We deduce that `Tₙ` is measurable.
  have mT n : MeasurableSet (T n) := (mS n).preimage (mg n)
  -- The sequence `(Bₙ)` satisfies the hypotheses of `firstLemma`, we now have to prove that we can
  -- rewrite the goal in terms of `B`.
  have B_anti : Antitone B := fun m n hmn ↦ preimage_mono <| A_anti hmn
  have B_inter : ⋂ n, B n = ∅ := by
    simp_rw [B, ← preimage_iInter, A_inter, Set.preimage_empty]
  have B_mem n : B n ∈ cylinders (fun k ↦ X (φ k)) :=
    (mem_cylinders (B n)).2 ⟨t n, T n, mT n, B_eq n⟩
  -- Taking the preimage of a product indexed by `sₙ` by `gₙ` yields a product indexed by `uₙ`,
  -- again we have to play with `cast`.
  have imp n (u : (i : s n) → Set (X i)) : (g n) ⁻¹' (Set.univ.pi u) =
      Set.univ.pi (fun k : t n ↦ u ⟨φ k, e' n k.1 k.2⟩) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Subtype.forall, g]
    constructor
    · intro h' k hk
      convert h' (φ k) (e' n k hk)
      simp only [Equiv.coe_fn_mk, aux]
      rw [@omg ℕ (fun k ↦ X (φ k)) (t n) x ⟨φ.symm (φ k), by simp [hk]⟩ ⟨k, hk⟩]
      simp
    · intro h' i hi
      convert h' (φ.symm i) (e n i hi)
      simp only [Equiv.coe_fn_mk, aux]
      rw [← @omg ι (fun i ↦ Set (X i)) (s n) u ⟨φ (φ.symm i), by simp [hi]⟩ ⟨i, hi⟩ (by simp) _,
        omg' (X (φ (φ.symm i))) (X i) (by simp) (x ⟨φ.symm i, e n i hi⟩)
          (u ⟨φ (φ.symm i), by simp [hi]⟩) (by simp)]
  -- The pushforward measure of the product measure of `(ν_{φ k})_{k ∈ tₙ}` by `gₙ` is the
  -- product measre of `(∨ᵢ)_{i ∈ sₙ}`.
  have test' n : Measure.pi (fun i : s n ↦ μ i) =
      (Measure.pi (fun k : t n ↦ μ (φ k))).map (g n) := by
    refine Measure.pi_eq (fun x mx ↦ ?_)
    rw [Measure.map_apply (mg n), imp n, Measure.pi_pi,
      Fintype.prod_equiv (aux n).symm _ (fun i ↦ (μ i) (x i))]
    · simp [aux]
    · exact MeasurableSet.pi countable_univ (by simp [mx])
  -- This yields the desired result: the `kolContent` of `Aₙ` is the same as the one of `Bₙ`.
  have crucial n : kolContent μ_proj (A n) = kolContent μ_proj' (B n) := by
    simp_rw [fun n ↦ kolContent_congr μ_proj
      (by rw [mem_cylinders]; exact ⟨s n, S n, mS n, A_eq n⟩) (A_eq n) (mS n),
      fun n ↦ kolContent_congr μ_proj'
      (by rw [mem_cylinders]; exact ⟨t n, T n, mT n, B_eq n⟩) (B_eq n) (mT n), T, test' n]
    rw [Measure.map_apply (mg n) (mS n)]
  simp_rw [crucial]
  refine firstLemma (fun k ↦ μ (φ k)) B B_mem B_anti B_inter

/-- This theorem is used to prove the existence of the product measure: the `kolContent` of
a decresaing sequence of cylinders with empty intersection converges to $0$.
This implies the $\sigma$-additivity of
`kolContent` (see `sigma_additive_addContent_of_tendsto_zero`),
which allows to extend it to the $\sigma$-algebra by Carathéodory's theorem. -/
theorem thirdLemma (A : ℕ → Set (∀ i, X i)) (A_mem : ∀ n, A n ∈ cylinders X) (A_anti : Antitone A)
    (A_inter : ⋂ n, A n = ∅) :
    Tendsto (fun n ↦ kolContent (isProjectiveMeasureFamily_pi μ) (A n)) atTop (𝓝 0) := by
  classical
  have : ∀ i, Nonempty (X i) := by
    have := fun i ↦ ProbabilityMeasure.nonempty ⟨μ i, hμ i⟩
    infer_instance
  set μ_proj := isProjectiveMeasureFamily_pi μ
  have A_cyl n : ∃ s S, MeasurableSet S ∧ A n = cylinder s S := by
    simpa only [mem_cylinders, exists_prop] using A_mem n
  choose s S mS A_eq using A_cyl
  -- The family `(Aₙ)` only depends on a countable set of coordinates, called `u`. Therefore our
  -- goal is to see it as a family indexed by this countable set,
  -- so that we can apply `secondLemma`. The proof is very similar to the previous one, except
  -- that the use of coercions avoids manipulating `cast`, as equalities will hold by `rfl`.
  let u := ⋃ n, (s n).toSet
  -- `tₙ` will be `sₙ` seen as a subset of `u`.
  let t : ℕ → Finset u := fun n ↦ (s n).preimage Subtype.val (Subtype.val_injective.injOn _)
  -- These are a few lemmas to move between `sₙ` and `tₙ`.
  have su n : (s n).toSet ⊆ u := Set.subset_iUnion (fun n ↦ (s n).toSet) n
  have st n i (hi : i ∈ s n) : ⟨i, su n hi⟩ ∈ t n := by simpa [t] using hi
  have ts n i (hi : i ∈ t n) : i.1 ∈ s n := by simpa [t] using hi
  -- This brings again `aux`.
  let aux : (n : ℕ) → (s n ≃ t n) := fun n ↦
    { toFun := fun i ↦ ⟨⟨i.1, su n i.2⟩, st n i i.2⟩
      invFun := fun i ↦ ⟨i.1.1, ts n i i.2⟩
      left_inv := by simp [Function.LeftInverse]
      right_inv := by simp [Function.RightInverse, Function.LeftInverse] }
  have h n (i : s n) : X (aux n i) = X i.1 := rfl
  have imp n (x : (i : s n) → Set (X i)) : Set.univ.pi (fun i : t n ↦ x ((aux n).invFun i)) =
      (fun x i ↦ cast (h n i) (x (aux n i))) ⁻¹' Set.univ.pi x := by
    ext y
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Subtype.forall, Set.mem_preimage]
    exact ⟨fun h i hi ↦ h i (su n hi) (st n i hi), fun h i hi1 hi2 ↦ h i (ts n ⟨i, hi1⟩ hi2)⟩
  have meas n : Measurable (fun (x : (i : t n) → X i) i ↦ cast (h n i) (x (aux n i))) := by
    apply measurable_pi_lambda
    exact fun _ ↦ measurable_pi_apply _
  have crucial n : Measure.pi (fun i : s n ↦ μ i) =
      (Measure.pi (fun i : t n ↦ μ i)).map (fun x i ↦ cast (h n i) (x (aux n i))) := by
    refine Measure.pi_eq (fun x mx ↦ ?_)
    rw [Measure.map_apply (meas n), ← imp n x, Measure.pi_pi, Fintype.prod_equiv (aux n)]
    · simp [aux]
    · exact MeasurableSet.pi countable_univ (by simp [mx])
  let T : (n : ℕ) → Set ((i : t n) → X i) :=
    fun n ↦ (fun x i ↦ cast (h n i) (x (aux n i))) ⁻¹' (S n)
  have mT n : MeasurableSet (T n) := by
    apply (mS n).preimage (meas n)
  let B : ℕ → Set (∀ i : u, X i) := fun n ↦ cylinder (t n) (T n)
  have B_eq n : B n = (fun x : (i : u) → X i ↦ fun i ↦ if hi : i ∈ u
      then x ⟨i, hi⟩ else Classical.ofNonempty) ⁻¹' (A n) := by
    ext x
    simp [B, T, -cast_eq]
    have this k : (fun i : s k ↦ (fun j ↦ if hj : j ∈ u then x ⟨j, hj⟩
        else Classical.ofNonempty) i.1) = fun i ↦ cast (h k i) (x (aux k i)) := by
      ext i
      simp only [i.2, su k i.2, ↓reduceDite, cast_eq]
      rfl
    rw [← this, ← mem_cylinder (s n) (S n) (fun j ↦ if hj : j ∈ u then x ⟨j, hj⟩
        else Classical.ofNonempty), ← A_eq]
  have B_anti : Antitone B := by
    intro m n hmn
    simp_rw [B_eq]
    exact preimage_mono <| A_anti hmn
  have B_inter : ⋂ n, B n = ∅ := by
    simp_rw [B_eq, ← preimage_iInter, A_inter, Set.preimage_empty]
  let μ_proj' := isProjectiveMeasureFamily_pi (fun i : u ↦ μ i)
  have this n : kolContent μ_proj (A n) = kolContent μ_proj' (B n) := by
    simp_rw [fun n ↦ kolContent_congr μ_proj
      (by rw [mem_cylinders]; exact ⟨s n, S n, mS n, A_eq n⟩) (A_eq n) (mS n),
      fun n ↦ kolContent_congr μ_proj'
      (by rw [mem_cylinders]; exact ⟨t n, T n, mT n, rfl⟩) rfl (mT n), T, crucial n]
    rw [Measure.map_apply (meas n) (mS n)]
  simp_rw [this]
  -- We now have two cases: if `u` is finite, then the result is simple because
  -- we have an actual measure.
  rcases finite_or_infinite u with (u_fin | u_inf)
  · have obv : (fun _ ↦ 1 : ((i : u) → X i) → ℝ≥0∞) = 1 := rfl
    have := Fintype.ofFinite u
    have concl n : kolContent μ_proj' (B n) =
        (Measure.pi (fun i : u ↦ μ i)) (cylinder (t n) (T n)) := by
      simp_rw [B,
        fun n ↦ kolContent_eq_lmarginal (fun i : u ↦ μ i) (t n) (mT n) Classical.ofNonempty]
      rw [← lmarginal_eq_of_disjoint_diff (μ := (fun i : u ↦ μ i)) _
          (dependsOn_cylinder_indicator (t n) (T n))
          (t n).subset_univ, lmarginal_univ, ← obv, lintegral_indicator_const]
      · simp
      · exact @measurableSet_cylinder u (fun i : u ↦ X i) _ (t n) (T n) (mT n)
      · rw [Finset.coe_univ, ← compl_eq_univ_diff]
        exact disjoint_compl_right
      · rw [← obv, measurable_indicator_const_iff 1]
        exact @measurableSet_cylinder u (fun i : u ↦ X i) _ (t n) (T n) (mT n)
    simp_rw [concl, ← measure_empty (μ := Measure.pi (fun i : u ↦ μ i)), ← B_inter]
    exact tendsto_measure_iInter (fun n ↦ measurableSet_cylinder (t n) (T n) (mT n))
      B_anti ⟨0, measure_ne_top _ _⟩
  · -- If `u` is infinite, then we have an equivalence with `ℕ` so we can apply `secondLemma`.
    have count_u : Countable u := Set.countable_iUnion (fun n ↦ (s n).countable_toSet)
    obtain ⟨φ, -⟩ := Classical.exists_true_of_nonempty (α := ℕ ≃ u) nonempty_equiv_of_countable
    refine secondLemma (fun i : u ↦ μ i) φ B (fun n ↦ ?_) B_anti B_inter
    simp only [mem_cylinders, exists_prop]
    exact ⟨t n, T n, mT n, rfl⟩

/-- The `kolContent` associated to a family of probability measures is $\simga$-subadditive. -/
theorem kolContent_sigma_subadditive ⦃f : ℕ → Set ((i : ι) → X i)⦄ (hf : ∀ n, f n ∈ cylinders X)
    (hf_Union : (⋃ n, f n) ∈ cylinders X) :
    kolContent (isProjectiveMeasureFamily_pi μ) (⋃ n, f n) ≤
    ∑' n, kolContent (isProjectiveMeasureFamily_pi μ) (f n) := by
  classical
  have : ∀ i, Nonempty (X i) := by
    have := fun i ↦ ProbabilityMeasure.nonempty ⟨μ i, hμ i⟩;
    infer_instance
  refine (kolContent (isProjectiveMeasureFamily_pi μ)).sigma_subadditive_of_sigma_additive
    setRing_cylinders (fun f hf hf_Union hf' ↦ ?_) f hf hf_Union
  refine sigma_additive_addContent_of_tendsto_zero setRing_cylinders
    (kolContent (isProjectiveMeasureFamily_pi μ)) (fun h ↦ ?_) ?_ hf hf_Union hf'
  · rcases (mem_cylinders _).1 h with ⟨s, S, mS, s_eq⟩
    rw [s_eq, kolContent_eq_lmarginal μ (mS := mS) (x := Classical.ofNonempty)]
    refine ne_of_lt (lt_of_le_of_lt ?_ (by norm_num : (1 : ℝ≥0∞) < ⊤))
    rw [← lmarginal_const (μ := μ) (s := s) 1 Classical.ofNonempty]
    apply lmarginal_mono
    intro x
    apply Set.indicator_le
    simp
  · intro s hs anti_s inter_s
    exact thirdLemma μ s hs anti_s inter_s

/-- The product measure of an arbitrary family of probability measures. It is defined as the unique
extension of the function which gives to cylinders the measure given by the assiocated product
measure. -/
noncomputable def measure_produit : Measure ((i : ι) → X i) := by
  exact Measure.ofAddContent setSemiringCylinders generateFrom_cylinders
    (kolContent (isProjectiveMeasureFamily_pi μ))
    (kolContent_sigma_subadditive μ)

/-- The product measure is the projective limit of the partial product measures. This ensures
uniqueness and expresses the value of the product measures applied to cylinders. -/
theorem isProjectiveLimit_measure_produit :
    IsProjectiveLimit (measure_produit μ) (fun I : Finset ι ↦ (Measure.pi (fun i : I ↦ μ i))) := by
  intro I
  ext1 s hs
  rw [Measure.map_apply _ hs]
  swap; · apply measurable_proj
  have h_mem : (fun (x : (i : ι) → X i) (i : I) ↦ x i) ⁻¹' s ∈ cylinders X := by
    rw [mem_cylinders]; exact ⟨I, s, hs, rfl⟩
  rw [measure_produit, Measure.ofAddContent_eq _ _ _ _ h_mem,
    kolContent_congr (isProjectiveMeasureFamily_pi μ) h_mem rfl hs]

instance : IsProbabilityMeasure (measure_produit μ) := by
  constructor
  rw [← cylinder_univ ∅, cylinder, ← Measure.map_apply, isProjectiveLimit_measure_produit μ]
  · simp
  · exact measurable_proj _
  · exact MeasurableSet.univ

theorem measure_boxes {s : Finset ι} {t : (i : ι) → Set (X i)}
    (mt : ∀ i ∈ s, MeasurableSet (t i)) :
    measure_produit μ (pi s t) = ∏ i ∈ s, (μ i) (t i) := by
  classical
  have : pi s t = cylinder s ((@Set.univ s).pi (fun i : s ↦ t i)) := by
    ext x
    simp
  rw [this, cylinder, ← Measure.map_apply, isProjectiveLimit_measure_produit μ,
    Measure.pi_pi]
  · rw [univ_eq_attach, Finset.prod_attach _ (fun i ↦ (μ i) (t i))]
  · exact measurable_proj _
  · apply MeasurableSet.pi countable_univ fun i _ ↦ mt i.1 i.2

theorem measure_cylinder {s : Finset ι} {S : Set ((i : s) → X i)} (mS : MeasurableSet S) :
    measure_produit μ (cylinder s S) = Measure.pi (fun i : s ↦ μ i) S := by
  rw [cylinder, ← Measure.map_apply _ mS, isProjectiveLimit_measure_produit μ]
  exact measurable_proj _

theorem integral_dep {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Finset ι} {f : ((i : s) → X i) → E} (hf : StronglyMeasurable f) :
    ∫ y, f ((fun x (i : s) ↦ x i) y) ∂measure_produit μ =
    ∫ y, f y ∂Measure.pi (fun i : s ↦ μ i) := by
  rw [← integral_map, isProjectiveLimit_measure_produit μ]
  · exact (measurable_proj _).aemeasurable
  · exact hf.aestronglyMeasurable

theorem integral_dependsOn [DecidableEq ι] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Finset ι} {f : ((i : ι) → X i) → E} (mf : StronglyMeasurable f) (hf : DependsOn f s)
    (x : (i : ι) → X i) :
    ∫ y, f y ∂measure_produit μ =
    ∫ y, f (Function.updateFinset x s y) ∂Measure.pi (fun i : s ↦ μ i) := by
  let g : ((i : s) → X i) → E := fun y ↦ f (Function.updateFinset x _ y)
  have this y : g ((fun z (i : s) ↦ z i) y) = f y := by
    apply hf
    intro i hi
    simp only [Function.updateFinset, dite_eq_ite, ite_eq_left_iff]
    exact fun h ↦ (h hi).elim
  rw [← integral_congr_ae <| eventually_of_forall this]
  rw [integral_dep]
  · sorry

theorem lintegral_dep {s : Finset ι} {f : ((i : s) → X i) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f ((fun x (i : s) ↦ x i) y) ∂measure_produit μ =
    ∫⁻ y, f y∂Measure.pi (fun i : s ↦ μ i) := by
  rw [← lintegral_map hf, isProjectiveLimit_measure_produit μ]
  exact (measurable_proj _)

theorem lintegral_dependsOn [DecidableEq ι]
    {f : ((i : ι) → X i) → ℝ≥0∞} (mf : Measurable f) {s : Finset ι} (hf : DependsOn f s)
    (x : (i : ι) → X i) : ∫⁻ y, f y ∂measure_produit μ = (∫⋯∫⁻_s, f ∂μ) x := by
  let g : ((i : s) → X i) → ℝ≥0∞ := fun y ↦ f (Function.updateFinset x _ y)
  have this y : g ((fun z (i : s) ↦ z i) y) = f y := by
    apply hf
    intro i hi
    simp only [Function.updateFinset, dite_eq_ite, ite_eq_left_iff]
    exact fun h ↦ (h hi).elim
  simp_rw [← this]
  rw [lintegral_dep]
  · rfl
  · exact mf.comp measurable_updateFinset

/- TODO: Add lemmas that show that the product measure behaves in the way we expect with respect
to measure of boxes and integral of functions depending on finitely many indices. -/

-- theorem prod_meas (S : Finset ℕ) (a : ℕ) (ha : a ∈ S) (μ : (n : S) → Measure (X n))
--     [∀ n, IsProbabilityMeasure (μ n)]
--     (s : (n : S) → Set (X n)) :
--     (Measure.pi μ) (univ.pi s) = ((μ ⟨a, ha⟩) (s ⟨a, ha⟩)) *
--     ((Measure.pi (fun (n : S.erase a) ↦ μ ⟨n.1, Finset.mem_of_mem_erase n.2⟩))
--     (univ.pi (fun n : S.erase a ↦ s ⟨n.1, Finset.mem_of_mem_erase n.2⟩))) := by
--   rw [Measure.pi_pi, Measure.pi_pi, mul_comm]
--   have h1 : (@Finset.univ S _).prod (fun n ↦ (μ n) (s n)) =
--       (@Finset.univ S.toSet _).prod (fun n ↦
--       ((fun n : ℕ ↦ if hn : n ∈ S then (μ ⟨n, hn⟩) (s ⟨n, hn⟩) else 1) n)) := by
--     apply Finset.prod_congr rfl (by simp)
--   have h2 : (@Finset.univ (S.erase a) _).prod (fun n ↦ (μ ⟨n.1, Finset.mem_of_mem_erase n.2⟩)
--       (s ⟨n.1, Finset.mem_of_mem_erase n.2⟩)) =
--       (@Finset.univ (S.erase a).toSet _).prod (fun n ↦
--       ((fun n : ℕ ↦ if hn : n ∈ S then (μ ⟨n, hn⟩) (s ⟨n, hn⟩) else 1) n)) := by
--     apply Finset.prod_congr rfl (fun x _ ↦ by simp [(Finset.mem_erase.1 x.2).2])
--   rw [h1, h2,
--     Finset.prod_set_coe (f := (fun n : ℕ ↦ if hn : n ∈ S then (μ ⟨n, hn⟩) (s ⟨n, hn⟩) else 1)),
--     Finset.prod_set_coe (f := (fun n : ℕ ↦ if hn : n ∈ S then (μ ⟨n, hn⟩) (s ⟨n, hn⟩) else 1)),
--     Finset.toFinset_coe, Finset.toFinset_coe, ← Finset.prod_erase_mul S _ ha]
--   congr
--   simp [ha]


  -- have := tendsto_of_antitone anti
  -- rcases this with hlim | ⟨l, hlim⟩
  -- · rw [OrderBot.atBot_eq] at hlim
  --   exact hlim.mono_right <| pure_le_nhds 0
  -- convert hlim
  -- by_contra zero_ne_l
  -- have := fun n ↦ anti.le_of_tendsto hlim n
  -- have : ∀ n, (kolContent μ_proj) (A n) =
  --     ∫⁻ x₀ : X 0, kolContent (μ_proj'' 1) (slice x₀ (A n)) ∂(μ 0) := by
  --   intro n
  --   have : ∀ x₀ : X 0, ∀ S : Set ((n : Finset.range (NA n + 1)) → X n),
  --       slice x₀ (cylinder (Finset.range (NA n + 1)) S) =
  --       cylinder (Finset.range (NA n)) (slice_range (NA n) x₀ S) := by
  --     intro x₀ S
  --     ext x
  --     simp [slice, slice_range, produit, produit_range]
  --     congrm ?_ ∈ S
  --     ext i
  --     cases i with
  --       | mk j hj => cases j with
  --         | zero => simp [produit_range]
  --         | succ => simp [produit_range]
  --   have : ∀ x₀, kolContent (μ_proj'' 1) (slice x₀ (A n)) =
  --       Measure.pi (fun n : Finset.range (NA n) ↦ μ (n + 1)) (slice_range (NA n) x₀ (SA n)) := by
  --     intro x₀
  --     rw [A_eq n, this x₀ (SA n), kolContent_eq,
  --       kolmogorovFun_congr (μ_proj'' 1) (cylinder_mem_cylinders (Finset.range (NA n))
  --       (slice_range (NA n) x₀ (SA n)) _)]
  --     rfl
  --     apply measurable_slice_range (mSA n)
  --     apply measurable_slice_range (mSA n)

      -- constructor
      -- · rintro ⟨y, hy, rfl, rfl⟩
      --   use fun i : Finset.range (NA n + 1) ↦ y i
      -- · rintro ⟨y, hy, hy', hy''⟩
      --   refine ⟨produit x₀ x, ?_, ?_, ?_⟩
      --   · have : (fun i : Finset.range (NA n + 1) ↦ produit x₀ x i) = y := by
      --       ext i
      --       cases i with
      --       | mk j hj =>
      --         cases j with
      --         | zero => simp [produit, hy']
      --         | succ m =>
      --           have : produit x₀ x (m + 1) = x m := by
      --             simp [produit]
      --           rw [this]
      --           have : x m = (fun i : Finset.range (NA n) ↦ x i) ⟨m, ok.2 hj⟩ := by simp
      --           rw [this, ← hy'']
      --     exact this ▸ hy
      --   · simp [produit]
      --   · ext n
      --     simp [produit]

    -- let extension : (∀ n : (Finset.range (NA n + 1)).erase 0, X n) → (∀ n : {k | k ≥ 1}, X n) :=
    --   fun x k ↦ by
    --     by_cases h : k.1 < NA n + 1
    --     · use x ⟨k.1, Finset.mem_erase.2 ⟨Nat.one_le_iff_ne_zero.1 k.2, Finset.mem_range.2 h⟩⟩
    --     · use Classical.ofNonempty
    -- let e : (Finset.range (NA n + 1)).erase 0 ≃
    --     {k : {k | k ≥ 1} | k.1 ∈ (Finset.range (NA n + 1)).erase 0} :=
    --   {
    --     toFun := fun x ↦ ⟨⟨x.1, Nat.one_le_iff_ne_zero.2 (Finset.mem_erase.1 x.2).1⟩, x.2⟩
    --     invFun := fun x ↦ ⟨x.1.1, x.2⟩
    --     left_inv := by simp [Function.LeftInverse]
    --     right_inv := by simp [Function.RightInverse, Function.LeftInverse]
    --   }
    -- have : Fintype {k : {k | k ≥ 1} | k.1 ∈ (Finset.range (NA n + 1)).erase 0} := by
    --   exact Fintype.ofEquiv ((Finset.range (NA n + 1)).erase 0) e
    -- let aux : X 0 → (∀ n : {k : {k | k ≥ 1} | k.1 ∈ (Finset.range (NA n + 1)).erase 0}.toFinset, X n) →
    --     (∀ n : Finset.range (NA n + 1), X n) :=
    --   fun x₀ x ↦
    --     (fun y : ∀ n, X n ↦ fun k : Finset.range (NA n + 1) ↦ y k.1) ((produit x₀) (extension
    --     (fun k : (Finset.range (NA n + 1)).erase 0 ↦
    --     x ⟨⟨k.1, Nat.one_le_iff_ne_zero.2 (Finset.mem_erase.1 k.2).1⟩, k.2⟩)))
    --   -- if h : k = ⟨0, zero_mem_range⟩ then h ▸ x₀ else by
    --   -- rw [← ne_eq, ← Subtype.val_inj.ne] at h
    --   -- have : k.1 - 1 ∈ Finset.range (NA n) := by
    --   --   rw [Finset.mem_range, Nat.sub_lt_iff_lt_add, add_comm 1]
    --   --   exact Finset.mem_range.1 k.2
    --   --   exact Nat.one_le_iff_ne_zero.2 h
    --   -- use Nat.succ_pred_eq_of_ne_zero h ▸ x ⟨k.1 - 1, this⟩
    -- have : ∀ x₀ : X 0, ∀ S : Set ((n : Finset.range (NA n + 1)) → X n),
    --     (produit x₀) ⁻¹' (cylinder (Finset.range (NA n + 1)) S) =
    --     cylinder (X := fun k : {k | k ≥ 1} ↦ X k)
    --     {k : {k | k ≥ 1} | k.1 ∈ (Finset.range (NA n + 1)).erase 0}.toFinset ((aux x₀) ⁻¹' S) := by
    --   intro x₀ S
    --   ext x
    --   simp [produit, aux]
    --   congrm ?_ ∈ S
    --   ext k
    --   by_cases h : k = ⟨0, zero_mem_range⟩
    --   · have : k.1 = 0 := by rw [h]
    --     simp [h, this]
    --     have : k = ⟨0, zero_mem_range⟩ ↔ k.1 = 0 := by
    --       refine ⟨fun h ↦ by rw [h], fun h' ↦ ?_⟩
    --       ext
    --       exact h'

    -- have : ∀ x₀, kolContent (μ_proj' 1) ((produit x₀) ⁻¹' (A n)) =
    --     Measure.pi (fun n : (Finset.range (NA n + 1)).erase 0 ↦ μ n) ((aux x₀) ⁻¹' (SA n)) := by
    --   intro x₀
    --   simp
    --   rw [kolContent_eq (μ_proj' 1)]
    -- rw [kolContent_eq μ_proj (A_mem n), kolmogorovFun_congr μ_proj (A_mem n) (A_eq n) (mSA n)]
    -- simp [kolContent_eq (μ_proj' 1), kolmogorovFun_congr μ_proj (A_mem n) (A_eq n) (mSA n)]
