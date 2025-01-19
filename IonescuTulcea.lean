import Mathlib.KolmogorovExtension4.Transition
import Mathlib.KolmogorovExtension4.Boxes
import Mathlib.KolmogorovExtension4.Projective
import Mathlib.Probability.Kernel.MeasureCompProd
import Mathlib.KolmogorovExtension4.DependsOn
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.KolmogorovExtension4.KolmogorovExtension

open MeasureTheory ProbabilityTheory MeasurableSpaceGraph Set ENNReal Filter Topology

variable {X : ℕ → Type*} [∀ n, Nonempty (X n)] [∀ n, MeasurableSpace (X n)]
variable (κ : (k : ℕ) → kernel ((transitionGraph X).node k) ((transitionGraph X).path k (k + 1)))
variable [∀ k, IsMarkovKernel (κ k)]
variable (x : (transitionGraph X).node 0)

noncomputable def family :
  (S : Finset ℕ) → Measure ((k : S) → X (k + 1)) := fun S ↦
  ((MeasurableSpaceGraph.transition κ).ker 0 (S.sup id + 1) x).map
  (fun x (i : S) ↦ x ⟨i.1 + 1,
    mem_Ioc.2 ⟨Nat.succ_pos _, Nat.succ_le_succ <| Finset.le_sup (f := id) i.2⟩⟩)

variable (μ : Measure ((transitionGraph X).node 0)) [IsProbabilityMeasure μ]

theorem map_compProd {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : Measure X) (κ : kernel X Y) {f : Y → Z} (mf : Measurable f) :
    (μ ⊗ₘ κ).map (Prod.map id f) = μ ⊗ₘ (kernel.map κ f mf) := by sorry

theorem markov1 (M : MeasurableSpaceGraph ℕ) {i j : ℕ} (κ : kernel (M.node i) (M.path i j))
    [IsMarkovKernel κ] (hij : i < j) (hjk : j < k)
    (η : kernel (M.node j) (M.path j k)) [IsMarkovKernel η] :
    IsMarkovKernel (M.compProd κ η) := by
  rw [compProd]
  simp [hij, hjk, split]
  infer_instance

theorem markov2 {M : MeasurableSpaceGraph ℕ} {i j : ℕ}
    (κ : kernel (M.node i) (M.path i j)) (h : j = k) [IsMarkovKernel κ] :
    IsMarkovKernel (castPath κ h) := by
  rw [castPath]; infer_instance

theorem markov {M : MeasurableSpaceGraph ℕ} {i j : ℕ}
    (κ₀ : kernel (M.node i) (M.path i j)) [h₀ : IsMarkovKernel κ₀]
    (κ : ∀ k, kernel (M.node k) (M.path k (k + 1)))
    [∀ k, IsMarkovKernel (κ k)]
    (k : ℕ) (hij : i < j) (hk : j ≤ k) :
    IsMarkovKernel (kerInterval κ₀ κ k) := by
  induction k with
  | zero => linarith
  | succ n hn =>
    rw [kerInterval_succ]
    split_ifs with h
    · apply markov2
    · have : j ≤ n := Nat.lt_succ.1 <| lt_iff_le_and_ne.2 ⟨hk, h⟩
      have aux := hn this
      apply markov1 M
      · exact lt_of_lt_of_le hij this
      · simp

theorem markov_kerNat {M : MeasurableSpaceGraph ℕ} {i j : ℕ}
    (κ : ∀ k, kernel (M.node k) (M.path k (k + 1))) [∀ k, IsMarkovKernel (κ k)] (hij : i < j) :
    IsMarkovKernel (kerNat κ i j) := by
  rw [kerNat]
  simp [hij]
  apply markov
  · simp
  · linarith

theorem test {k l : ℕ} (hk : 0 < k) (hkl : k ≤ l) :
    kernel.map ((transition κ).ker 0 l)
    (fun (x : ((i : Ioc 0 l) → X i)) (i : Ioc 0 k) ↦
      x ⟨i.1, Ioc_subset_Ioc_right hkl i.2⟩)
    (measurable_proj₂ ..) =
    (transition κ).ker 0 k := by
  by_cases h : k = l
  · have : (fun (x : ((i : Ioc 0 l) → X i)) (i : Ioc 0 k) ↦
        x ⟨i.1, Ioc_subset_Ioc_right hkl i.2⟩) =
        transitionGraph.path_eq X ▸ (e_path_eq _ h.symm).toFun := by aesop
    conv_lhs =>
      enter [2]
      rw [this]
    simp only [Equiv.toFun_as_coe, MeasurableEquiv.coe_toEquiv]
    simp_rw [transition_ker]
    apply (kerNat_cast _ _ _ _ _).symm
  · have hkl : k < l := lt_iff_le_and_ne.2 ⟨hkl, h⟩
    ext x s ms
    rw [kernel.map_apply', transition_ker κ 0 l, ← compProd_kerNat κ hk hkl,
      compProd_apply' _ _ hk hkl]
    simp_rw [preimage_preimage]
    have aux1 (b : (transitionGraph X).path 0 k) (c : (transitionGraph X).path k l) :
        b ∈ s ↔
        c ∈ {c | (b, c) ∈ (fun x (i : Ioc 0 k) ↦
        (transitionGraph X).er 0 k l hk hkl x ⟨i.1, _⟩) ⁻¹' s} := by
      have : (fun (i : Ioc 0 k) ↦ (transitionGraph X).er 0 k l hk hkl (b, c)
          ⟨i.1, Ioc_subset_Ioc_right hkl.le i.2⟩) = b := by
        ext i
        rw [er_eq]
        simp [ProbabilityTheory.er, (mem_Ioc.2 i.2).2]
      simp [this]
    have aux2 b (hb : b ∈ s) :
        {c | (b, c) ∈ (fun x (i : Ioc 0 k) ↦
        (transitionGraph X).er 0 k l hk hkl x ⟨i.1, _⟩) ⁻¹' s} = univ := by
      ext c
      simp only [mem_preimage, mem_univ, iff_true]
      exact (aux1 b c).1 hb
    have aux3 b (hb : b ∉ s) :
        {c | (b, c) ∈ (fun x (i : Ioc 0 k) ↦
        (transitionGraph X).er 0 k l hk hkl x ⟨i.1, _⟩) ⁻¹' s} = ∅ := by
      ext c
      simp only [mem_preimage, mem_empty_iff_false, iff_false]
      exact (aux1 b c).not.1 hb
    have aux4 b : ((kerNat κ k l) ((transitionGraph X).el 0 k hk (x, b)))
        {c | (b, c) ∈ (fun x (i : Ioc 0 k) ↦
        (transitionGraph X).er 0 k l hk hkl x ⟨↑i, _⟩) ⁻¹' s} =
        s.indicator 1 b := by
      have := markov_kerNat κ hkl
      by_cases hb : b ∈ s
      · simp_rw [indicator, aux2 b hb]
        simp [hb]
      · simp_rw [aux3 b hb]
        simp [hb]
    simp_rw [aux4]
    · have : (1 : (transitionGraph X).path 0 k → ℝ≥0∞) = fun _ ↦ 1 := rfl
      rw [this, lintegral_indicator_const, transition_ker, one_mul]
      · rfl
      · exact ms
    · exact ms.preimage <| measurable_proj₂ _ _ <| Icc_subset_Icc_right hkl.le
    · exact ms

theorem kernel.map_map {X Y Z T : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    [MeasurableSpace T]
    (κ : kernel X Y) (f : Y → Z) (hf : Measurable f) (g : Z → T) (hg : Measurable g) :
    kernel.map (kernel.map κ f hf) g hg = kernel.map κ (g ∘ f) (hg.comp hf) := by
  ext1 x
  rw [kernel.map_apply, kernel.map_apply, Measure.map_map, ← kernel.map_apply]
  · exact hg
  · exact hf

theorem proj_family : IsProjectiveMeasureFamily (α := fun k : ℕ ↦ X (k + 1)) (family κ x) := by
  intro S T hTS
  have aux1 : T.sup id + 1 ≤ S.sup id + 1 := Nat.succ_le_succ <| Finset.sup_mono (f := id) hTS
  have aux : Ioc 0 (T.sup id + 1) ⊆ Ioc 0 (S.sup id + 1) := Ioc_subset_Ioc_right aux1
  simp only [family]
  rw [← kernel.map_apply, ← test _ _ aux1, Measure.map_map, kernel.map_map, kernel.map_apply]
  · rfl
  · simp_all only [Finset.le_eq_subset, add_le_add_iff_right, Finset.sup_le_iff, id_eq]
    apply measurable_pi_lambda
    intro a
    apply Measurable.eval
    apply measurable_id'
  · simp_all only [Finset.le_eq_subset, add_le_add_iff_right, Finset.sup_le_iff, id_eq]
    apply measurable_pi_lambda
    intro a
    apply Measurable.eval
    apply measurable_id'
  · simp_all only [Finset.le_eq_subset, add_le_add_iff_right, Finset.sup_le_iff, id_eq]
    apply measurable_pi_lambda
    intro a
    apply Measurable.eval
    apply measurable_id'
  · exact Nat.succ_pos _

noncomputable def updateSet {ι : Type*} {α : ι → Type*} (x : (i : ι) → α i) (s : Set ι)
    (y : (i : s) → α i) (i : ι) : α i := by
  classical
  exact if hi : i ∈ s then y ⟨i, hi⟩ else x i

noncomputable def kerint (k N : ℕ) (f : ((n : ℕ) → X n) → ℝ≥0∞)
    (x : (i : ℕ) → X i) : ℝ≥0∞ := by
  classical
  exact ∫⁻ z : (i : Ioc k N) → X i,
    f (updateSet x _ z) ∂((transition κ).ker k N (fun i ↦ x i))

-- lemma omg (s : Set ι) (x : (i : s) → X i) (i j : s) (h : i = j) (h' : X i = X j) :
--     cast h' (x i) = x j := by
--   subst h

-- def eq (k : ℕ) : ((i : Ioc k (k + 1)) → X i) ≃ᵐ X (k + 1) :=
--   { toFun := fun x ↦ x ⟨k + 1, right_mem_Ioc.2 <| Nat.lt_succ_self _⟩
--     invFun := fun x i ↦ by
--       have : i = k + 1 := by
--         rcases mem_Ioc.2 i.2 with ⟨h1, h2⟩
--         exact eq_of_le_of_not_lt h2 (by linarith)
--       exact cast (congrArg X this.symm) x
--     left_inv := by
--       simp only [Function.LeftInverse]
--       intro x
--       ext i
--        }

theorem auxiliaire (f : ℕ → (∀ n, X n) → ℝ≥0∞) (N : ℕ → ℕ)
    (hcte : ∀ n, DependsOn (f n) (Finset.Icc 0 (N n))) (mf : ∀ n, Measurable (f n))
    (bound : ℝ≥0∞) (fin_bound : bound ≠ ∞) (le_bound : ∀ n x, f n x ≤ bound) (k : ℕ)
    (anti : ∀ x, Antitone (fun n ↦ kerint κ (k + 1) (N n) (f n) x))
    (l : ((n : ℕ) → X n) → ℝ≥0∞)
    (htendsto : ∀ x, Tendsto (fun n ↦ kerint κ (k + 1) (N n) (f n) x) atTop (𝓝 (l x)))
    (ε : ℝ≥0∞)
    (y : (n : Iic k) → X n)
    (hpos : ∀ x, ∀ n, ε ≤ kerint κ k (N n) (f n) (updateSet x _ y)) :
    ∃ z, ∀ x n,
    ε ≤ kerint κ (k + 1) (N n) (f n) (Function.update (updateSet x _ y) (k + 1) z) := by
  -- Shorter name for integrating over all the variables except the first `k + 1`.
  let F : ℕ → ((n : ℕ) → X n) → ℝ≥0∞ := fun n ↦ kerint κ (k + 1) (N n) (f n)
  -- `Fₙ` converges to `l` by hypothesis.
  have tendstoF x : Tendsto (F · x) atTop (𝓝 (l x)) := htendsto x
  -- Integrating `fₙ` over all the variables except the first `k` is the same as integrating
  -- `Fₙ` over the `k`-th variable.
  have f_eq x n : kerint κ k (N n) (f n) x = kerint κ k (k + 1) (F n) x := by sorry
    -- by_cases h : k ≤ N n
    -- · rw [Finset.Icc_eq_left_union h, lmarginal_union _ _ (mf n) (by simp)]
    -- · have : ¬k + 1 ≤ N n := fun h' ↦ h <| le_trans k.le_succ h'
    --   simp only [F]
    --   rw [Finset.Icc_eq_empty h, Finset.Icc_eq_empty this,
    --     lmarginal_eq_of_disjoint (hcte n) (by simp),
    --     lmarginal_eq_of_disjoint (hcte n) (by simp [h])]
  -- `F` is also a bounded sequence.
  have F_le n x : F n x ≤ bound := by sorry
    -- rw [← lmarginal_const (μ := μ) (s := Finset.Icc (k + 1) (N n)) bound x]
    -- apply lmarginal_mono <| le_bound n
  -- By dominated convergence, the integral of `fₙ` with respect to all the variable except
  -- the `k` first converges to the integral of `l`.
  have tendsto_int x : Tendsto (fun n ↦ kerint κ k (N n) (f n) x) atTop
      (𝓝 (kerint κ k (k + 1) l x)) := by
    simp_rw [f_eq, kerint]
    refine tendsto_lintegral_of_dominated_convergence (fun _ ↦ bound) ?_ ?_ ?_ ?_
    · sorry
    · exact fun n ↦ eventually_of_forall <| fun y ↦ F_le n _
    · rw [transition_ker]
      have := markov_kerNat κ (by linarith : k < k + 1)
      simp [fin_bound]
    · exact eventually_of_forall (fun _ ↦ tendstoF _)
  -- By hypothesis, we have `ε ≤ ∫ F(y, xₖ) ∂μₖ`, so this is also true for `l`.
  have ε_le_lint x : ε ≤ kerint κ k (k + 1) l (updateSet x _ y) :=
    ge_of_tendsto (tendsto_int _) (by simp [hpos])
  let x_ : (n : ℕ) → X n := Classical.ofNonempty
  -- We now have that the integral of `l` with respect to a probability measure is greater than `ε`,
  -- therefore there exists `x'` such that `ε ≤ l(y, x')`.
  obtain ⟨x', hx'⟩ : ∃ x', ε ≤ l (Function.update (updateSet x_ _ y) (k + 1) x') := by
    have aux : ∫⁻ (a : (i : Ioc k (k + 1)) → X i),
        l (updateSet (updateSet x_ _ y) _ a) ∂(κ k y) ≠ ⊤ := by
      apply ne_top_of_le_ne_top fin_bound
      rw [← mul_one bound, ← measure_univ (μ := κ k y), ← lintegral_const]
      exact lintegral_mono <| fun y ↦ le_of_tendsto' (tendstoF _) <| fun _ ↦ F_le _ _
    rcases exists_lintegral_le aux with ⟨x', hx'⟩
    refine ⟨x' ⟨k + 1, right_mem_Ioc.2 <| Nat.lt_succ_self _⟩, ?_⟩
    calc
      ε ≤ ∫⁻ (z : (i : Ioc k (k + 1)) → X i),
          l (updateSet (updateSet x_ _ y) _ z) ∂(κ k y) := by
          have : y = (fun i : Iic k ↦ updateSet x_ _ y i) := by
            ext i
            simp [updateSet, i.2]
          rw [← kerNat_succ κ k, ← transition_ker]
          nth_rw 1 [this]
          apply ε_le_lint
      _ ≤ l (updateSet (updateSet x_ _ y) _ x') := hx'
      _ = l (Function.update (updateSet x_ _ y) _ (x' ⟨k + 1, _⟩)) := by
          congr
          ext i
          simp only [updateSet, mem_Ioc, mem_Iic, Function.update]
          split_ifs with h1 h2 h3 h4 h5 h6
          · aesop
          · have : i = k + 1 := eq_of_le_of_not_lt h1.2 (by linarith)
            exact (h2 this).elim
          · exact (not_or.2 ⟨h3, h2⟩ (Nat.le_succ_iff.1 h1.2)).elim
          · exfalso; linarith
          · rfl
          · push_neg at h1
            exfalso; linarith [h1 <| lt_iff_not_le.2 h4]
          · rfl
  refine ⟨x', fun x n ↦ ?_⟩
  -- As `F` is a non-increasing sequence, we have `ε ≤ Fₙ(y, x')` for any `n`.
  have := le_trans hx' ((anti _).le_of_tendsto (tendstoF _) n)
  -- This part below is just to say that this is true for any `x : (i : ι) → X i`,
  -- as `Fₙ` technically depends on all the variables, but really depends only on the first `k + 1`.
  have aux : F n (Function.update (updateSet x_ _ y) (k + 1) x') =
      F n (Function.update (updateSet x _ y) (k + 1) x') := by
    sorry
    -- simp only [F]
    -- have := dependsOn_lmarginal (μ := μ) (hcte n) (Finset.Icc (k + 1) (N n))
    -- rw [← coe_sdiff] at this
    -- have := dependsOn_updateFinset (dependsOn_update this k x') (Finset.Ico 0 k) y
    -- have aux : (Finset.Icc 0 (N n) \ Finset.Icc (k + 1) (N n)).erase k \ Finset.Ico 0 k = ∅ := by
    --   ext i
    --   simp only [Nat.Ico_zero_eq_range, mem_sdiff, mem_erase, ne_eq, Finset.mem_Icc, zero_le,
    --     true_and, not_and, not_le, Finset.mem_range, not_lt, Finset.not_mem_empty, iff_false,
    --     and_imp]
    --   intro h1 h2 h3
    --   refine lt_iff_le_and_ne.2 ⟨?_, h1⟩
    --   by_contra!
    --   rw [← Nat.succ_le] at this
    --   exact (lt_iff_not_le.1 (h3 this)) h2
    -- rw [← coe_sdiff, aux, coe_empty] at this
    -- apply dependsOn_empty this
  simp only [F] at aux
  rw [aux] at this
  exact this

theorem cylinders_nat :
    cylinders X = ⋃ (N) (S) (_ : MeasurableSet S), {cylinder (Finset.Icc 0 N) S} := by
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

def key (ind : (k : ℕ) → ((i : Finset.Ico 0 k) → X i) → X k) : (k : ℕ) → X k := fun k ↦ by
  use ind k (fun i ↦ key ind i)
  decreasing_by
  exact (Finset.mem_Ico.1 i.2).2

/-- This is the key theorem to prove the existence of the product measure: the `kolContent` of
a decresaing sequence of cylinders with empty intersection converges to $0$, in the case where
the measurable spaces are indexed by $\mathbb{N}$. This implies the $\sigma$-additivity of
`kolContent` (see `sigma_additive_addContent_of_tendsto_zero`),
which allows to extend it to the $\sigma$-algebra by Carathéodory's theorem. -/
theorem firstLemma (A : ℕ → Set ((n : ℕ) → X (n + 1))) (A_mem : ∀ n, A n ∈ cylinders _)
    (A_anti : Antitone A) (A_inter : ⋂ n, A n = ∅) (x₀ : (i : Iic 0) → X i) :
    Tendsto (fun n ↦ kolContent
    (proj_family κ ((transitionGraph.node_equiv X).symm x)) (A n)) atTop (𝓝 0) := by
  -- `Aₙ` is a cylinder, it can be writtent `cylinder sₙ Sₙ`.
  have A_cyl n : ∃ N S, MeasurableSet S ∧ A n = cylinder (Finset.Icc 0 N) S := by
    simpa [cylinders_nat] using A_mem n
  choose N S mS A_eq using A_cyl
  set proj := proj_family κ ((transitionGraph.node_equiv X).symm x)
  -- We write `χₙ` for the indicator function of `Aₙ`.
  let χ n := (A n).indicator (1 : (∀ n, X (n + 1)) → ℝ≥0∞)
  let ψ n (x : (n : ℕ) → X n) : ℝ≥0∞ := χ n (fun i ↦ x (i + 1))
  -- `χₙ` is measurable.
  have mχ n : Measurable (χ n) := by
    simp_rw [χ, A_eq]
    exact (measurable_indicator_const_iff 1).2 <| measurableSet_cylinder _ _ (mS n)
  -- `χₙ` only depends on the first coordinates.
  have χ_dep n : DependsOn (χ n) (Finset.Icc 0 (N n)) := by sorry
    -- simp_rw [χ, A_eq]
    -- exact dependsOn_cylinder_indicator _ _
  -- Therefore its integral is constant.
  have lma_const x y n : kerint κ 0 (N n) (ψ n) x =
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

-- theorem test
--     (μ : Measure ((transitionGraph X).node 0)) [IsProbabilityMeasure μ] :
--     ∃ ν : Measure ((k : ℕ) → X k), ∀ k : ℕ, (hk : 0 < k) →
--     ν.map (fun x (i : Iic k) ↦ x i) =
--     (μ ⊗ₘ (MeasurableSpaceGraph.transition κ).ker 0 k).map ((transitionGraph X).el 0 k hk) := by sorry

-- theorem test' :
--     ∃ ν : kernel ((transitionGraph X).node 0) ((k : Ioi 0) → X k), ∀ k : ℕ, (hk : 0 < k) →
--     kernel.map ν
--       (fun x (i : Ioc 0 k) ↦ x ⟨i.1, Ioc_subset_Ioi_self i.2⟩
--         : ((k : Ioi 0) → X k) → (transitionGraph X).path 0 k)
--       (measurable_proj₂ _ _ Ioc_subset_Ioi_self) =
--     (MeasurableSpaceGraph.transition κ).ker 0 k := by sorry
