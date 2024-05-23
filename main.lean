import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.KolmogorovExtension4.Projective
import Mathlib.KolmogorovExtension4.KolmogorovExtension
import Mathlib.Topology.Defs.Filter
-- import Mathlib.KolmogorovExtension4.section_file
import Mathlib.KolmogorovExtension4.DependsOn
import Mathlib.MeasureTheory.Integral.Marginal

open Set MeasureTheory Filter Topology ENNReal Finset symmDiff

open scoped Classical

theorem preimage_proj {ι : Type*} {X : ι → Type*} (I J : Finset ι)
    (hIJ : I ⊆ J) (s : ∀ i : I, Set (X i)) :
    (fun t : (∀ j : J, X j) ↦ fun i : I ↦ t ⟨i, hIJ i.2⟩) ⁻¹' (univ.pi s) =
    (@Set.univ J).pi (fun j ↦ if h : j.1 ∈ I then s ⟨j.1, h⟩ else univ) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Subtype.forall]
  refine ⟨fun h i hi ↦ ?_, fun h i i_mem ↦ by simpa [i_mem] using h i (hIJ i_mem)⟩
  split_ifs with i_mem
  · simp [i_mem, h i i_mem]
  · simp [i_mem]

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)] [∀ n, Nonempty (X n)]
variable (μ : (n : ℕ) → Measure (X n)) [∀ n, IsProbabilityMeasure (μ n)]

theorem isProjectiveMeasureFamily_prod {ι : Type*} {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (m : (i : ι) → Measure (α i)) [∀ i, IsProbabilityMeasure (m i)] :
    IsProjectiveMeasureFamily (fun S : Finset ι ↦ (Measure.pi (fun n : S ↦ m n))) := by
  intro T S hST
  refine Measure.pi_eq (fun s ms ↦ ?_)
  rw [Measure.map_apply (measurable_proj₂' (α := α) T S hST) (MeasurableSet.univ_pi ms),
    preimage_proj S T hST, Measure.pi_pi]
  have h1 : (@Finset.univ T _).prod (fun n ↦ (m n) (if hn : n.1 ∈ S then s ⟨n.1, hn⟩ else univ)) =
      (@Finset.univ T.toSet _).prod (fun n ↦ (fun k : ι ↦ if k ∈ T then (m k)
        (if hk' : k ∈ S then s ⟨k, hk'⟩ else univ) else 1) n) := Finset.prod_congr rfl (by simp)
  have h2 : (@Finset.univ S _).prod (fun n ↦ (m n) (s n)) =
      (@Finset.univ S.toSet _).prod (fun n ↦ (fun k : ι ↦ if k ∈ T then (m k)
        (if hk' : k ∈ S then s ⟨k, hk'⟩ else univ) else 1) n) := by
    apply Finset.prod_congr rfl
    simp only [univ_eq_attach, mem_attach, coe_mem, ↓reduceDite, true_implies, Subtype.forall]
    exact fun a ha ↦ by simp [hST ha]
  rw [h1, h2, Finset.prod_set_coe (f := fun k : ι ↦ if k ∈ T then (m k)
      (if hk' : k ∈ S then s ⟨k, hk'⟩ else univ) else 1),
    Finset.prod_set_coe (f := fun k : ι ↦ if k ∈ T then (m k)
      (if hk' : k ∈ S then s ⟨k, hk'⟩ else univ) else 1),
    Finset.toFinset_coe, Finset.toFinset_coe,
    Finset.prod_subset hST (fun _ h h' ↦ by simp [h, h'])]

theorem cyl_dependsOn (s : Finset ℕ) (S : Set ((n : s) → X n)) :
    DependsOn ((cylinder s S).indicator (1 : (∀ n, X n) → ℝ≥0∞)) s := by
  intro x y hxy
  have : x ∈ cylinder s S ↔ y ∈ cylinder s S := by simp [hxy]
  by_cases h : x ∈ cylinder s S
  · simp [h, this.1 h]
  · simp [h, this.not.1 h]

theorem cylinders_nat : cylinders X =
    ⋃ (N) (S) (_ : MeasurableSet S), {cylinder (Icc 0 N) S} := by
  ext s
  simp only [mem_cylinders, exists_prop, mem_iUnion, mem_singleton_iff]
  constructor
  · rintro ⟨t, S, mS, rfl⟩
    refine ⟨t.sup id, (fun (f : (∀ n : Finset.Icc 0 (t.sup id), X n)) (k : t) ↦
      f ⟨k.1, Finset.mem_Icc.2 ⟨Nat.zero_le k.1, Finset.le_sup (f := id) k.2⟩⟩) ⁻¹' S,
      by measurability, ?_⟩
    dsimp only [cylinder]
    rw [← preimage_comp]
    rfl
  · rintro ⟨N, S, mS, rfl⟩
    exact ⟨Finset.Icc 0 N, S, mS, rfl⟩

lemma useful (s : Set (∀ n, X n)) (s_mem : s ∈ cylinders X) :
    ∃ N S, MeasurableSet S ∧ s = cylinder (Finset.Icc 0 N) S := by
  simpa [cylinders_nat] using s_mem

theorem eq (s : Finset ℕ) (S : Set ((n : s) → X n)) (mS : MeasurableSet S) (x : ∀ n, X n) :
    kolContent (isProjectiveMeasureFamily_prod μ) ((cylinder s S)) =
    (∫⋯∫⁻_s, (cylinder s S).indicator 1 ∂μ) x := by
  rw [kolContent_congr (isProjectiveMeasureFamily_prod μ)
      (by simp only [mem_cylinders, exists_prop]; exact ⟨s, S, mS, rfl⟩) rfl mS,
    ← lintegral_indicator_one₀ mS.nullMeasurableSet]
  refine lintegral_congr <| fun a ↦ ?_
  by_cases ha : a ∈ S <;> simp [ha, Function.updateFinset]

theorem ge_of_int {α : Type*} [MeasurableSpace α] {m : Measure α} [IsProbabilityMeasure m]
    {ε : ℝ≥0∞} {f : α → ℝ≥0∞} (hf : ε ≤ ∫⁻ a, f a ∂m) (fin_lint : ∫⁻ a, f a ∂m ≠ ∞) :
    ∃ a, ε ≤ f a := by
  by_contra!
  have : ∫⁻ a, f a ∂m < ε := by
    rw [← mul_one ε, ← measure_univ (μ := m), ← lintegral_const]
    apply lintegral_strict_mono (NeZero.ne' m).symm aemeasurable_const fin_lint
      (eventually_of_forall this)
  exact not_le_of_lt this hf

theorem Finset.Icc_eq_left_union (h : k ≤ N) : Finset.Icc k N = {k} ∪ (Finset.Icc (k + 1) N) := by
  ext x
  simp
  refine ⟨fun ⟨h1, h2⟩ ↦ ?_, ?_⟩
  · by_cases hxk : x = k
    · exact Or.inl hxk
    · exact Or.inr ⟨Nat.succ_le_of_lt <| Nat.lt_of_le_of_ne h1 (fun h ↦ hxk h.symm), h2⟩
  · rintro (h1 | ⟨h2, h3⟩)
    · exact ⟨h1 ▸ le_refl _, h1 ▸ h⟩
    · exact ⟨Nat.le_of_succ_le h2, h3⟩

theorem auxiliaire (f : ℕ → (∀ n, X n) → ℝ≥0∞) (N : ℕ → ℕ)
    (hcte : ∀ n, DependsOn (f n) (Finset.Icc 0 (N n))) (mf : ∀ n, Measurable (f n))
    (bound : ℝ≥0∞) (fin_bound : bound ≠ ∞) (le_bound : ∀ n x, f n x ≤ bound)
    (k : ℕ)
    (anti : ∀ x, Antitone (fun n ↦ (∫⋯∫⁻_Finset.Icc (k + 1) (N n), f n ∂μ) x))
    (l : ((n : ℕ) → X n) → ℝ≥0∞)
    (htendsto : ∀ x, Tendsto (fun n ↦ (∫⋯∫⁻_Finset.Icc (k + 1) (N n), f n ∂μ) x) atTop (𝓝 (l x)))
    (ε : ℝ≥0∞)
    (y : (n : Finset.Ico 0 k) → X n)
    (hpos : ∀ x, ∀ n,
    ε ≤ (∫⋯∫⁻_Finset.Icc k (N n), f n ∂μ) (Function.updateFinset x (Finset.Ico 0 k) y)) :
    ∃ z, ∀ x n, ε ≤ (∫⋯∫⁻_Finset.Icc (k + 1) (N n), f n ∂μ)
    (Function.update (Function.updateFinset x (Finset.Ico 0 k) y) k z) := by
  let F : ℕ → (∀ n, X n) → ℝ≥0∞ := fun n ↦ (∫⋯∫⁻_Finset.Icc (k + 1) (N n), f n ∂μ)
  have tendstoF : ∀ x, Tendsto (F · x) atTop (𝓝 (l x)) := htendsto
  have f_eq : ∀ x, (fun n ↦ (∫⋯∫⁻_Finset.Icc k (N n), f n ∂μ) x) =
      fun n ↦ (∫⋯∫⁻_{k}, F n ∂μ) x := by
    intro x
    ext1 n
    by_cases h : k ≤ N n
    · rw [Finset.Icc_eq_left_union h, lmarginal_union]
      exact mf n
      simp
    · have : ¬k + 1 ≤ N n := fun h' ↦ h <| le_trans k.le_succ h'
      simp only [F]
      rw [Finset.Icc_eq_empty h, Finset.Icc_eq_empty this,
        lmarginal_eq (hcte n) (disjoint_empty_right _), lmarginal_eq (hcte n) (by simp [h])]
  have F_le : ∀ n x, F n x ≤ bound := by
    intro n x
    rw [← lmarginal_const (μ := μ) (s := Finset.Icc (k + 1) (N n)) bound x]
    apply lmarginal_mono <| le_bound n
  have tendsto_int : ∀ x, Tendsto (fun n ↦ (∫⋯∫⁻_Finset.Icc k (N n), f n ∂μ) x) atTop
      (𝓝 ((∫⋯∫⁻_{k}, l ∂μ) x)) := by
    intro x
    simp_rw [f_eq, lmarginal_singleton]
    exact tendsto_lintegral_of_dominated_convergence (fun _ ↦ bound)
      (fun n ↦ ((mf n).lmarginal μ).comp <| measurable_update ..)
      (fun n ↦ eventually_of_forall <| fun y ↦ F_le n _)
      (by simp [fin_bound])
      (eventually_of_forall (fun _ ↦ tendstoF _))
  have ε_le_lint : ∀ x, ε ≤ (∫⋯∫⁻_{k}, l ∂μ) (Function.updateFinset x _ y) :=
    fun _ ↦ ge_of_tendsto (tendsto_int _) (by simp [hpos])
  have : ∀ x, ε ≤ ∫⁻ xₐ : X k,
    l (Function.update (Function.updateFinset x _ y) k xₐ) ∂μ k := by
    simpa [lmarginal_singleton] using ε_le_lint
  let x_ : ∀ n, X n := Classical.ofNonempty
  have : ∃ x', ε ≤ l (Function.update (Function.updateFinset x_ _ y) k x') := by
    simp_rw [lmarginal_singleton] at ε_le_lint
    apply ge_of_int (ε_le_lint x_)
    apply ne_top_of_le_ne_top fin_bound
    rw [← mul_one bound, ← measure_univ (μ := μ k), ← lintegral_const]
    exact lintegral_mono <| fun y ↦ le_of_tendsto' (tendstoF _) <| fun _ ↦ F_le _ _
  rcases this with ⟨x', hx'⟩
  refine ⟨x', fun x n ↦ ?_⟩
  have := le_trans hx' ((anti _).le_of_tendsto (tendstoF _) n)
  have aux : F n (Function.update
      (Function.updateFinset x_ (Finset.Ico 0 k) y) k x') =
      F n (Function.update
      (Function.updateFinset x (Finset.Ico 0 k) y) k x') := by
    simp only [F]
    have := updateFinset_dependsOn
      (update_dependsOn (lmarginal_dependsOn (μ := μ) (Finset.Icc (k + 1) (N n)) (hcte n)) k x')
      (Finset.Ico 0 k) y
    have aux : (Finset.Icc 0 (N n) \ Finset.Icc (k + 1) (N n)).erase k \ Finset.Ico 0 k = ∅ := by
      ext i
      simp
      intro h1 h2 h3
      refine lt_iff_le_and_ne.2 ⟨?_, h1⟩
      by_contra!
      rw [← Nat.succ_le] at this
      linarith [h2, h3 this]
    rw [aux] at this
    apply dependsOn_empty this
  simp [F] at aux
  rw [aux] at this
  exact this

def key (init : X 0) (ind : (k : ℕ) → ((i : Finset.Ico 0 (k + 1)) → X i) → X (k + 1)) :
    (k : ℕ) → X k
  | 0 => init
  | m + 1 => by
    use ind m (fun i ↦ key init ind i)
    decreasing_by
    exact (Finset.mem_Ico.1 i.2).2

lemma not_mem_symmDiff {s t : Finset ℕ} {x : ℕ} :
    (x ∈ s ∧ x ∈ t) ∨ (x ∉ s ∧ x ∉ t) → x ∉ s ∆ t := by
  rw [Finset.mem_symmDiff.not]
  push_neg
  rintro (⟨hs, ht⟩ | ⟨hs, ht⟩) <;> simp [hs, ht]

theorem firstLemma (A : ℕ → Set (∀ n, X n)) (A_mem : ∀ n, A n ∈ cylinders X) (A_anti : Antitone A)
    (A_inter : ⋂ n, A n = ∅) :
    Tendsto (fun n ↦ kolContent (isProjectiveMeasureFamily_prod μ) (A n)) atTop (𝓝 0) := by
  have A_cyl := fun n ↦ useful (A n) (A_mem n)
  choose N S mS A_eq using A_cyl
  set μ_proj := isProjectiveMeasureFamily_prod μ
  let χ := fun n ↦ (A n).indicator (1 : (∀ n, X n) → ℝ≥0∞)
  have concl : ∀ x, (fun n ↦ kolContent μ_proj (A n)) =
      fun n ↦ (∫⋯∫⁻_Finset.Icc 0 (N n), χ n ∂μ) x := by
    intro x
    ext n
    simp only [χ, A_eq]
    simp_rw [eq μ (Finset.Icc 0 (N n)) (S n) (mS n) x]
  have mχ : ∀ n, Measurable (χ n) := by
    intro n
    simp only [χ, A_eq]
    exact (measurable_indicator_const_iff 1).2 <| measurableSet_cylinder _ _ (mS n)
  have χ_dep : ∀ n, DependsOn (χ n) (Finset.Icc 0 (N n)) := by
    intro n
    simp only [χ, A_eq]
    apply cyl_dependsOn
  have lma_const : ∀ k x y z,
      (fun n ↦(∫⋯∫⁻_Finset.Icc k (N n), χ n ∂μ) (Function.updateFinset x (Finset.Ico 0 k) z)) =
      fun n ↦ (∫⋯∫⁻_Finset.Icc k (N n), χ n ∂μ) (Function.updateFinset y (Finset.Ico 0 k) z) := by
    intro k x y z; ext n
    have := lmarginal_dependsOn (μ := μ) (Finset.Icc k (N n)) (χ_dep n)
    have := updateFinset_dependsOn this (Finset.Ico 0 k) z
    have aux : (Finset.Icc 0 (N n) \ Finset.Icc k (N n)) \ Finset.Ico 0 k = ∅ := by
      ext i
      simp
      intro h1 h2
      by_contra!
      linarith [h1, h2 this]
    apply this
    rw [aux]
    simp
  have anti : Antitone χ := by
    intro m n hmn y
    simp only [χ]
    apply indicator_le
    intro a ha
    simp [A_anti hmn ha]
  have anti_lma : ∀ k x, Antitone fun n ↦ (∫⋯∫⁻_Finset.Icc k (N n), χ n ∂μ) x := by
    intro k x m n hmn
    simp
    rw [lmarginal_eq'' (χ_dep n) (mχ n) (Finset.Icc k (N n))
        ((Finset.Icc k (N n)) ∪ (Finset.Icc k (N m))),
      lmarginal_eq'' (χ_dep m) (mχ m) (Finset.Icc k (N m))
        ((Finset.Icc k (N n)) ∪ (Finset.Icc k (N m)))]
    · exact lmarginal_mono (anti hmn) x
    · rw [Finset.disjoint_iff_inter_eq_empty]
      ext i
      simp
      by_cases h : k ≤ i
      · exact fun h' ↦ not_mem_symmDiff <| Or.inl ⟨(Finset.mem_Icc.2 ⟨h, h'⟩),
          (Finset.mem_union_right _ (Finset.mem_Icc.2 ⟨h, h'⟩))⟩
      · refine fun _ ↦ not_mem_symmDiff <| Or.inr ⟨?_, ?_⟩
        · exact fun h' ↦ h (Finset.mem_Icc.1 h').1
        · exact Finset.not_mem_union.2
            ⟨fun h' ↦ h (Finset.mem_Icc.1 h').1, fun h' ↦ h (Finset.mem_Icc.1 h').1⟩
    · rw [Finset.disjoint_iff_inter_eq_empty]
      ext i
      simp
      by_cases h : k ≤ i
      · exact fun h' ↦ not_mem_symmDiff <| Or.inl ⟨(Finset.mem_Icc.2 ⟨h, h'⟩),
          (Finset.mem_union_left _ (Finset.mem_Icc.2 ⟨h, h'⟩))⟩
      · refine fun _ ↦ not_mem_symmDiff <| Or.inr ⟨?_, ?_⟩
        · exact fun h' ↦ h (Finset.mem_Icc.1 h').1
        · exact Finset.not_mem_union.2
            ⟨fun h' ↦ h (Finset.mem_Icc.1 h').1, fun h' ↦ h (Finset.mem_Icc.1 h').1⟩
  have : ∀ k x, ∃ l, Tendsto (fun n ↦ (∫⋯∫⁻_Finset.Icc k (N n), χ n ∂μ) x) atTop (𝓝 l) := by
    intro k x
    have := tendsto_of_antitone <| anti_lma k x
    rcases this with h | h
    · rw [OrderBot.atBot_eq] at h
      exact ⟨0, h.mono_right <| pure_le_nhds 0⟩
    · exact h
  choose l hl using this
  have l_const : ∀ x y, l 0 x = l 0 y := by
    intro x y
    have := hl 0 x
    have aux := lma_const 0 x y Classical.ofNonempty
    rw [Finset.Ico_self 0] at aux
    simp [Function.updateFinset] at aux
    rw [aux] at this
    exact tendsto_nhds_unique this (hl 0 _)
  have : ∃ l', ∀ x, l 0 x = l' := by
    use l 0 Classical.ofNonempty
    exact fun x ↦ l_const ..
  choose l' hl' using this
  have hpos : ∀ x n, l' ≤ (∫⋯∫⁻_Finset.Icc 0 (N n), χ n ∂μ) x := by
    intro x n
    exact hl' x ▸ ((anti_lma 0 _).le_of_tendsto (hl 0 _)) n
  have χ_le : ∀ n x, χ n x ≤ 1 := by
    intro n x
    simp [χ]
    apply Set.indicator_le
    simp
  rcases auxiliaire μ χ N χ_dep mχ 1 (by norm_num) χ_le 0 (anti_lma 1) (l 1) (hl 1) l'
    Classical.ofNonempty hpos with ⟨init, hinit⟩
  simp [Function.updateFinset_def] at hinit
  choose! ind hind using
    fun k y h ↦ auxiliaire μ χ N χ_dep mχ 1 (by norm_num) χ_le (k + 1) (anti_lma (k + 2))
      (l (k + 2)) (hl (k + 2)) l' y h
  let z := key init ind
  have crucial : ∀ k x n, l' ≤ (∫⋯∫⁻_Finset.Icc (k + 1) (N n), χ n ∂μ)
      (Function.updateFinset x (Finset.Icc 0 k) (fun (i : Finset.Icc 0 k) ↦ z i)) := by
    intro k
    induction k with
    | zero =>
      intro x n
      have : Function.updateFinset x (Finset.Icc 0 0) (fun i ↦ z i) =
          Function.update x 0 (z 0) := by
        ext i
        simp [Function.updateFinset, Function.update]
        split_ifs with h
        · aesop
        · rfl
      rw [this]
      convert hinit x n
    | succ m hm =>
      intro x n
      have : Function.updateFinset x (Finset.Icc 0 (m + 1)) (fun i ↦ z i) =
          Function.update (Function.updateFinset x (Finset.Icc 0 m) (fun i ↦ z i))
          (m + 1) (z (m + 1)) := by
        ext i
        simp [Function.updateFinset, Function.update]
        by_cases hi : i ≤ m + 1
        · simp [hi]
          by_cases hi' : i = m + 1
          · simp [hi']
            aesop
          · have : i ≤ m := Nat.lt_succ.1 <| lt_iff_le_and_ne.2 ⟨hi, hi'⟩
            simp [hi', this]
        have h1 : ¬i = m + 1 := fun h ↦ hi (le_of_eq h)
        have h2 : ¬i ≤ m := fun h ↦ hi (le_trans h (Nat.le_succ _))
        simp [hi, h1, h2]
      rw [this]
      convert hind m (fun i ↦ z i) hm x n using 2
  by_cases l'_eq : 0 < l'
  · have incr : ∀ n, z ∈ A n := by
      intro n
      have : χ n z = (∫⋯∫⁻_Finset.Icc (N n + 1) (N n), χ n ∂μ)
          (Function.updateFinset z (Finset.Icc 0 (N n)) (fun i ↦ z i)) := by
        rw [Finset.Icc_eq_empty, lmarginal_empty]
        congr
        ext i
        by_cases h : i ∈ Finset.Icc 0 (N n) <;> simp [Function.updateFinset, h]
        simp
      have : 0 < χ n z := by
        rw [this]
        exact lt_of_lt_of_le l'_eq (crucial _ _ _)
      exact mem_of_indicator_ne_zero (ne_of_lt this).symm
    exact (A_inter ▸ mem_iInter.2 incr).elim
  · have : l' = 0 := nonpos_iff_eq_zero.1 <| not_lt.1 l'_eq
    rw [concl Classical.ofNonempty]
    rw [← this, ← hl' Classical.ofNonempty]
    exact hl _ _

theorem kolContent_sigma_subadditive_bis ⦃f : ℕ → Set (∀ n, X n)⦄
    (hf : ∀ i, f i ∈ cylinders X) (hf_Union : (⋃ i, f i) ∈ cylinders X) :
    kolContent (isProjectiveMeasureFamily_prod μ) (⋃ i, f i) ≤
    ∑' i, kolContent (isProjectiveMeasureFamily_prod μ) (f i) := by
  refine (kolContent (isProjectiveMeasureFamily_prod μ)).sigma_subadditive_of_sigma_additive
    setRing_cylinders (fun f hf hf_Union hf' ↦ ?_) f hf hf_Union
  refine sigma_additive_addContent_of_tendsto_zero setRing_cylinders
    (kolContent (isProjectiveMeasureFamily_prod μ)) (fun hs ↦ ?_) ?_ hf hf_Union hf'
  · rename_i s
    rcases useful _ hs with ⟨N, S, mS, s_eq⟩
    rw [s_eq, eq μ (mS := mS) (x := Classical.ofNonempty)]
    refine ne_of_lt (lt_of_le_of_lt ?_ (by norm_num : (1 : ℝ≥0∞) < ⊤))
    rw [← lmarginal_const (μ := μ) (s := Finset.Icc 0 N) 1 Classical.ofNonempty]
    apply lmarginal_mono
    intro x
    apply Set.indicator_le
    simp
  · intro s hs anti_s inter_s
    exact firstLemma μ s hs anti_s inter_s

noncomputable def measure_produit : Measure (∀ n, X n) :=
  Measure.ofAddContent setSemiringCylinders generateFrom_cylinders
    (kolContent (isProjectiveMeasureFamily_prod μ))
    (kolContent_sigma_subadditive_bis μ)

theorem isProjectiveLimit_measure_produit :
    IsProjectiveLimit (measure_produit μ) (fun S : Finset ℕ ↦ (Measure.pi (fun n : S ↦ μ n))) := by
  intro S
  ext1 s hs
  rw [Measure.map_apply _ hs]
  swap; · apply measurable_proj
  have h_mem : (fun (x : ∀ n : ℕ, (fun i : ℕ ↦ X i) n) (n : ↥S) ↦ x ↑n) ⁻¹' s ∈ cylinders X := by
    rw [mem_cylinders]; exact ⟨S, s, hs, rfl⟩
  rw [measure_produit, Measure.ofAddContent_eq _ _ _ _ h_mem,
    kolContent_congr (isProjectiveMeasureFamily_prod μ) h_mem rfl hs]

theorem prod_meas (S : Finset ℕ) (a : ℕ) (ha : a ∈ S) (μ : (n : S) → Measure (X n))
    [∀ n, IsProbabilityMeasure (μ n)]
    (s : (n : S) → Set (X n)) :
    (Measure.pi μ) (univ.pi s) = ((μ ⟨a, ha⟩) (s ⟨a, ha⟩)) *
    ((Measure.pi (fun (n : S.erase a) ↦ μ ⟨n.1, Finset.mem_of_mem_erase n.2⟩))
    (univ.pi (fun n : S.erase a ↦ s ⟨n.1, Finset.mem_of_mem_erase n.2⟩))) := by
  rw [Measure.pi_pi, Measure.pi_pi, mul_comm]
  have h1 : (@Finset.univ S _).prod (fun n ↦ (μ n) (s n)) =
      (@Finset.univ S.toSet _).prod (fun n ↦
      ((fun n : ℕ ↦ if hn : n ∈ S then (μ ⟨n, hn⟩) (s ⟨n, hn⟩) else 1) n)) := by
    apply Finset.prod_congr rfl (by simp)
  have h2 : (@Finset.univ (S.erase a) _).prod (fun n ↦ (μ ⟨n.1, Finset.mem_of_mem_erase n.2⟩)
      (s ⟨n.1, Finset.mem_of_mem_erase n.2⟩)) =
      (@Finset.univ (S.erase a).toSet _).prod (fun n ↦
      ((fun n : ℕ ↦ if hn : n ∈ S then (μ ⟨n, hn⟩) (s ⟨n, hn⟩) else 1) n)) := by
    apply Finset.prod_congr rfl (fun x _ ↦ by simp [(Finset.mem_erase.1 x.2).2])
  rw [h1, h2,
    Finset.prod_set_coe (f := (fun n : ℕ ↦ if hn : n ∈ S then (μ ⟨n, hn⟩) (s ⟨n, hn⟩) else 1)),
    Finset.prod_set_coe (f := (fun n : ℕ ↦ if hn : n ∈ S then (μ ⟨n, hn⟩) (s ⟨n, hn⟩) else 1)),
    Finset.toFinset_coe, Finset.toFinset_coe, ← Finset.prod_erase_mul S _ ha]
  congr
  simp [ha]


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
    --     cylinder (α := fun k : {k | k ≥ 1} ↦ X k)
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
