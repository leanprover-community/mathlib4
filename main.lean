import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.KolmogorovExtension4.Projective
import Mathlib.KolmogorovExtension4.KolmogorovExtension
import Mathlib.Topology.Defs.Filter
-- import Mathlib.KolmogorovExtension4.section_file
import Mathlib.KolmogorovExtension4.DependsOn
import Mathlib.MeasureTheory.Integral.Marginal

open Set MeasureTheory Filter Topology ENNReal Finset symmDiff

theorem preimage_proj {ι : Type*} {X : ι → Type*} (I J : Finset ι) [∀ j : J, Decidable (j.1 ∈ I)]
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

open scoped Classical in
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

noncomputable def proba (s : Finset ℕ) (S : Set ((n : s) → X n)) : ℝ≥0∞ :=
  (∫⋯∫⁻_s, (cylinder s S).indicator 1 ∂μ) (Classical.ofNonempty)

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

theorem bonjour' (f : ℕ → (∀ n, X n) → ℝ≥0∞) (anti : Antitone f) (ε : ℝ≥0∞) (k : ℕ)
    (N : ℕ → ℕ) (hcte : ∀ n, DependsOn (f n) (Finset.Icc 0 (N n))) (mf : ∀ n, Measurable (f n))
    (bound : ℝ≥0∞) (le_bound : ∀ n x, f n x ≤ bound) (fin_bound : bound ≠ ∞)
    (y : (n : Finset.Ico 0 k) → X n)
    (hpos : ∀ x, ∀ n,
    ε ≤ (∫⋯∫⁻_Finset.Icc k (N n), f n ∂μ) (Function.updateFinset x (Finset.Ico 0 k) y)) :
    ∃ z, ∀ x n, ε ≤ (∫⋯∫⁻_Finset.Icc (k + 1) (N n), f n ∂μ)
    (Function.update (Function.updateFinset x (Finset.Ico 0 k) y) k z) := by
  let F : ℕ → (∀ n, X n) → ℝ≥0∞ := fun n ↦ (∫⋯∫⁻_Finset.Icc (k + 1) (N n), f n ∂μ)
  have antiF : Antitone F := by
    intro m n hmn
    simp only [F]
    rw [lmarginal_eq'' (hcte n) (mf n) (Finset.Icc (k + 1) (N n))
        ((Finset.Icc (k + 1) (N n)) ∪ (Finset.Icc (k + 1) (N m))),
      lmarginal_eq'' (hcte m) (mf m) (Finset.Icc (k + 1) (N m))
        ((Finset.Icc (k + 1) (N n)) ∪ (Finset.Icc (k + 1) (N m)))]
    apply lmarginal_mono <| anti hmn
    rw [symmDiff_def, disjoint_sup_right]
    constructor
    · rw [Finset.sdiff_eq_empty_iff_subset.2]
      exact Finset.disjoint_empty_right _
      exact Finset.subset_union_right ..
    · rw [Finset.union_sdiff_right, Finset.disjoint_iff_inter_eq_empty, ← Finset.inter_sdiff_assoc,
        Finset.inter_comm, Finset.inter_sdiff_assoc]
      ext i
      simp only [Finset.mem_inter, Finset.mem_Icc, mem_sdiff, zero_le, true_and, not_and, not_le,
        Finset.not_mem_empty, iff_false, Classical.not_imp, not_lt, and_imp]
      exact fun h1 _ h2 ↦ ⟨h1, h2⟩
    rw [symmDiff_def, disjoint_sup_right]
    constructor
    · rw [Finset.sdiff_eq_empty_iff_subset.2]
      exact Finset.disjoint_empty_right _
      exact Finset.subset_union_left ..
    · rw [Finset.union_sdiff_left, Finset.disjoint_iff_inter_eq_empty, ← Finset.inter_sdiff_assoc,
        Finset.inter_comm, Finset.inter_sdiff_assoc]
      ext i
      simp [Finset.mem_Icc]
      exact fun h1 _ h2 ↦ ⟨h1, h2⟩
  have tendstoF : ∀ x, ∃ l, Tendsto (F · x) atTop (𝓝 l) := by
    intro x
    have : Antitone (F · x) := fun m n hmn ↦ antiF hmn x
    have := tendsto_of_antitone this
    rcases this with h | h
    · rw [OrderBot.atBot_eq] at h
      exact ⟨0, h.mono_right <| pure_le_nhds 0⟩
    · exact h
  choose l hl using tendstoF
  have f_eq : ∀ x, (fun n ↦ (∫⋯∫⁻_Finset.Icc k (N n), f n ∂μ) x) =
      fun n ↦ (∫⋯∫⁻_{k}, F n ∂μ) x := by
    intro x
    ext1 n
    by_cases h : k ≤ N n
    · rw [Finset.Icc_eq_left_union h, lmarginal_union]
      exact mf n
      simp
    · simp [F]
      rw [Finset.Icc_eq_empty h, lmarginal_eq (hcte n), lmarginal_eq (hcte n),
        lmarginal_eq (hcte n)]
      · simp [Finset.mem_Icc, h]
      · rw [Finset.disjoint_iff_inter_eq_empty]
        ext i
        simp [Finset.mem_Icc]
        exact fun h1 h2 ↦ by linarith [h, h1, h2]
      · simp
  have F_le : ∀ n x, F n x ≤ bound := by
    intro n x
    rw [← lmarginal_const (μ := μ) (s := Finset.Icc (k + 1) (N n)) bound x]
    apply lmarginal_mono
    exact le_bound n
  have tendsto_int : ∀ x, Tendsto (fun n ↦ (∫⋯∫⁻_Finset.Icc k (N n), f n ∂μ) x) atTop
      (𝓝 ((∫⋯∫⁻_{k}, l ∂μ) x)) := by
    intro x
    simp_rw [f_eq, lmarginal_singleton]
    apply tendsto_lintegral_of_dominated_convergence (fun _ ↦ bound)
    · intro n
      apply ((mf n).lmarginal μ).comp <| measurable_update ..
    · intro n
      apply eventually_of_forall
      intro y
      apply F_le n
    · rw [lintegral_const]
      simp [fin_bound]
    apply eventually_of_forall
    simp [hl]
  have le_int_l : ∀ x, ε ≤ (∫⋯∫⁻_{k}, l ∂μ) (Function.updateFinset x _ y) := by
    intro x
    apply ge_of_tendsto (tendsto_int _)
    simp [hpos]
  have : ∀ x, ε ≤ ∫⁻ xₐ : X k,
    l (Function.update (Function.updateFinset x _ y) k xₐ) ∂μ k := by
    simp_rw [lmarginal_singleton] at le_int_l
    exact le_int_l
  let x_ : ∀ n, X n := Classical.ofNonempty
  have : ∃ x', ε ≤ l (Function.update
      (Function.updateFinset x_ _ y) k x') := by
    simp_rw [lmarginal_singleton] at le_int_l
    apply ge_of_int (le_int_l x_)
    apply ne_top_of_le_ne_top fin_bound
    rw [← mul_one bound, ← measure_univ (μ := μ k), ← lintegral_const]
    apply lintegral_mono
    intro y
    apply le_of_tendsto' (hl _)
    simp [F_le]
  rcases this with ⟨x', hx'⟩
  use x'
  intro x n
  have : ∀ x, Antitone (F · x) := fun x ↦ fun m n hmn ↦ antiF hmn x
  have := le_trans hx' ((this _).le_of_tendsto (hl _) n)
  have aux : F n (Function.update
      (Function.updateFinset x_ (Finset.Ico 0 k) y) k x') =
      F n (Function.update
      (Function.updateFinset x (Finset.Ico 0 k) y) k x') := by
    simp only [F]
    apply lmarginal_dependsOn _ (hcte n)
    intro i hi
    simp only [mem_sdiff, Finset.mem_Icc, zero_le, true_and, not_and, not_le] at hi
    have : i ≤ k := by
      rw [← Nat.lt_succ]
      by_contra!
      linarith [hi.1, hi.2 this]
    simp only [Function.update, Function.updateFinset, Nat.Ico_zero_eq_range, Finset.mem_range]
    split_ifs with h1 h2
    · rfl
    · rfl
    · exact (not_or.2 ⟨h2, h1⟩ <| Nat.le_iff_lt_or_eq.1 this).elim
  rw [aux] at this
  exact this

def key (init : X 0) (ind : (k : ℕ) → ((i : Finset.Icc 0 k) → X i) → X (k + 1)) :
    (k : ℕ) → X k
  | 0 => init
  | m + 1 => by
    use ind m (fun i ↦ key init ind i)
    decreasing_by
    exact Nat.lt_succ_iff.2 (Finset.mem_Icc.1 i.2).2

example (a : ℝ≥0∞) (h : ¬0 < a) : a = 0 := nonpos_iff_eq_zero.1 <| not_lt.1 h

open scoped Classical in
theorem firstLemma (A : ℕ → Set (∀ n, X n)) (A_mem : ∀ n, A n ∈ cylinders X) (A_anti : Antitone A)
    (A_inter : ⋂ n, A n = ∅) :
    Tendsto (kolContent (isProjectiveMeasureFamily_prod μ) ∘ A) atTop (𝓝 0) := by
  have A_cyl := fun n ↦ useful (A n) (A_mem n)
  choose NA SA mSA A_eq using A_cyl
  set μ_proj := isProjectiveMeasureFamily_prod μ
  let χA := fun n ↦ (A n).indicator (1 : (∀ n, X n) → ℝ≥0∞)
  have concl : ∀ x, (kolContent μ_proj) ∘ A =
      fun n ↦ (∫⋯∫⁻_Finset.Icc 0 (NA n), χA n ∂μ) x := by
    intro x
    ext n
    simp [A_eq, Function.updateFinset_def, χA]
    simp_rw [eq μ (Finset.Icc 0 (NA n)) (SA n) (mSA n) x]
  have mχA : ∀ n, Measurable (χA n) := by
    intro n
    simp [χA, A_eq]
    have : (1 : (∀ n, X n) → ℝ≥0∞) = fun x ↦ 1 := rfl
    rw [this, measurable_indicator_const_iff]
    apply measurableSet_cylinder
    exact mSA n
  have χA_dep : ∀ n, DependsOn (χA n) (Finset.Icc 0 (NA n)) := by
    intro n
    simp [χA, A_eq]
    apply cyl_dependsOn
  have anti : Antitone χA := by
    intro m n hmn y
    simp [χA]
    apply indicator_le
    intro a ha
    simp [A_anti hmn ha]
  have anti_lma : ∀ x, Antitone fun n ↦ (∫⋯∫⁻_Finset.Icc 0 (NA n), χA n ∂μ) x := by
    intro x m n hmn
    simp
    rw [lmarginal_eq'' (χA_dep n) (mχA n) (Finset.Icc 0 (NA n))
        ((Finset.Icc 0 (NA n)) ∪ (Finset.Icc 0 (NA m)))]
    rw [lmarginal_eq'' (χA_dep m) (mχA m) (Finset.Icc 0 (NA m))
        ((Finset.Icc 0 (NA n)) ∪ (Finset.Icc 0 (NA m)))]
    exact lmarginal_mono (anti hmn) x
    rw [symmDiff_def, disjoint_sup_right]
    constructor
    · rw [Finset.sdiff_eq_empty_iff_subset.2]
      exact Finset.disjoint_empty_right _
      exact Finset.subset_union_right ..
    · rw [Finset.union_sdiff_right, Finset.disjoint_iff_inter_eq_empty, ← Finset.inter_sdiff_assoc,
        Finset.inter_comm, Finset.inter_sdiff_assoc]
      simp
    rw [symmDiff_def, disjoint_sup_right]
    constructor
    · rw [Finset.sdiff_eq_empty_iff_subset.2]
      exact Finset.disjoint_empty_right _
      exact Finset.subset_union_left ..
    · rw [Finset.union_sdiff_left, Finset.disjoint_iff_inter_eq_empty, ← Finset.inter_sdiff_assoc,
        Finset.inter_comm, Finset.inter_sdiff_assoc]
      simp
  have : ∀ x, ∃ l, Tendsto (fun n ↦ (∫⋯∫⁻_Finset.Icc 0 (NA n), χA n ∂μ) x) atTop (𝓝 l) := by
    intro x
    have := tendsto_of_antitone <| anti_lma x
    rcases this with h | h
    · rw [OrderBot.atBot_eq] at h
      exact ⟨0, h.mono_right <| pure_le_nhds 0⟩
    · exact h
  choose l hl using this
  have l_const : ∀ x y, l x = l y := by
    intro x y
    have lol : (fun n ↦ (∫⋯∫⁻_Finset.Icc 0 (NA n), χA n ∂μ) x) =
        fun n ↦ (∫⋯∫⁻_Finset.Icc 0 (NA n), χA n ∂μ) y := by
      ext n
      apply lmarginal_dependsOn (Finset.Icc 0 (NA n)) (χA_dep n)
      simp
    have := hl x
    rw [lol] at this
    exact tendsto_nhds_unique this (hl y)
  have : ∃ l', ∀ x, l x = l' := by
    use l Classical.ofNonempty
    exact fun x ↦ l_const ..
  rcases this with ⟨l', hl'⟩
  have : ∀ n x, l' ≤ (∫⋯∫⁻_Finset.Icc 0 (NA n), χA n ∂μ) x := by
    intro n x
    exact hl' x ▸ ((anti_lma x).le_of_tendsto (hl x)) n
  have χA_le : ∀ n x, χA n x ≤ 1 := by
    intro n x
    simp [χA]
    apply Set.indicator_le
    simp
  have hpos : ∀ y x n,
      l' ≤ (∫⋯∫⁻_Finset.Icc 0 (NA n), χA n ∂μ) (Function.updateFinset x (Finset.Ico 0 0) y) := by
    exact fun _ x n ↦ this n x
  rcases bonjour' μ χA anti l' 0 NA χA_dep mχA 1 χA_le (by norm_num)
    Classical.ofNonempty (hpos (Classical.ofNonempty)) with ⟨init, hinit⟩
  simp [Function.updateFinset_def] at hinit
  choose! ind hind using
    fun k y h ↦ bonjour' μ χA anti l' (k + 1) NA χA_dep mχA 1 χA_le (by norm_num) y h
  let z := key init ind
  have crucial : ∀ k x n, l' ≤ (∫⋯∫⁻_Finset.Icc (k + 1) (NA n), χA n ∂μ)
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
      have : χA n z = (∫⋯∫⁻_Finset.Icc (NA n + 1) (NA n), χA n ∂μ)
          (Function.updateFinset z (Finset.Icc 0 (NA n)) (fun i ↦ z i)) := by
        rw [Finset.Icc_eq_empty, lmarginal_empty]
        congr
        ext i
        by_cases h : i ∈ Finset.Icc 0 (NA n) <;> simp [Function.updateFinset, h]
        simp
      have : 0 < χA n z := by
        rw [this]
        exact lt_of_lt_of_le l'_eq (crucial _ _ _)
      exact mem_of_indicator_ne_zero (ne_of_lt this).symm
    exact (A_inter ▸ mem_iInter.2 incr).elim
  · have : l' = 0 := nonpos_iff_eq_zero.1 <| not_lt.1 l'_eq
    rw [concl Classical.ofNonempty]
    rw [← this, ← hl' Classical.ofNonempty]
    exact hl _


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
