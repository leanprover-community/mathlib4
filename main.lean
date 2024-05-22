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
  ext x; simp
  refine ⟨fun h i hi ↦ ?_, fun h i i_mem ↦ by simpa [i_mem] using h i (hIJ i_mem)⟩
  by_cases i_mem : i ∈ I
  · simp [i_mem, h i i_mem]
  · simp [i_mem]

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)] [∀ n, Nonempty (X n)]
variable (μ : (n : ℕ) → Measure (X n)) [∀ n, IsProbabilityMeasure (μ n)]

open scoped Classical in
theorem isProjectiveMeasureFamily_prod {ι : Type*} {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (m : (i : ι) → Measure (α i)) [∀ i, IsProbabilityMeasure (m i)] :
    IsProjectiveMeasureFamily (fun S : Finset ι ↦ (Measure.pi (fun n : S ↦ m n))) := by
  intro T S hST
  -- simp only
  refine Measure.pi_eq (fun s ms ↦ ?_)
  rw [Measure.map_apply (measurable_proj₂' (α := α) T S hST) (MeasurableSet.univ_pi ms),
    preimage_proj S T hST, Measure.pi_pi]
  let e : S ≃ {a : T | a.1 ∈ S} :=
    {
      toFun := fun a ↦ ⟨⟨a.1, hST a.2⟩, a.2⟩,
      invFun := fun a ↦ ⟨a.1.1, a.2⟩,
      left_inv := by simp [Function.LeftInverse]
      right_inv := by simp [Function.RightInverse, Function.LeftInverse]
    }
  conv_rhs =>
    change Finset.univ.prod (fun i ↦ ((fun i : S ↦ (m i) (s i)) ∘ e.invFun) (e i))
    rw [e.prod_comp]
  have : (fun i ↦ (((fun j : S ↦ (m j) (s j)) ∘ e.invFun) i)) =
      fun i : {a : T | a.1 ∈ S} ↦
      (fun i : T ↦ (m i) (if h : i.1 ∈ S then s ⟨i, h⟩ else univ)) i := by
    ext i
    have : i.1.1 ∈ S := i.2
    simp [this]
  rw [this, Finset.prod_set_coe (f := fun i : T ↦ (m i) (if h : i.1 ∈ S then s ⟨i, h⟩ else univ))]
  refine (Finset.prod_subset (Finset.subset_univ _) (fun x _ hx ↦ ?_)).symm
  simp only [mem_setOf_eq, toFinset_setOf, Finset.univ_eq_attach, Finset.mem_filter,
    Finset.mem_attach, true_and] at hx
  simp [hx]

theorem cylinders_nat : cylinders X =
    ⋃ (N) (S) (_ : MeasurableSet S), {cylinder (Icc 0 N) S} := by
  ext s; simp
  constructor
  rintro ⟨t, S, mS, rfl⟩
  · use t.sup id
    use (fun (f : (∀ n : Finset.Icc 0 (t.sup id), X n)) (k : t) ↦
      f ⟨k.1, Finset.mem_Icc.2 ⟨Nat.zero_le k.1, Finset.le_sup (f := id) k.2⟩⟩) ⁻¹' S
    constructor
    · apply mS.preimage
      rw [measurable_pi_iff]
      intro a
      measurability
    · dsimp only [cylinder]
      rw [← preimage_comp]
      rfl
  · rintro ⟨N, S, mS, rfl⟩
    exact ⟨Finset.Icc 0 N, S, mS, rfl⟩

lemma useful (s : Set (∀ n, X n)) (s_mem : s ∈ cylinders X) :
    ∃ N S, MeasurableSet S ∧ s = cylinder (Finset.Icc 0 N) S := by
  simpa [cylinders_nat] using s_mem

noncomputable def proba (s : Finset ℕ) (S : Set ((n : s) → X n)) : ℝ≥0∞ :=
  (∫⋯∫⁻_s, (cylinder s S).indicator 1 ∂μ) (Classical.ofNonempty)

theorem eq (s : Finset ℕ) (S : Set ((n : s) → X n)) :
  kolContent (isProjectiveMeasureFamily_prod μ) ((cylinder s S)) = proba μ s S := by sorry

#check Finset.Icc

theorem cyl_dependsOn (s : Finset ℕ) (S : Set ((n : s) → X n)) :
    DependsOn ((cylinder s S).indicator (1 : (∀ n, X n) → ℝ≥0∞)) s := by
  intro x y hxy
  have xy : (fun (i : s) ↦ x i) = fun (i : s) ↦ y i := by simp [hxy]
  by_cases h : x ∈ cylinder s S
  · simp [h]
    have : y ∈ cylinder s S := by
      simp at *
      rwa [← xy]
    simp [this]
  · simp [h]
    have : y ∉ cylinder s S := by
      simp at *
      rwa [← xy]
    simp [this]

theorem ge_of_int {α : Type*} [MeasurableSpace α] {m : Measure α} [IsProbabilityMeasure m]
    (ε : ℝ≥0∞) (f : α → ℝ≥0∞) (hf : ε ≤ ∫⁻ a, f a ∂m) (fin_lint : ∫⁻ a, f a ∂m ≠ ∞) :
    ∃ a, ε ≤ f a := by
  by_contra!
  have : ∫⁻ a, f a ∂m < ε := by
    rw [← mul_one ε, ← measure_univ (μ := m), ← lintegral_const]
    apply lintegral_strict_mono
    · exact Ne.symm (NeZero.ne' m)
    · simp
    · exact fin_lint
    · simp [this]
  exact not_le_of_lt this hf

example (n : ℕ) (h : n ≠ 0) : n - 1 + 1 = n := by exact Nat.succ_pred_eq_of_ne_zero h

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

example (n : ℕ) (h : n ≠ 0) : 1 ≤ n := by exact Nat.one_le_iff_ne_zero.2 h

theorem omg (k N : ℕ) (h : k ≤ N) : Finset.Icc k N = (Finset.Icc (k + 1) N) ∪ {k} := by
  ext x; simp [Finset.mem_Icc]; constructor
  · rintro ⟨h1, h2⟩
    by_cases hxk : x = k
    · exact Or.inr hxk
    · refine Or.inl ⟨?_, h2⟩
      rw [Nat.succ_le]
      exact Nat.lt_of_le_of_ne h1 fun a => hxk (id (Eq.symm a))
  · rintro (⟨h1, h2⟩ | h')
    · exact ⟨Nat.le_of_succ_le h1, h2⟩
    · exact ⟨h' ▸ le_refl _, h' ▸ h⟩

example : μ 0 ≠ 0 := by exact Ne.symm (NeZero.ne' (μ 0))

lemma important (k : ℕ) (y : ∀ n : Finset.Icc 0 k, X n) (z : X (k + 1)) :
    ∃ t, ∀ x : ∀ n, X n, Function.update (Function.updateFinset x (Finset.Icc 0 k) y) (k + 1) z =
    Function.updateFinset x (Finset.Icc 0 (k + 1)) t := by
  let t : ∀ n : Finset.Icc 0 (k + 1), X n := fun n ↦ by
    cases n with
    | mk i hi =>
      by_cases h : i = k + 1
      · use h ▸ z
      · have : i ∈ Finset.Icc 0 k := by
          rw [Finset.mem_Icc] at *
          simp
          rcases Nat.le_or_eq_of_le_succ hi.2 with h' | h'
          exact h'
          exact (h h').elim
        use y ⟨i, this⟩
  use t
  intro x
  ext i
  simp [Function.update, Function.updateFinset]
  by_cases h : i = k + 1
  · simp [h, t]
    aesop
  · simp [h, t]
    by_cases h' : i ≤ k
    · have : i ≤ k + 1 := le_trans h' (Nat.le_succ _)
      simp [h', this]
    · have : ¬i ≤ k + 1 := by
        intro h''
        rcases Nat.le_iff_lt_or_eq.1 h'' with h'' | h''
        linarith [h', h'']
        exact h h''
      simp [h', this]

theorem thm1 (f : ℕ → (∀ n, X n) → ℝ≥0∞) (anti : Antitone f) (ε : ℝ≥0∞)
    (N : ℕ → ℕ) (hcte : ∀ n, DependsOn (f n) (Finset.Icc 0 (N n)))
    (mf : ∀ n, Measurable (f n)) (x : ∀ n, X n)
    (bound : ℝ≥0∞) (le_bound : ∀ n y, f n y ≤ bound) (fin_bound : bound ≠ ∞)
    (hpos : ∀ n, ε ≤ (∫⋯∫⁻_Finset.Icc 0 (N n), f n ∂μ) x) :
    ∃ x₀, ∀ n, ε ≤ (∫⋯∫⁻_Finset.Icc 1 (N n), f n ∂μ)
    (Function.updateFinset x (Finset.Icc 0 0) x₀) := by
  let F : ℕ → (∀ n, X n) → ℝ≥0∞ := fun n ↦ (∫⋯∫⁻_Finset.Icc 1 (N n), f n ∂μ)
  have antiF : Antitone F := by
    intro m n hmn
    simp [F]
    rw [lmarginal_eq'' (hcte n) (mf n) (Finset.Icc 1 (N n))
        ((Finset.Icc 1 (N n)) ∪ (Finset.Icc 1 (N m))),
      lmarginal_eq'' (hcte m) (mf m) (Finset.Icc 1 (N m))
        ((Finset.Icc 1 (N n)) ∪ (Finset.Icc 1 (N m)))]
    apply lmarginal_mono <| anti hmn
    rw [symmDiff_def, disjoint_sup_right]
    constructor
    · rw [Finset.sdiff_eq_empty_iff_subset.2]
      exact Finset.disjoint_empty_right _
      exact Finset.subset_union_right ..
    · rw [Finset.union_sdiff_right, Finset.disjoint_iff_inter_eq_empty, ← Finset.inter_sdiff_assoc,
        Finset.inter_comm, Finset.inter_sdiff_assoc]
      ext i
      simp [Finset.mem_Icc]
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
  have f_eq : ∀ x, (fun n ↦ (∫⋯∫⁻_Finset.Icc 0 (N n), f n ∂μ) x) =
      fun n ↦ (∫⋯∫⁻_{0}, F n ∂μ) x := by
    intro x
    ext1 n
    rw [omg 0 (N n), lmarginal_union']
    exact mf n
    simp [Finset.mem_Icc]
    simp
  have F_le : ∀ n x, F n x ≤ bound := by
    intro n x
    rw [← lmarginal_const (μ := μ) (s := Finset.Icc 1 (N n)) bound x]
    apply lmarginal_mono
    exact le_bound n
  have tendsto_int : ∀ x, Tendsto (fun n ↦ (∫⋯∫⁻_Finset.Icc 0 (N n), f n ∂μ) x) atTop
      (𝓝 ((∫⋯∫⁻_{0}, l ∂μ) x)) := by
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
  have le_int_l : ε ≤ (∫⋯∫⁻_{0}, l ∂μ) x := by
    apply ge_of_tendsto (tendsto_int _)
    simp [hpos]
  have imp : ∀ y, ∃ z, Function.update x 0 y = Function.updateFinset x (Finset.Icc 0 0) z := by
    intro y
    let z : ∀ n : Finset.Icc 0 0, X n := fun n ↦ by
      have := n.2
      simp [Finset.Icc_self 0] at this
      rw [this]
      use y
    use z
    rw [Function.update_eq_updateFinset]
    rfl
  have : ∃ x', ε ≤ l (Function.update x 0 x') := by
    simp_rw [lmarginal_singleton] at le_int_l
    apply ge_of_int ε _ le_int_l
    apply ne_top_of_le_ne_top fin_bound
    rw [← mul_one bound, ← measure_univ (μ := μ 0), ← lintegral_const]
    apply lintegral_mono
    intro y
    apply le_of_tendsto' (hl _)
    simp [F_le]
  rcases this with ⟨x', hx'⟩
  rcases imp x' with ⟨z, hz⟩
  use z
  intro n
  have : ∀ x, Antitone (F · x) := fun x ↦ fun m n hmn ↦ antiF hmn x
  have := le_trans hx' ((this _).le_of_tendsto (hl _) n)
  rw [hz] at this
  exact this

theorem bonjour (f : ℕ → (∀ n, X n) → ℝ≥0∞) (anti : Antitone f) (ε : ℝ≥0∞) (k : ℕ)
    (N : ℕ → ℕ) (hcte : ∀ n, DependsOn (f n) (Finset.Icc 0 (N n))) (mf : ∀ n, Measurable (f n))
    (bound : ℝ≥0∞) (le_bound : ∀ n x, f n x ≤ bound) (fin_bound : bound ≠ ∞)
    (y : (n : Finset.Icc 0 k) → X n)
    (hpos : ∀ x, ∀ n,
    ε ≤ (∫⋯∫⁻_Finset.Icc (k + 1) (N n), f n ∂μ) (Function.updateFinset x (Finset.Icc 0 k) y)) :
    ∃ z, ∀ x n, ε ≤ (∫⋯∫⁻_Finset.Icc (k + 2) (N n), f n ∂μ)
    (Function.update (Function.updateFinset x (Finset.Icc 0 k) y) (k + 1) z) := by
  let F : ℕ → (∀ n, X n) → ℝ≥0∞ := fun n ↦ (∫⋯∫⁻_Finset.Icc (k + 2) (N n), f n ∂μ)
  have F_const : ∀ n x y z, F n (Function.updateFinset x (Finset.Icc 0 (k + 1)) z) =
      F n (Function.updateFinset y (Finset.Icc 0 (k + 1)) z) := by
    simp [F]
    intro n x y z
    apply lmarginal_dependsOn _ (hcte n)
    intro i hi
    simp [Finset.mem_Icc] at hi
    have : i ≤ k + 1 := by
      by_contra!
      rw [← Nat.succ_le_iff] at this
      linarith [hi.1, hi.2 this]
    simp [this, Function.updateFinset]
  have antiF : Antitone F := by
    intro m n hmn
    simp [F]
    rw [lmarginal_eq'' (hcte n) (mf n) (Finset.Icc (k + 2) (N n))
        ((Finset.Icc (k + 2) (N n)) ∪ (Finset.Icc (k + 2) (N m))),
      lmarginal_eq'' (hcte m) (mf m) (Finset.Icc (k + 2) (N m))
        ((Finset.Icc (k + 2) (N n)) ∪ (Finset.Icc (k + 2) (N m)))]
    apply lmarginal_mono <| anti hmn
    rw [symmDiff_def, disjoint_sup_right]
    constructor
    · rw [Finset.sdiff_eq_empty_iff_subset.2]
      exact Finset.disjoint_empty_right _
      exact Finset.subset_union_right ..
    · rw [Finset.union_sdiff_right, Finset.disjoint_iff_inter_eq_empty, ← Finset.inter_sdiff_assoc,
        Finset.inter_comm, Finset.inter_sdiff_assoc]
      ext i
      simp [Finset.mem_Icc]
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
  have f_eq : ∀ x, (fun n ↦ (∫⋯∫⁻_Finset.Icc (k + 1) (N n), f n ∂μ) x) =
      fun n ↦ (∫⋯∫⁻_{k + 1}, F n ∂μ) x := by
    intro x
    ext1 n
    by_cases h : k + 1 ≤ N n
    · rw [omg (k + 1) (N n), lmarginal_union']
      exact mf n
      simp [Finset.mem_Icc]
      exact h
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
    rw [← lmarginal_const (μ := μ) (s := Finset.Icc (k + 2) (N n)) bound x]
    apply lmarginal_mono
    exact le_bound n
  have tendsto_int : ∀ x, Tendsto (fun n ↦ (∫⋯∫⁻_Finset.Icc (k + 1) (N n), f n ∂μ) x) atTop
      (𝓝 ((∫⋯∫⁻_{k + 1}, l ∂μ) x)) := by
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
  have le_int_l : ∀ x, ε ≤ (∫⋯∫⁻_{k + 1}, l ∂μ) (Function.updateFinset x _ y) := by
    intro x
    apply ge_of_tendsto (tendsto_int _)
    simp [hpos]
  have : ∀ x, ε ≤ ∫⁻ xₐ : X (k + 1),
    l (Function.update (Function.updateFinset x _ y) (k + 1) xₐ) ∂μ (k + 1) := by
    simp_rw [lmarginal_singleton] at le_int_l
    exact le_int_l
  let x_ : ∀ n, X n := Classical.ofNonempty
  have : ∃ x', ε ≤ l (Function.update
      (Function.updateFinset x_ (Finset.Icc 0 k) y) (k + 1) x') := by
    simp_rw [lmarginal_singleton] at le_int_l
    apply ge_of_int ε _ (le_int_l x_)
    apply ne_top_of_le_ne_top fin_bound
    rw [← mul_one bound, ← measure_univ (μ := μ (k + 1)), ← lintegral_const]
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
      (Function.updateFinset x_ (Finset.Icc 0 k) y) (k + 1) x') =
      F n (Function.update
      (Function.updateFinset x (Finset.Icc 0 k) y) (k + 1) x') := by
    simp [F]
    apply lmarginal_dependsOn _ (hcte n)
    intro i hi
    simp [Finset.mem_Icc] at hi
    have : i ≤ k + 1 := by
      by_contra!
      rw [← Nat.succ_le_iff] at this
      linarith [hi.1, hi.2 this]
    simp [this, Function.update, Function.updateFinset]
    by_cases h : i = k + 1
    · simp [h]
    · have := Nat.lt_succ.1 <| lt_iff_le_and_ne.2 ⟨this, h⟩
      simp [h, this]
  rw [aux] at this
  exact this

open scoped Classical in
theorem firstLemma (A : ℕ → Set (∀ n, X n)) (A_mem : ∀ n, A n ∈ cylinders X) (A_anti : Antitone A)
    (A_inter : ⋂ n, A n = ∅) :
    Tendsto (kolContent (isProjectiveMeasureFamily_prod μ) ∘ A) atTop (𝓝 0) := by
  have A_cyl := fun n ↦ useful (A n) (A_mem n)
  choose NA SA mSA A_eq using A_cyl
  set μ_proj := isProjectiveMeasureFamily_prod μ
  let χA := fun n ↦ (A n).indicator (1 : (∀ n, X n) → ℝ≥0∞)
  have : ∀ x, (kolContent μ_proj) ∘ A =
      fun n ↦ (∫⋯∫⁻_Finset.Icc 0 (NA n), χA n ∂μ) x := by
    intro x
    ext n
    simp [A_eq, eq, proba, Function.updateFinset_def, χA]
    apply lmarginal_dependsOn (hf := cyl_dependsOn (Finset.Icc 0 (NA n)) (SA n))
    simp
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
  choose a b using
    fun k y h ↦ bonjour μ χA anti l' k NA χA_dep mχA 1 χA_le (by norm_num) y h
  let z : ∀ k, (X k) × (∀ x n, l' ≤ (∫⋯∫⁻_Finset.Icc (k + 1) (NA n), χA n ∂μ)
      (Function.updateFinset x (Finset.Icc 0 k) (fun i : Finset.Icc 0 k ↦ z i))) := by sorry
  have crucial : ∀ k, ∃ z, ∀ x n, l' ≤ (∫⋯∫⁻_Finset.Icc (k + 1) (NA n), χA n ∂μ)
      (Function.updateFinset x (Finset.Icc 0 k) z) := by
    have init := fun x ↦ thm1 μ χA anti l' NA χA_dep mχA x 1 χA_le (by norm_num) (this · x)
    intro k
    induction k with
    | zero => exact init
    | succ m hm => exact fun x ↦ ind m x hm
  let x_ : ∀ n, X n := Classical.ofNonempty
  have crucial' : ∃ z : ∀ n, X n, ∀ k n, l' ≤ (∫⋯∫⁻_Finset.Icc (k + 1) (NA n), χA n ∂μ)
      (Function.updateFinset x_ (Finset.Icc 0 k) (fun i : Finset.Icc 0 k ↦ z i)) := by
    let z : ∀ n, X n := by
      intro n
      induction n
  rw [this]

theorem test (A : ℕ → Set (∀ n, X n)) (A_mem : ∀ n, A n ∈ cylinders X) (A_anti : Antitone A)
    (A_inter : ⋂ n, A n = ∅) :
    Tendsto (kolContent (isProjectiveMeasureFamily_prod μ) ∘ A) atTop (𝓝 0) := by
  have A_cyl := fun n ↦ useful (A n) (A_mem n)
  choose NA SA mSA A_eq using A_cyl
  set μ_proj := isProjectiveMeasureFamily_prod μ
  have : (kolContent μ_proj) ∘ A = fun n ↦ (proba μ (Finset.range (NA n + 1)) (SA n)) := by
    ext n
    simp
    rw [← eq, A_eq n]
  rw [this]
  simp [proba]
  let χA := fun n ↦ (cylinder (Finset.range (NA n + 1)) (SA n)).indicator (1 : (∀ n, X n) → ℝ≥0∞)
  let f := fun n ↦ (∫⋯∫⁻_Finset.range (NA n + 1), χA n ∂μ) Classical.ofNonempty
  suffices Tendsto f atTop (𝓝 0) by simp [this, f, χA]

  have anti : Antitone f := by
    refine fun m n hmn ↦ kolContent_mono μ_proj (A_mem n) (A_mem m) <| A_anti hmn
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
