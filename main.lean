import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.KolmogorovExtension4.Projective
import Mathlib.KolmogorovExtension4.KolmogorovExtension
import Mathlib.Topology.Defs.Filter

open Set MeasureTheory Filter Topology ENNReal Finset

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
    ⋃ (N) (S) (_ : MeasurableSet S), {cylinder (Finset.range (N + 1)) S} := by
  ext s; simp
  constructor
  rintro ⟨t, S, mS, rfl⟩
  · use t.sup id
    use (fun f : ∀ n : Finset.range (t.sup id).succ,
      X n ↦ fun k : t ↦
      f ⟨k, t.subset_range_sup_succ k.2⟩) ⁻¹' S
    constructor
    · apply mS.preimage
      apply measurable_proj₂
    · dsimp only [cylinder]
      rw [← preimage_comp]
      rfl
  · rintro ⟨N, S, mS, rfl⟩
    exact ⟨Finset.range (N + 1), S, mS, rfl⟩

lemma useful (s : Set (∀ n, X n)) (s_mem : s ∈ cylinders X) :
    ∃ N S, MeasurableSet S ∧ s = cylinder (Finset.range (N + 1)) S := by
  simpa [cylinders_nat] using s_mem

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

lemma zero_mem_range {n : ℕ} : 0 ∈ Finset.range (n + 1) := by simp

example (n : ℕ) (h : n ≠ 0) : 1 ≤ n := by exact Nat.one_le_iff_ne_zero.2 h

theorem test (A : ℕ → Set (∀ n, X n)) (A_mem : ∀ n, A n ∈ cylinders X) (A_anti : Antitone A)
    (A_inter : ⋂ n, A n = ∅) :
    Tendsto (kolContent (isProjectiveMeasureFamily_prod μ) ∘ A) atTop (𝓝 0) := by
  have : ∀ n, Nonempty (∀ k, X (k + n)) := by
    intro n
    let x := Classical.ofNonempty (α := ∀ n, X n)
    use fun k ↦ x (k + n)
  have A_cyl := fun n ↦ useful (A n) (A_mem n)
  choose NA SA mSA A_eq using A_cyl
  set μ_proj := isProjectiveMeasureFamily_prod μ
  set μ_proj' := fun n ↦ isProjectiveMeasureFamily_prod (fun k : {k | k ≥ n} ↦ μ k.1)
  have anti : Antitone (kolContent μ_proj ∘ A) := by
    refine fun m n hmn ↦ kolContent_mono μ_proj (A_mem n) (A_mem m) <| A_anti hmn
  have := tendsto_of_antitone anti
  rcases this with hlim | ⟨l, hlim⟩
  · rw [OrderBot.atBot_eq] at hlim
    exact hlim.mono_right <| pure_le_nhds 0
  convert hlim
  by_contra zero_ne_l
  have := fun n ↦ anti.le_of_tendsto hlim n
  let produit : X 0 → (∀ n : {k | k ≥ 1}, X n) → (∀ n, X n) :=
    fun x₀ x n ↦ by
      cases n with
      | zero => use x₀
      | succ m => use x ⟨m + 1, by simp⟩
  have : ∀ n, (kolContent μ_proj) (A n) =
      ∫⁻ x₀ : X 0, kolContent (μ_proj' 1) ((produit x₀) ⁻¹' (A n)) ∂(μ 0) := by
    intro n
    -- let extension : (∀ n : Finset.range (NA n), X (n + 1)) → (∀ n, X (n + 1)) :=
    --   fun x k ↦ by
    --     by_cases h : k < NA n
    --     · use x ⟨k, Finset.mem_range.2 h⟩
    --     · use Some
    let aux : X 0 → (∀ n : (Finset.range (NA n + 1)).erase 0, X n) →
        (∀ n : Finset.range (NA n + 1), X n) :=
      fun x₀ x k ↦ by
        have := k.2
        induction (k : ℕ) generalizing this with
        | zero => use x₀
        | succ m =>
      -- if h : k = ⟨0, zero_mem_range⟩ then h ▸ x₀ else by
      -- rw [← ne_eq, ← Subtype.val_inj.ne] at h
      -- have : k.1 - 1 ∈ Finset.range (NA n) := by
      --   rw [Finset.mem_range, Nat.sub_lt_iff_lt_add, add_comm 1]
      --   exact Finset.mem_range.1 k.2
      --   exact Nat.one_le_iff_ne_zero.2 h
      -- use Nat.succ_pred_eq_of_ne_zero h ▸ x ⟨k.1 - 1, this⟩
    have : ∀ x₀ : X 0, ∀ S : Set ((n : Finset.range (NA n + 1)) → X n),
        (produit x₀) ⁻¹' (cylinder (Finset.range (NA n + 1)) S) =
        cylinder (Finset.range (NA n)) ((aux x₀) ⁻¹' S) := by
      intro x₀ S
      ext x
      simp [produit, aux]
      congrm ?_ ∈ S
      ext k
      by_cases h : k = ⟨0, zero_mem_range⟩
      · have : k.1 = 0 := by rw [h]
        simp [h, this]
        have : k = ⟨0, zero_mem_range⟩ ↔ k.1 = 0 := by
          refine ⟨fun h ↦ by rw [h], fun h' ↦ ?_⟩
          ext
          exact h'

    have : ∀ x₀, kolContent (μ_proj' 1) ((produit x₀) ⁻¹' (A n)) =
        Measure.pi (fun n : (Finset.range (NA n + 1)).erase 0 ↦ μ n) ((aux x₀) ⁻¹' (SA n)) := by
      intro x₀
      simp
      rw [kolContent_eq (μ_proj' 1)]
    rw [kolContent_eq μ_proj (A_mem n), kolmogorovFun_congr μ_proj (A_mem n) (A_eq n) (mSA n)]
    simp [kolContent_eq (μ_proj' 1), kolmogorovFun_congr μ_proj (A_mem n) (A_eq n) (mSA n)]
