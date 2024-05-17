import Mathlib.MeasureTheory.Constructions.Pi

open Set MeasureTheory

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]

theorem ok {n N : ℕ} : n ∈ Finset.range N ↔ n + 1 ∈ Finset.range (N + 1) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp only [Finset.mem_range, add_lt_add_iff_right]
    exact Finset.mem_range.1 h
  · simp only [Finset.mem_range]
    have := Finset.mem_range.1 h
    rwa [add_lt_add_iff_right] at this

lemma zero_mem_range {n : ℕ} : 0 ∈ Finset.range (n + 1) := by simp

def produit (x₀ : X 0) (x : ∀ n, X (n + 1)) : ∀ n, X n :=
  fun n ↦ by
    induction n with
    | zero => use x₀
    | succ m => use x m

def measurable_produit (x₀ : X 0) : Measurable (produit x₀) := by
  rw [measurable_pi_iff]
  intro n
  simp_rw [produit]
  cases n with
  | zero => simp
  | succ m => apply measurable_pi_apply

def produit_range (N : ℕ) (x₀ : X 0) (x : ∀ n : Finset.range N, X (n + 1)) :
    ∀ n : Finset.range (N + 1), X n :=
  fun n ↦ by
    cases n with
    | mk k hk => induction k with
      | zero => use x₀
      | succ m => use x ⟨m, ok.2 hk⟩

def measurable_produit_range (N : ℕ) (x₀ : X 0) : Measurable (produit_range N x₀) := by
  rw [measurable_pi_iff]
  intro n
  simp_rw [produit_range]
  cases n with
  | mk k hk => cases k with
    | zero => simp
    | succ => apply measurable_pi_apply

def slice (x₀ : X 0) (A : Set (∀ n, X n)) : Set (∀ n, X (n + 1)) := (produit x₀) ⁻¹' A

def slice_range (N : ℕ) (x₀ : X 0) (A : Set (∀ n : Finset.range (N + 1), X n)) :
    Set (∀ n : Finset.range N, X (n + 1)) :=
  (produit_range N x₀) ⁻¹' A

theorem measurable_slice {x₀ : X 0} {A : Set (∀ n, X n)} (mA : MeasurableSet A) :
  MeasurableSet (slice x₀ A) := mA.preimage <| measurable_produit _

theorem measurable_slice_range {N : ℕ} {x₀ : X 0} {A : Set (∀ n : Finset.range (N + 1), X n)}
    (mA : MeasurableSet A) :
  MeasurableSet (slice_range N x₀ A) := mA.preimage <| measurable_produit_range _ _

-- theorem prod_meas (N : ℕ) (μ : (n : Finset.range (N + 1)) → Measure (X n))
--     (s : (n : Finset.range (N + 1)) → Set (X n)) :
--     (Measure.pi μ) (univ.pi s) = (μ ⟨0, zero_mem_range⟩) (s ⟨0, zero_mem_range⟩) *
--     Measure.pi (fun n : Finset.range N ↦ μ (n + 1)) (univ.pi (fun n : Finset.range N ↦ s (n + 1))) := by
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

theorem measure_prod (N : ℕ) (μ : (n : Finset.range (N + 1)) → Measure (X n))
    [∀ n, IsProbabilityMeasure (μ n)] (x₀ : X 0)
    (A : Set (∀ n : Finset.range (N + 1), X n)) (mA : MeasurableSet A) :
    Measure.pi μ A =
      ((μ ⟨0, zero_mem_range⟩).prod (Measure.pi (fun n : Finset.range N ↦ μ ⟨n + 1, ok.1 n.2⟩)))
      ((fun x : (∀ n : Finset.range (N + 1), X n) ↦
      (x ⟨0, zero_mem_range⟩, fun n : Finset.range N ↦ x ⟨n + 1, ok.1 n.2⟩)) '' A) := by
  have : ∀ s : (n : Finset.range (N + 1)) → Set (X n),
      Measure.pi μ (univ.pi s) =
      ((μ ⟨0, zero_mem_range⟩) (s ⟨0, zero_mem_range⟩)) *
      (Finset.univ.prod
      (fun n : Finset.range N ↦ (μ ⟨n + 1, ok.1 n.2⟩) (s ⟨n + 1, ok.1 n.2⟩))) := by
    intro s
    rw [Measure.pi_pi]
