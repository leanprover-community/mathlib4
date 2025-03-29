import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Basic

open Set

variable {α : Type*}

-- TO DO: Tidy this result, find a good location for it, tidy the use of the result in `Real.lean`.

-- Similar to stuff in `Mathlib/Order/Interval/Set/Disjoint.lean` but adding this there probably
-- not good because it would require more imports

open Set

lemma iUnion_Ioc_Ioc {X : Type*} [LinearOrderedSemiring X]
    (N : ℕ) (c : X) {δ : X} (hδ : 0 ≤ δ) :
    ⋃ n ∈ Finset.range N, Ioc (c + n * δ) (c + n * δ + δ) = Ioc c (c + N * δ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    simp only [Finset.mem_insert, iUnion_iUnion_eq_or_left, Nat.cast_add,
      Nat.cast_one, ih, Finset.range_succ]
    rw [union_comm, Ioc_union_Ioc_eq_Ioc]
    · simp [add_mul, add_assoc]
    · simp only [le_add_iff_nonneg_right]
      -- exact mul_nonneg (Nat.cast_nonneg' N) hδ
      positivity
    · simp [hδ]

lemma Fin_to_Nat {X : Type*} (N : ℕ) (s : ℕ → Set X) :
    ⋃ (n : Fin N), s n = ⋃ n ∈ Finset.range N, s n := by
  ext x
  constructor
  · intro h
    apply Set.mem_iUnion.mpr
    rw [Set.mem_iUnion] at h
    obtain ⟨n, hn⟩ := h
    use n
    simp only [Finset.mem_range, Fin.is_lt, iUnion_true]
    exact hn
  · intro h
    apply Set.mem_iUnion.mpr
    rw [Set.mem_iUnion₂] at h
    obtain ⟨n, hn⟩ := h
    simp only [Finset.mem_range, exists_prop] at hn
    use ⟨n, hn.1⟩
    simp only
    exact hn.2

/-- An `Ioc` partitions into a finite union of `Ioc`s. -/
lemma RMK_iUnion_Ioc {N : ℕ} (c : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ⋃ n : Fin N, Ioc (c + n * δ) (c + n * δ + δ) = Ioc (c) (c + N * δ) := by
  rw [Fin_to_Nat N (fun n => Ioc (c + n * δ) (c + n * δ + δ))]
  -- Use the above to prove this.
  exact iUnion_Ioc_Ioc N c (show 0 ≤ δ by linarith)

#min_imports
#find_home Fin_to_Nat
