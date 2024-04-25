import Mathlib

open MeasureTheory TopologicalSpace Uniformity Filter

lemma TotallyBounded.isSeparable5 {α : Type*} [UniformSpace α] [i : IsCountablyGenerated (𝓤 α)] {s : Set α} (h : TotallyBounded s) :
    TopologicalSpace.IsSeparable s:= by
  unfold TopologicalSpace.IsSeparable
  obtain ⟨V, hVa, hVb⟩ := UniformSpace.has_seq_basis α
  choose! f hf hfb using (fun n : ℕ => h (V n))
  have hVc : ∀ n, (V n) ∈ 𝓤 α := by
    intro n
    exact HasAntitoneBasis.mem hVa n
  have := fun n => h.exists_subset (hVc n)
  choose! g hg hg' hg'' using this
  use ⋃ n, g n
  constructor
  · apply Set.countable_iUnion
    exact fun i => Set.Finite.countable (hg' i)
  · sorry

lemma TotallyBounded.isSeparable2 {α : Type*} [UniformSpace α] [i : IsCountablyGenerated (𝓤 α)] {s : Set α} (h : TotallyBounded s) :
    TopologicalSpace.IsSeparable s:= by
  unfold TopologicalSpace.IsSeparable
  obtain ⟨x, hx⟩ := isCountablyGenerated_iff_exists_antitone_basis.mp i
  choose! f hf hfb using (fun n : ℕ => h (x n))
  use ⋃ n, f n
  have hnu : ∀ n, x n ∈ 𝓤 α := by
    intro n
    exact HasAntitoneBasis.mem hx n
  have hf := fun n => hf n (hnu n)
  have hfb := fun n => hfb n (hnu n)
  constructor
  · apply Set.countable_iUnion
    exact fun i => Set.Finite.countable (hf i)
  · intro y hy
    sorry


lemma TotallyBounded.isSeparable4 {α : Type*} [PseudoMetricSpace α] {s : Set α} (h : TotallyBounded s) :
    TopologicalSpace.IsSeparable s:= by
  rw [Metric.totallyBounded_iff] at h
  choose! f hf hfb using (fun n : ℕ => h (1/(n+1)) Nat.one_div_pos_of_nat)
  use ⋃ n, f n
  constructor
  · apply Set.countable_iUnion
    exact fun i => (hf i).countable
  · intro x hx
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    have : ∃ b ∈ f n, dist x b < ε := by
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hfb n hx)
      simp only [one_div, Set.mem_iUnion, Metric.mem_ball, exists_prop] at hi
      use i, hi.1
      apply lt_trans hi.2 ?_
      rw [inv_eq_one_div]
      exact hn
    aesop

lemma TotallyBounded.isSeparable3 {α : Type*} [PseudoMetricSpace α] {s : Set α} (h : TotallyBounded s) :
    TopologicalSpace.IsSeparable s:= by
  apply TotallyBounded.isSeparable2 h
