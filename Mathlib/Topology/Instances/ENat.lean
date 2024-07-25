import Mathlib.Data.ENat.Lattice
import Mathlib.Topology.Algebra.Order.Compact
import Mathlib.Algebra.CharP.Defs

open ENat Filter Topology TopologicalSpace Set

instance : TopologicalSpace ℕ∞ := Preorder.topology ℕ∞

instance : OrderTopology ℕ∞ := OrderTopology.mk rfl

theorem isOpen_singleton (n : ℕ) : IsOpen {(n : ℕ∞)} := by
  cases n with
  | zero =>
    refine GenerateOpen.basic _ ⟨1, Or.inr ?_⟩
    ext x
    simp only [CharP.cast_eq_zero, Set.mem_singleton_iff, Set.mem_setOf_eq]
    exact lt_one_iff_eq_zero.symm
  | succ k =>
    have : {(↑(k + 1) : ℕ∞)} = (Set.Iio ↑(k + 2)) ∩ (Set.Ioi ↑k) := by
      rw [Iio_inter_Ioi]
      ext x
      simp only [mem_singleton_iff, mem_Ioo]
      rcases eq_or_ne x ⊤ with h | h
      · simp only [h, not_top_lt, and_false, iff_false]
        exact top_ne_coe _
      · lift x to ℕ using h
        norm_cast
        omega
    rw [this]
    apply GenerateOpen.inter <;> constructor
    · exact ⟨(↑(k + 2) : ℕ∞), Or.inr rfl⟩
    · exact ⟨k, Or.inl rfl⟩

theorem isOpen_top_not_mem (s : Set ℕ∞) (h : ⊤ ∉ s) : IsOpen s := by
  rw [← Set.biUnion_of_singleton s]
  refine isOpen_biUnion fun x hx ↦ ?_
  lift x to ℕ using ne_of_mem_of_not_mem hx h
  exact isOpen_singleton x

theorem ENat.coe_max (a b : ℕ) : (↑(max a b) : ℕ∞) = max ↑a ↑b := by
  apply eq_max <;> try norm_cast
  · exact le_max_left _ _
  · exact le_max_right _ _
  · intro d h1 h2
    rcases max_choice a b with h | h <;> rwa [h]

theorem isOpen_iff_top_mem (s : Set ℕ∞) (top_mem : ⊤ ∈ s) :
    IsOpen s ↔ ∃ x : ℕ, Set.Ioi ↑x ⊆ s where
  mp hs := by
    rcases (nhds_top_basis.mem_iff' s).1 (hs.mem_nhds top_mem) with ⟨x, x_lt, hx⟩
    lift x to ℕ using x_lt.ne
    exact ⟨x, hx⟩
  mpr := by
    rintro ⟨a, ha⟩
    rw [← Set.inter_union_compl s (Set.Ioi a)]
    apply IsOpen.union
    · rw [Set.inter_eq_self_of_subset_right ha]
      exact GenerateOpen.basic _ ⟨a, Or.inl rfl⟩
    · apply isOpen_top_not_mem
      simp [top_mem]

theorem ENat.tendsto_coe_atTop :
    Tendsto (@Nat.cast ℕ∞ _) atTop (𝓝 ⊤) := by
  rw [tendsto_atTop_nhds]
  intro U mem_U hU
  rcases (isOpen_iff_top_mem _ mem_U).1 hU with ⟨x, hU⟩
  refine ⟨x + 1, fun n hn ↦ hU ?_⟩
  simp only [Set.mem_Ioi, Nat.cast_lt]
  omega

variable {X : Type*} (f : ℕ → X) (x : X)

def compactSequence : ℕ∞ → X := fun n ↦
  match n with
  | some k => f k
  | none => x

theorem compactSequence_coe (n : ℕ) : compactSequence f x n = f n := rfl

theorem compactSequence_ne_top (n : ℕ∞) (hn : n ≠ ⊤) : compactSequence f x n = f n.toNat := by
  lift n to ℕ using hn
  rfl

theorem compactSequence_top : compactSequence f x ⊤ = x := rfl

theorem range_compactSequence : range (compactSequence f x) = insert x (range f) := by
  ext y
  constructor
  · rintro ⟨n, rfl⟩
    rcases eq_or_ne n ⊤ with rfl | hn
    · exact mem_insert _ _
    · exact mem_insert_of_mem _ ⟨n.toNat, (compactSequence_ne_top f x n hn).symm⟩
  · rw [mem_insert_iff]
    rintro (rfl | ⟨n, rfl⟩)
    · exact ⟨⊤, rfl⟩
    · exact ⟨n, rfl⟩

variable [TopologicalSpace X]

theorem continuous_compactSequence (h : Tendsto f atTop (𝓝 x)) :
    Continuous (compactSequence f x) where
  isOpen_preimage s hs := by
    by_cases htop : ⊤ ∈ (compactSequence f x ⁻¹' s)
    · rw [isOpen_iff_top_mem _ htop]
      rcases tendsto_atTop_nhds.1 h s htop hs with ⟨N, hN⟩
      refine ⟨N, fun y hy ↦ ?_⟩
      rcases eq_or_ne y ⊤ with rfl | y_ne_top
      · exact htop
      · lift y to ℕ using y_ne_top
        exact hN _ (by simpa using hy : N < y).le
    · exact isOpen_top_not_mem _ htop

theorem isCompact_range_compactSequence (h : Tendsto f atTop (𝓝 x)) :
    IsCompact (range (compactSequence f x)) := isCompact_range (continuous_compactSequence f x h)
