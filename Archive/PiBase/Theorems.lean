import Mathlib.Topology.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Logic.Nontrivial.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Topology.Compactification.OnePoint
import Archive.PiBase.Properties
open Topology Set Filter Nontrivial Fintype

universe u

namespace πBase

theorem T119 (X : Type u) [TopologicalSpace X]
    (p2: P2 X): P1 X := by
  rw [P1, P2] at *
  exact T1Space.t0Space

theorem T226 (X : Type u) [TopologicalSpace X]
    (p99: P99 X): P2 X := by
  rw [P99, P2] at *
  rw [t1Space_iff_exists_open]
  intro x y
  contrapose; simp at *
  intro hyp
  let f : ℕ → X := fun _ ↦ y
  have h : Tendsto f atTop (𝓝 x) →
      Tendsto f atTop (𝓝 y) → x = y := by
    apply p99
  apply h
  · intro N NNx
    have yinN : y ∈ N := by
      rw [mem_nhds_iff] at NNx
      rcases NNx with ⟨ U, ⟨ UsubN, Uopen, xinU⟩ ⟩
      apply UsubN
      apply hyp
      exact Uopen
      exact xinU
    apply mem_map.mpr
    simp
    use 0
    simp
    intro b
    have : f b = y := by
      simp
    rw [this]
    exact yinN
  · exact tendsto_const_nhds

lemma wh_h_image (X : Type u) [TopologicalSpace X]
    (p143: P143 X): ∀ K : CompHaus.{u}, ∀ f : K → X,
    Continuous f →
    ∀ x ∈ f '' univ, ∀ y ∈ f '' univ, x ≠ y →
    ∃ Nx ∈ 𝓝 x, ∃ Ny ∈ 𝓝 y, Nx ∩ Ny = ∅ := by
  intro K f fcont x ximf y yimf xney
  have : T1Space X := by sorry
  have : SeparatedNhds (f ⁻¹' {x}) (f ⁻¹' {y}) := by
    apply normal_separation
    apply IsClosed.preimage fcont
    apply isClosed_singleton
    apply IsClosed.preimage fcont
    apply isClosed_singleton
    intro S
    simp
    intro SsubX SsubY
    intro z zinS
    simp
    apply xney
    have : f z = x := by
      apply SsubX at zinS
      apply zinS
    rw [← this]
    have : f z = y := by
      apply SsubY at zinS
      apply zinS
    rw [← this]
  rw [separatedNhds_iff_disjoint, disjoint_iff] at this
  have : ∃ Nxi ∈ 𝓝ˢ (f ⁻¹' {x}), ∃ Nyi ∈ 𝓝ˢ (f ⁻¹' {y}),
      Nxi ∩ Nyi = ∅ := sorry
  rcases this with ⟨ Nxi, Nxiof, Nyi, Nyiof, NxyiDisjoint ⟩
  sorry


theorem T229 (X : Type u) [TopologicalSpace X]
    (p143: P143 X): P171 X := by
  rw [P171] at *
  intro K f fcont k l fk_not_fl
  have : ∃ Nfk ∈ 𝓝 (f k), ∃ Nfl ∈ 𝓝 (f l), Nfk ∩ Nfl = ∅ := by
    apply wh_h_image
    · exact p143
    · exact fcont
    use k
    constructor <;> trivial
    use l
    constructor <;> trivial
    exact fk_not_fl
  rcases this with ⟨ Nfk, NfkNhd, Nfl, NflNhd, NfKNflDisjoint⟩
  use f ⁻¹' Nfk
  constructor
  · apply ContinuousAt.preimage_mem_nhds
    apply Continuous.continuousAt fcont
    exact NfkNhd
  use f ⁻¹' Nfl
  constructor
  · apply ContinuousAt.preimage_mem_nhds
    apply Continuous.continuousAt fcont
    exact NflNhd
  repeat rw [Set.image, Set.preimage]
  simp
  have : {x | ∃ a, f a ∈ Nfk ∧ f a = x} ⊆ Nfk := by
    intro x
    simp
    intro y fy eq
    rw [← eq]
    exact fy
  have : {x | ∃ a, f a ∈ Nfl ∧ f a = x} ⊆ Nfl := by
    intro x
    simp
    intro y fy eq
    rw [← eq]
    exact fy
  rw [← subset_empty_iff]
  have : {x | ∃ a, f a ∈ Nfk ∧ f a = x} ∩
      {x | ∃ a, f a ∈ Nfl ∧ f a = x} ⊆ Nfk ∩ Nfl := by
    apply Set.inter_subset_inter
    · intro x
      simp
      intro y fy eq
      rw [← eq]
      exact fy
    · intro x
      simp
      intro y fy eq
      rw [← eq]
      exact fy
  apply Set.Subset.trans this
  rw [subset_empty_iff]
  exact NfKNflDisjoint


  -- have : IsCompact ({k' | f k' = f k}) := by
  --   sorry
  -- have : IsCompact ({l' | f l' = f l}) := by
  --   sorry
  -- have : SeparatedNhds
  --     {k' | f k' = f k} {l' | f l' = f l} := by
  --   sorry
  -- rw [SeparatedNhds] at this
  -- rcases this with ⟨ U, V, ⟨ Uopen, Vopen, ksubU, lsubV, UVdis ⟩ ⟩
  -- use U
  -- constructor
  -- · sorry
  -- use V
  -- constructor
  -- · sorry




theorem T250 (X : Type u) [TopologicalSpace X]
    (np78: ¬ P78 X): P125 X := by
  rw [P78, P125] at *
  simp at np78
  apply Infinite.instNontrivial

theorem T425 (X : Type u) [TopologicalSpace X]
    (p171: P171 X): P99 X := by
  rw [P171, P99] at *
  intro x y f ftox ftoy
  by_contra xnoty
  let K := OnePoint ℕ ⊕ OnePoint ℕ
  let k : K := sorry -- K.inl ∞
  let l : K := sorry -- K.inr ∞
  let f₂ : K → X := λ z ↦ sorry
    -- if ∃ n ∈ ℕ, z = K.inl n ∨ z = K.inr n then f n
    -- else if z = k then x else y
  have disjoint_images : ∃ N_k ∈ 𝓝 k, ∃ N_l ∈ 𝓝 l,
      f₂ '' N_k ∩ f₂ '' N_l = ∅ := sorry
  --   -- p171 using K f₂ k l
  rcases disjoint_images with
    ⟨ N_k , N_k_nhd, N_l, N_l_nhd, disjoint⟩
  -- contradiction: pick sufficiently large n,
  -- then f₂ K.inl n = f n = f₂ K.inr n
  -- contradicts disjoint
  sorry

end πBase
