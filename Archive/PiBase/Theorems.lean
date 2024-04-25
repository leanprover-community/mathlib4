import Mathlib.Topology.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Logic.Nontrivial.Defs
import Mathlib.Data.Fintype.Card
import Archive.PiBase.Properties
import Archive.PiBase.Spaces
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
  let K := S20 ⊕ S20 -- OnePoint ℕ ⊕ OnePoint ℕ
  let k : K := sorry -- K.inl ∞
  let l : K := sorry -- K.inr ∞
  let f₂ : K → X := λ z ↦ sorry
    -- if ∃ n ∈ ℕ, z = K.inl n ∨ z = K.inr n then f n
    -- else if z = k then x else y
  have disjoint_images : ∃ N_k ∈ 𝓝 k, ∃ N_l ∈ 𝓝 l,
      f₂ '' N_k ∩ f₂ '' N_l = ∅ := sorry
    -- p171 using K f₂ k l
  rcases disjoint_images with
    ⟨ N_k , N_k_nhd, N_l, N_l_nhd, disjoint⟩
  -- contradiction: pick sufficiently large n,
  -- then f₂ K.inl n = f n = f₂ K.inr n
  -- contradicts disjoint
  sorry

end πBase
