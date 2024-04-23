import Mathlib.Topology.Basic
import Mathlib.Topology.Inseparable
import Mathlib.Data.Set.Basic
open Topology TopologicalSpace Set

universe u

variable (X : Type u)

def πBaseP1 (_ : TopologicalSpace X) : Prop :=
  ∀ x y : X, Inseparable x y → x = y

def πBaseP2 (_ : TopologicalSpace X) : Prop :=
  ∀ x : X, IsClosed ({x} : Set X)

theorem πBaseT119 (Y : TopologicalSpace X) :
    πBaseP2 X Y → πBaseP1 X Y := by
  intro h
  rw [πBaseP1, πBaseP2] at *
  intro x y g
  have ySClosed : IsClosed {y} := by
    exact h y
  have yCOpen : IsOpen {y}ᶜ := by
    exact isOpen_compl_iff.2 ySClosed
  rw [Inseparable] at g
  by_contra h
  have : {y}ᶜ ∈ 𝓝 x := by
    rw [mem_nhds_iff]
    use {y}ᶜ
    constructor
    · simp
    · constructor
      · exact yCOpen
      · apply h
  have gotcha : {y}ᶜ ∈ 𝓝 y := by
    rw [g] at this
    exact this
  have uhoh : y ∉ {y}ᶜ := by
    rw [mem_compl_singleton_iff]
    simp
  have (s: Set X): s ∈ 𝓝 y → y ∈ s := by
    intro H
    apply mem_of_mem_nhds
    exact H
  apply uhoh
  apply this
  exact gotcha

