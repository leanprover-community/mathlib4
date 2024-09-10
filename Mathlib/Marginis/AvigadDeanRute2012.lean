/-
Copyright (c) 2024 Bjørn Kjos-Hanssen· All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Data.Real.Basic

/-!

Marginis:

A metastable dominated convergence theorem.
Jeremy Avigad, Edward T Dean, Jason Rute.

We prove the equivalence between the two first displayed
equations mentioned on page 2. We generalize from the real numbers ℝ to
any structure with the instances Dist, Ring, Lattice.

instance : Dist ℝ := inferInstance
instance : Ring ℝ := inferInstance
instance : Lattice ℝ := inferInstance

-/


open Classical

/-- A metastable dominated convergence theorem.
Jeremy Avigad, Edward T Dean, Jason Rute: Equivalence between the two first displayed
equations mentioned on page 2. -/
theorem metastable {R : Type} [Dist R] [Ring R] [Lattice R] (a : ℕ → R) :
    (∀ ε > 0, ∃ m, ∀ n ≥ m, ∀ n' ≥ m, dist (a n) (a n') < ε) ↔
    ∀ ε > 0, ∀ F : ℕ → ℕ, ∃ m, ∀ n  ∈ Set.Icc m (F m), ∀ n' ∈ Set.Icc m (F m),
    dist (a n) (a n') < ε := by
  constructor
  · intro h ε hε F
    obtain ⟨m,hm⟩ := h ε hε
    use m
    exact fun n hn n' hn' => hm n hn.1 n' hn'.1
  · intro h ε hε
    have Q := h ε hε
    contrapose Q
    push_neg
    push_neg at Q
    have Q' : ∀ m : ℕ, ∃ k : ℕ, ∃ n ∈ Set.Icc m k, ∃ n' ∈ Set.Icc m k, ε ≤ dist (a n) (a n') := by
      intro m
      have W := Q m
      let n := Nat.find W
      have hn := Nat.find_spec W
      let n' := Nat.find hn.2
      use max n n', n
      constructor
      · exact ⟨hn.1, Nat.le_max_left n n'⟩
      · use n'
        exact ⟨⟨(Nat.find_spec hn.2).1, Nat.le_max_right n n'⟩, (Nat.find_spec hn.2).2⟩
    use fun m ↦ Nat.find <| Q' m
    intro m
    have W := Nat.find_spec (Q' m)
    use Nat.find W
    exact Nat.find_spec W
