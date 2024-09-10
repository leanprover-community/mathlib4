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
equations mentioned on page 2.

-/

open Classical

/-- A metastable dominated convergence theorem.
Jeremy Avigad, Edward T Dean, Jason Rute: Equivalence between the two first displayed
equations mentioned on page 2. -/
theorem metastable (a : ℕ → ℝ) :
  (∀ ε > 0, ∃ m, ∀ n ≥ m, ∀ n' ≥ m, |a n - a n'| < ε) ↔
  (
    ∀ ε > 0, ∀ F : ℕ → ℕ, ∃ m,
      ∀ n  ∈ Set.Icc m (F m),
      ∀ n' ∈ Set.Icc m (F m), |a n - a n'| < ε
  ) := by
    constructor
    · intro h ε hε F
      obtain ⟨m,hm⟩ := h ε hε
      use m
      intro n hn n' hn'
      exact hm n hn.1 n' hn'.1
    · intro h ε hε
      have Q := h ε hε
      contrapose Q
      push_neg
      push_neg at Q
      have Q' : ∀ m : ℕ, ∃ k : ℕ,
        ∃ n ∈ Set.Icc m k, ∃ n' ∈ Set.Icc m k, ε ≤ |a n - a n'| := by
        intro m
        have W := Q m
        let n := Nat.find W
        have hn := Nat.find_spec W
        have hn₂ := hn.2
        let n' := Nat.find hn₂
        have := Nat.find_spec hn₂
        use max n n'
        use n
        constructor
        · constructor
          · tauto
          · exact Nat.le_max_left n n'
        · use n'
          constructor
          · constructor
            · tauto
            · exact Nat.le_max_right n n'
          tauto
      exists (fun m ↦ (Nat.find (Q' m)))
      intro m
      let W := Nat.find_spec (Q' m)
      have := Nat.find_spec W
      use Nat.find W
