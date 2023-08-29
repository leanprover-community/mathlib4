/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.ContinuousFunction.Bounded

#align_import topology.urysohns_bounded from "leanprover-community/mathlib"@"af683b11d1bd89d1e85a03bf1eb5519379aabdc9"

/-!
# Urysohn's lemma for bounded continuous functions

In this file we reformulate Urysohn's lemma `exists_continuous_zero_one_of_closed` in terms of
bounded continuous functions `X →ᵇ ℝ`. These lemmas live in a separate file because
`Topology.ContinuousFunction.Bounded` imports too many other files.

## Tags

Urysohn's lemma, normal topological space
-/


open BoundedContinuousFunction

open Set Function

/-- Urysohn's lemma: if `s` and `t` are two disjoint closed sets in a normal topological space `X`,
then there exists a continuous function `f : X → ℝ` such that

* `f` equals zero on `s`;
* `f` equals one on `t`;
* `0 ≤ f x ≤ 1` for all `x`.
-/
theorem exists_bounded_zero_one_of_closed {X : Type*} [TopologicalSpace X] [NormalSpace X]
    {s t : Set X} (hs : IsClosed s) (ht : IsClosed t) (hd : Disjoint s t) :
    ∃ f : X →ᵇ ℝ, EqOn f 0 s ∧ EqOn f 1 t ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1 :=
  let ⟨f, hfs, hft, hf⟩ := exists_continuous_zero_one_of_closed hs ht hd
  ⟨⟨f, 1, fun _ _ => Real.dist_le_of_mem_Icc_01 (hf _) (hf _)⟩, hfs, hft, hf⟩
#align exists_bounded_zero_one_of_closed exists_bounded_zero_one_of_closed

/-- Urysohn's lemma: if `s` and `t` are two disjoint closed sets in a normal topological space `X`,
and `a ≤ b` are two real numbers, then there exists a continuous function `f : X → ℝ` such that

* `f` equals `a` on `s`;
* `f` equals `b` on `t`;
* `a ≤ f x ≤ b` for all `x`.
-/
theorem exists_bounded_mem_Icc_of_closed_of_le {X : Type*} [TopologicalSpace X] [NormalSpace X]
    {s t : Set X} (hs : IsClosed s) (ht : IsClosed t) (hd : Disjoint s t) {a b : ℝ} (hle : a ≤ b) :
    ∃ f : X →ᵇ ℝ, EqOn f (Function.const X a) s ∧ EqOn f (Function.const X b) t ∧
    ∀ x, f x ∈ Icc a b :=
  let ⟨f, hfs, hft, hf01⟩ := exists_bounded_zero_one_of_closed hs ht hd
  ⟨BoundedContinuousFunction.const X a + (b - a) • f, fun x hx => by simp [hfs hx], fun x hx => by
                                                                     -- 🎉 no goals
    simp [hft hx], fun x =>
    -- 🎉 no goals
    ⟨by dsimp; nlinarith [(hf01 x).1], by dsimp; nlinarith [(hf01 x).2]⟩⟩
        -- ⊢ a ≤ a + (b - a) * ↑f x
               -- 🎉 no goals
                                          -- ⊢ a + (b - a) * ↑f x ≤ b
                                                 -- 🎉 no goals
#align exists_bounded_mem_Icc_of_closed_of_le exists_bounded_mem_Icc_of_closed_of_le
