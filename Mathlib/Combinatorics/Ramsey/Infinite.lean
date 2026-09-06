/-
Copyright (c) 2026 Haoyu Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haoyu Chen
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Order.Filter.Ultrafilter.Basic

/-!
# The infinite Ramsey theorem for pairs

This file formalises **Ramsey's infinite theorem** for pairs and finitely many colours:

> for any colouring `c : ℕ → ℕ → β` of the pairs `{i, j}` (`i < j`) of natural numbers by a
> finite set `β` of colours, there is an infinite set `S ⊆ ℕ` all of whose pairs get the same
> colour.

## Main results

* `Ramsey.exists_infinite_monochromatic` — the infinite Ramsey theorem for pairs.
* `SimpleGraph.exists_infinite_isClique_or_isIndepSet` — the graph-theoretic corollary: every
  graph on `ℕ` has an infinite clique or an infinite independent set.

## Proof

The standard ultrafilter proof. Fix a nonprincipal ultrafilter `U` on `ℕ` (the `hyperfilter`).
Every set in `U` is infinite, and every `Set.Ioi n` lies in `U`.

Since `β` is finite, for each `n` there is a unique colour `f n` with
`{m | c n m = f n} ∈ U`, and there is a colour `b₀` with `{n | f n = b₀} ∈ U`.

Now build a decreasing chain of `U`-sets: start from `B = {n | f n = b₀}`, and at each step
pick a point `x k` of the current set `P k` and cut down to
`P (k+1) = P k ∩ {m | c (x k) m = f (x k)} ∩ Set.Ioi (x k)`, which is again in `U`.
The resulting sequence `x` is strictly increasing, every `x k` lies in `B`, and for `i < j` we
have `x j ∈ P (i+1)`, whence `c (x i) (x j) = f (x i) = b₀`. So `Set.range x` works.

## References

* F. P. Ramsey, *On a problem of formal logic*, Proc. London Math. Soc. (1930).
-/

@[expose] public section

open Filter Set

namespace Ramsey

/-- A choice function on sets of naturals: `pick s` is an element of `s` whenever `s` is
nonempty. -/
noncomputable def pick (s : Set ℕ) : ℕ := sInf s

theorem pick_mem {s : Set ℕ} (h : s.Nonempty) : pick s ∈ s := Nat.sInf_mem h

variable {β : Type*}

/-- One step of the shrinking construction: keep only the points of `s` beyond `pick s` whose
colour with `pick s` is the `U`-colour `f (pick s)`. -/
noncomputable def shrink (c : ℕ → ℕ → β) (f : ℕ → β) (s : Set ℕ) : Set ℕ :=
  s ∩ {m | c (pick s) m = f (pick s)} ∩ Set.Ioi (pick s)

/-- The decreasing chain of sets used in the proof of the infinite Ramsey theorem. -/
noncomputable def chain (c : ℕ → ℕ → β) (f : ℕ → β) (B : Set ℕ) : ℕ → Set ℕ
  | 0 => B
  | k + 1 => shrink c f (chain c f B k)

theorem chain_succ_subset (c : ℕ → ℕ → β) (f : ℕ → β) (B : Set ℕ) (k : ℕ) :
    chain c f B (k + 1) ⊆ chain c f B k :=
  fun _ hx => hx.1.1

theorem chain_subset_of_le (c : ℕ → ℕ → β) (f : ℕ → β) (B : Set ℕ) {i j : ℕ}
    (h : i ≤ j) :
    chain c f B j ⊆ chain c f B i := by
  induction j with
  | zero => rw [Nat.le_zero.1 h]
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with hij | hij
    · exact (chain_succ_subset c f B j).trans (ih (Nat.lt_succ_iff.1 hij))
    · rw [Nat.le_antisymm h hij]

/-- **The infinite Ramsey theorem for pairs.**

If the pairs of natural numbers are coloured by a finite set `β` of colours, then there is a
colour `b` and an infinite set `S` of natural numbers such that every pair `i < j` of elements
of `S` has colour `b`. -/
theorem exists_infinite_monochromatic [Finite β] (c : ℕ → ℕ → β) :
    ∃ (b : β) (S : Set ℕ), S.Infinite ∧ ∀ i ∈ S, ∀ j ∈ S, i < j → c i j = b := by
  classical
  set U : Ultrafilter ℕ := hyperfilter ℕ with hUdef
  -- Every final segment of `ℕ` lies in `U`.
  have hIoi : ∀ n : ℕ, Set.Ioi n ∈ U := by
    intro n
    refine Filter.mem_hyperfilter_of_finite_compl ?_
    simp
  -- A map from `ℕ` to a finite type has a fibre in `U`.
  have key : ∀ g : ℕ → β, ∃ b, {n | g n = b} ∈ U := by
    intro g
    obtain ⟨b, hb⟩ := (Ultrafilter.map g U).eq_pure_of_finite
    refine ⟨b, ?_⟩
    have hmem : {b} ∈ Ultrafilter.map g U := by
      rw [hb]; exact Ultrafilter.mem_pure.2 rfl
    rw [Ultrafilter.mem_map] at hmem
    exact hmem
  -- `f n` is the `U`-colour of `n`.
  choose f hf using fun n : ℕ => key (c n)
  -- `b₀` is the `U`-colour of the map `f`.
  obtain ⟨b₀, hb₀⟩ := key f
  set B : Set ℕ := {n | f n = b₀} with hB
  set P : ℕ → Set ℕ := chain c f B with hP
  set x : ℕ → ℕ := fun k => pick (P k) with hx
  -- Every `P k` lies in `U`.
  have hPU : ∀ k, P k ∈ U := by
    intro k
    induction k with
    | zero => exact hb₀
    | succ k ih =>
      have h1 : P (k + 1) = P k ∩ {m | c (x k) m = f (x k)} ∩ Set.Ioi (x k) := rfl
      rw [h1]
      exact Filter.inter_mem (Filter.inter_mem ih (hf (x k))) (hIoi (x k))
  have hxP : ∀ k, x k ∈ P k := fun k => pick_mem (Filter.nonempty_of_mem (hPU k))
  -- The sequence is strictly increasing.
  have hstep : ∀ k, x k < x (k + 1) := by
    intro k
    have : x (k + 1) ∈ Set.Ioi (x k) := (hxP (k + 1)).2
    exact this
  have hmono : StrictMono x := strictMono_nat_of_lt_succ hstep
  -- Every `x k` has `U`-colour `b₀`.
  have hxb : ∀ k, f (x k) = b₀ := by
    intro k
    have : x k ∈ P 0 := chain_subset_of_le c f B (Nat.zero_le k) (hxP k)
    exact this
  -- Pairs from the sequence are monochromatic.
  have hpair : ∀ i j, i < j → c (x i) (x j) = b₀ := by
    intro i j hij
    have hmem : x j ∈ P (i + 1) := chain_subset_of_le c f B hij (hxP j)
    have : c (x i) (x j) = f (x i) := hmem.1.2
    rw [this, hxb i]
  refine ⟨b₀, Set.range x, Set.infinite_range_of_injective hmono.injective, ?_⟩
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hlt
  exact hpair i j (hmono.lt_iff_lt.1 hlt)

/-- **Schur's theorem.**

For every colouring of the natural numbers by finitely many colours there are positive
integers `x`, `y`, `z` of the same colour with `x + y = z`.

(Schur's theorem is not in Mathlib either; it drops out of the infinite Ramsey theorem by
colouring the pair `i < j` with the colour of the difference `j - i`.) -/
theorem schur {β : Type*} [Finite β] (c : ℕ → β) :
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ x + y = z ∧ c x = c z ∧ c y = c z := by
  obtain ⟨b, S, hSinf, hS⟩ := exists_infinite_monochromatic (fun i j => c (j - i))
  obtain ⟨n₀, hn₀, -⟩ := hSinf.exists_gt 0
  obtain ⟨n₁, hn₁, h01⟩ := hSinf.exists_gt n₀
  obtain ⟨n₂, hn₂, h12⟩ := hSinf.exists_gt n₁
  have e01 : c (n₁ - n₀) = b := hS n₀ hn₀ n₁ hn₁ h01
  have e12 : c (n₂ - n₁) = b := hS n₁ hn₁ n₂ hn₂ h12
  have e02 : c (n₂ - n₀) = b := hS n₀ hn₀ n₂ hn₂ (h01.trans h12)
  exact ⟨n₁ - n₀, n₂ - n₁, n₂ - n₀, by omega, by omega, by omega,
    e01.trans e02.symm, e12.trans e02.symm⟩

end Ramsey

namespace SimpleGraph

/-- **Infinite Ramsey theorem, graph form.** Every graph on the natural numbers contains an
infinite clique or an infinite independent set. -/
theorem exists_infinite_isClique_or_isIndepSet (G : SimpleGraph ℕ) :
    (∃ S : Set ℕ, S.Infinite ∧ G.IsClique S) ∨
      (∃ S : Set ℕ, S.Infinite ∧ G.IsIndepSet S) := by
  classical
  obtain ⟨b, S, hSinf, hS⟩ :=
    Ramsey.exists_infinite_monochromatic (fun i j => decide (G.Adj i j))
  cases b with
  | false =>
    refine Or.inr ⟨S, hSinf, ?_⟩
    have h : ∀ p ∈ S, ∀ q ∈ S, p < q → ¬ G.Adj p q := by
      intro p hp q hq hpq
      simpa using hS p hp q hq hpq
    intro i hi j hj hne
    rcases Nat.lt_or_ge i j with hlt | hge
    · exact h i hi j hj hlt
    · exact fun hadj => h j hj i hi (lt_of_le_of_ne hge (Ne.symm hne)) hadj.symm
  | true =>
    refine Or.inl ⟨S, hSinf, ?_⟩
    have h : ∀ p ∈ S, ∀ q ∈ S, p < q → G.Adj p q := by
      intro p hp q hq hpq
      simpa using hS p hp q hq hpq
    intro i hi j hj hne
    rcases Nat.lt_or_ge i j with hlt | hge
    · exact h i hi j hj hlt
    · exact (h j hj i hi (lt_of_le_of_ne hge (Ne.symm hne))).symm

end SimpleGraph
