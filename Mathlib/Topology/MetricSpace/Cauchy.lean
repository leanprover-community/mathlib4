/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.EMetricSpace.Basic

/-!
## Cauchy sequences in (pseudo-)metric spaces

Various results on Cauchy sequences in (pseudo-)metric spaces, including

* `Metric.complete_of_cauchySeq_tendsto` A pseudo-metric space is complete iff each Cauchy sequences
  converges to some limit point.
* `cauchySeq_bdd`: a Cauchy sequence on the natural numbers is bounded
* various characterisation of Cauchy and uniformly Cauchy sequences

## Tags

metric, `PseudoMetric`, Cauchy sequence
-/

public section

open Filter
open scoped Uniformity Topology

universe u v w

variable {α : Type u} {β : Type v} {X ι : Type*}
variable [PseudoMetricSpace α]

/-- A very useful criterion to show that a space is complete is to show that all sequences
which satisfy a bound of the form `dist (u n) (u m) < B N` for all `n m ≥ N` are
converging. This is often applied for `B N = 2^{-N}`, i.e., with a very fast convergence to
`0`, which makes it possible to use arguments of converging series, while this is impossible
to do in general for arbitrary Cauchy sequences. -/
theorem Metric.complete_of_convergent_controlled_sequences (B : ℕ → Real) (hB : ∀ n, 0 < B n)
    (H : ∀ u : ℕ → α, (∀ N n m : ℕ, N ≤ n → N ≤ m → dist (u n) (u m) < B N) →
      ∃ x, Tendsto u atTop (𝓝 x)) :
    CompleteSpace α :=
  UniformSpace.complete_of_convergent_controlled_sequences
    (fun n => { p : α × α | dist p.1 p.2 < B n }) (fun n => dist_mem_uniformity <| hB n) H

/-- A pseudo-metric space is complete iff every Cauchy sequence converges. -/
theorem Metric.complete_of_cauchySeq_tendsto :
    (∀ u : ℕ → α, CauchySeq u → ∃ a, Tendsto u atTop (𝓝 a)) → CompleteSpace α :=
  EMetric.complete_of_cauchySeq_tendsto

section CauchySeq

variable [Nonempty β] [SemilatticeSup β]

/-- In a pseudometric space, Cauchy sequences are characterized by the fact that, eventually,
the distance between its elements is arbitrarily small -/
theorem Metric.cauchySeq_iff {u : β → α} :
    CauchySeq u ↔ ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, dist (u m) (u n) < ε :=
  uniformity_basis_dist.cauchySeq_iff

/-- A variation around the pseudometric characterization of Cauchy sequences -/
theorem Metric.cauchySeq_iff' {u : β → α} :
    CauchySeq u ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (u n) (u N) < ε :=
  uniformity_basis_dist.cauchySeq_iff'

-- see Note [nolint_ge]
/-- In a pseudometric space, uniform Cauchy sequences are characterized by the fact that,
eventually, the distance between all its elements is uniformly, arbitrarily small. -/
theorem Metric.uniformCauchySeqOn_iff {γ : Type*} {F : β → γ → α} {s : Set γ} :
    UniformCauchySeqOn F atTop s ↔ ∀ ε > (0 : ℝ),
      ∃ N : β, ∀ m ≥ N, ∀ n ≥ N, ∀ x ∈ s, dist (F m x) (F n x) < ε := by
  constructor
  · intro h ε hε
    let u := { a : α × α | dist a.fst a.snd < ε }
    have hu : u ∈ 𝓤 α := Metric.mem_uniformity_dist.mpr ⟨ε, hε, by simp [u]⟩
    rw [← Filter.eventually_atTop_prod_self' (p := fun m =>
      ∀ x ∈ s, dist (F m.fst x) (F m.snd x) < ε)]
    specialize h u hu
    rw [prod_atTop_atTop_eq] at h
    exact h.mono fun n h x hx => h x hx
  · intro h u hu
    rcases Metric.mem_uniformity_dist.mp hu with ⟨ε, hε, hab⟩
    rcases h ε hε with ⟨N, hN⟩
    rw [prod_atTop_atTop_eq, eventually_atTop]
    use (N, N)
    intro b hb x hx
    rcases hb with ⟨hbl, hbr⟩
    exact hab (hN b.fst hbl.ge b.snd hbr.ge x hx)

/-- If the distance between `s n` and `s m`, `n ≤ m` is bounded above by `b n`
and `b` converges to zero, then `s` is a Cauchy sequence. -/
theorem cauchySeq_of_le_tendsto_0' {s : β → α} (b : β → ℝ)
    (h : ∀ n m : β, n ≤ m → dist (s n) (s m) ≤ b n) (h₀ : Tendsto b atTop (𝓝 0)) : CauchySeq s :=
  Metric.cauchySeq_iff'.2 fun ε ε0 => (h₀.eventually (gt_mem_nhds ε0)).exists.imp fun N hN n hn =>
    calc dist (s n) (s N) = dist (s N) (s n) := dist_comm _ _
    _ ≤ b N := h _ _ hn
    _ < ε := hN

/-- If the distance between `s n` and `s m`, `n, m ≥ N` is bounded above by `b N`
and `b` converges to zero, then `s` is a Cauchy sequence. -/
theorem cauchySeq_of_le_tendsto_0 {s : β → α} (b : β → ℝ)
    (h : ∀ n m N : β, N ≤ n → N ≤ m → dist (s n) (s m) ≤ b N) (h₀ : Tendsto b atTop (𝓝 0)) :
    CauchySeq s :=
  cauchySeq_of_le_tendsto_0' b (fun _n _m hnm => h _ _ _ le_rfl hnm) h₀

/-- A Cauchy sequence on the natural numbers is bounded. -/
theorem cauchySeq_bdd {u : ℕ → α} (hu : CauchySeq u) : ∃ R > 0, ∀ m n, dist (u m) (u n) < R := by
  rcases Metric.cauchySeq_iff'.1 hu 1 zero_lt_one with ⟨N, hN⟩
  rsuffices ⟨R, R0, H⟩ : ∃ R > 0, ∀ n, dist (u n) (u N) < R
  · exact ⟨_, add_pos R0 R0, fun m n =>
      lt_of_le_of_lt (dist_triangle_right _ _ _) (add_lt_add (H m) (H n))⟩
  let R := Finset.sup (Finset.range N) fun n => nndist (u n) (u N)
  refine ⟨↑R + 1, add_pos_of_nonneg_of_pos R.2 zero_lt_one, fun n => ?_⟩
  rcases le_or_gt N n with h | h
  · exact lt_of_lt_of_le (hN _ h) (le_add_of_nonneg_left R.2)
  · have : _ ≤ R := Finset.le_sup (Finset.mem_range.2 h)
    exact lt_of_le_of_lt this (lt_add_of_pos_right _ zero_lt_one)

/-- Yet another metric characterization of Cauchy sequences on integers. This one is often the
most efficient. -/
theorem cauchySeq_iff_le_tendsto_0 {s : ℕ → α} :
    CauchySeq s ↔
      ∃ b : ℕ → ℝ,
        (∀ n, 0 ≤ b n) ∧
          (∀ n m N : ℕ, N ≤ n → N ≤ m → dist (s n) (s m) ≤ b N) ∧ Tendsto b atTop (𝓝 0) :=
  ⟨fun hs => by
    /- `s` is a Cauchy sequence. The sequence `b` will be constructed by taking
      the supremum of the distances between `s n` and `s m` for `n m ≥ N`.
      First, we prove that all these distances are bounded, as otherwise the Sup
      would not make sense. -/
    let S N := (fun p : ℕ × ℕ => dist (s p.1) (s p.2)) '' { p | p.1 ≥ N ∧ p.2 ≥ N }
    have hS : ∀ N, ∃ x, ∀ y ∈ S N, y ≤ x := by
      rcases cauchySeq_bdd hs with ⟨R, -, hR⟩
      refine fun N => ⟨R, ?_⟩
      rintro _ ⟨⟨m, n⟩, _, rfl⟩
      exact le_of_lt (hR m n)
    -- Prove that it bounds the distances of points in the Cauchy sequence
    have ub : ∀ m n N, N ≤ m → N ≤ n → dist (s m) (s n) ≤ sSup (S N) := fun m n N hm hn =>
      le_csSup (hS N) ⟨⟨_, _⟩, ⟨hm, hn⟩, rfl⟩
    have S0m : ∀ n, (0 : ℝ) ∈ S n := fun n => ⟨⟨n, n⟩, ⟨le_rfl, le_rfl⟩, dist_self _⟩
    have S0 := fun n => le_csSup (hS n) (S0m n)
    -- Prove that it tends to `0`, by using the Cauchy property of `s`
    refine ⟨fun N => sSup (S N), S0, ub, Metric.tendsto_atTop.2 fun ε ε0 => ?_⟩
    refine (Metric.cauchySeq_iff.1 hs (ε / 2) (half_pos ε0)).imp fun N hN n hn => ?_
    rw [Real.dist_0_eq_abs, abs_of_nonneg (S0 n)]
    refine lt_of_le_of_lt (csSup_le ⟨_, S0m _⟩ ?_) (half_lt_self ε0)
    rintro _ ⟨⟨m', n'⟩, ⟨hm', hn'⟩, rfl⟩
    exact le_of_lt (hN _ (le_trans hn hm') _ (le_trans hn hn')),
   fun ⟨b, _, b_bound, b_lim⟩ => cauchySeq_of_le_tendsto_0 b b_bound b_lim⟩

lemma Metric.exists_subseq_bounded_of_cauchySeq (u : ℕ → α) (hu : CauchySeq u) (b : ℕ → ℝ)
    (hb : ∀ n, 0 < b n) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ ∀ n, ∀ m ≥ f n, dist (u m) (u (f n)) < b n := by
  rw [cauchySeq_iff] at hu
  have hu' : ∀ k, ∀ᶠ (n : ℕ) in atTop, ∀ m ≥ n, dist (u m) (u n) < b k := by
    intro k
    rw [eventually_atTop]
    obtain ⟨N, hN⟩ := hu (b k) (hb k)
    exact ⟨N, fun m hm r hr => hN r (hm.trans hr) m hm⟩
  exact Filter.extraction_forall_of_eventually hu'

end CauchySeq
