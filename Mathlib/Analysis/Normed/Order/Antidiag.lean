/-
Copyright (c) 2025 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
module

public import Mathlib.Algebra.Order.Antidiag.Prod
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Algebra.Order.GroupWithZero.Finset

/-!
# tendsto_antidiagonal

`tendsto_antidiagonal` : Given two functions `f g` from a monoid to a non-archimedean Normed ring,
  and a function `C` from the monoid to ℝ, if `Tendsto (fun i ↦ ‖f i‖ * C i) cofinite (𝓝 0))`
  and `Tendsto (fun i ↦ ‖g i‖ * C i) cofinite (𝓝 0))` holds, then we also have
  `Tendsto (fun a ↦ ‖∑ p ∈ Finset.antidiagonal a, (f p.1 * g p.2)‖ * C a) cofinite (𝓝 0)`.

-/

@[expose] public section

open Filter
open scoped Topology Pointwise

open IsUltrametricDist

lemma Finset.nonempty_antidiagonal {M : Type*} [AddMonoid M] [Finset.HasAntidiagonal M] (a : M) :
    (Finset.antidiagonal a).Nonempty :=
  ⟨(0, a), by simp⟩

open Filter Pointwise in
lemma tendsto_sup'_antidiagonal_cofinite
    {M R : Type*} [AddMonoid M] [Finset.HasAntidiagonal M] {f : M × M → R}
    [LinearOrder R] {F : Filter R} (hf : Tendsto f cofinite F) :
    Tendsto (fun a ↦ (Finset.antidiagonal a).sup' (Finset.nonempty_antidiagonal _) f)
      cofinite F := by
  intro U hU
  refine ((((hf hU).image Prod.fst)).add ((hf hU).image Prod.snd)).subset ?_
  simp only [Set.subset_def, Set.mem_compl_iff, Set.mem_preimage]
  intro x hx
  obtain ⟨i, hi, e⟩ := Finset.exists_mem_eq_sup' (Finset.nonempty_antidiagonal x) f
  obtain rfl : i.1 + i.2 = x := by simpa using hi
  exact Set.add_mem_add (by simpa using ⟨i.2, e ▸ hx⟩) (by simpa using ⟨i.1, e ▸ hx⟩)

open IsUltrametricDist Filter Topology Pointwise in
lemma tendsto_antidiagonal {M S : Type*} [AddMonoid M] [Finset.HasAntidiagonal M] [NormedRing S]
    [IsUltrametricDist S] {C : M → ℝ} (hC : ∀ a b, C (a + b) = C a * C b) {f g : M → S}
    (hf : Tendsto (fun i ↦ ‖f i‖ * C i) cofinite (𝓝 0))
    (hg : Tendsto (fun i ↦ ‖g i‖ * C i) cofinite (𝓝 0)) :
    Tendsto (fun a ↦ ‖∑ p ∈ Finset.antidiagonal a, (f p.1 * g p.2)‖ * C a) cofinite (𝓝 0) := by
  wlog hC' : 0 ≤ C generalizing C
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa using this (C := |C|) (by simp [hC]) (by simpa using hf.norm)
      (by simpa using hg.norm) (fun _ => by simp)
  refine .squeeze tendsto_const_nhds
    (tendsto_sup'_antidiagonal_cofinite (tendsto_mul_cofinite_nhds_zero hf hg))
    (fun x => by simpa using (mul_nonneg (by simp) (hC' x))) fun a ↦ ?_
  have : 0 ≤ C a := hC' a
  grw [(Finset.nonempty_antidiagonal _).norm_sum_le_sup'_norm, Finset.sup'_mul₀ this]
  refine Finset.sup'_mono_fun fun x hx ↦ ?_
  grw [mul_mul_mul_comm, ← hC, Finset.mem_antidiagonal.mp hx, ← norm_mul_le]
