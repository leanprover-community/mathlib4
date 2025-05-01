/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Sums over residue classes

We consider infinite sums over functions `f` on `ℕ`, restricted to a residue class mod `m`.

The main result is `summable_indicator_mod_iff`, which states that when `f : ℕ → ℝ` is
decreasing, then the sum over `f` restricted to any residue class
mod `m ≠ 0` converges if and only if the sum over all of `ℕ` converges.
-/


lemma Finset.sum_indicator_mod {R : Type*} [AddCommMonoid R] (m : ℕ) [NeZero m] (f : ℕ → R) :
    f = ∑ a : ZMod m, {n : ℕ | (n : ZMod m) = a}.indicator f := by
  ext n
  simp only [Finset.sum_apply, Set.indicator_apply, Set.mem_setOf_eq, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte]

open Set in
/-- A sequence `f` with values in an additive topological group `R` is summable on the
residue class of `k` mod `m` if and only if `f (m*n + k)` is summable. -/
lemma summable_indicator_mod_iff_summable {R : Type*} [AddCommGroup R] [TopologicalSpace R]
    [IsTopologicalAddGroup R] (m : ℕ) [hm : NeZero m] (k : ℕ) (f : ℕ → R) :
    Summable ({n : ℕ | (n : ZMod m) = k}.indicator f) ↔ Summable fun n ↦ f (m * n + k) := by
  trans Summable ({n : ℕ | (n : ZMod m) = k ∧ k ≤ n}.indicator f)
  · rw [← (finite_lt_nat k).summable_compl_iff (f := {n : ℕ | (n : ZMod m) = k}.indicator f)]
    simp only [summable_subtype_iff_indicator, indicator_indicator, inter_comm, setOf_and,
      compl_setOf, not_lt]
  · let g : ℕ → ℕ := fun n ↦ m * n + k
    have hg : Function.Injective g := fun m n hmn ↦ by simpa [g, hm.ne] using hmn
    have hg' : ∀ n ∉ range g, {n : ℕ | (n : ZMod m) = k ∧ k ≤ n}.indicator f n = 0 := by
      intro n hn
      contrapose! hn
      exact (Nat.range_mul_add m k).symm ▸ mem_of_indicator_ne_zero hn
    convert (Function.Injective.summable_iff hg hg').symm using 3
    simp only [Function.comp_apply, mem_setOf_eq, Nat.cast_add, Nat.cast_mul, CharP.cast_eq_zero,
      zero_mul, zero_add, le_add_iff_nonneg_left, zero_le, and_self, indicator_of_mem, g]

/-- If `f : ℕ → ℝ` is decreasing and has a negative term, then `f` is not summable. -/
lemma not_summable_of_antitone_of_neg {f : ℕ → ℝ} (hf : Antitone f) {n : ℕ} (hn : f n < 0) :
    ¬ Summable f := by
  intro hs
  have := hs.tendsto_atTop_zero
  simp only [Metric.tendsto_atTop, dist_zero_right, Real.norm_eq_abs] at this
  obtain ⟨N, hN⟩ := this (|f n|) (abs_pos_of_neg hn)
  specialize hN (max n N) (n.le_max_right N)
  contrapose! hN; clear hN
  have H : f (max n N) ≤ f n := hf (n.le_max_left N)
  rwa [abs_of_neg hn, abs_of_neg (H.trans_lt hn), neg_le_neg_iff]

/-- If `f : ℕ → ℝ` is decreasing and has a negative term, then `f` restricted to a residue
class is not summable. -/
lemma not_summable_indicator_mod_of_antitone_of_neg {m : ℕ} [hm : NeZero m] {f : ℕ → ℝ}
    (hf : Antitone f) {n : ℕ} (hn : f n < 0) (k : ZMod m) :
    ¬ Summable ({n : ℕ | (n : ZMod m) = k}.indicator f) := by
  rw [← ZMod.natCast_zmod_val k, summable_indicator_mod_iff_summable]
  exact not_summable_of_antitone_of_neg
    (hf.comp_monotone <| (Covariant.monotone_of_const m).add_const k.val) <|
    (hf <| (Nat.le_mul_of_pos_left n Fin.pos').trans <| Nat.le_add_right ..).trans_lt hn

/-- If a decreasing sequence of real numbers is summable on one residue class
modulo `m`, then it is also summable on every other residue class mod `m`. -/
lemma summable_indicator_mod_iff_summable_indicator_mod {m : ℕ} [NeZero m] {f : ℕ → ℝ}
    (hf : Antitone f) {k : ZMod m} (l : ZMod m)
    (hs : Summable ({n : ℕ | (n : ZMod m) = k}.indicator f)) :
    Summable ({n : ℕ | (n : ZMod m) = l}.indicator f) := by
  by_cases hf₀ : ∀ n, 0 ≤ f n -- the interesting case
  · rw [← ZMod.natCast_zmod_val k, summable_indicator_mod_iff_summable] at hs
    have hl : (l.val + m : ZMod m) = l := by
      simp only [ZMod.natCast_val, ZMod.cast_id', id_eq, CharP.cast_eq_zero, add_zero]
    rw [← hl, ← Nat.cast_add, summable_indicator_mod_iff_summable]
    exact hs.of_nonneg_of_le (fun _ ↦ hf₀ _)
      fun _ ↦ hf <| Nat.add_le_add Nat.le.refl (k.val_lt.trans_le <| m.le_add_left l.val).le
  · push_neg at hf₀
    obtain ⟨n, hn⟩ := hf₀
    exact (not_summable_indicator_mod_of_antitone_of_neg hf hn k hs).elim

/-- A decreasing sequence of real numbers is summable on a residue class
if and only if it is summable. -/
lemma summable_indicator_mod_iff {m : ℕ} [NeZero m] {f : ℕ → ℝ} (hf : Antitone f) (k : ZMod m) :
    Summable ({n : ℕ | (n : ZMod m) = k}.indicator f) ↔ Summable f := by
  refine ⟨fun H ↦ ?_, fun H ↦ Summable.indicator H _⟩
  rw [Finset.sum_indicator_mod m f]
  convert summable_sum (s := Finset.univ)
    fun a _ ↦ summable_indicator_mod_iff_summable_indicator_mod hf a H
  simp only [Finset.sum_apply]

open ZMod

/-- If `f` is a summable function on `ℕ`, and `0 < N`, then we may compute `∑' n : ℕ, f n` by
summing each residue class mod `N` separately. -/
lemma Nat.sumByResidueClasses {R : Type*} [AddCommGroup R] [UniformSpace R] [IsUniformAddGroup R]
    [CompleteSpace R] [T0Space R] {f : ℕ → R} (hf : Summable f) (N : ℕ) [NeZero N] :
    ∑' n, f n = ∑ j : ZMod N, ∑' m, f (j.val + N * m) := by
  rw [← (residueClassesEquiv N).symm.tsum_eq f, Summable.tsum_prod, tsum_fintype,
    residueClassesEquiv, Equiv.coe_fn_symm_mk]
  exact hf.comp_injective (residueClassesEquiv N).symm.injective
