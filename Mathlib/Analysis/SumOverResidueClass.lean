/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Instances.ENNReal

/-!
# Sums over residue classes

We consider infinite sums over functions `f` on `ℕ`, restricted to a residue class mod `m`.

The main result is `summable_indicator_mod_iff`, which states that when `f : ℕ → ℝ` is
decreasing and takes nonnegative values, then the sum over `f` restricted to any residue class
mod `m ≠ 0` converges if and only if the sum over all of `ℕ` converges.

(Note that we want to use `Summable.of_nonneg_of_le`, which insists on `ℝ` as the target.)
-/


open BigOperators in
lemma Finset.sum_indicator_mod {R : Type*} [AddCommMonoid R] (m : ℕ) [NeZero m] (f : ℕ → R) :
    f = ∑ a : ZMod m, {n : ℕ | (n : ZMod m) = a}.indicator f := by
  ext n
  simp only [Finset.sum_apply, Set.indicator_apply, Set.mem_setOf_eq, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte]

variable (m : ℕ) [hm : NeZero m]

open Set in
/-- A sequence `f` with values in an additive topological group `R` is summable on the
residue class of `k` mod `m` if and only if `f (m*n + k)` is summable. -/
lemma summable_indicator_mod_iff_summable {R : Type*} [AddCommGroup R] [TopologicalSpace R]
    [TopologicalAddGroup R] (k : ℕ) (f : ℕ → R) :
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

variable {f : ℕ → ℝ}

/-- If a decreasing nonngeative sequence of real numbers is summable on one residue class
modulo `m`, then it is also summable on every other residue class mod `m`. -/
lemma summable_indicator_mod_iff_summable_indicator_mod (hf : Antitone f) (hf₀ : ∀ n, 0 ≤ f n)
    {k : ZMod m} (l : ZMod m) (hs : Summable ({n : ℕ | (n : ZMod m) = k}.indicator f)) :
    Summable ({n : ℕ | (n : ZMod m) = l}.indicator f) := by
  rw [← ZMod.nat_cast_zmod_val k, summable_indicator_mod_iff_summable] at hs
  have hl : (l.val + m : ZMod m) = l := by
    simp only [ZMod.nat_cast_val, ZMod.cast_id', id_eq, CharP.cast_eq_zero, add_zero]
  rw [← hl, ← Nat.cast_add, summable_indicator_mod_iff_summable]
  refine Summable.of_nonneg_of_le (fun n ↦ hf₀ _) (fun n ↦ hf <| Nat.add_le_add Nat.le.refl ?_) hs
  exact ((ZMod.val_lt k).trans_le <| m.le_add_left (ZMod.val l)).le

/-- A decreasing nonnegative sequence of real numbers is summable on a residue class
if and only if it is summable. -/
lemma summable_indicator_mod_iff (hf : Antitone f) (hf₀ : ∀ n, 0 ≤ f n) (k : ZMod m) :
    Summable ({n : ℕ | (n : ZMod m) = k}.indicator f) ↔ Summable f := by
  refine ⟨fun H ↦ ?_, fun H ↦ Summable.indicator H _⟩
  have key (a : ZMod m) : Summable ({n : ℕ | (n :ZMod m) = a}.indicator f) :=
    summable_indicator_mod_iff_summable_indicator_mod m hf hf₀ a H
  rw [Finset.sum_indicator_mod m f]
  convert summable_sum (s := Finset.univ) fun a _ ↦ key a
  simp only [Finset.sum_apply]
