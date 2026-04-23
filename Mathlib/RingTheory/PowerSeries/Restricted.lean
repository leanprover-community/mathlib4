/-
Copyright (c) 2025 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.AdaptationNote
import Mathlib.Tactic.Bound
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Order.T5

/-!
# Restricted power series

`IsRestricted` : We say a power series over a normed ring `R` is restricted for a parameter `c` if
`‖coeff R i f‖ * c ^ i → 0`.

-/

@[expose] public section

namespace PowerSeries

variable {R : Type*} [NormedRing R] (c : ℝ)

open PowerSeries Filter
open scoped Topology

/-- A power series over `R` is restricted of parameter `c` if we have
`‖coeff R i f‖ * c ^ i → 0`. -/
def IsRestricted (f : PowerSeries R) :=
  Tendsto (fun (i : ℕ) ↦ (norm (coeff i f)) * c ^ i) atTop (𝓝 0)

namespace IsRestricted

lemma isRestricted_iff {f : PowerSeries R} : IsRestricted c f ↔
    ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → ‖‖(coeff n) f‖ * c ^ n‖ < ε := by
  simp [IsRestricted, NormedAddCommGroup.tendsto_atTop]

lemma isRestricted_iff_abs (f : PowerSeries R) : IsRestricted c f ↔ IsRestricted |c| f := by
  simp [isRestricted_iff]

lemma zero : IsRestricted c (0 : PowerSeries R) := by
  simp [IsRestricted]

lemma one : IsRestricted c (1 : PowerSeries R) := by
  simp only [isRestricted_iff, coeff_one, norm_mul, norm_pow, Real.norm_eq_abs]
  refine fun _ _ ↦ ⟨1, fun n hn ↦ ?_ ⟩
  split
  · lia
  · simpa

lemma monomial (n : ℕ) (a : R) : IsRestricted c (monomial n a) := by
  simp only [monomial_eq_mk, isRestricted_iff, coeff_mk, norm_mul, norm_pow,
    Real.norm_eq_abs, abs_norm]
  refine fun _ _ ↦ ⟨n + 1, fun _ _ ↦ ?_⟩
  split
  · lia
  · simpa

lemma C (a : R) : IsRestricted c (C a) := by
  simpa [monomial_zero_eq_C_apply] using monomial c 0 a

lemma add {f g : PowerSeries R} (hf : IsRestricted c f) (hg : IsRestricted c g) :
    IsRestricted c (f + g) := by
  simp only [isRestricted_iff, map_add, norm_mul, norm_pow, Real.norm_eq_abs] at ⊢ hf hg
  intro ε hε
  obtain ⟨fN, hfN⟩ := hf (ε / 2) (by positivity)
  obtain ⟨gN, hgN⟩ := hg (ε / 2) (by positivity)
  simp only [abs_norm] at hfN hgN ⊢
  refine ⟨max fN gN, fun n hn ↦ ?_ ⟩
  calc _ ≤ ‖(coeff n) f‖ * |c| ^ n + ‖(coeff n) g‖ * |c| ^ n := by grw [norm_add_le, add_mul]
       _ < ε / 2 + ε / 2 := by gcongr <;> grind
       _ = ε := by ring

lemma neg {f : PowerSeries R} (hf : IsRestricted c f) : IsRestricted c (-f) := by
  simpa [isRestricted_iff] using hf

lemma smul {f : PowerSeries R} (hf : IsRestricted c f) (r : R) : IsRestricted c (r • f) := by
  if h : r = 0 then simpa [h] using zero c else
  simp_rw [isRestricted_iff, norm_mul, norm_pow, Real.norm_eq_abs, abs_norm] at ⊢ hf
  intro ε _
  obtain ⟨n, hn⟩ := hf (ε / ‖r‖) (by positivity)
  refine ⟨n, fun N hN ↦ ?_⟩
  calc _ ≤ ‖r‖ * ‖(coeff N) f‖ * |c| ^ N :=
        mul_le_mul_of_nonneg (norm_mul_le _ _) (by simp) (by simp) (by simp)
       _ < ‖r‖ * (ε / ‖r‖) := by
        rw [mul_assoc]; aesop
       _ = ε := mul_div_cancel₀ _ (by aesop)


/-- The set of `‖coeff R i f‖ * c ^ i` for a given power series `f` and parameter `c`. -/
def convergenceSet (f : PowerSeries R) : Set ℝ := {‖coeff i f‖ * c^i | i : ℕ}

open Finset in
lemma convergenceSet_BddAbove {f : PowerSeries R} (hf : IsRestricted c f) :
    BddAbove (convergenceSet c f) := by
  simp_rw [isRestricted_iff] at hf
  obtain ⟨N, hf⟩ := by simpa using (hf 1)
  rw [bddAbove_def, convergenceSet]
  use max 1 (max' (image (fun i ↦ ‖coeff i f‖ * c ^ i) (range (N + 1))) (by simp))
  simp only [Set.mem_setOf_eq, le_sup_iff, forall_exists_index, forall_apply_eq_imp_iff]
  intro i
  rcases le_total i N with h | h
  · right
    apply le_max'
    simp only [mem_image, mem_range]
    exact ⟨i, by lia, rfl⟩
  · left
    calc _ ≤ ‖(coeff i) f‖ * |c ^ i| := by bound
         _ ≤ 1 := by simpa using (hf i h).le

variable [IsUltrametricDist R]

open IsUltrametricDist

lemma mul {f g : PowerSeries R} (hf : IsRestricted c f) (hg : IsRestricted c g) :
    IsRestricted c (f * g) := by
  obtain ⟨a, ha, fBound1⟩ := (bddAbove_iff_exists_ge 1).mp (convergenceSet_BddAbove _
    ((isRestricted_iff_abs c f).mp hf))
  obtain ⟨b, hb, gBound1⟩ := (bddAbove_iff_exists_ge 1).mp (convergenceSet_BddAbove _
    ((isRestricted_iff_abs c g).mp hg))
  simp only [convergenceSet, Set.mem_setOf_eq, forall_exists_index, forall_apply_eq_imp_iff]
    at fBound1 gBound1
  simp only [isRestricted_iff, norm_mul, norm_pow, Real.norm_eq_abs, abs_norm,
    PowerSeries.coeff_mul] at ⊢ hf hg
  intro ε hε
  obtain ⟨Nf, fBound2⟩ := (hf (ε / (max a b))) (by positivity)
  obtain ⟨Ng, gBound2⟩ := (hg (ε / (max a b))) (by positivity)
  refine ⟨2 * max Nf Ng, fun n hn ↦ ?_⟩
  obtain ⟨⟨fst, snd⟩, hi, ultrametric⟩ := exists_norm_finset_sum_le (Finset.antidiagonal n)
    (fun a ↦ (coeff a.1) f * (coeff a.2) g)
  obtain ⟨rfl⟩ := by simpa using hi (⟨(0, n), by simp⟩)
  calc _ ≤ ‖(coeff fst) f * (coeff snd) g‖ * |c| ^ (fst + snd) := by bound
       _ ≤ ‖(coeff fst) f‖ * |c| ^ fst * (‖(coeff snd) g‖ * |c| ^ snd) := by
        grw [norm_mul_le]
        #adaptation_note
        /--
        Broken in `nightly-2025-10-26`: this was by `grind`, but is now no longer supported.
        See https://github.com/leanprover/lean4/pull/10970.
        -/
        rw [pow_add]
        grind
  have : max Nf Ng ≤ fst ∨ max Nf Ng ≤ snd := by lia
  rcases this with this | this
  · calc _ < ε / max a b * b := by
          grw [gBound1 snd]
          gcongr
          exact fBound2 fst (by omega)
         _ ≤ ε := by
          rw [div_mul_comm, mul_le_iff_le_one_left ‹_›]
          bound
  · calc _ < a * (ε / max a b) := by
          grw [fBound1 fst]
          gcongr
          exact gBound2 snd (by omega)
         _ ≤ ε := by
          rw [mul_div_left_comm, mul_le_iff_le_one_right ‹_›]
          bound

end IsRestricted
end PowerSeries
