/-
Copyright (c) 2026 Nikolas Tapia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nikolas Tapia
-/
module
public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.Order.WithBotTop
public import Mathlib.Analysis.Controls.ControlOn

/-!
# Bounded Variation

## Main statements

We prove facts relating control functions (see `Mathlib.Analysis.Controls.Defs`) and functions of
bounded variation on a subset.

- `eVariationOn.bdd_of_le_control`: if the consecutive values of a function distances bounded by a
control function, then its variation is bounded by the same control.
- `eVariationOn.boundedVariation_of_le`: under the same hypotheses, said function is of locally
bounded variation on `s`.

## Tags

control function, bounded variation
-/

@[expose] public section

open scoped ENNReal NNReal

variable {α E} [LinearOrder α] [TopologicalSpace α] [PseudoEMetricSpace E]
variable {s : Set α}

namespace ControlOn

@[simp]
theorem sum_seq_le (ω : ControlOn α s) (p : ℕ × {u : ℕ → α // Monotone u ∧ ∀ i, u i ∈ s}) :
    ∑ i ∈ Finset.range p.1, ω (p.2.1 i) (p.2.1 i.succ) ≤ ω (p.2.1 0) (p.2.1 p.1) := by
  induction p.1 with
  | zero => simp
  | succ n ha => {
      have := (add_le_add_left ha (ω (p.2.1 n) (p.2.1 n.succ))).trans <| ω.superadd (p.2.2.2 0)
        (p.2.2.2 n) (p.2.2.2 n.succ) (p.2.2.1.imp (by positivity)) (p.2.2.1.imp n.le_succ)
      simpa [Finset.sum_range_succ]
    }

end ControlOn

namespace eVariationOn

variable {f : α → E} {ω : ControlOn α s}

theorem bdd_of_le_control {a b} {C : ℝ≥0} (ha : IsLeast s a) (hb : IsGreatest s b)
    (hbd : ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → x ≤ y → edist (f y) (f x) ≤ C * ω x y) :
    eVariationOn f s ≤ C * ω a b := by
  wlog hC : C = 1 with H
  · simpa using H (ω := C • ω) (C := 1) ha hb (by simpa)
  · simp only [hC, ENNReal.coe_one, one_mul] at hbd ⊢
    apply iSup_le
    intro ⟨n, u, hmon, hmem⟩
    suffices hω : ENNReal.ofNNReal (ω (u 0) (u n)) ≤ ENNReal.ofNNReal (ω a b) by
      exact (Finset.sum_le_sum (s := Finset.range n) fun i _ => hbd (hmem i) (hmem i.succ)
        (hmon.imp i.le_succ)).trans (by exact_mod_cast ω.sum_seq_le ⟨n, u, hmon, hmem⟩) |>.trans hω
    exact_mod_cast (ω.mono_right_of_le_le (hmem 0) (hmem n) hb.1
      (hmon.imp (by positivity)) (hb.2 (hmem n))).trans <|
      ω.anti_left_of_le_le ha.1 (hmem 0) hb.1 (ha.2 (hmem 0)) (hb.2 (hmem 0))

theorem boundedVariationOn_of_le {C : ℝ≥0}
    (hbd : ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → x ≤ y → edist (f y) (f x) ≤ C * ω x y) :
    LocallyBoundedVariationOn f s := by
  intro a b ha hb

  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.coe_ne_top (r := C)) ()) ()


end eVariationOn
