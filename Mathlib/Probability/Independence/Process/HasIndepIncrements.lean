/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion, Joris van Winden
-/
module

public import Mathlib


@[expose] public section

open MeasureTheory NNReal WithLp Finset MeasurableSpace Filtration Filter
open scoped ENNReal NNReal Topology BoundedContinuousFunction

namespace ProbabilityTheory

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : T → Ω → E}

section Def

variable [Preorder T] [Sub E] [MeasurableSpace E]

/-- A process `X : T → Ω → E` has independent increments if for any `n ≥ 1` and `t₁ ≤ ... ≤ tₙ`,
the random variables `X t₂ - X t₁, ..., X tₙ - X tₙ₋₁` are independent. -/
def HasIndepIncrements (X : T → Ω → E) (P : Measure Ω := by volume_tac) : Prop :=
  ∀ n, ∀ t : Fin (n + 1) → T, Monotone t →
    iIndepFun (fun (i : Fin n) ω ↦ X (t i.succ) ω - X (t i.castSucc) ω) P

lemma HasIndepIncrements.increments_nat
    (hX : HasIndepIncrements X P) {t : ℕ → T} (ht : Monotone t) :
    iIndepFun (fun i ω ↦ X (t (i + 1)) ω - X (t i) ω) P := by
  refine iIndepFun_iff_finset.2 fun s ↦ ?_
  by_cases! hs : s.Nonempty
  · let g (x : s) : Fin (s.max' hs + 1) := ⟨x.1, Nat.lt_add_one_of_le (s.le_max' x.1 x.2)⟩
    refine iIndepFun.precomp (g := g) ?_ (hX (s.max' hs + 1) (fun m ↦ t m) ?_)
    · simp [g, Function.Injective]
    · exact ht.comp Fin.val_strictMono.monotone
  · have := (hX 0 (fun _ ↦ t 0) (fun _ ↦ by grind)).isProbabilityMeasure
    rw [hs]
    exact iIndepFun.of_subsingleton

lemma HasIndepIncrements.of_increments_nat
    (h : ∀ t : ℕ → T, Monotone t → EventuallyConst t atTop →
      iIndepFun (fun i ω ↦ X (t (i + 1)) ω - X (t i) ω) P) :
    HasIndepIncrements X P := by
  intro n t ht
  let t' k := t ⟨min n k, by grind⟩
  convert (h t' ?_ ?_).precomp Fin.val_injective with i ω
  · simp
  · grind
  · exact fun a b hab ↦ ht (by grind)
  · exact eventuallyConst_atTop.2 ⟨n, by grind⟩

lemma hasIndepIncrements_iff_nat :
    HasIndepIncrements X P ↔
    ∀ t : ℕ → T, Monotone t → iIndepFun (fun i ω ↦ X (t (i + 1)) ω - X (t i) ω) P where
  mp h _ ht := h.increments_nat ht
  mpr h := .of_increments_nat (fun t ht _ ↦ h t ht)

end Def

end ProbabilityTheory
