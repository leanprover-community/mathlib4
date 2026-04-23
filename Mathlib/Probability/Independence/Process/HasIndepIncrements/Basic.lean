/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion, Joris van Winden
-/
module

public import Mathlib.Probability.Independence.Basic

import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
public import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
# Stochastic processes with independent increments

A stochastic process `X : T → Ω → E` has independent increments if for any `n ≥ 1` and
`t₁ ≤ ... ≤ tₙ`, the random variables `X t₂ - X t₁, ..., X tₙ - X tₙ₋₁` are independent.
Equivalently, for any monotone sequence `(tₙ)`, the random variables `(X tₙ₊₁ - X tₙ)`
are independent.

## Main definition

* `HasIndepIncrements`: A stochastic process `X : T → Ω → E` has independent increments if for any
  `n ≥ 1` and `t₁ ≤ ... ≤ tₙ`, the random variables `X t₂ - X t₁, ..., X tₙ - X tₙ₋₁` are
  independent.

## Main statement

* `hasIndepIncrements_iff_nat`: A stochastic process `X : T → Ω → E` has independent increments if
  and only if for any monotone sequence `(tₙ)`, the random variables `(X tₙ₊₁ - X tₙ)` are
  independent.

## Tags

independent increments
-/

@[expose] public section

open MeasureTheory Filter

namespace ProbabilityTheory

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : T → Ω → E}
  [Preorder T] [MeasurableSpace E]

section Def

variable [Sub E]

/-- A stochastic process `X : T → Ω → E` has independent increments if for any `n ≥ 1` and
`t₁ ≤ ... ≤ tₙ`, the random variables `X t₂ - X t₁, ..., X tₙ - X tₙ₋₁` are independent.

Although this corresponds to the standard definition, dealing with `Fin` might make things
complicated in some cases. Therefore we provide `HasIndepIncrements.of_nat` which instead requires
to prove that for any monotone sequence `(tₙ)` that is eventually constant,
the random variables `X tₙ₊₁ - X tₙ` are independent. -/
def HasIndepIncrements (X : T → Ω → E) (P : Measure Ω := by volume_tac) : Prop :=
  ∀ n, ∀ t : Fin (n + 1) → T, Monotone t →
    iIndepFun (fun (i : Fin n) ω ↦ X (t i.succ) ω - X (t i.castSucc) ω) P

protected lemma HasIndepIncrements.nat
    (hX : HasIndepIncrements X P) {t : ℕ → T} (ht : Monotone t) :
    iIndepFun (fun i ω ↦ X (t (i + 1)) ω - X (t i) ω) P := by
  refine iIndepFun_iff_finset.2 fun s ↦ ?_
  obtain rfl | hs := s.eq_empty_or_nonempty
  · have := (hX 0 (fun _ ↦ t 0) (fun _ ↦ by grind)).isProbabilityMeasure
    exact iIndepFun.of_subsingleton
  · let g (x : s) : Fin (s.max' hs + 1) := ⟨x.1, Nat.lt_add_one_of_le (s.le_max' x.1 x.2)⟩
    refine iIndepFun.precomp (g := g) ?_ (hX (s.max' hs + 1) (fun m ↦ t m) ?_)
    · simp [g, Function.Injective]
    · exact ht.comp Fin.val_strictMono.monotone

protected lemma HasIndepIncrements.of_nat
    (h : ∀ t : ℕ → T, Monotone t → EventuallyConst t atTop →
      iIndepFun (fun i ω ↦ X (t (i + 1)) ω - X (t i) ω) P) :
    HasIndepIncrements X P := by
  intro n t ht
  let t' k := t ⟨min n k, by grind⟩
  convert (h t' ?_ ?_).precomp Fin.val_injective with i ω
  · grind
  · grind
  · exact fun a b hab ↦ ht (by grind)
  · exact eventuallyConst_atTop.2 ⟨n, by grind⟩

lemma hasIndepIncrements_iff_nat :
    HasIndepIncrements X P ↔
    ∀ t : ℕ → T, Monotone t → iIndepFun (fun i ω ↦ X (t (i + 1)) ω - X (t i) ω) P where
  mp h _ ht := h.nat ht
  mpr h := .of_nat (fun t ht _ ↦ h t ht)

end Def

lemma HasIndepIncrements.indepFun_sub_sub [Sub E] (hX : HasIndepIncrements X P) {r s t : T}
    (hrs : r ≤ s) (hst : s ≤ t) :
    (X s - X r) ⟂ᵢ[P] (X t - X s) := by
  let τ : ℕ → T
    | 0 => r
    | 1 => s
    | _ => t
  exact hX.nat (t := τ) (fun _ ↦ by grind) |>.indepFun (by grind : 0 ≠ 1)

lemma HasIndepIncrements.indepFun_eval_sub [SubNegZeroMonoid E] (hX : HasIndepIncrements X P)
    {r s t : T} (hrs : r ≤ s) (hst : s ≤ t) (h : ∀ᵐ ω ∂P, X r ω = 0) :
    (X s) ⟂ᵢ[P] (X t - X s) := by
  refine (hX.indepFun_sub_sub hrs hst).congr ?_ .rfl
  filter_upwards [h] with ω hω using by simp [hω]

protected lemma HasIndepIncrements.map' {F G : Type*} [MeasurableSpace G] [FunLike F E G]
    [AddGroup E] [SubtractionMonoid G] [AddMonoidHomClass F E G] {f : F} (hf : Measurable f)
    (hX : HasIndepIncrements X P) :
    HasIndepIncrements (fun t ω ↦ f (X t ω)) P := by
  intro n t ht
  simp_rw [← map_sub]
  exact (hX n t ht).comp (fun _ ↦ f) (fun _ ↦ hf)

protected lemma HasIndepIncrements.map {R F : Type*} [Semiring R] [SeminormedAddCommGroup E]
    [Module R E] [OpensMeasurableSpace E] [SeminormedAddCommGroup F] [Module R F]
    [MeasurableSpace F] [BorelSpace F] (L : E →L[R] F) (hX : HasIndepIncrements X P) :
    HasIndepIncrements (fun t ω ↦ L (X t ω)) P :=
  hX.map' L.measurable

protected lemma HasIndepIncrements.smul {R : Type*} [AddGroup E] [DistribSMul R E]
    [MeasurableConstSMul R E] (hX : HasIndepIncrements X P) (c : R) :
    HasIndepIncrements (fun t ω ↦ c • (X t ω)) P :=
  hX.map' (f := DistribSMul.toAddMonoidHom E c) (MeasurableConstSMul.measurable_const_smul c)

protected lemma HasIndepIncrements.neg [AddCommGroup E] [MeasurableNeg E]
    (hX : HasIndepIncrements X P) :
    HasIndepIncrements (-X) P :=
  hX.map' (f := negAddMonoidHom) measurable_neg

end ProbabilityTheory
