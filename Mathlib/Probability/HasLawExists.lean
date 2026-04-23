/-
Copyright (c) 2025 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Probability.HasLaw
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
# Existence of Random Variables

This file contains lemmas that state the existence of random variables with given distributions
and a given dependency structure (currently only mutual independence is considered).
-/

public section

open MeasureTheory Measure

namespace ProbabilityTheory

universe u v

lemma _root_.MeasureTheory.Measure.exists_hasLaw {𝓧 : Type u} {m𝓧 : MeasurableSpace 𝓧}
    (μ : Measure 𝓧) :
    ∃ Ω : Type u, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω, ∃ X : Ω → 𝓧,
      Measurable X ∧ HasLaw X μ P :=
  ⟨𝓧, m𝓧, μ, id, measurable_id, .id⟩

lemma exists_hasLaw_indepFun {ι : Type v} (𝓧 : ι → Type u)
    {m𝓧 : ∀ i, MeasurableSpace (𝓧 i)} (μ : (i : ι) → Measure (𝓧 i))
    [hμ : ∀ i, IsProbabilityMeasure (μ i)] :
    ∃ Ω : Type (max u v), ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω, ∃ X : (i : ι) → Ω → (𝓧 i),
      (∀ i, Measurable (X i)) ∧ (∀ i, HasLaw (X i) (μ i) P)
        ∧ iIndepFun X P ∧ IsProbabilityMeasure P := by
  use Π i, (𝓧 i), .pi, infinitePi μ, fun i ↦ Function.eval i
  refine ⟨by fun_prop, fun i ↦ MeasurePreserving.hasLaw (measurePreserving_eval_infinitePi _ _),
    ?_, by infer_instance⟩
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop), map_id']
  congr
  funext i
  exact ((measurePreserving_eval_infinitePi μ i).map_eq).symm

lemma exists_iid (ι : Type v) {𝓧 : Type u} {m𝓧 : MeasurableSpace 𝓧}
    (μ : Measure 𝓧) [IsProbabilityMeasure μ] :
    ∃ Ω : Type (max u v), ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω, ∃ X : ι → Ω → 𝓧,
      (∀ i, Measurable (X i)) ∧ (∀ i, HasLaw (X i) μ P) ∧ iIndepFun X P ∧ IsProbabilityMeasure P :=
  exists_hasLaw_indepFun (fun _ ↦ 𝓧) (fun _ ↦ μ)

end ProbabilityTheory
