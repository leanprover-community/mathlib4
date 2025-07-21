/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.ProductMeasure

/-!
# Random variables are independent iff their joint distribution is the product measure.

There are several possible measurability assumptions:
* The map `ω ↦ (Xᵢ(ω))ᵢ` is measurable.
* For all `i`, the map `ω ↦ Xᵢ(ω)` is measurable.
* The map `ω ↦ (Xᵢ(ω))ᵢ` is almost everywhere measurable.
* For all `i`, the map `ω ↦ Xᵢ(ω)` is almost everywhere measurable.
Although the first two options are equivalent, the last two are not if the index set is not
countable. Therefore we first prove the third case `iIndepFun_iff_map_fun_eq_infinitePi_map₀`,
then deduce the fourth case in `iIndepFun_iff_map_fun_eq_infinitePi_map₀'` (assuming the index
type is countable), and we prove the first case in `iIndepFun_iff_map_fun_eq_infinitePi_map`.
-/

open MeasureTheory Measure ProbabilityTheory

namespace ProbabilityTheory

variable {ι Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {𝓧 : ι → Type*} {m𝓧 : ∀ i, MeasurableSpace (𝓧 i)} {X : Π i, Ω → 𝓧 i}

/-- Random variables are independent iff their joint distribution is the product measure. This
is a version where the random variable `ω ↦ (Xᵢ(ω))ᵢ` is almost everywhere measurable.
See `iIndepFun_iff_map_fun_eq_infinitePi_map₀'` for a version which only assumes that
each `Xᵢ` is almost everywhere measurable and that `ι` is countable. -/
lemma iIndepFun_iff_map_fun_eq_infinitePi_map₀ (mX : AEMeasurable (fun ω i ↦ X i ω) μ) :
    haveI _ i := isProbabilityMeasure_map (mX.eval i)
    iIndepFun X μ ↔ μ.map (fun ω i ↦ X i ω) = infinitePi (fun i ↦ μ.map (X i)) where
  mp h := by
    have _ i := isProbabilityMeasure_map (mX.eval i)
    refine eq_infinitePi _ fun s t ht ↦ ?_
    rw [iIndepFun_iff_finset] at h
    have : s.toSet.pi t = s.restrict ⁻¹' (Set.univ.pi fun i ↦ t i) := by ext; simp
    rw [this, ← map_apply, AEMeasurable.map_map_of_aemeasurable]
    · have : s.restrict ∘ (fun ω i ↦ X i ω) = fun ω i ↦ s.restrict X i ω := by ext; simp
      rw [this, (iIndepFun_iff_map_fun_eq_pi_map ?_).1 (h s), pi_pi]
      · simp only [Finset.restrict]
        rw [s.prod_coe_sort fun i ↦ μ.map (X i) (t i)]
      exact fun i ↦ mX.eval i
    any_goals fun_prop
    · exact mX
    · exact .univ_pi fun i ↦ ht i i.2
  mpr h := by
    rw [iIndepFun_iff_finset]
    intro s
    rw [iIndepFun_iff_map_fun_eq_pi_map]
    · have : s.restrict ∘ (fun ω i ↦ X i ω) = fun ω i ↦ s.restrict X i ω := by ext; simp
      rw [← this, ← AEMeasurable.map_map_of_aemeasurable, h, infinitePi_map_restrict]
      · simp
      · fun_prop
      exact mX
    exact fun i ↦ mX.eval i

/-- Random variables are independent iff their joint distribution is the product measure. This is
an `AEMeasurable` version of `iIndepFun_iff_map_fun_eq_infinitePi_map`, which is why it requires
`ι` to be countable. -/
lemma iIndepFun_iff_map_fun_eq_infinitePi_map₀' [Countable ι] (mX : ∀ i, AEMeasurable (X i) μ) :
    haveI _ i := isProbabilityMeasure_map (mX i)
    iIndepFun X μ ↔ μ.map (fun ω i ↦ X i ω) = infinitePi (fun i ↦ μ.map (X i)) :=
  iIndepFun_iff_map_fun_eq_infinitePi_map₀ <| aemeasurable_pi_iff.2 mX

/-- Random variables are independent iff their joint distribution is the product measure. -/
lemma iIndepFun_iff_map_fun_eq_infinitePi_map (mX : ∀ i, Measurable (X i)) :
    haveI _ i := isProbabilityMeasure_map (μ := μ) (mX i).aemeasurable
    iIndepFun X μ ↔ μ.map (fun ω i ↦ X i ω) = infinitePi (fun i ↦ μ.map (X i)) :=
  iIndepFun_iff_map_fun_eq_infinitePi_map₀ <| measurable_pi_iff.2 mX |>.aemeasurable

variable {Ω : ι → Type*} {mΩ : ∀ i, MeasurableSpace (Ω i)}
    {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)] {X : (i : ι) → Ω i → 𝓧 i}

/-- Given random variables `X i : Ω i → 𝓧 i`, they are independent when viewed as random
variables defined on the product space `Π i, Ω i`. -/
lemma iIndepFun_infinitePi (mX : ∀ i, Measurable (X i)) :
    iIndepFun (fun i ω ↦ X i (ω i)) (infinitePi μ) := by
  refine iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop) |>.2 ?_
  rw [infinitePi_map_pi _ mX]
  congr
  ext i : 1
  rw [← (measurePreserving_eval_infinitePi μ i).map_eq, map_map (mX i) (by fun_prop)]
  rfl

end ProbabilityTheory
