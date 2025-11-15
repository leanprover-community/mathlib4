import Mathlib.Tactic.DataSynth.Elab
import Mathlib.Tactic.DataSynth.Attr

import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib

open Set

variable {α : Type*} [MetricSpace α]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

@[data_synth out center radius]
def HasBoundingBall (s : Set α) (center : α) (radius : ℝ) : Prop :=
  s ⊆ Metric.closedBall center radius

@[data_synth]
theorem hasBoundingBall_Icc (a b : ℝ) :
    HasBoundingBall (Icc a b) ((a+b)/2) (|b-a|/2) := sorry

@[data_synth]
theorem hasBoundingBall_union (s₁ s₂ : Set X) {c₁ r₁ c₂ r₂}
    (hs₁ : HasBoundingBall s₁ c₁ r₁) (hs₂ : HasBoundingBall s₂ c₂ r₂) :
    HasBoundingBall (s₁ ∪ s₂)
      (let d := ‖c₁ - c₂‖
       if d + min r₁ r₂ ≤ max r₁ r₂ then
         if r₁ ≤ r₂ then c₂ else c₁
       else
         let w := (1+(r₁-r₂)/d)/2
         (w•c₁+(1-w)•c₂))
      (let d := ‖c₁ - c₂‖
       if d + min r₁ r₂ ≤ max r₁ r₂ then
         if r₁ ≤ r₂ then r₂ else r₁
       else
         (d+r₁+r₂)/2) := sorry

set_option pp.proofs false

#check
 (by data_synth (disch:=skip) (norm:=norm_num) :
  HasBoundingBall (Icc (-1:ℝ) (2:ℝ) ∪ Icc 5 6) _ _)
