/-
Copyright (c) 2024 Tomáš Skřivan All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomáš Skřivan
-/
import Mathlib.Topology.Constructions
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Field
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

import Mathlib.Tactic.FProp

/-!
## `fprop` minimal setup for Continuous(At/On)
-/

section Missing

section lambda_rules


variable {α : Type*} {β : Type*} {γ : Type*}
variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
variable {ι : Type*} {π : ι → Type*} {κ : Type*} [TopologicalSpace α]
  [T : ∀ i, TopologicalSpace (π i)] {f : α → ∀ i : ι, π i}

theorem continuousAt_id' (y) : ContinuousAt (fun x : α => x) y := continuousAt_id

theorem continuousOn_id' (s) : ContinuousOn (fun x : α => x) s := continuousOn_id

theorem ContinuousAt.comp' {g : β → γ} {f : α → β} {x : α} (hg : ContinuousAt g (f x))
    (hf : ContinuousAt f x) : ContinuousAt (fun x => g (f x)) x := ContinuousAt.comp hg hf

theorem ContinuousOn.comp'' {g : β → γ} {f : α → β} {s : Set α} {t : Set β} (hg : ContinuousOn g t)
    (hf : ContinuousOn f s) (h : Set.MapsTo f s t) : ContinuousOn (fun x => g (f x)) s :=
  ContinuousOn.comp hg hf h

theorem continuousOn_apply (i : ι) (s) : ContinuousOn (fun p : ∀ i, π i => p i) s :=
  Continuous.continuousOn (continuous_apply i)

theorem continuousAt_pi' {f : α → ∀ i, π i} {x : α} (hf : ∀ i, ContinuousAt (fun y => f y i) x) :
    ContinuousAt f x := continuousAt_pi.2 hf

theorem continuousOn_pi' {f : α → ∀ i, π i} {s : Set α}
    (hf : ∀ i, ContinuousOn (fun y => f y i) s) : ContinuousOn f s := continuousOn_pi.2 hf

end lambda_rules

section div

variable {α β G₀ : Type*} [TopologicalSpace α]
variable [GroupWithZero G₀] [TopologicalSpace G₀] [HasContinuousInv₀ G₀] [ContinuousMul G₀]
  {f g : α → G₀} {a} {s}

theorem Continuous.div₀ (hf : Continuous f) (hg : Continuous g) (h₀ : ∀ x, g x ≠ 0) :
    Continuous (fun x => f x / g x) := by simpa only [div_eq_mul_inv] using hf.mul (hg.inv₀ h₀)

theorem ContinuousAt.div₀ (hf : ContinuousAt f a) (hg : ContinuousAt g a) (h₀ : g a ≠ 0) :
    ContinuousAt (fun x => f x / g x) a := ContinuousAt.div hf hg h₀

theorem ContinuousOn.div₀ (hf : ContinuousOn f s) (hg : ContinuousOn g s) (h₀ : ∀ x ∈ s, g x ≠ 0) :
    ContinuousOn (fun x => f x / g x) s := ContinuousOn.div hf hg h₀


end div

end Missing



-- mark definition
attribute [fprop]
  Continuous
  ContinuousAt
  ContinuousOn


-- lambda rules
attribute [fprop]
  continuous_id'
  continuous_const
  Continuous.comp'
  continuous_apply
  continuous_pi

  continuousAt_id'
  continuousAt_const
  ContinuousAt.comp'
  continuousAt_apply
  continuousAt_pi'

  continuousOn_id'
  continuousOn_const
  ContinuousOn.comp'
  continuousOn_apply
  continuousOn_pi'

-- product
attribute [fprop]
  Continuous.prod_mk
  Continuous.fst
  Continuous.snd

  ContinuousAt.prod
  ContinuousAt.fst
  ContinuousAt.snd

  ContinuousOn.prod
  ContinuousOn.fst
  ContinuousOn.snd

-- transitions
attribute [fprop]
  Continuous.continuousAt
  Continuous.continuousOn

-- algebra
attribute [fprop]
  Continuous.add
  Continuous.sub
  Continuous.neg
  Continuous.mul
  Continuous.smul
  Continuous.div'
  Continuous.div₀
  Continuous.inv
  Continuous.inv₀

  ContinuousAt.add
  ContinuousAt.sub
  ContinuousAt.neg
  ContinuousAt.mul
  ContinuousAt.smul
  ContinuousAt.div'
  ContinuousAt.div₀
  ContinuousAt.inv
  ContinuousAt.inv₀

  ContinuousOn.add
  ContinuousOn.sub
  ContinuousOn.neg
  ContinuousOn.mul
  ContinuousOn.smul
  ContinuousOn.div'
  ContinuousOn.div₀
  ContinuousOn.inv
  ContinuousOn.inv₀


-- special function
attribute [fprop]
  Continuous.exp
  Continuous.log
  Continuous.pow

  ContinuousAt.exp
  ContinuousAt.log
  ContinuousAt.pow

  ContinuousOn.exp
  ContinuousOn.log
  ContinuousOn.pow


example : ContinuousOn (fun x => x * (Real.log x) ^ 2 - Real.exp x / x) {0}ᶜ :=
  by fprop (disch:=aesop)

example (y : ℝ) (hy : y≠0) : ContinuousAt (fun x => x * (Real.log x) ^ 2 - Real.exp x / x) y :=
  by fprop (disch:=aesop)

private noncomputable def S (a b c d : ℝ) : ℝ :=
    a / (a + b + d) + b / (a + b + c) +
    c / (b + c + d) + d / (a + c + d)

private noncomputable def T (t : ℝ) : ℝ := S 1 (1 - t) t (t * (1 - t))

example : ContinuousOn T (Set.Icc 0 1) := by
  unfold T S
  fprop (disch:=(rintro x ⟨a,b⟩; nlinarith))
