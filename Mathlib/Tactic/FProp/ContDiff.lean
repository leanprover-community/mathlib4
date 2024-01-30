/-
Copyright (c) 2024 Tomáš Skřivan All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomáš Skřivan
-/
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv


import Mathlib.Tactic.FProp
import Mathlib.Tactic.FProp.Continuous
import Mathlib.Tactic.FProp.Differentiable

section Missing

section lambda_rules

variable {K : Type*} [NontriviallyNormedField K]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace K E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace K F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace K G]
variable {G' : Type*} [NormedAddCommGroup G'] [NormedSpace K G']
variable {f f₀ f₁ g : E → F} {x} {s t} {n}

theorem contDiff_id' : ContDiff K n (fun x : E => x) := contDiff_id

theorem contDiffAt_id' : ContDiffAt K n (fun x : E => x) x := contDiffAt_id

theorem contDiffOn_id' : ContDiffOn K n (fun x : E => x) s :=
  contDiff_id.contDiffOn

theorem ContDiff.comp' {g : F → G} (hg : ContDiff K n g) (hf : ContDiff K n f) :
    ContDiff K n (fun x => g (f x)) := ContDiff.comp hg hf

theorem ContDiffAt.comp' {f : E → F} {g : F → G} (hg : ContDiffAt K n g (f x))
    (hf : ContDiffAt K n f x) : ContDiffAt K n (fun x => g (f x)) x := ContDiffAt.comp x hg hf

-- theorem ContDiffOn.comp'' {g : F → G} {t : Set F} (hg : ContDiffOn K n g t)
--     (hf : ContDiffOn K n f s) (st : Set.MapsTo f s t) : ContDiffOn K n (fun x => g (f x)) s :=

variable {ι ι' : Type*} [Fintype ι] [Fintype ι'] {F' : ι → Type*} [∀ i, NormedAddCommGroup (F' i)]
  [∀ i, NormedSpace K (F' i)] {φ : ∀ i, E → F' i} {Φ : E → ∀ i, F' i}

theorem contDiff_pi' (hΦ : ∀ i, ContDiff K n fun x => Φ x i) : ContDiff K n Φ :=
  contDiff_pi.2 hΦ

theorem contDiffOn_pi' (hΦ : ∀ i, ContDiffOn K n (fun x => Φ x i) s) : ContDiffOn K n Φ s :=
  contDiffOn_pi.2 hΦ

theorem contDiffAt_pi' (hΦ : ∀ i, ContDiffAt K n (fun x => Φ x i) x) : ContDiffAt K n Φ x :=
  contDiffAt_pi.2 hΦ

end lambda_rules

section div

variable {K : Type*} [NontriviallyNormedField K]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace K E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace K F]
variable {f f₀ f₁ g : E → F} {x} {s t} {n}

theorem ContDiffOn.div' [CompleteSpace K] {f g : E → K} {n} (hf : ContDiffOn K n f s)
    (hg : ContDiffOn K n g s) (h₀ : ∀ x ∈ s, g x ≠ 0) : ContDiffOn K n (fun x => f x / g x) s :=
  ContDiffOn.div hf hg h₀


end div


section deriv

variable {K : Type*} [NontriviallyNormedField K]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace K E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace K F]

/-- Original version `ContDiff.differentiable_iteratedDeriv` introduces a new variable `(n:ℕ∞)`
and `fprop` can't work with such theorem. The theorem should be state where `n` is explicitely
the smallest possible value i.e. `n=m+1`.

In conjunction with `ContDiff.of_le` we can recover the full power of the original theorem.  -/
theorem ContDiff.differentiable_iteratedDeriv' {m : ℕ} {f : K → F}
    (hf : ContDiff K (m+1) f) : Differentiable K (iteratedDeriv m f) :=
  ContDiff.differentiable_iteratedDeriv m hf (Nat.cast_lt.mpr m.lt_succ_self)

end deriv

end Missing


-- mark definition
attribute [fprop]
  ContDiff
  ContDiffAt
  ContDiffOn


-- lambda rules
attribute [fprop]
  contDiff_id'
  contDiff_const
  ContDiff.comp'
  contDiff_apply
  contDiff_pi'

  contDiffAt_id'
  contDiffAt_const
  ContDiffAt.comp'
  -- contDiffAt_apply -- missing
  contDiffAt_pi'

  contDiffOn_id'
  contDiffOn_const
  ContDiffOn.comp'
  -- contDiffOn_apply -- missing
  contDiffOn_pi'

-- product
attribute [fprop]
  ContDiff.prod
  ContDiff.fst
  ContDiff.snd

  ContDiffAt.prod
  ContDiffAt.fst
  ContDiffAt.snd

  ContDiffOn.prod
  ContDiffOn.fst
  ContDiffOn.snd

-- transitions
attribute [fprop]
  ContDiff.contDiffAt
  ContDiff.contDiffOn
  ContDiffAt.differentiableAt
  ContDiffOn.differentiableOn
  ContDiffAt.continuousAt
  ContDiffOn.continuousOn
  ContDiff.of_le

-- algebra
attribute [fprop]
  ContDiff.add
  ContDiff.sub
  ContDiff.neg
  ContDiff.mul
  ContDiff.smul
  ContDiff.div
  ContDiff.inv

  ContDiffAt.add
  ContDiffAt.sub
  ContDiffAt.neg
  ContDiffAt.mul
  ContDiffAt.smul
  ContDiffAt.div
  ContDiffAt.inv

  ContDiffOn.add
  ContDiffOn.sub
  ContDiffOn.neg
  ContDiffOn.mul
  ContDiffOn.smul
  ContDiffOn.div'
  ContDiffOn.inv


-- special function
attribute [fprop]
  ContDiff.exp
  ContDiff.log
  ContDiff.pow

  ContDiffAt.exp
  ContDiffAt.log
  ContDiffAt.pow

  ContDiffOn.exp
  ContDiffOn.log
  ContDiffOn.pow

  ContDiff.differentiable_iteratedDeriv'

example {n} : ContDiffOn ℝ n (fun x => x * (Real.log x) ^ 2 - Real.exp x / x) {0}ᶜ :=
  by fprop (disch:=aesop)

example {n} (y : ℝ) (hy : y≠0) :
    ContDiffAt ℝ n (fun x => x * (Real.log x) ^ 2 - Real.exp x / x) y :=
  by fprop (disch:=aesop)

private noncomputable def S (a b c d : ℝ) : ℝ :=
    a / (a + b + d) + b / (a + b + c) +
    c / (b + c + d) + d / (a + c + d)

private noncomputable def T (t : ℝ) : ℝ := S 1 (1 - t) t (t * (1 - t))

example {n}: ContDiffOn ℝ n T (Set.Icc 0 1) := by
  unfold T S
  fprop (disch:=(rintro x ⟨a,b⟩; nlinarith))

private axiom t1 : (5: ℕ) + (1 : ℕ∞) ≤ (12 : ℕ∞)

example {f : ℝ → ℝ} (hf : ContDiff ℝ 12 f) :
    Differentiable ℝ (iteratedDeriv 5 (fun x => f (2*(f (x + x))) + x)) :=
  by fprop (disch:=(exact t1))
