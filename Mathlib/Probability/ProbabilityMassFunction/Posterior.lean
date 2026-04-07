/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Mathlib.Probability.ProbabilityMassFunction.Monad

/-!
# Joint and Posterior Distributions for Probability Mass Functions

Given a prior `p : PMF α` and a family of distributions `f : α → PMF β`,
this file defines:

* The **joint** distribution on `α × β`, where `a` is sampled from `p` and then
  `b` is sampled from `f a`.
* The **posterior** distribution on `α` conditioned on an observed value `b : β`.

## Main definitions

* `PMF.joint`: The joint distribution on `α × β` induced by a prior and a Markov kernel.
* `PMF.posterior`: The posterior distribution `Pr[A = a | B = b]`.

## Main results

* `PMF.joint_apply`: `(p.joint f) (a, b) = p a * f a b`.
* `PMF.tsum_joint_fst`: Marginalizing over the first component gives `(p.bind f) b`.
* `PMF.posterior_hasSum`: Posterior probabilities sum to 1.
-/

@[expose] public section

noncomputable section

variable {α β : Type*}

open ENNReal

namespace PMF

section Joint

/-- The joint distribution on `α × β` induced by a prior `p : PMF α` and a family of
distributions `f : α → PMF β`. Sampling from `p.joint f` is equivalent to first sampling
`a ← p` and then `b ← f a`, returning `(a, b)`. -/
def joint (p : PMF α) (f : α → PMF β) : PMF (α × β) :=
  p.bind fun a => (f a).bind fun b => pure (a, b)

@[simp]
theorem joint_apply (p : PMF α) (f : α → PMF β) (a : α) (b : β) :
    (p.joint f) (a, b) = p a * f a b := by
  simp only [joint, bind_apply, pure_apply, Prod.mk.injEq]
  rw [tsum_eq_single a]
  · congr 1; rw [tsum_eq_single b]
    · simp
    · intro b' hb'; simp [hb'.symm]
  · intro a' ha'; simp [ha'.symm]

theorem tsum_joint_fst (p : PMF α) (f : α → PMF β) (b : β) :
    ∑' a, (p.joint f) (a, b) = (p.bind f) b := by
  simp [bind_apply]

end Joint

section Posterior

/-- Posterior probabilities `joint(a, b) / marginal(b)` sum to 1
when `b` is in the support of the marginal. -/
theorem posterior_hasSum (p : PMF α) (f : α → PMF β) (b : β)
    (hb : b ∈ (p.bind f).support) :
    HasSum (fun a => (p.joint f) (a, b) / (p.bind f) b) 1 := by
  have hne := (mem_support_iff _ _).mp hb
  have hne_top := (p.bind f).apply_ne_top b
  have h : ∑' a, (p.joint f) (a, b) / (p.bind f) b = 1 := by
    simp only [div_eq_mul_inv]
    rw [ENNReal.tsum_mul_right, tsum_joint_fst]
    exact ENNReal.mul_inv_cancel hne hne_top
  exact h ▸ ENNReal.summable.hasSum

/-- The posterior distribution `Pr[A = a | B = b]` as a `PMF`,
given a prior `p`, a family of distributions `f`, and that `b` has positive marginal
probability under `p.bind f`. -/
def posterior (p : PMF α) (f : α → PMF β) (b : β)
    (hb : b ∈ (p.bind f).support) : PMF α :=
  ⟨fun a => (p.joint f) (a, b) / (p.bind f) b, posterior_hasSum p f b hb⟩

@[simp]
theorem posterior_apply (p : PMF α) (f : α → PMF β) (b : β)
    (hb : b ∈ (p.bind f).support) (a : α) :
    (p.posterior f b hb) a = (p.joint f) (a, b) / (p.bind f) b :=
  rfl

end Posterior

end PMF
