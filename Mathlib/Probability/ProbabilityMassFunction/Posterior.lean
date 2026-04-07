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

end Joint

end PMF
