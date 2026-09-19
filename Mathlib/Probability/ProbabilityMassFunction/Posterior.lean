/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Joint and Posterior Distributions for Probability Mass Functions

Given a prior `p : PMF α` and a family of distributions `f : α → PMF β`,
this file defines:

* The **joint** distribution on `α × β`, where `a` is sampled from `p` and then
  `b` is sampled from `f a`.
* The **posterior** distribution on `α` conditioned on an observed value `b : β`.

This is an elementary, combinatorial treatment of discrete Bayesian inference.
For the general measure-theoretic posterior defined via disintegration, see
`ProbabilityTheory.posterior` in `Mathlib.Probability.Kernel.Posterior`.
The two constructions compute the same thing at different levels of generality:
`PMF.posterior` gives the explicit formula `P(A=a | B=b) = P(A=a) · P(B=b|A=a) / P(B=b)`,
while `ProbabilityTheory.posterior` is defined as a conditional kernel and requires
standard Borel spaces and the disintegration theorem.

## Main definitions

* `PMF.joint`: The joint distribution on `α × β` induced by a prior and a family of
  distributions.
* `PMF.posterior`: The posterior distribution `Pr[A = a | B = b]`.

## Main results

* `PMF.joint_apply`: `(p.joint f) (a, b) = p a * f a b`.
* `PMF.tsum_joint_fst`: Marginalizing over the first component gives `(p.bind f) b`.
* `PMF.tsum_joint_snd`: Marginalizing over the second component gives `p a`.
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
  p.bind fun a => (f a).map (Prod.mk a)

variable (p : PMF α) (f : α → PMF β)

@[simp]
theorem joint_apply (a : α) (b : β) :
    (p.joint f) (a, b) = p a * f a b := by
  simp only [joint, bind_apply, map_apply, Prod.mk.injEq]
  rw [tsum_eq_single a (fun a' ha' => by simp [ha'.symm]),
      tsum_eq_single b (fun b' hb' => by simp [hb'.symm])]
  simp

@[simp]
theorem support_joint :
    (p.joint f).support = {ab | ab.1 ∈ p.support ∧ ab.2 ∈ (f ab.1).support} := by
  ext ⟨a, b⟩
  simp [mem_support_iff, mul_eq_zero, not_or]

theorem mem_support_joint_iff (ab : α × β) :
    ab ∈ (p.joint f).support ↔ ab.1 ∈ p.support ∧ ab.2 ∈ (f ab.1).support := by
  simp

theorem tsum_joint_fst (b : β) :
    ∑' a, (p.joint f) (a, b) = (p.bind f) b := by
  simp [bind_apply]

theorem tsum_joint_snd (a : α) :
    ∑' b, (p.joint f) (a, b) = p a := by
  simp [ENNReal.tsum_mul_left]

end Joint

section Posterior

/-- Posterior probabilities `joint(a, b) / marginal(b)` sum to 1
when `b` is in the support of the marginal. -/
theorem posterior_hasSum (p : PMF α) (f : α → PMF β) (b : β)
    (hb : b ∈ (p.bind f).support) :
    HasSum (fun a => (p.joint f) (a, b) / (p.bind f) b) 1 :=
  ENNReal.summable.hasSum_iff.2 <| by
    simp_rw [div_eq_mul_inv, ENNReal.tsum_mul_right, tsum_joint_fst]
    exact ENNReal.mul_inv_cancel ((mem_support_iff _ _).mp hb) ((p.bind f).apply_ne_top b)

/-- The posterior distribution `Pr[A = a | B = b]` as a `PMF`,
given a prior `p`, a family of distributions `f`, and that `b` has positive marginal
probability under `p.bind f`. -/
def posterior (p : PMF α) (f : α → PMF β) (b : β)
    (hb : b ∈ (p.bind f).support) : PMF α :=
  ⟨fun a => (p.joint f) (a, b) / (p.bind f) b, posterior_hasSum p f b hb⟩

variable (p : PMF α) (f : α → PMF β)

@[simp]
theorem posterior_apply (b : β) (hb : b ∈ (p.bind f).support) (a : α) :
    (p.posterior f b hb) a = p a * f a b / (p.bind f) b := by
  change (p.joint f) (a, b) / (p.bind f) b = _; simp

@[simp]
theorem support_posterior (b : β) (hb : b ∈ (p.bind f).support) :
    (p.posterior f b hb).support = {a | a ∈ p.support ∧ b ∈ (f a).support} := by
  ext a
  simp only [mem_support_iff, posterior_apply, Set.mem_setOf_eq, ne_eq,
    ENNReal.div_ne_zero, mul_eq_zero, not_or]
  exact ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, (p.bind f).apply_ne_top b⟩⟩

theorem mem_support_posterior_iff (b : β) (hb : b ∈ (p.bind f).support) (a : α) :
    a ∈ (p.posterior f b hb).support ↔ a ∈ p.support ∧ b ∈ (f a).support := by
  simp

end Posterior

end PMF
