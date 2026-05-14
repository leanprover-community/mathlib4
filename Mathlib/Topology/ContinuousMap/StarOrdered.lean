/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Topology.ContinuousMap.ContinuousMapZero
public import Mathlib.Topology.ContinuousMap.Ordered
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-! # Continuous functions as a star-ordered ring

The type class `ContinuousSqrt` gives a sufficient condition on `R` to make `C(α, R)`
and `C(α, R)₀` into a `StarOrderedRing` for any topological space `α`, thereby providing a means
by which we can ensure `C(α, R)` has this property. This condition is satisfied
by `ℝ≥0`, `ℝ`, and `ℂ`, and the instances can be found in the file
`Mathlib/Topology/ContinuousMap/ContinuousSqrt.lean`.

## Implementation notes

Instead of asking for a well-behaved square root on `{x : R | 0 ≤ x}` in the obvious way, we instead
require that, for every `x y  : R` such that `x ≤ y`, there exist some `s` such that `x + s*s = y`.
This is because we need this type class to work for `ℝ≥0` for the
continuous functional calculus. We could instead assume `[OrderedSub R] [ContinuousSub R]`, but that
would lead to a proliferation of type class assumptions in the general case of the continuous
functional calculus, which we want to avoid because there is *already* a proliferation of type
classes there. At the moment, we only expect this class to be used in that context so this is a
reasonable compromise.

The field `ContinuousSqrt.sqrt` is data, which means that, if we implement an instance of the class
for a generic C⋆-algebra, we'll get a non-defeq diamond for the case `R := ℂ`. This shouldn't really
be a problem since the only purpose is to obtain the instance `StarOrderedRing C(α, R)`, which is a
`Prop`, but we note it for future reference.
-/

public section

/-- A type class encoding the property that there is a continuous square root function on
nonnegative elements. This holds for `ℝ≥0`, `ℝ` and `ℂ` (as well as any C⋆-algebra), and this
allows us to derive an instance of `StarOrderedRing C(α, R)` under appropriate hypotheses.
In order for this to work on `ℝ≥0`, we actually must force our square root function to be defined
on and well-behaved for pairs `x : R × R` with `x.1 ≤ x.2`. -/
class ContinuousSqrt (R : Type*) [LE R] [NonUnitalSemiring R] [TopologicalSpace R] where
  /-- `sqrt (a, b)` returns a value `s` such that `b = a + s * s` when `a ≤ b`. -/
  protected sqrt : R × R → R
  protected continuousOn_sqrt : ContinuousOn sqrt {x | x.1 ≤ x.2}
  protected sqrt_nonneg (x : R × R) : x.1 ≤ x.2 → 0 ≤ sqrt x
  protected sqrt_mul_sqrt (x : R × R) : x.1 ≤ x.2 → x.2 = x.1 + sqrt x * sqrt x

namespace ContinuousMap

variable {α : Type*} [TopologicalSpace α]

set_option backward.isDefEq.respectTransparency false in
instance {R : Type*} [PartialOrder R] [NonUnitalSemiring R] [StarRing R]
    [StarOrderedRing R] [TopologicalSpace R] [ContinuousStar R] [IsTopologicalSemiring R]
    [ContinuousSqrt R] : StarOrderedRing C(α, R) := by
  refine StarOrderedRing.of_le_iff ?_
  intro f g
  constructor
  · rw [ContinuousMap.le_def]
    intro h
    use (mk _ ContinuousSqrt.continuousOn_sqrt.restrict).comp
      ⟨_, map_continuous (f.prodMk g) |>.codRestrict (s := {x | x.1 ≤ x.2}) (by exact h)⟩
    ext x
    simpa [IsSelfAdjoint.star_eq <| .of_nonneg (ContinuousSqrt.sqrt_nonneg (f x, g x) (h x))]
      using ContinuousSqrt.sqrt_mul_sqrt (f x, g x) (h x)
  · rintro ⟨p, rfl⟩
    exact fun x ↦ le_add_of_nonneg_right (star_mul_self_nonneg (p x))

end ContinuousMap

namespace ContinuousMapZero

variable {α : Type*} [TopologicalSpace α] [Zero α]

instance instStarOrderedRing {R : Type*}
    [TopologicalSpace R] [CommSemiring R] [PartialOrder R] [NoZeroDivisors R] [StarRing R]
    [StarOrderedRing R] [IsTopologicalSemiring R] [ContinuousStar R] [StarOrderedRing C(α, R)] :
    StarOrderedRing C(α, R)₀ where
  le_iff f g := by
    constructor
    · rw [le_def, ← ContinuousMap.coe_coe, ← ContinuousMap.coe_coe g, ← ContinuousMap.le_def,
        StarOrderedRing.le_iff]
      rintro ⟨p, hp_mem, hp⟩
      induction hp_mem using AddSubmonoid.closure_induction_left generalizing f g with
      | zero => exact ⟨0, zero_mem _, by ext x; congrm($(hp) x)⟩
      | add_left s s_mem p p_mem hp' =>
        obtain ⟨s, rfl⟩ := s_mem
        simp only at *
        have h₀ : (star s * s + p) 0 = 0 := by simpa using congr($(hp) 0).symm
        rw [← add_assoc] at hp
        have p'₀ : 0 ≤ p 0 := by rw [← StarOrderedRing.nonneg_iff] at p_mem; exact p_mem 0
        have s₉ : (star s * s) 0 = 0 := le_antisymm ((le_add_of_nonneg_right p'₀).trans_eq h₀)
          (star_mul_self_nonneg (s 0))
        have s₀' : s 0 = 0 := by aesop
        let s' : C(α, R)₀ := ⟨s, s₀'⟩
        obtain ⟨p', hp'_mem, rfl⟩ := hp' (f + star s' * s') g hp
        refine ⟨star s' * s' + p', ?_, by rw [add_assoc]⟩
        exact add_mem (AddSubmonoid.subset_closure ⟨s', rfl⟩) hp'_mem
    · rintro ⟨p, hp, rfl⟩
      induction hp using AddSubmonoid.closure_induction generalizing f with
      | mem s s_mem =>
        obtain ⟨s, rfl⟩ := s_mem
        exact fun x ↦ le_add_of_nonneg_right (star_mul_self_nonneg (s x))
      | zero => simp
      | add g₁ g₂ _ _ h₁ h₂ => calc
          f ≤ f + g₁ := h₁ f
          _ ≤ (f + g₁) + g₂ := h₂ (f + g₁)
          _ = f + (g₁ + g₂) := add_assoc _ _ _

end ContinuousMapZero
