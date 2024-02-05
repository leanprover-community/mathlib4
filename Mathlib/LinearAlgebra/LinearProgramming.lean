/-
Copyright (c) 2023 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak, Antoine Chambert-Loir
-/
import Mathlib.Analysis.Convex.Cone.Pointed
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.RingTheory.Finiteness

/-!

# Linear programming

TODO

-/

section LP_general

/-- Typically `M` is `ℝ^m` and `N` is `ℝ^n` -/
structure ConeProgram (R M N : Type*) [OrderedSemiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] where
  /-- Linear map -/
  linmap : M →ₗ[R] N
  /-- Right-hand side -/
  upper : N
  /-- Objective function -/
  objective : M →ₗ[R] R
  /-- Cone defines nonnegative elements -/
  cone : PointedCone R N

abbrev LinearProgram {R M N : Type*} [OrderedSemiring R]
    [AddCommMonoid M] [Module R M] [OrderedAddCommGroup N] [Module R N] [OrderedSMul R N]
    (l : M →ₗ[R] N) (u : N) (o : M →ₗ[R] R) :=
  ConeProgram.mk l u o (PointedCone.positive R N)

variable {R M N : Type*}
  [LinearOrderedSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- `LP.primal = { x : M | LP.linmap x ≤ LP.upper }` -/
def ConeProgram.primal (LP : ConeProgram R M N) :=
  { x : M | ∃ c ∈ LP.cone, LP.linmap x + c = LP.upper }

/-- `LP.dual = { g : N →ₗ[R] R | LP.objective = g ∘ LP.linmap ∧ 0 ≤ g }` -/
def ConeProgram.dual (LP : ConeProgram R M N) :=
  { g : N →ₗ[R] R | LP.objective = g ∘ LP.linmap ∧ ∀ a ∈ LP.cone, 0 ≤ g a }

-- From here on, we will probably need `[LinearOrderedField R] [AddCommGroup M] [AddCommGroup N]`

theorem ConeProgram.weakDuality (LP : ConeProgram R M N)
    {c : M} (hc : c ∈ LP.primal) {d : N →ₗ[R] R} (hd : d ∈ LP.dual) :
    LP.objective c ≤ d LP.upper := by
  unfold ConeProgram.primal at hc
  unfold ConeProgram.dual at hd
  rw [Set.mem_setOf_eq] at hc hd
  obtain ⟨p, hp, hcp⟩ := hc
  obtain ⟨hobj, hd'⟩ := hd
  rw [← hcp, map_add, hobj, Function.comp_apply, le_add_iff_nonneg_right]
  apply hd'
  exact hp

/-- Theorem 1.4.1.a, TODO we probably need more assumptions (finite-dimensional `M` and `N` ?) -/
theorem ConeProgram.strongDuality (LP : ConeProgram R M N)
    (hC : LP.primal.Nonempty) (hD : LP.dual.Nonempty) :
    ∃ c ∈ LP.primal, ∃ d ∈ LP.dual, LP.objective c = d LP.upper :=
  sorry

/-- Theorem 1.4.1.b (TODO maybe add item (iii), which is easy,
    and item (iv), which holds when `N` is `ℝ^n` and `LP.cone` is the positive ortant) -/
theorem ConeProgram.min_max (LP : ConeProgram R M N)
    {c : M} (hc : c ∈ LP.primal) {d : N →ₗ[R] R} (hd : d ∈ LP.dual) (hs : LP.cone.FG) :
    -- TODO maybe `hs` is not needed
    (∀ x ∈ LP.primal, LP.objective x ≤ LP.objective c) ∧ (∀ g ∈ LP.dual, d LP.upper ≤ g LP.upper) ↔
      LP.objective c = d LP.upper :=
  sorry

/-- Theorem 1.4.1.c(1) -/
theorem ConeProgram.empty_dual (LP : ConeProgram R M N)
    (hC : LP.primal.Nonempty) (hD : LP.dual = ∅) :
    ∀ r : R, ∃ d ∈ LP.dual, d LP.upper < r :=
  sorry

/-- Theorem 1.4.1.c(2) -/
theorem ConeProgram.empty_primal (LP : ConeProgram R M N)
    (hC : LP.primal = ∅) (hD : LP.dual.Nonempty) :
    ∀ r : R, ∃ c ∈ LP.primal, r < LP.objective c :=
  sorry

end LP_general

/-
-- If we assume `R = ℝ` and `Module.Finite M` and `Module.Finite N`, we can use something like...

open Set

open Pointwise

variable {𝕜 E : Type*} [TopologicalSpace E] [AddCommGroup E] [TopologicalAddGroup E] [Module ℝ E]
  [ContinuousSMul ℝ E] {cone t : Set E} {x y : E} [LocallyConvexSpace ℝ E]

lemma geometric_hahn_banach_point_closed' (ht₁ : Convex ℝ t) (disj : x ∉ t) :
    ∃ (f : E →L[ℝ] ℝ) (u : ℝ), f x ≤ u ∧ ∀ b ∈ t, u ≤ f b := by
  obtain ⟨f, hf⟩ :=
    geometric_hahn_banach_open_point ht₁.interior isOpen_interior
      (fun h => disj (interior_subset h))
  use (-f)
  use -(f x)
  constructor
  · rfl
  intro b hb
  rw [ContinuousLinearMap.neg_apply, neg_le_neg_iff]
  sorry
-/
