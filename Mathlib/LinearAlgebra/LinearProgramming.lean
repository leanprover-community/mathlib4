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

/-- Linear program is a conic program where nonnegativity is defined by the positive orthant. -/
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

theorem ConeProgram.weakDuality (LP : ConeProgram R M N)
    {c : M} (hc : c ∈ LP.primal) {d : N →ₗ[R] R} (hd : d ∈ LP.dual) :
    LP.objective c ≤ d LP.upper := by
  unfold ConeProgram.primal at hc
  unfold ConeProgram.dual at hd
  rw [Set.mem_setOf_eq] at hc hd -- These three lines should probably get replaced by two lemmas.
  obtain ⟨p, hp, hcp⟩ := hc
  obtain ⟨hobj, hd'⟩ := hd
  rw [← hcp, map_add, hobj, Function.comp_apply, le_add_iff_nonneg_right]
  apply hd'
  exact hp

-- From here on, we will probably need `[LinearOrderedField R] [AddCommGroup M] [AddCommGroup N]`

set_option linter.unusedVariables false

/-- Theorem 1.4.1.a, TODO we probably need more assumptions (finite-dimensional `M` and `N` ?) -/
@[nolint unusedArguments]
proof_wanted ConeProgram.strongDuality (LP : ConeProgram R M N)
    (hC : LP.primal.Nonempty) (hD : LP.dual.Nonempty) :
    ∃ c ∈ LP.primal, ∃ d ∈ LP.dual, LP.objective c = d LP.upper

/-- Theorem 1.4.1.b (TODO maybe add item (iii), which is easy,
    and item (iv), which holds when `N` is `ℝ^n` and `LP.cone` is the positive ortant) -/
@[nolint unusedArguments]
proof_wanted ConeProgram.min_max (LP : ConeProgram R M N)
    {c : M} (hc : c ∈ LP.primal) {d : N →ₗ[R] R} (hd : d ∈ LP.dual) (hs : LP.cone.FG) :
    -- TODO maybe `hs` is not needed
    (∀ x ∈ LP.primal, LP.objective x ≤ LP.objective c) ∧ (∀ g ∈ LP.dual, d LP.upper ≤ g LP.upper) ↔
      LP.objective c = d LP.upper

/-- Theorem 1.4.1.c(1) -/
@[nolint unusedArguments]
proof_wanted ConeProgram.empty_dual (LP : ConeProgram R M N)
    (hC : LP.primal.Nonempty) (hD : LP.dual = ∅) :
    ∀ r : R, ∃ d ∈ LP.dual, d LP.upper < r

/-- Theorem 1.4.1.c(2) -/
@[nolint unusedArguments]
proof_wanted ConeProgram.empty_primal (LP : ConeProgram R M N)
    (hC : LP.primal = ∅) (hD : LP.dual.Nonempty) :
    ∀ r : R, ∃ c ∈ LP.primal, r < LP.objective c
