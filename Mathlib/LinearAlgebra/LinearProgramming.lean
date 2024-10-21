/-
Copyright (c) 2023 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak, Antoine Chambert-Loir
-/
import Mathlib.Analysis.Convex.Cone.Pointed
import Mathlib.Algebra.Order.Group.Defs

/-!

# Linear programming

TODO

-/

/-- Typically `M` is `ℝ^m` and `N` is `ℝ^n` -/
structure ConeProgram (R V W M N : Type*) [OrderedRing R]
    [AddCommGroup V] [Module R V] [AddTorsor V M]
    [AddCommGroup W] [Module R W] [AddTorsor W N]
    where
  /-- Linear map -/
  linmap : M →ᵃ[R] N
  /-- Right-hand side -/
  upper : N
  /-- Objective function -/
  objective : M →ᵃ[R] R
  /-- Cone defines nonnegative elements -/
  cone : PointedCone R W

abbrev LinearProgram {R V W M N : Type*} [OrderedRing R]
    [AddCommGroup V] [Module R V] [AddTorsor V M]
    [OrderedAddCommGroup W] [Module R W] [OrderedSMul R W] [AddTorsor W N]
    (l : M →ᵃ[R] N) (u : N) (o : M →ᵃ[R] R) :=
  ConeProgram.mk l u o (PointedCone.positive R W)

variable {R V W M N : Type*} [OrderedRing R]
    [AddCommGroup V] [Module R V] [AddTorsor V M]
    [AddCommGroup W] [Module R W] [AddTorsor W N]

/-- `LP.primal = { x : M | LP.linmap x ≤ LP.upper }` -/
def ConeProgram.primal (LP : ConeProgram R V W M N) :=
  { x : M | LP.upper -ᵥ LP.linmap x ∈ LP.cone }

/-- `LP.dual = { g : N →ᵃ[R] R | LP.objective = g ∘ LP.linmap ∧ ∀ a, ∀ b, a ≤ b → g a ≤ g b }` -/
def ConeProgram.dual (LP : ConeProgram R V W M N) :=
  { g : N →ᵃ[R] R | LP.objective = g ∘ LP.linmap ∧
      ∀ a : N, ∀ b : N, (b -ᵥ a) ∈ LP.cone → g a ≤ g b }

-- From here on, we will need more assumptions than currently written

theorem ConeProgram.weakDuality (LP : ConeProgram R V W M N)
    {c : M} (hc : c ∈ LP.primal) {d : N →ᵃ[R] R} (hd : d ∈ LP.dual) :
    LP.objective c ≤ d LP.upper := by
  simp_all [ConeProgram.primal, ConeProgram.dual]

/-- Theorem 1.4.1.a, TODO we probably need more assumptions (finite-dimensional `M` and `N` ?) -/
theorem ConeProgram.strongDuality (LP : ConeProgram R V W M N)
    (hC : LP.primal.Nonempty) (hD : LP.dual.Nonempty) :
    ∃ c ∈ LP.primal, ∃ d ∈ LP.dual, LP.objective c = d LP.upper :=
  sorry

/-- Theorem 1.4.1.b (TODO maybe add item (iii), which is easy,
    and item (iv), which holds when `N` is `ℝ^n` and `LP.cone` is the positive ortant) -/
theorem ConeProgram.min_max (LP : ConeProgram R V W M N)
    {c : M} (hc : c ∈ LP.primal) {d : N →ᵃ[R] R} (hd : d ∈ LP.dual) (hs : LP.cone.FG) :
    -- TODO maybe `hs` is not needed
    (∀ x ∈ LP.primal, LP.objective x ≤ LP.objective c) ∧ (∀ g ∈ LP.dual, d LP.upper ≤ g LP.upper) ↔
      LP.objective c = d LP.upper :=
  sorry

/-- Theorem 1.4.1.c(1) -/
theorem ConeProgram.empty_dual (LP : ConeProgram R V W M N)
    (hC : LP.primal.Nonempty) (hD : LP.dual = ∅) :
    ∀ r : R, ∃ d ∈ LP.dual, d LP.upper < r :=
  sorry

/-- Theorem 1.4.1.c(2) -/
theorem ConeProgram.empty_primal (LP : ConeProgram R V W M N)
    (hC : LP.primal = ∅) (hD : LP.dual.Nonempty) :
    ∀ r : R, ∃ c ∈ LP.primal, r < LP.objective c :=
  sorry
