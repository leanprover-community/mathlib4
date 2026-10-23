/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
public import Mathlib.Tactic.CFCPull

/-!
# Lemmas for the `cfc_pull` tactic

This file tags the lemmas used by the `cfc_pull` tactic, which rewrites an expression in a
C⋆-algebra into the form `cfc f a`. See `Mathlib/Tactic/CFCPull.lean` for a description of the
tactic and the two kinds of lemmas it uses.
-/

public section

variable {R A : Type*} {p : A → Prop} [CommSemiring R] [StarRing R] [MetricSpace R]
  [IsTopologicalSemiring R] [ContinuousStar R] [TopologicalSpace A] [Ring A] [StarRing A]
  [Algebra R A] [ContinuousFunctionalCalculus R A p]

lemma cfc_const_ofNat (n : ℕ) [n.AtLeastTwo] (a : A) (ha : p a := by cfc_tac) :
    cfc (fun _ : R ↦ (OfNat.ofNat n : R)) a = OfNat.ofNat n := by
  rw [cfc_const _ a, map_ofNat]

/-! ### Atoms -/

attribute [cfc_pull 2000] cfc_id'
attribute [cfc_pull] cfc_const_one cfc_const_zero cfc_const_ofNat cfc_const

/-! ### Algebraic operations -/

attribute [cfc_pull] cfc_add cfc_sub cfc_mul cfc_neg cfc_pow cfc_star cfc_smul
-- Prefer `fun x ↦ r * f x` to `fun x ↦ r • f x` when the scalar is in `R`.
attribute [cfc_pull 1100] cfc_const_mul

/-! ### Composition and changing the scalar ring -/

attribute [cfc_pull] cfc_comp' cfcₙ_eq_cfc
attribute [cfc_pull ←] cfc_real_eq_complex cfc_nnreal_eq_real
