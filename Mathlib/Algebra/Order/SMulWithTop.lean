/-
Copyright (c) 2025 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.Algebra.Order.AddTorsor
import Mathlib.Order.WithBot
import Mathlib.Tactic.Set

/-!
# Ordered scalar multiplication and vector addition with top
This file has some lemmas for extending ordered scalar multiplication and vector addition to allow
top elements.

## Implementation
We use a type alias `SMulTop P` for `WithTop P`, because if we made a `SMul (WithTop G) (WithTop P)`
instance given `SMul G P`, we would have two inequivalent `SMul` instances (i.e., a diamond) when
`P = WithTop G`.

## Instances
 * SMul (WithTop G) (SMulTop P)
 * VAdd (WithTop G) (VAddTop P)
 * IsOrderedSMul (WithTop G) (SMulTop P)
 * IsOrderedVAdd (WithTop G) (VAddTop P)
-/

open Function

variable {G P : Type*}

/-- A type alias for WithTop P, for avoiding a `P = WithTop G` diamond. -/
@[to_additive " A type alias for WithTop P, for avoiding a `P = WithTop G` diamond. "]
def SMulTop (P) := WithTop P

/-- The casting function to the type synonym. -/
@[to_additive " The casting function to the type synonym. "]
def SMulTop.of (P)  : WithTop P ≃ SMulTop P :=
  Equiv.refl _

@[to_additive]
instance : Top (SMulTop P) where
  top := SMulTop.of P ⊤

/-- Recursion principle to reduce a result about the synonym to the original type. -/
@[to_additive (attr := elab_as_elim) " Recursion principle to reduce a result about the synonym to
the original type. "]
def SMulTop.rec {motive : SMulTop P → Sort*} (h : ∀ x : WithTop P, motive (of P x)) :
    ∀ x, motive x :=
  fun x => h <| (of P).symm x

@[to_additive (attr := simp)] lemma SMulTop.of_top : of P ⊤ = ⊤ := rfl
@[to_additive (attr := simp)] lemma SMulTop.of_symm_top : (of P).symm ⊤ = ⊤ := rfl

@[to_additive]
instance (priority := 10) [LT P] : LT (SMulTop P) where
  lt a b := LT.lt ((SMulTop.of P).symm a) ((SMulTop.of P).symm b)

@[to_additive]
lemma SMulTop.lt_iff [LT P] {x y : SMulTop P} : x < y ↔ ((of P).symm x) < ((of P).symm y) :=
  gt_iff_lt

@[to_additive]
lemma SMulTop.lt_top_iff_ne_top [LT P] {x : SMulTop P} : x < ⊤ ↔ x ≠ ⊤ := by
  simp only [lt_iff, of_symm_top, ne_eq, WithTop.lt_top_iff_ne_top]
  exact Injective.ne_iff' (fun ⦃a₁ a₂⦄ a ↦ a) rfl

@[to_additive]
instance (priority := 10) [LE P] : LE (SMulTop P) where
  le a b := LE.le ((SMulTop.of P).symm a) ((SMulTop.of P).symm b)

@[to_additive]
lemma SMulTop.le_iff [LE P] {x y : SMulTop P} : x ≤ y ↔ ((of P).symm x) ≤ ((of P).symm y) :=
  ge_iff_le

@[to_additive (attr := simp)]
lemma SMulTop.le_top [LE P] {x : SMulTop P} : x ≤ ⊤ :=
  le_iff.mpr <| of_symm_top ▸ OrderTop.le_top ((of P).symm x)

@[to_additive (attr := simp)]
lemma SMulTop.top_le_iff [LE P] {x : SMulTop P} : ⊤ ≤ x ↔ x = ⊤ := by
  rw [le_iff, of_symm_top, WithTop.top_le_iff, Equiv.symm_apply_eq, of_top]

@[to_additive (attr := simp)]
lemma SMulTop.smultop_ne_coe {p : P} : ⊤ ≠ of P p :=
  nofun

@[to_additive (attr := simp)]
lemma SMulTop.coe_ne_smultop {p : P} : of P p ≠ ⊤ :=
  nofun

@[to_additive]
instance [SMul G P] : SMul (WithTop G) (SMulTop P) :=
  ⟨Option.map₂ (· • ·)⟩

@[to_additive  (attr := simp)]
lemma SMulTop.coe_SMul [SMul G P] (g : G) (p : P) :
    of P ↑(g • p) = (g : WithTop G) • (of P p : SMulTop P) :=
  rfl

variable [SMul G P]  {g : WithTop G} {p : SMulTop P}

@[to_additive (attr := simp)]
lemma SMulTop.top_SMul : (⊤ : WithTop G) • p = ⊤ :=
  rfl

@[to_additive (attr := simp)]
lemma SMulTop.smul_top : g • (⊤ : SMulTop P) = ⊤ := by cases g <;> rfl

@[to_additive (attr := simp)]
lemma SMulTop.smul_eq_top : g • p = ⊤ ↔ g = ⊤ ∨ p = ⊤ :=
  of_top.symm ▸ Option.map₂_eq_none_iff

@[to_additive]
lemma SMulTop.smul_ne_top : g • p ≠ ⊤ ↔ g ≠ ⊤ ∧ p ≠ ⊤ :=
  smul_eq_top.not.trans not_or

@[to_additive]
lemma SMulTop.smul_lt_top [LT G] [LT P] : g • p < ⊤ ↔ g < ⊤ ∧ p < ⊤ := by
  simp_rw [WithTop.lt_top_iff_ne_top, lt_top_iff_ne_top, smul_ne_top]

@[to_additive]
lemma SMulTop.smul_coe_eq_top_iff {p : P} : g • of P p = ⊤ ↔ g = ⊤ := by simp

@[to_additive]
lemma SMulTop.coe_smul_eq_top_iff {g : G} : (g : WithTop G) • p = ⊤ ↔ p = ⊤ := by simp

@[to_additive]
instance [LE G] [LE P] [IsOrderedSMul G P] :
    IsOrderedSMul (WithTop G) (SMulTop P) where
  smul_le_smul_left p p' hpp' g := by
    set q := (SMulTop.of P).symm p with hq
    set q' := (SMulTop.of P).symm p' with hq'
    rw [show p = SMulTop.of P q by exact hq, show p' = SMulTop.of P q' by exact hq']
    have hqq' : q ≤ q' := (propext SMulTop.le_iff).mpr hpp'
    match g, q, q' with
    | ⊤, _, _ => simp
    | (g : G), _, ⊤ => simp
    | (g : G), ⊤, (p' : P) => exact (WithTop.not_top_le_coe p' hqq').elim
    | (g : G), (p : P), (p' : P) =>
      simp only [SMulTop.le_iff, WithTop.coe_le_coe, ← SMulTop.coe_SMul,
        Equiv.symm_apply_apply] at *
      exact IsOrderedSMul.smul_le_smul_left p p' hqq' g
  smul_le_smul_right := fun g g' hgg' p => by
    set q := (SMulTop.of P).symm p with hq
    rw [show p = SMulTop.of P q by exact hq]
    match g, g', q with
    | _, _, ⊤ => simp
    | _, ⊤, (p : P) => simp
    | ⊤, (g' : G), _ => exact (WithTop.not_top_le_coe g' hgg').elim
    | (g : G), (g' : G), (p : P) =>
      simp only [WithTop.coe_le_coe, ← SMulTop.coe_SMul, SMulTop.le_iff,
        Equiv.symm_apply_apply] at *
      exact IsOrderedSMul.smul_le_smul_right g g' hgg' p
