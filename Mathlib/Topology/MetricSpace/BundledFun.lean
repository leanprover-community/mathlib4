/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Topology.UniformSpace.Ultra.Basic

/-!
# Pseudometrics as bundled functions

This file defines a pseudometric as a bundled function.
This allows one to define a semilattice on them, and to construct families of pseudometrics.

## Implementation notes

The `PseudoMetric` definition works over any ordered commutative additive monoid,
which allows one to talk about functions mapping into `ℝ`, `ℝ≥0`, `ℝ≥0∞`, etc.
Proving that the pseudometric is nonnegative relies on a linear order,
so the `PseudoMetric` is (overly) restricted to require a linear order in the codomain.
The linear order also allows to define the supremum of two pseudometrics.

-/

variable {X R : Type*} [LinearOrderedAddCommMonoid R]

variable (X R) in
/-- A pseudometric as a bundled function. -/
@[ext]
structure PseudoMetric where
  /-- The underlying binary function mapping into a linearly ordered additive monoid. -/
  toFun : X → X → R
  /-- A pseudometric must take identical elements to 0. -/
  refl' x : toFun x x = 0
  /-- A pseudometric must be symmetric. -/
  symm' x y : toFun x y = toFun y x
  /-- A pseudometric must respect the triangle inequality. -/
  triangle' x y z : toFun x z ≤ toFun x y + toFun y z

namespace PseudoMetric

instance : FunLike (PseudoMetric X R) X (X → R) where
  coe := PseudoMetric.toFun
  coe_injective' _ := by aesop

variable (d : PseudoMetric X R)

@[simp, norm_cast]
lemma coe_mk (d : X → X → R) (refl symm triangle) : mk d refl symm triangle = d := rfl

lemma mk_apply (d : X → X → R) (refl symm triangle) (x y : X) :
    mk d refl symm triangle x y = d x y :=
  rfl

@[simp]
protected lemma refl (x : X) : d x x = 0 := d.refl' x
protected lemma symm (x y : X) : d x y = d y x := d.symm' x y
protected lemma triangle (x y z : X) : d x z ≤ d x y + d y z := d.triangle' x y z

instance : LE (PseudoMetric X R) := ⟨fun d d' ↦ ⇑d ≤ d'⟩

@[simp, norm_cast]
protected lemma coe_le_coe_iff_le {d d' : PseudoMetric X R} :
    (d : X → X → R) ≤ d' ↔ d ≤ d'  :=
  Iff.rfl

instance : PartialOrder (PseudoMetric X R) where
  le_refl := by simp [← PseudoMetric.coe_le_coe_iff_le]
  le_trans f _ _ := le_trans (a := ⇑f)
  le_antisymm f g := by simpa [← PseudoMetric.coe_le_coe_iff_le, PseudoMetric.ext_iff]
    using le_antisymm

instance : Bot (PseudoMetric X R) where
  bot.toFun := 0
  bot.refl' _ := rfl
  bot.symm' _ _ := rfl
  bot.triangle' _ _ _ := by simp

@[simp, norm_cast]
lemma coe_bot : ⇑(⊥ : PseudoMetric X R) = 0 := rfl

@[simp]
protected lemma bot_apply (x y : X) :
    (⊥ : PseudoMetric X R) x y = 0 :=
  rfl

instance : Max (PseudoMetric X R) where
  max d d' := {
    toFun := fun x y ↦ (d x y) ⊔ (d' x y)
    refl' _ := by simp
    symm' x y := by simp [d.symm, d'.symm]
    triangle' := by
      intro x y z
      simp only [sup_le_iff]
      refine ⟨(d.triangle x y z).trans ?_, (d'.triangle x y z).trans ?_⟩ <;>
      apply add_le_add <;> simp
  }

@[simp]
protected lemma sup_apply (d' : PseudoMetric X R) (x y : X) :
    (d ⊔ d') x y = (d x y) ⊔ (d' x y) := rfl

instance : SemilatticeSup (PseudoMetric X R) where
  sup := max
  le_sup_left := by simp [← PseudoMetric.coe_le_coe_iff_le, Pi.le_def]
  le_sup_right := by simp [← PseudoMetric.coe_le_coe_iff_le, Pi.le_def]
  sup_le _ _ _ := fun h h' _ _ ↦ sup_le (h _ _) (h' _ _)

section OrderBot

variable [AddLeftStrictMono R]

protected lemma nonneg (x y : X) : 0 ≤ d x y := by
  by_contra! H
  have : d x x < 0 := by
    calc d x x ≤ d x y + d y x := d.triangle' x y x
      _ < 0 + 0 := by refine add_lt_add H (d.symm x y ▸ H)
      _ = 0 := by simp
  exact this.not_le (d.refl' x).ge

instance : OrderBot (PseudoMetric X R) where
  bot_le f _ _ := f.nonneg _ _

lemma finsetSup_apply {Y : Type*} {f : Y → PseudoMetric X R}
    {s : Finset Y} (hs : s.Nonempty) (x y : X) :
    (s.sup f) x y = s.sup' hs fun i ↦ (f i) x y := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i => simp
  | cons a s ha hs ih => simp [hs, ih]

end OrderBot

section IsUltra

/-- A pseudometric can be nonarchimedean (or ultrametric), with a stronger triangle
inequality such that `d x z ≤ max (d x y) (d y z)`. -/
def IsUltra (d : PseudoMetric X R) : Prop :=
  ∀ x y z, d x z ≤ d x y ⊔ d y z

protected lemma IsUltra.bot : IsUltra (⊥ : PseudoMetric X R) := by
  simp [IsUltra]

protected lemma IsUltra.sup {d d' : PseudoMetric X R} (hd : IsUltra d)
    (hd' : IsUltra d') : IsUltra (d ⊔ d') := by
  intro x y z
  simp only [PseudoMetric.sup_apply]
  calc d x z ⊔ d' x z ≤ d x y ⊔ d y z ⊔ (d' x y ⊔ d' y z) := sup_le_sup (hd x y z) (hd' x y z)
  _ ≤ d x y ⊔ d' x y ⊔ (d y z ⊔ d' y z) := by simp [sup_comm, sup_assoc, sup_left_comm]

lemma IsUltra.finsetSup {Y : Type*} [AddLeftStrictMono R] {f : Y → PseudoMetric X R}
    {s : Finset Y} (h : ∀ d ∈ s, IsUltra (f d)) :
    IsUltra (s.sup f) := by
  intro x y z
  rcases s.eq_empty_or_nonempty with rfl|hs
  · simp
  simp_rw [finsetSup_apply hs]
  apply Finset.sup'_le
  simp only [le_sup_iff, Finset.le_sup'_iff]
  intro i hi
  specialize h i hi x y z
  simp only [le_sup_iff] at h
  refine h.imp ?_ ?_ <;>
  intro H <;>
  exact ⟨i, hi, H⟩

end IsUltra

section ball

lemma isSymmetricRel_ball (ε : R) :
    IsSymmetricRel {xy | d xy.1 xy.2 < ε} := by
  simp [IsSymmetricRel, d.symm]

lemma isTransitiveRel_ball_of_isTriangleMax {d : PseudoMetric X R} (ε : R)
    (h : d.IsUltra) :
    IsTransitiveRel {xy | d xy.1 xy.2 < ε} :=
  fun x y z hxy hyz ↦ (h x y z).trans_lt (max_lt hxy hyz)

end ball

end PseudoMetric
