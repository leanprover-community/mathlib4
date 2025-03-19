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

The `PseudoMetricFun` works over any ordered commutative additive monoid,
which allows one to talk about functions mapping into `ℝ`, `ℝ≥0`, `ℝ≥0∞`, etc.
Proving that the pseudometric is nonnegative relies on a linear order,
so the `PseudoMetricFun` is (overly) restricted to require a linear order in the codomain.
The linear order also allows to define the supremum of two pseudometrics.

-/

variable {X R : Type*} [LinearOrderedAddCommMonoid R]

variable (X R) in
/-- A pseudometric as a bundled function. -/
@[ext]
structure PseudoMetricFun where
  /-- The underlying binary function mapping into a linearly ordered additive monoid. -/
  toFun : X → X → R
  /-- A pseudometric must take identical elements to 0. -/
  refl' x : toFun x x = 0
  /-- A pseudometric must be symmetric. -/
  symm' x y : toFun x y = toFun y x
  /-- A pseudometric must respect the triangle inequality. -/
  triangle' x y z : toFun x z ≤ toFun x y + toFun y z

namespace PseudoMetricFun

instance : FunLike (PseudoMetricFun X R) X (X → R) where
  coe := PseudoMetricFun.toFun
  coe_injective' := by
    intro a
    aesop

variable (d : PseudoMetricFun X R)

@[simp]
lemma mk_apply (d : X → X → R) (refl symm triangle) (x y : X) :
    PseudoMetricFun.mk d refl symm triangle x y = d x y :=
  rfl

@[simp]
protected lemma refl (x : X) : d x x = 0 := d.refl' x
protected lemma symm (x y : X) : d x y = d y x := d.symm' x y
protected lemma triangle (x y z : X) : d x z ≤ d x y + d y z := d.triangle' x y z

instance : LE (PseudoMetricFun X R) := ⟨fun d d' ↦ ∀ x y, d x y ≤ d' x y⟩

@[simp]
protected lemma le_iff_coe_le_coe (d d' : PseudoMetricFun X R) :
    d ≤ d' ↔ (d : X → X → R) ≤ d' :=
  Iff.rfl

instance : PartialOrder (PseudoMetricFun X R) where
  le_refl := by simp
  le_trans f _ _ := le_trans (a := ⇑f)
  le_antisymm f g := by simpa [PseudoMetricFun.ext_iff] using le_antisymm

/-- The trivial pseudometric sends everything to 0. -/
protected def bot : PseudoMetricFun X R where
  toFun := 0
  refl' _ := rfl
  symm' _ _ := rfl
  triangle' _ _ _ := by simp

instance : Bot (PseudoMetricFun X R) where
  bot := PseudoMetricFun.bot

@[simp]
protected lemma bot_eq_bot : PseudoMetricFun.bot (X := X) (R := R) = ⊥ := rfl

@[simp]
protected lemma bot_apply (x y : X) :
    (⊥ : PseudoMetricFun X R) x y = 0 :=
  rfl

/-- The supremum of two pseudometrics `f` `g` is the pseudometric that maps to the sup of the values
of `f x y` and `g x y`. -/
protected def sup (d' : PseudoMetricFun X R) : PseudoMetricFun X R where
  toFun := fun x y ↦ (d x y) ⊔ (d' x y)
  refl' _ := by simp
  symm' x y := by simp [d.symm, d'.symm]
  triangle' := by
    intro x y z
    simp only [sup_le_iff]
    refine ⟨(d.triangle x y z).trans ?_, (d'.triangle x y z).trans ?_⟩ <;>
    apply add_le_add <;> simp

instance : Max (PseudoMetricFun X R) where
  max := PseudoMetricFun.sup

@[simp]
protected lemma sup_eq_sup (d' : PseudoMetricFun X R) :
    (d.sup d') = d ⊔ d' := rfl

@[simp]
protected lemma sup_apply (d' : PseudoMetricFun X R) (x y : X) :
    (d ⊔ d') x y = (d x y) ⊔ (d' x y) := rfl

instance : SemilatticeSup (PseudoMetricFun X R) where
  sup := max
  le_sup_left := by simp [Pi.le_def]
  le_sup_right := by simp [Pi.le_def]
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

instance : OrderBot (PseudoMetricFun X R) where
  bot_le f _ _ := f.nonneg _ _

lemma finset_sup_apply {Y : Type*} {f : Y → PseudoMetricFun X R}
    {s : Finset Y} (hs : s.Nonempty) (x y : X) :
    (s.sup f) x y = s.sup' hs fun i ↦ (f i) x y := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i => simp
  | cons a s ha hs ih => simp [hs, ih]

end OrderBot

section IsTriangleMax

/-- A pseudometric can be nonarchimedean (or ultrametric), with a stronger triangle
inequality such that `d x z ≤ max (d x y) (d y z)`. -/
def IsTriangleMax (d : PseudoMetricFun X R) : Prop :=
  ∀ x y z, d x z ≤ d x y ⊔ d y z

lemma isTriangleMax_bot : IsTriangleMax (⊥ : PseudoMetricFun X R) := by
  simp [IsTriangleMax]

lemma isTriangleMax_sup {d d' : PseudoMetricFun X R} (hd : IsTriangleMax d)
    (hd' : IsTriangleMax d') : IsTriangleMax (d ⊔ d') := by
  intro x y z
  simp only [PseudoMetricFun.sup_apply]
  calc d x z ⊔ d' x z ≤ d x y ⊔ d y z ⊔ (d' x y ⊔ d' y z) := sup_le_sup (hd x y z) (hd' x y z)
  _ ≤ d x y ⊔ d' x y ⊔ (d y z ⊔ d' y z) := by simp [sup_comm, sup_assoc, sup_left_comm]

lemma isTriangleMax_finset_sup {Y : Type*} [AddLeftStrictMono R] {f : Y → PseudoMetricFun X R}
    {s : Finset Y} (h : ∀ d ∈ s, IsTriangleMax (f d)) :
    IsTriangleMax (s.sup f) := by
  intro x y z
  rcases s.eq_empty_or_nonempty with rfl|hs
  · simp
  simp_rw [finset_sup_apply hs]
  apply Finset.sup'_le
  simp only [le_sup_iff, Finset.le_sup'_iff]
  intro i hi
  specialize h i hi x y z
  simp only [le_sup_iff] at h
  refine h.imp ?_ ?_ <;>
  intro H <;>
  exact ⟨i, hi, H⟩

end IsTriangleMax

section ball

lemma isSymmetricRel_ball (ε : R) :
    IsSymmetricRel {xy | d xy.1 xy.2 < ε} := by
  simp [IsSymmetricRel, d.symm]

lemma isTransitiveRel_ball_of_isTriangleMax {d : PseudoMetricFun X R} (ε : R)
    (h : d.IsTriangleMax) :
    IsTransitiveRel {xy | d xy.1 xy.2 < ε} :=
  fun x y z hxy hyz ↦ (h x y z).trans_lt (max_lt hxy hyz)

end ball

end PseudoMetricFun
