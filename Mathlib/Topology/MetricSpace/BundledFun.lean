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

The `PseudoMetric` definition is made as general as possible without any required axioms
for the codomain. The axioms come into play only in proofs and further constructions
like the `SemilatticeSup` instance. This allows one to talk about functions mapping into
something like `{ fuel: ℕ, time: ℕ }` even though there is no linear order.

In most cases, the codomain will be a linear ordered additive monoid like
`ℝ`, `ℝ≥0`, `ℝ≥0∞`, in which all of the axioms below are satisfied.

-/

variable {X R : Type*}

variable (X R) in
/-- A pseudometric as a bundled function. -/
@[ext]
structure PseudoMetric [Zero R] [Add R] [LE R] where
  /-- The underlying binary function mapping into a linearly ordered additive monoid. -/
  toFun : X → X → R
  /-- A pseudometric must take identical elements to 0. -/
  refl' x : toFun x x = 0
  /-- A pseudometric must be symmetric. -/
  symm' x y : toFun x y = toFun y x
  /-- A pseudometric must respect the triangle inequality. -/
  triangle' x y z : toFun x z ≤ toFun x y + toFun y z

namespace PseudoMetric

section Basic

variable [Zero R] [Add R] [LE R] (d : PseudoMetric X R)

instance : FunLike (PseudoMetric X R) X (X → R) where
  coe := PseudoMetric.toFun
  coe_injective' _ := by aesop

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
protected lemma coe_le_coe {d d' : PseudoMetric X R} :
    (d : X → X → R) ≤ d' ↔ d ≤ d' :=
  Iff.rfl

end Basic

instance [Zero R] [Add R] [PartialOrder R] : PartialOrder (PseudoMetric X R) :=
  .lift _ DFunLike.coe_injective

instance [AddZeroClass R] [Preorder R] : Bot (PseudoMetric X R) where
  bot.toFun := 0
  bot.refl' _ := rfl
  bot.symm' _ _ := rfl
  bot.triangle' _ _ _ := by simp

@[simp, norm_cast]
lemma coe_bot [AddZeroClass R] [Preorder R] : ⇑(⊥ : PseudoMetric X R) = 0 := rfl

@[simp]
protected lemma bot_apply [AddZeroClass R] [Preorder R] (x y : X) :
    (⊥ : PseudoMetric X R) x y = 0 :=
  rfl

instance [AddZeroClass R] [SemilatticeSup R] [AddLeftMono R] [AddRightMono R] :
    Max (PseudoMetric X R) where
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

@[simp, push_cast]
lemma coe_sup [AddZeroClass R] [SemilatticeSup R] [AddLeftMono R] [AddRightMono R]
    (d d' : PseudoMetric X R) :
    ((d ⊔ d' : PseudoMetric X R) : X → X → R) = (d : X → X → R) ⊔ d' := rfl

@[simp]
protected lemma sup_apply [AddZeroClass R] [SemilatticeSup R] [AddLeftMono R] [AddRightMono R]
    (d d' : PseudoMetric X R) (x y : X) :
    (d ⊔ d') x y = d x y ⊔ d' x y :=
  rfl

instance [AddZeroClass R] [SemilatticeSup R] [AddLeftMono R] [AddRightMono R] :
    SemilatticeSup (PseudoMetric X R) where
  sup := max
  le_sup_left := by simp [← PseudoMetric.coe_le_coe]
  le_sup_right := by simp [← PseudoMetric.coe_le_coe]
  sup_le _ _ _ := fun h h' _ _ ↦ sup_le (h _ _) (h' _ _)

section OrderBot

variable [AddCommMonoid R] [LinearOrder R] [AddLeftStrictMono R]

protected lemma nonneg (d : PseudoMetric X R) (x y : X) : 0 ≤ d x y := by
  by_contra! H
  have : d x x < 0 := by
    calc d x x ≤ d x y + d y x := d.triangle' x y x
      _ < 0 + 0 := by refine add_lt_add H (d.symm x y ▸ H)
      _ = 0 := by simp
  exact this.ne (d.refl x)

instance : OrderBot (PseudoMetric X R) where
  bot_le f _ _ := f.nonneg _ _

@[simp, push_cast]
lemma coe_finsetSup [IsOrderedAddMonoid R] {Y : Type*} {f : Y → PseudoMetric X R} {s : Finset Y}
    (hs : s.Nonempty) :
    ⇑(s.sup f) = s.sup' hs (f ·) := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i => simp
  | cons a s ha hs ih => funext; simp [hs, ih]

lemma finsetSup_apply [IsOrderedAddMonoid R] {Y : Type*} {f : Y → PseudoMetric X R}
    {s : Finset Y} (hs : s.Nonempty) (x y : X) :
    s.sup f x y = s.sup' hs fun i ↦ f i x y := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i => simp
  | cons a s ha hs ih => simp [hs, ih]

end OrderBot

section IsUltra

/-- A pseudometric can be nonarchimedean (or ultrametric), with a stronger triangle
inequality such that `d x z ≤ max (d x y) (d y z)`. -/
class IsUltra [Zero R] [Add R] [LE R] [Max R] (d : PseudoMetric X R) : Prop where
  /-- Strong triangle inequality of an ultrametric. -/
  le_sup' : ∀ x y z, d x z ≤ d x y ⊔ d y z

lemma IsUltra.le_sup [Zero R] [Add R] [LE R] [Max R] {d : PseudoMetric X R} [hd : IsUltra d]
    {x y z : X} : d x z ≤ d x y ⊔ d y z :=
  hd.le_sup' x y z

instance IsUltra.bot [AddZeroClass R] [SemilatticeSup R] :
    IsUltra (⊥ : PseudoMetric X R) where
  le_sup' := by simp

instance IsUltra.sup [AddZeroClass R] [SemilatticeSup R] [AddLeftMono R] [AddRightMono R]
    {d d' : PseudoMetric X R} [IsUltra d] [IsUltra d'] : IsUltra (d ⊔ d') := by
  constructor
  intro x y z
  simp only [PseudoMetric.sup_apply]
  calc d x z ⊔ d' x z ≤ d x y ⊔ d y z ⊔ (d' x y ⊔ d' y z) := sup_le_sup le_sup le_sup
  _ ≤ d x y ⊔ d' x y ⊔ (d y z ⊔ d' y z) := by simp [sup_comm, sup_left_comm]

lemma IsUltra.finsetSup {Y : Type*} [AddCommMonoid R] [LinearOrder R] [AddLeftStrictMono R]
    [IsOrderedAddMonoid R] {f : Y → PseudoMetric X R} {s : Finset Y} (h : ∀ d ∈ s, IsUltra (f d)) :
    IsUltra (s.sup f) := by
  constructor
  intro x y z
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  simp_rw [finsetSup_apply hs]
  apply Finset.sup'_le
  simp only [le_sup_iff, Finset.le_sup'_iff]
  intro i hi
  have h := (h i hi).le_sup' x y z
  simp only [le_sup_iff] at h
  refine h.imp ?_ ?_ <;>
  intro H <;>
  exact ⟨i, hi, H⟩

end IsUltra

section ball

lemma isSymmetricRel_ball [Add R] [Zero R] [Preorder R] (d : PseudoMetric X R) {ε : R} :
    IsSymmetricRel {xy | d xy.1 xy.2 < ε} := by
  simp [IsSymmetricRel, d.symm]

lemma isSymmetricRel_closedBall [Add R] [Zero R] [LE R] (d : PseudoMetric X R) {ε : R} :
    IsSymmetricRel {xy | d xy.1 xy.2 ≤ ε} := by
  simp [IsSymmetricRel, d.symm]

lemma IsUltra.isTransitiveRel_ball [Add R] [Zero R] [LinearOrder R] (d : PseudoMetric X R)
    [d.IsUltra] {ε : R} :
    IsTransitiveRel {xy | d xy.1 xy.2 < ε} :=
  fun _ _ _ hxy hyz ↦ le_sup.trans_lt (max_lt hxy hyz)

lemma IsUltra.isTransitiveRel_closedBall [Add R] [Zero R] [SemilatticeSup R] (d : PseudoMetric X R)
    [d.IsUltra] {ε : R} :
    IsTransitiveRel {xy | d xy.1 xy.2 ≤ ε} :=
  fun _ _ _ hxy hyz ↦ le_sup.trans (sup_le hxy hyz)

end ball

end PseudoMetric
