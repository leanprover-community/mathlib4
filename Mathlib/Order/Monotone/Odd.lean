/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Monoid.OrderDual
public import Mathlib.Order.Monotone.Union

/-!
# Monotonicity of odd functions

An odd function on a linear ordered additive commutative group `G` is monotone on the whole group
provided that it is monotone on `Set.Ici 0`, see `monotone_of_odd_of_monotoneOn_nonneg`. We also
prove versions of this lemma for `Antitone`, `StrictMono`, and `StrictAnti`.
-/

public section


open Set

variable {G H : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [AddCommGroup H] [PartialOrder H] [IsOrderedAddMonoid H]

/-- An odd function on a linear ordered additive commutative group is strictly monotone on the whole
group provided that it is strictly monotone on `Set.Ici 0`. -/
theorem strictMono_of_odd_strictMonoOn_nonneg {f : G → H} (h₁ : ∀ x, f (-x) = -f x)
    (h₂ : StrictMonoOn f (Ici 0)) : StrictMono f := by
  refine StrictMonoOn.Iic_union_Ici (fun x hx y hy hxy => neg_lt_neg_iff.1 ?_) h₂
  rw [← h₁, ← h₁]
  exact h₂ (neg_nonneg.2 hy) (neg_nonneg.2 hx) (neg_lt_neg hxy)

/-- An odd function on a linear ordered additive commutative group is strictly antitone on the whole
group provided that it is strictly antitone on `Set.Ici 0`. -/
theorem strictAnti_of_odd_strictAntiOn_nonneg {f : G → H} (h₁ : ∀ x, f (-x) = -f x)
    (h₂ : StrictAntiOn f (Ici 0)) : StrictAnti f := by
  have h : StrictMono (fun x => -f x) :=
    strictMono_of_odd_strictMonoOn_nonneg (fun x => by simp [h₁])
      (fun a ha b hb hab => neg_lt_neg (h₂ ha hb hab))
  exact fun a b hab => neg_lt_neg_iff.mp (h hab)

/-- An odd function on a linear ordered additive commutative group is monotone on the whole group
provided that it is monotone on `Set.Ici 0`. -/
theorem monotone_of_odd_of_monotoneOn_nonneg {f : G → H} (h₁ : ∀ x, f (-x) = -f x)
    (h₂ : MonotoneOn f (Ici 0)) : Monotone f := by
  refine MonotoneOn.Iic_union_Ici (fun x hx y hy hxy => neg_le_neg_iff.1 ?_) h₂
  rw [← h₁, ← h₁]
  exact h₂ (neg_nonneg.2 hy) (neg_nonneg.2 hx) (neg_le_neg hxy)

/-- An odd function on a linear ordered additive commutative group is antitone on the whole group
provided that it is monotone on `Set.Ici 0`. -/
theorem antitone_of_odd_of_monotoneOn_nonneg {f : G → H} (h₁ : ∀ x, f (-x) = -f x)
    (h₂ : AntitoneOn f (Ici 0)) : Antitone f := by
  have h : Monotone (fun x => -f x) :=
    monotone_of_odd_of_monotoneOn_nonneg (fun x => by simp [h₁])
      (fun a ha b hb hab => neg_le_neg (h₂ ha hb hab))
  exact fun a b hab => neg_le_neg_iff.mp (h hab)
