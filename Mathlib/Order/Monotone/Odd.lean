/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module order.monotone.odd
! leanprover-community/mathlib commit 9116dd6709f303dcf781632e15fdef382b0fc579
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Monotone.Union
import Mathbin.Algebra.Order.Group.Instances

/-!
# Monotonicity of odd functions

An odd function on a linear ordered additive commutative group `G` is monotone on the whole group
provided that is is monotone on `set.Ici 0`, see `monotone_of_odd_of_monotone_on_nonneg`. We also
prove versions of this lemma for `antitone`, `strict_mono`, and `strict_anti`.
-/


open Set

variable {G H : Type _} [LinearOrderedAddCommGroup G] [OrderedAddCommGroup H]

/-- An odd function on a linear ordered additive commutative group is strictly monotone on the whole
group provided that it is strictly monotone on `set.Ici 0`. -/
theorem strict_mono_of_odd_strict_mono_on_nonneg {f : G → H} (h₁ : ∀ x, f (-x) = -f x)
    (h₂ : StrictMonoOn f (Ici 0)) : StrictMono f := by
  refine' StrictMonoOn.Iic_union_Ici (fun x hx y hy hxy => neg_lt_neg_iff.1 _) h₂
  rw [← h₁, ← h₁]
  exact h₂ (neg_nonneg.2 hy) (neg_nonneg.2 hx) (neg_lt_neg hxy)
#align strict_mono_of_odd_strict_mono_on_nonneg strict_mono_of_odd_strict_mono_on_nonneg

/-- An odd function on a linear ordered additive commutative group is strictly antitone on the whole
group provided that it is strictly antitone on `set.Ici 0`. -/
theorem strict_anti_of_odd_strict_anti_on_nonneg {f : G → H} (h₁ : ∀ x, f (-x) = -f x)
    (h₂ : StrictAntiOn f (Ici 0)) : StrictAnti f :=
  @strict_mono_of_odd_strict_mono_on_nonneg G Hᵒᵈ _ _ _ h₁ h₂
#align strict_anti_of_odd_strict_anti_on_nonneg strict_anti_of_odd_strict_anti_on_nonneg

/-- An odd function on a linear ordered additive commutative group is monotone on the whole group
provided that it is monotone on `set.Ici 0`. -/
theorem monotone_of_odd_of_monotone_on_nonneg {f : G → H} (h₁ : ∀ x, f (-x) = -f x)
    (h₂ : MonotoneOn f (Ici 0)) : Monotone f := by
  refine' MonotoneOn.Iic_union_Ici (fun x hx y hy hxy => neg_le_neg_iff.1 _) h₂
  rw [← h₁, ← h₁]
  exact h₂ (neg_nonneg.2 hy) (neg_nonneg.2 hx) (neg_le_neg hxy)
#align monotone_of_odd_of_monotone_on_nonneg monotone_of_odd_of_monotone_on_nonneg

/-- An odd function on a linear ordered additive commutative group is antitone on the whole group
provided that it is monotone on `set.Ici 0`. -/
theorem antitone_of_odd_of_monotone_on_nonneg {f : G → H} (h₁ : ∀ x, f (-x) = -f x)
    (h₂ : AntitoneOn f (Ici 0)) : Antitone f :=
  @monotone_of_odd_of_monotone_on_nonneg G Hᵒᵈ _ _ _ h₁ h₂
#align antitone_of_odd_of_monotone_on_nonneg antitone_of_odd_of_monotone_on_nonneg

