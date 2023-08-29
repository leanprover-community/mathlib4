/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Order.Monotone.Union
import Mathlib.Algebra.Order.Group.Instances

#align_import order.monotone.odd from "leanprover-community/mathlib"@"9116dd6709f303dcf781632e15fdef382b0fc579"

/-!
# Monotonicity of odd functions

An odd function on a linear ordered additive commutative group `G` is monotone on the whole group
provided that it is monotone on `Set.Ici 0`, see `monotone_of_odd_of_monotoneOn_nonneg`. We also
prove versions of this lemma for `Antitone`, `StrictMono`, and `StrictAnti`.
-/


open Set

variable {G H : Type*} [LinearOrderedAddCommGroup G] [OrderedAddCommGroup H]

/-- An odd function on a linear ordered additive commutative group is strictly monotone on the whole
group provided that it is strictly monotone on `Set.Ici 0`. -/
theorem strictMono_of_odd_strictMonoOn_nonneg {f : G → H} (h₁ : ∀ x, f (-x) = -f x)
    (h₂ : StrictMonoOn f (Ici 0)) : StrictMono f := by
  refine' StrictMonoOn.Iic_union_Ici (fun x hx y hy hxy => neg_lt_neg_iff.1 _) h₂
  -- ⊢ -f y < -f x
  rw [← h₁, ← h₁]
  -- ⊢ f (-y) < f (-x)
  exact h₂ (neg_nonneg.2 hy) (neg_nonneg.2 hx) (neg_lt_neg hxy)
  -- 🎉 no goals
#align strict_mono_of_odd_strict_mono_on_nonneg strictMono_of_odd_strictMonoOn_nonneg

/-- An odd function on a linear ordered additive commutative group is strictly antitone on the whole
group provided that it is strictly antitone on `Set.Ici 0`. -/
theorem strictAnti_of_odd_strictAntiOn_nonneg {f : G → H} (h₁ : ∀ x, f (-x) = -f x)
    (h₂ : StrictAntiOn f (Ici 0)) : StrictAnti f :=
  @strictMono_of_odd_strictMonoOn_nonneg G Hᵒᵈ _ _ _ h₁ h₂
#align strict_anti_of_odd_strict_anti_on_nonneg strictAnti_of_odd_strictAntiOn_nonneg

/-- An odd function on a linear ordered additive commutative group is monotone on the whole group
provided that it is monotone on `Set.Ici 0`. -/
theorem monotone_of_odd_of_monotoneOn_nonneg {f : G → H} (h₁ : ∀ x, f (-x) = -f x)
    (h₂ : MonotoneOn f (Ici 0)) : Monotone f := by
  refine' MonotoneOn.Iic_union_Ici (fun x hx y hy hxy => neg_le_neg_iff.1 _) h₂
  -- ⊢ -f y ≤ -f x
  rw [← h₁, ← h₁]
  -- ⊢ f (-y) ≤ f (-x)
  exact h₂ (neg_nonneg.2 hy) (neg_nonneg.2 hx) (neg_le_neg hxy)
  -- 🎉 no goals
#align monotone_of_odd_of_monotone_on_nonneg monotone_of_odd_of_monotoneOn_nonneg

/-- An odd function on a linear ordered additive commutative group is antitone on the whole group
provided that it is monotone on `Set.Ici 0`. -/
theorem antitone_of_odd_of_monotoneOn_nonneg {f : G → H} (h₁ : ∀ x, f (-x) = -f x)
    (h₂ : AntitoneOn f (Ici 0)) : Antitone f :=
  @monotone_of_odd_of_monotoneOn_nonneg G Hᵒᵈ _ _ _ h₁ h₂
#align antitone_of_odd_of_monotone_on_nonneg antitone_of_odd_of_monotoneOn_nonneg
