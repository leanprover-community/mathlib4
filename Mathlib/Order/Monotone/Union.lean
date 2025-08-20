/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Sébastien Gouëzel
-/
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.Interval.Set.LinearOrder

/-!
# Monotonicity on intervals

In this file we prove that a function is (strictly) monotone (or antitone) on a linear order `α`
provided that it is (strictly) monotone on `(-∞, a]` and on `[a, +∞)`. This is a special case
of a more general statement where one deduces monotonicity on a union from monotonicity on each
set.
-/


open Set

variable {α β : Type*} [LinearOrder α] [Preorder β] {a : α} {f : α → β}

/-- If `f` is strictly monotone both on `s` and `t`, with `s` to the left of `t` and the center
point belonging to both `s` and `t`, then `f` is strictly monotone on `s ∪ t` -/
protected theorem StrictMonoOn.union {s t : Set α} {c : α} (h₁ : StrictMonoOn f s)
    (h₂ : StrictMonoOn f t) (hs : IsGreatest s c) (ht : IsLeast t c) : StrictMonoOn f (s ∪ t) := by
  have A : ∀ x, x ∈ s ∪ t → x ≤ c → x ∈ s := by
    intro x hx hxc
    cases hx
    · assumption
    rcases eq_or_lt_of_le hxc with (rfl | h'x)
    · exact hs.1
    exact (lt_irrefl _ (h'x.trans_le (ht.2 (by assumption)))).elim
  have B : ∀ x, x ∈ s ∪ t → c ≤ x → x ∈ t := by
    intro x hx hxc
    match hx with
    | Or.inr hx => exact hx
    | Or.inl hx =>
      rcases eq_or_lt_of_le hxc with (rfl | h'x)
      · exact ht.1
      exact (lt_irrefl _ (h'x.trans_le (hs.2 hx))).elim
  intro x hx y hy hxy
  rcases lt_or_ge x c with (hxc | hcx)
  · have xs : x ∈ s := A _ hx hxc.le
    rcases lt_or_ge y c with (hyc | hcy)
    · exact h₁ xs (A _ hy hyc.le) hxy
    · exact (h₁ xs hs.1 hxc).trans_le (h₂.monotoneOn ht.1 (B _ hy hcy) hcy)
  · have xt : x ∈ t := B _ hx hcx
    have yt : y ∈ t := B _ hy (hcx.trans hxy.le)
    exact h₂ xt yt hxy

/-- If `f` is strictly monotone both on `(-∞, a]` and `[a, ∞)`, then it is strictly monotone on the
whole line. -/
protected theorem StrictMonoOn.Iic_union_Ici (h₁ : StrictMonoOn f (Iic a))
    (h₂ : StrictMonoOn f (Ici a)) : StrictMono f := by
  rw [← strictMonoOn_univ, ← @Iic_union_Ici _ _ a]
  exact StrictMonoOn.union h₁ h₂ isGreatest_Iic isLeast_Ici

/-- If `f` is strictly antitone both on `s` and `t`, with `s` to the left of `t` and the center
point belonging to both `s` and `t`, then `f` is strictly antitone on `s ∪ t` -/
protected theorem StrictAntiOn.union {s t : Set α} {c : α} (h₁ : StrictAntiOn f s)
    (h₂ : StrictAntiOn f t) (hs : IsGreatest s c) (ht : IsLeast t c) : StrictAntiOn f (s ∪ t) :=
  (h₁.dual_right.union h₂.dual_right hs ht).dual_right

/-- If `f` is strictly antitone both on `(-∞, a]` and `[a, ∞)`, then it is strictly antitone on the
whole line. -/
protected theorem StrictAntiOn.Iic_union_Ici (h₁ : StrictAntiOn f (Iic a))
    (h₂ : StrictAntiOn f (Ici a)) : StrictAnti f :=
  (h₁.dual_right.Iic_union_Ici h₂.dual_right).dual_right

/-- If `f` is monotone both on `s` and `t`, with `s` to the left of `t` and the center
point belonging to both `s` and `t`, then `f` is monotone on `s ∪ t` -/
protected theorem MonotoneOn.union_right {s t : Set α} {c : α} (h₁ : MonotoneOn f s)
    (h₂ : MonotoneOn f t) (hs : IsGreatest s c) (ht : IsLeast t c) : MonotoneOn f (s ∪ t) := by
  have A : ∀ x, x ∈ s ∪ t → x ≤ c → x ∈ s := by
    intro x hx hxc
    cases hx
    · assumption
    rcases eq_or_lt_of_le hxc with (rfl | h'x)
    · exact hs.1
    exact (lt_irrefl _ (h'x.trans_le (ht.2 (by assumption)))).elim
  have B : ∀ x, x ∈ s ∪ t → c ≤ x → x ∈ t := by
    intro x hx hxc
    match hx with
    | Or.inr hx => exact hx
    | Or.inl hx =>
      rcases eq_or_lt_of_le hxc with (rfl | h'x)
      · exact ht.1
      exact (lt_irrefl _ (h'x.trans_le (hs.2 hx))).elim
  intro x hx y hy hxy
  rcases lt_or_ge x c with (hxc | hcx)
  · have xs : x ∈ s := A _ hx hxc.le
    rcases lt_or_ge y c with (hyc | hcy)
    · exact h₁ xs (A _ hy hyc.le) hxy
    · exact (h₁ xs hs.1 hxc.le).trans (h₂ ht.1 (B _ hy hcy) hcy)
  · have xt : x ∈ t := B _ hx hcx
    have yt : y ∈ t := B _ hy (hcx.trans hxy)
    exact h₂ xt yt hxy

/-- If `f` is monotone both on `(-∞, a]` and `[a, ∞)`, then it is monotone on the whole line. -/
protected theorem MonotoneOn.Iic_union_Ici (h₁ : MonotoneOn f (Iic a)) (h₂ : MonotoneOn f (Ici a)) :
    Monotone f := by
  rw [← monotoneOn_univ, ← @Iic_union_Ici _ _ a]
  exact MonotoneOn.union_right h₁ h₂ isGreatest_Iic isLeast_Ici

/-- If `f` is antitone both on `s` and `t`, with `s` to the left of `t` and the center
point belonging to both `s` and `t`, then `f` is antitone on `s ∪ t` -/
protected theorem AntitoneOn.union_right {s t : Set α} {c : α} (h₁ : AntitoneOn f s)
    (h₂ : AntitoneOn f t) (hs : IsGreatest s c) (ht : IsLeast t c) : AntitoneOn f (s ∪ t) :=
  (h₁.dual_right.union_right h₂.dual_right hs ht).dual_right

/-- If `f` is antitone both on `(-∞, a]` and `[a, ∞)`, then it is antitone on the whole line. -/
protected theorem AntitoneOn.Iic_union_Ici (h₁ : AntitoneOn f (Iic a)) (h₂ : AntitoneOn f (Ici a)) :
    Antitone f :=
  (h₁.dual_right.Iic_union_Ici h₂.dual_right).dual_right
