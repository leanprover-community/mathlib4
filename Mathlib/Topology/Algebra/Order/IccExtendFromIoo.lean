/-
Copyright (c) 2023 Wen Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wen Yang
-/
import Mathlib.Topology.Algebra.Order.MonotoneContinuity

/-!
# Extend the domain of f from an open interval to the closed interval

Sometimes a function `f : (a, b) → β` can be naturally extended to `[a, b]`.

## Main statements

* `StrictMonoOn.Ioo_continuous_extend_Icc`:
A strictly monotone function between open intervals can be extended to be
an homeomorphism between the closed intervals.
-/

open OrderDual Function Set
universe u
variable {α β : Type*} {f : α → β} [DecidableEq α]

section update
variable {s : Set α} {a : α} {b : β}

/-- Modifying the value of `f` at one point does not affect its value elsewhere.​-/
theorem Function.update.EqOn (f : α → β) (ha : a ∉ s) : EqOn (update f a b) f s := by
  intro x hx
  unfold update
  simp only [eq_rec_constant, dite_eq_ite]
  have : x ≠ a := ne_of_mem_of_not_mem hx ha
  aesop

theorem Function.update.image (f : α → β) (ha : a ∉ s) :
    (update f a b) '' (s ∪ {a}) = f '' s ∪ {b} := by
  calc
    _ = (update f a b) '' s ∪ (update f a b) '' {a} := image_union (update f a b) s {a}
    _ = (update f a b) '' s ∪ {b} := by simp
    _ = f '' s ∪ {b} := by simp only [(update.EqOn f ha).image_eq]

/-- If `a` is a strict upper bound of `s`,
`b` is a strict upper bound of `f(s)`,
and `f` is strictly monotone (increasing) on `s`,
then `f` can be extended to be strictly monotone (increasing) on `s ∪ {a}`.-/
theorem StrictMonoOn.update_strict_upper_bound  [PartialOrder α] [Preorder β]
    (hf_mono : StrictMonoOn f s) (hf_mapsto : f '' s ⊆ Iio b)
    (ha : ∀ x ∈ s, x < a) :
    StrictMonoOn (update f a b) (s ∪ {a}) := by
  unfold update
  simp only [eq_rec_constant, dite_eq_ite, union_singleton]
  intro x hx y hy hxy
  simp only
  have hxa : x ≠ a := by
    by_contra' hxa
    rw [hxa] at hxy
    cases hy with
    | inl h => rw [h] at hxy; exact hxy.false
    | inr h => exact (hxy.trans (ha y h)).false
  by_cases hya : y = a
  aesop
  aesop

/-- If `a` is a strict lower bound of `s`,
`b` is a strict lower bound of `f(s)`,
and `f` is strictly antitone (decreasing) on `s`,
then `f` can be extended to be strictly antitone (decreasing) on `s ∪ {a}`.-/
theorem StrictMonoOn.update_strict_lower_bound [PartialOrder α] [Preorder β]
    (hf_mono : StrictMonoOn f s) (hf_mapsto : f '' s ⊆ Ioi b)
    (ha : ∀ x ∈ s, a < x) :
    StrictMonoOn (update f a b) (s ∪ {a}) := by
  let g : OrderDual α → OrderDual β := f
  have hg_mono : StrictMonoOn g s := strict_mono_on_dual_iff.mp hf_mono
  have := hg_mono.update_strict_upper_bound hf_mapsto ha
  exact strict_mono_on_dual_iff.mp this

end update

section StrictMonoOn
variable [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
    [LinearOrder β] [TopologicalSpace β] [OrderTopology β]
    {a b : α} {c d : β}

/-- Extend strictly monotone (increasing) functions between open intervals to homeomorphisms
between the closed intervals.-/
theorem StrictMonoOn.Ioo_continuous_extend_Icc (hf_increasing : StrictMonoOn f (Ioo a b))
    (hf_mapsto : f '' (Ioo a b) = Ioo c d) (hab : a < b) (hcd : c < d) :
    ∃ (g : (Icc a b) ≃ₜ (Icc c d)),
    ∀ x, (hx : x ∈ Ioo a b) → f x = (g ⟨x, mem_Icc_of_Ioo hx⟩).val := by
  let g := update (update f a c) b d
  --  First, we verify that `g` is strictly monotone.
  have ha : a ∉ Ioo a b := by simp
  have ha' : Ico a b = (Ioo a b) ∪ {a} := (Ioo_union_left hab).symm
  have hf_mono' : StrictMonoOn (update f a c) (Ico a b) := by
    rw [ha']
    refine hf_increasing.update_strict_lower_bound ?mapsto ?ha
    · rw [hf_mapsto]
      exact Ioo_subset_Ioi_self
    · aesop
  have hf_mapsto' : (update f a c) '' (Ico a b) = Ico c d := by
    rw [ha', image_union]
    simp only [(update.EqOn f ha).image_eq]
    aesop
  have : (update f a c) '' (Ico a b) ⊆ Iio d := by
    rw [hf_mapsto']
    exact Ico_subset_Iio_self
  have hb : ∀ x ∈ Ico a b, x < b := by simp
  have hf_mono'' := hf_mono'.update_strict_upper_bound this hb
  replace : Ico a b ∪ {b} = Icc a b := Ico_union_right hab.le
  rw [this] at hf_mono''
  have hg_mono : StrictMonoOn g (Icc a b) := hf_mono''
  -- Second, we verify that the image of `g` is `[c, d]`.
  have hg_mapsto : g '' Icc a b = Icc c d := by
    unfold_let g
    have hb : b ∉ Ico a b := by simp
    rw [← Ico_union_right hab.le, update.image (update f a c) hb, ← Ioo_union_left hab,
        update.image f ha, hf_mapsto, Ioo_union_left hcd, Ico_union_right hcd.le]
  -- Third, we find that `g` is an order isomorphism.
  let iso := hg_mono.orderIso g _
  have hg_image : OrderTopology (g '' (Icc a b)) := by
    rw [hg_mapsto]
    exact orderTopology_of_ordConnected
  let F := iso.toHomeomorph
  have h_eq_fg (x) (hx : x ∈ Ioo a b) : f x = g x := by
    unfold_let g
    unfold update
    have hxa : x ≠ a := by
      by_contra'
      rw [this] at hx
      revert hx
      simp
    have hxb : x ≠ b := by
      by_contra'
      rw [this] at hx
      revert hx
      simp
    simp [hxa, hxb]
  have hgF (x : Icc a b) : g x = F.toFun x := rfl
  have hF : ∀ x, (hx : x ∈ Ioo a b) → f x = (F.toFun ⟨x, mem_Icc_of_Ioo hx⟩).val := by
    intro x hx
    rw [h_eq_fg x hx, hgF ⟨x, _⟩]
  have : ∃ (G : (Icc a b) ≃ₜ (g '' Icc a b)), ∀ x, (hx : x ∈ Ioo a b) →
      f x = (G.toFun ⟨x, mem_Icc_of_Ioo hx⟩).val := by use F
  rw [hg_mapsto] at this
  exact this

/-- Extend strictly antitone (decreasing) functions between open intervals to homeomorphisms
between the closed intervals.-/
theorem StrictAntiOn.Ioo_continuous_extend_Icc (hf_decreasing : StrictAntiOn f (Ioo a b))
    (hf_mapsto : f '' (Ioo a b) = Ioo c d) (hab : a < b) (hcd : c < d) :
    ∃ (g : (Icc a b) ≃ₜ (Icc c d)),
    ∀ x, (hx : x ∈ Ioo a b) → f x = (g ⟨x, mem_Icc_of_Ioo hx⟩).val := by
  let F : α → OrderDual β := f
  have hF_increasing : StrictMonoOn F (Ioo a b) := hf_decreasing
  have hF_mapsto : F '' (Ioo a b) = Ioo (toDual d) (toDual c) := by aesop
  obtain h := hF_increasing.Ioo_continuous_extend_Icc hF_mapsto hab hcd
  have : Icc (toDual d) (toDual c) = Icc c d := by aesop
  rw [this] at h
  exact h

end StrictMonoOn
