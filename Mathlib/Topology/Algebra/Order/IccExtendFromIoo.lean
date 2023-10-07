/-
Copyright (c) 2023 Wen Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wen Yang
-/
import Mathlib.Data.Set.FunctionToVal
import Mathlib.Topology.Algebra.Order.MonotoneContinuity

/-!
# Extend the domain of f from an open interval to the closed interval

Sometimes a function `f : (a, b) → β` can be naturally extended to `[a, b]`.

## Main statements

* `StrictMonoOn.Ioo_extend_Icc` and `StrictAntiOn.Ioo_extend_Icc`:
A strictly monotone function on an open interval can be extended to be
strictly monotone on the closed interval.
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
variable [PartialOrder α] [PartialOrder β] {a b : α} {c d : β}

/-- A strictly monotone (increasing) function on an open interval can be extended
to be strictly monotone (increasing) on the closed interval.-/
theorem StrictMonoOn.Ioo_extend_Icc (hf_mono : StrictMonoOn f (Ioo a b))
    (hf_mapsto : f '' (Ioo a b) ⊆ Ioo c d) (hab : a < b) (hcd : c < d) :
    ∃ g, StrictMonoOn g (Icc a b) ∧
    EqOn f g {a, b}ᶜ ∧
    g '' (Icc a b) = f '' (Ioo a b) ∪ {c, d} ∧
    g = update (update f a c) b d := by
  let g : α → β := update (update f a c) b d
  use g
  have ha : a ∉ Ioo a b := by simp
  have hg_mono : StrictMonoOn g (Icc a b) := by
    have ha' : Ico a b = (Ioo a b) ∪ {a} := (Ioo_union_left hab).symm
    have hf_mono' : StrictMonoOn (update f a c) (Ico a b) := by
      rw [ha']
      refine hf_mono.update_strict_lower_bound ?mapsto ?ha
      · exact hf_mapsto.trans Ioo_subset_Ioi_self
      · aesop
    have hf_mapsto' : (update f a c) '' (Ico a b) ⊆ Ico c d := by
      rw [ha', image_union]
      simp only [(update.EqOn f ha).image_eq]
      rw [← Ioo_union_left hcd]
      simp [insert_subset_insert hf_mapsto]
    have : (update f a c) '' (Ico a b) ⊆ Iio d := hf_mapsto'.trans Ico_subset_Iio_self
    have hb : ∀ x ∈ Ico a b, x < b := by simp
    have hf_mono'' := hf_mono'.update_strict_upper_bound this hb
    replace : Ico a b ∪ {b} = Icc a b := Ico_union_right hab.le
    rw [this] at hf_mono''
    exact hf_mono''
  have hg_eq : EqOn f g {a, b}ᶜ := by
    intro x hx
    unfold_let g
    unfold update
    aesop
  have hg_image : g '' Icc a b = f '' Ioo a b ∪ {c, d} := by
    unfold_let g
    have hb : b ∉ Ico a b := by simp
    rw [← Ico_union_right hab.le, update.image (update f a c) hb,
        ← Ioo_union_left hab, update.image f ha]
    have := insert_comm d c (f '' Ioo a b)
    simp [this]
  trivial

/-- A strictly antitone (decreasing) function on an open interval can be extended
to be strictly antitone (decreasing) on the closed interval.-/
theorem StrictAntiOn.Ioo_extend_Icc (hf_mono : StrictAntiOn f (Ioo a b))
    (hf_mapsto : f '' (Ioo a b) ⊆ Ioo c d) (hab : a < b) (hcd : c < d) :
    ∃ g, StrictAntiOn g (Icc a b) ∧
    EqOn f g {a, b}ᶜ ∧
    g '' (Icc a b) = f '' (Ioo a b) ∪ {c, d} ∧
    g = update (update f a d) b c := by
  let g : α → OrderDual β := f
  have hg_mono : StrictMonoOn g (Ioo a b) := hf_mono
  have hg_mapsto : g '' (Ioo a b) ⊆ Ioo (toDual d) (toDual c) := by aesop
  choose G hG using hg_mono.Ioo_extend_Icc hg_mapsto hab hcd
  let F : α → β := G
  use F
  constructor
  · aesop
  · constructor
    · aesop
    · constructor
      · rw [hG.2.2.1]
        have := insert_comm (toDual d) (toDual c) ((fun a ↦ f a) '' Ioo a b)
        aesop
      · aesop

end StrictMonoOn

open Set2Set

section StrictMonoOn2
variable [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
    [LinearOrder β] [TopologicalSpace β] [OrderTopology β] [Nonempty β]
    {a b : α} {c d : β}

/-- Extend strictly monotone (increasing) functions between open intervals to homeomorphisms
between the closed intervals.-/
theorem StrictMonoOn.Ioo_continuous_extend_Icc (hf_increasing : StrictMonoOn f (Ioo a b))
    (hf_mapsto : f '' (Ioo a b) = Ioo c d) (hab : a < b) (hcd : c < d) :
    ∃ (g : (Icc a b) ≃ₜ (Icc c d)), EqOn f g.toFun.toval (Ioo a b) := by
  obtain ⟨g, hg⟩ := hf_increasing.Ioo_extend_Icc hf_mapsto.subset hab hcd
  have : Nonempty β := Nonempty.intro c
  have hg_mapsto := hg.2.2.1
  rw [hf_mapsto, ← Icc_diff_Ioo_same hcd.le] at hg_mapsto
  replace hg_mapsto : g '' Icc a b = Icc c d := by
    rw [hg_mapsto, @union_diff_self]
    exact union_eq_self_of_subset_left Ioo_subset_Icc_self
  let iso := hg.1.orderIso g _
  have hg_image : OrderTopology (g '' (Icc a b)) := by
    rw [hg_mapsto]
    exact orderTopology_of_ordConnected
  let F := iso.toHomeomorph
  have h_eq_fg : EqOn f g (Ioo a b) := by
    intro x hx
    apply hg.2.1
    aesop
  have h_eq_gF : EqOn g (toval iso.toFun) (Icc a b) := by
    rw [← @restrict_eq_restrict_iff, ← toval_eq, @restrict_eq]
    exact rfl
  have hF : EqOn f (toval F.toFun) (Ioo a b) := by
    intro x hx
    rw [h_eq_fg hx, h_eq_gF (mem_Icc_of_Ioo hx)]
    exact rfl
  have : ∃ (g : (Icc a b) ≃ₜ g '' (Icc a b)), EqOn f g.toFun.toval (Ioo a b) := by use F
  rw [hg_mapsto] at this
  exact this

/-- Extend strictly antitone (decreasing) functions between open intervals to homeomorphisms
between the closed intervals.-/
theorem StrictAntiOn.Ioo_continuous_extend_Icc (hf_decreasing : StrictAntiOn f (Ioo a b))
    (hf_mapsto : f '' (Ioo a b) = Ioo c d) (hab : a < b) (hcd : c < d) :
    ∃ (g : (Icc a b) ≃ₜ (Icc c d)), EqOn f g.toFun.toval (Ioo a b) := by
  let F : α → OrderDual β := f
  have hF_increasing : StrictMonoOn F (Ioo a b) := hf_decreasing
  have hF_mapsto : F '' (Ioo a b) = Ioo (toDual d) (toDual c) := by aesop
  obtain h := hF_increasing.Ioo_continuous_extend_Icc hF_mapsto hab hcd
  have : Icc (toDual d) (toDual c) = Icc c d := by aesop
  rw [this] at h
  exact h

end StrictMonoOn2
