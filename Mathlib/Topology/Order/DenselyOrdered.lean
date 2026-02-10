/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
module

public import Mathlib.Topology.Order.IsLUB

/-!
# Order topology on a densely ordered set
-/

@[expose] public section

open Set Filter TopologicalSpace Topology Function

open OrderDual (toDual ofDual)

variable {α β : Type*}

section DenselyOrdered

variable [TopologicalSpace α] [LinearOrder α] [OrderTopology α] [DenselyOrdered α] {a b : α}
  {s : Set α}

/-- The closure of the interval `(a, +∞)` is the closed interval `[a, +∞)`, unless `a` is a top
element. -/
theorem closure_Ioi' {a : α} (h : (Ioi a).Nonempty) : closure (Ioi a) = Ici a := by
  apply Subset.antisymm
  · exact closure_minimal Ioi_subset_Ici_self isClosed_Ici
  · rw [← diff_subset_closure_iff, Ici_diff_Ioi_same, singleton_subset_iff]
    exact isGLB_Ioi.mem_closure h

/-- The closure of the interval `(a, +∞)` is the closed interval `[a, +∞)`. -/
@[simp]
theorem closure_Ioi (a : α) [NoMaxOrder α] : closure (Ioi a) = Ici a :=
  closure_Ioi' nonempty_Ioi

/-- The closure of the interval `(-∞, a)` is the closed interval `(-∞, a]`, unless `a` is a bottom
element. -/
theorem closure_Iio' (h : (Iio a).Nonempty) : closure (Iio a) = Iic a :=
  closure_Ioi' (α := αᵒᵈ) h

/-- The closure of the interval `(-∞, a)` is the interval `(-∞, a]`. -/
@[simp]
theorem closure_Iio (a : α) [NoMinOrder α] : closure (Iio a) = Iic a :=
  closure_Iio' nonempty_Iio

/-- The closure of the open interval `(a, b)` is the closed interval `[a, b]`. -/
@[simp]
theorem closure_Ioo {a b : α} (hab : a ≠ b) : closure (Ioo a b) = Icc a b := by
  apply Subset.antisymm
  · exact closure_minimal Ioo_subset_Icc_self isClosed_Icc
  · rcases hab.lt_or_gt with hab | hab
    · rw [← diff_subset_closure_iff, Icc_diff_Ioo_same hab.le]
      have hab' : (Ioo a b).Nonempty := nonempty_Ioo.2 hab
      simp only [insert_subset_iff, singleton_subset_iff]
      exact ⟨(isGLB_Ioo hab).mem_closure hab', (isLUB_Ioo hab).mem_closure hab'⟩
    · rw [Icc_eq_empty_of_lt hab]
      exact empty_subset _

@[simp]
theorem closure_uIoo {a b : α} (hab : a ≠ b) : closure (uIoo a b) = uIcc a b := by
  simp [uIoo, uIcc, hab]

/-- The closure of the interval `(a, b]` is the closed interval `[a, b]`. -/
@[simp]
theorem closure_Ioc {a b : α} (hab : a ≠ b) : closure (Ioc a b) = Icc a b := by
  apply Subset.antisymm
  · exact closure_minimal Ioc_subset_Icc_self isClosed_Icc
  · apply Subset.trans _ (closure_mono Ioo_subset_Ioc_self)
    rw [closure_Ioo hab]

@[simp]
theorem closure_uIoc {a b : α} (hab : a ≠ b) : closure (uIoc a b) = uIcc a b := by
  simp [uIoc, uIcc, hab]

/-- The closure of the interval `[a, b)` is the closed interval `[a, b]`. -/
@[simp]
theorem closure_Ico {a b : α} (hab : a ≠ b) : closure (Ico a b) = Icc a b := by
  apply Subset.antisymm
  · exact closure_minimal Ico_subset_Icc_self isClosed_Icc
  · apply Subset.trans _ (closure_mono Ioo_subset_Ico_self)
    rw [closure_Ioo hab]

@[simp]
theorem interior_Ici' {a : α} (ha : (Iio a).Nonempty) : interior (Ici a) = Ioi a := by
  rw [← compl_Iio, interior_compl, closure_Iio' ha, compl_Iic]

theorem interior_Ici [NoMinOrder α] {a : α} : interior (Ici a) = Ioi a :=
  interior_Ici' nonempty_Iio

@[simp]
theorem interior_Iic' {a : α} (ha : (Ioi a).Nonempty) : interior (Iic a) = Iio a :=
  interior_Ici' (α := αᵒᵈ) ha

theorem interior_Iic [NoMaxOrder α] {a : α} : interior (Iic a) = Iio a :=
  interior_Iic' nonempty_Ioi

@[simp]
theorem interior_Icc [NoMinOrder α] [NoMaxOrder α] {a b : α} : interior (Icc a b) = Ioo a b := by
  rw [← Ici_inter_Iic, interior_inter, interior_Ici, interior_Iic, Ioi_inter_Iio]

@[simp]
theorem Icc_mem_nhds_iff [NoMinOrder α] [NoMaxOrder α] {a b x : α} :
    Icc a b ∈ 𝓝 x ↔ x ∈ Ioo a b := by
  rw [← interior_Icc, mem_interior_iff_mem_nhds]

@[simp]
theorem interior_Ico [NoMinOrder α] {a b : α} : interior (Ico a b) = Ioo a b := by
  rw [← Ici_inter_Iio, interior_inter, interior_Ici, interior_Iio, Ioi_inter_Iio]

@[simp]
theorem Ico_mem_nhds_iff [NoMinOrder α] {a b x : α} : Ico a b ∈ 𝓝 x ↔ x ∈ Ioo a b := by
  rw [← interior_Ico, mem_interior_iff_mem_nhds]

@[simp]
theorem interior_Ioc [NoMaxOrder α] {a b : α} : interior (Ioc a b) = Ioo a b := by
  rw [← Ioi_inter_Iic, interior_inter, interior_Ioi, interior_Iic, Ioi_inter_Iio]

@[simp]
theorem Ioc_mem_nhds_iff [NoMaxOrder α] {a b x : α} : Ioc a b ∈ 𝓝 x ↔ x ∈ Ioo a b := by
  rw [← interior_Ioc, mem_interior_iff_mem_nhds]

theorem closure_interior_Icc {a b : α} (h : a ≠ b) : closure (interior (Icc a b)) = Icc a b :=
  (closure_minimal interior_subset isClosed_Icc).antisymm <|
    calc
      Icc a b = closure (Ioo a b) := (closure_Ioo h).symm
      _ ⊆ closure (interior (Icc a b)) :=
        closure_mono (interior_maximal Ioo_subset_Icc_self isOpen_Ioo)

theorem Ioc_subset_closure_interior (a b : α) : Ioc a b ⊆ closure (interior (Ioc a b)) := by
  rcases eq_or_ne a b with (rfl | h)
  · simp
  · calc
      Ioc a b ⊆ Icc a b := Ioc_subset_Icc_self
      _ = closure (Ioo a b) := (closure_Ioo h).symm
      _ ⊆ closure (interior (Ioc a b)) :=
        closure_mono (interior_maximal Ioo_subset_Ioc_self isOpen_Ioo)

theorem Ico_subset_closure_interior (a b : α) : Ico a b ⊆ closure (interior (Ico a b)) := by
  simpa only [Ioc_toDual] using
    Ioc_subset_closure_interior (OrderDual.toDual b) (OrderDual.toDual a)

@[simp]
theorem frontier_Ici' {a : α} (ha : (Iio a).Nonempty) : frontier (Ici a) = {a} := by
  simp [frontier, ha]

theorem frontier_Ici [NoMinOrder α] {a : α} : frontier (Ici a) = {a} :=
  frontier_Ici' nonempty_Iio

@[simp]
theorem frontier_Iic' {a : α} (ha : (Ioi a).Nonempty) : frontier (Iic a) = {a} := by
  simp [frontier, ha]

theorem frontier_Iic [NoMaxOrder α] {a : α} : frontier (Iic a) = {a} :=
  frontier_Iic' nonempty_Ioi

@[simp]
theorem frontier_Ioi' {a : α} (ha : (Ioi a).Nonempty) : frontier (Ioi a) = {a} := by
  simp [frontier, closure_Ioi' ha]

theorem frontier_Ioi [NoMaxOrder α] {a : α} : frontier (Ioi a) = {a} :=
  frontier_Ioi' nonempty_Ioi

@[simp]
theorem frontier_Iio' {a : α} (ha : (Iio a).Nonempty) : frontier (Iio a) = {a} := by
  simp [frontier, closure_Iio' ha]

theorem frontier_Iio [NoMinOrder α] {a : α} : frontier (Iio a) = {a} :=
  frontier_Iio' nonempty_Iio

@[simp]
theorem frontier_Icc [NoMinOrder α] [NoMaxOrder α] {a b : α} (h : a ≤ b) :
    frontier (Icc a b) = {a, b} := by simp [frontier, h, Icc_diff_Ioo_same]

@[simp]
theorem frontier_Ioo {a b : α} (h : a < b) : frontier (Ioo a b) = {a, b} := by
  rw [frontier, closure_Ioo h.ne, interior_Ioo, Icc_diff_Ioo_same h.le]

@[simp]
theorem frontier_Ico [NoMinOrder α] {a b : α} (h : a < b) : frontier (Ico a b) = {a, b} := by
  rw [frontier, closure_Ico h.ne, interior_Ico, Icc_diff_Ioo_same h.le]

@[simp]
theorem frontier_Ioc [NoMaxOrder α] {a b : α} (h : a < b) : frontier (Ioc a b) = {a, b} := by
  rw [frontier, closure_Ioc h.ne, interior_Ioc, Icc_diff_Ioo_same h.le]

theorem nhdsWithin_Ioi_neBot' {a b : α} (H₁ : (Ioi a).Nonempty) (H₂ : a ≤ b) :
    NeBot (𝓝[Ioi a] b) :=
  mem_closure_iff_nhdsWithin_neBot.1 <| by rwa [closure_Ioi' H₁]

theorem nhdsWithin_Ioi_neBot [NoMaxOrder α] {a b : α} (H : a ≤ b) : NeBot (𝓝[Ioi a] b) :=
  nhdsWithin_Ioi_neBot' nonempty_Ioi H

theorem nhdsGT_neBot_of_exists_gt {a : α} (H : ∃ b, a < b) : NeBot (𝓝[>] a) :=
  nhdsWithin_Ioi_neBot' H (le_refl a)

instance nhdsGT_neBot [NoMaxOrder α] (a : α) : NeBot (𝓝[>] a) := nhdsWithin_Ioi_neBot le_rfl

theorem nhdsWithin_Iio_neBot' {b c : α} (H₁ : (Iio c).Nonempty) (H₂ : b ≤ c) :
    NeBot (𝓝[Iio c] b) :=
  mem_closure_iff_nhdsWithin_neBot.1 <| by rwa [closure_Iio' H₁]

theorem nhdsWithin_Iio_neBot [NoMinOrder α] {a b : α} (H : a ≤ b) : NeBot (𝓝[Iio b] a) :=
  nhdsWithin_Iio_neBot' nonempty_Iio H

theorem nhdsLT_neBot_of_exists_lt {b : α} (H : ∃ a, a < b) : NeBot (𝓝[<] b) :=
  nhdsWithin_Iio_neBot' H (le_refl b)

@[deprecated (since := "2026-01-16")] alias nhdsWithin_Iio_self_neBot' := nhdsLT_neBot_of_exists_lt

instance nhdsLT_neBot [NoMinOrder α] (a : α) : NeBot (𝓝[<] a) := nhdsWithin_Iio_neBot (le_refl a)

theorem right_nhdsWithin_Ico_neBot {a b : α} (H : a < b) : NeBot (𝓝[Ico a b] b) :=
  (isLUB_Ico H).nhdsWithin_neBot (nonempty_Ico.2 H)

theorem left_nhdsWithin_Ioc_neBot {a b : α} (H : a < b) : NeBot (𝓝[Ioc a b] a) :=
  (isGLB_Ioc H).nhdsWithin_neBot (nonempty_Ioc.2 H)

theorem left_nhdsWithin_Ioo_neBot {a b : α} (H : a < b) : NeBot (𝓝[Ioo a b] a) :=
  (isGLB_Ioo H).nhdsWithin_neBot (nonempty_Ioo.2 H)

theorem right_nhdsWithin_Ioo_neBot {a b : α} (H : a < b) : NeBot (𝓝[Ioo a b] b) :=
  (isLUB_Ioo H).nhdsWithin_neBot (nonempty_Ioo.2 H)

instance (x : α) [Nontrivial α] : NeBot (𝓝[≠] x) := by
  refine forall_mem_nonempty_iff_neBot.1 fun s hs => ?_
  obtain ⟨u, u_open, xu, us⟩ : ∃ u : Set α, IsOpen u ∧ x ∈ u ∧ u ∩ {x}ᶜ ⊆ s := mem_nhdsWithin.1 hs
  obtain ⟨a, b, a_lt_b, hab⟩ : ∃ a b : α, a < b ∧ Ioo a b ⊆ u := u_open.exists_Ioo_subset ⟨x, xu⟩
  obtain ⟨y, hy⟩ : ∃ y, a < y ∧ y < b := exists_between a_lt_b
  rcases ne_or_eq x y with (xy | rfl)
  · exact ⟨y, us ⟨hab hy, xy.symm⟩⟩
  obtain ⟨z, hz⟩ : ∃ z, a < z ∧ z < x := exists_between hy.1
  exact ⟨z, us ⟨hab ⟨hz.1, hz.2.trans hy.2⟩, hz.2.ne⟩⟩

/-- If the order topology for a dense linear ordering is discrete, the space has at most one point.

We would prefer for this to be an instance but even at `(priority := 100)` this was problematic so
we have deferred this issue. TODO Promote this to an `instance`! -/
lemma DenselyOrdered.subsingleton_of_discreteTopology [DiscreteTopology α] : Subsingleton α := by
  suffices ∀ a b : α, b ≤ a from ⟨fun a b ↦ le_antisymm (this b a) (this a b)⟩
  intro a b
  by_contra! contra
  suffices b ∈ Ioo a b by
    #adaptation_note /-- 2025-10-25 https://github.com/leanprover/lean4/issues/10953
      Used to be `grind`. -/
    simp_all
  rw [← (isClosed_discrete (Ioo a b)).closure_eq, closure_Ioo contra.ne]
  grind

/-- Let `s` be a dense set in a nontrivial dense linear order `α`. If `s` is a
separable space (e.g., if `α` has a second countable topology), then there exists a countable
dense subset `t ⊆ s` such that `t` does not contain bottom/top elements of `α`. -/
theorem Dense.exists_countable_dense_subset_no_bot_top [Nontrivial α] {s : Set α} [SeparableSpace s]
    (hs : Dense s) :
    ∃ t, t ⊆ s ∧ t.Countable ∧ Dense t ∧ (∀ x, IsBot x → x ∉ t) ∧ ∀ x, IsTop x → x ∉ t := by
  rcases hs.exists_countable_dense_subset with ⟨t, hts, htc, htd⟩
  refine ⟨t \ ({ x | IsBot x } ∪ { x | IsTop x }), ?_, ?_, ?_, fun x hx => ?_, fun x hx => ?_⟩
  · exact diff_subset.trans hts
  · exact htc.mono diff_subset
  · exact htd.diff_finite ((subsingleton_isBot α).finite.union (subsingleton_isTop α).finite)
  · simp [hx]
  · simp [hx]

variable (α) in
/-- If `α` is a nontrivial separable dense linear order, then there exists a
countable dense set `s : Set α` that contains neither top nor bottom elements of `α`.
For a dense set containing both bot and top elements, see
`exists_countable_dense_bot_top`. -/
theorem exists_countable_dense_no_bot_top [SeparableSpace α] [Nontrivial α] :
    ∃ s : Set α, s.Countable ∧ Dense s ∧ (∀ x, IsBot x → x ∉ s) ∧ ∀ x, IsTop x → x ∉ s := by
  simpa using dense_univ.exists_countable_dense_subset_no_bot_top

/-- `Set.Ico a b` is only closed if it is empty. -/
@[simp]
theorem isClosed_Ico_iff {a b : α} : IsClosed (Set.Ico a b) ↔ b ≤ a := by
  refine ⟨fun h => le_of_not_gt fun hab => ?_, by simp_all⟩
  have := h.closure_eq
  rw [closure_Ico hab.ne, Icc_eq_Ico_same_iff] at this
  exact this hab.le

/-- `Set.Ioc a b` is only closed if it is empty. -/
@[simp]
theorem isClosed_Ioc_iff {a b : α} : IsClosed (Set.Ioc a b) ↔ b ≤ a := by
  refine ⟨fun h => le_of_not_gt fun hab => ?_, by simp_all⟩
  have := h.closure_eq
  rw [closure_Ioc hab.ne, Icc_eq_Ioc_same_iff] at this
  exact this hab.le

/-- `Set.Ioo a b` is only closed if it is empty. -/
@[simp]
theorem isClosed_Ioo_iff {a b : α} : IsClosed (Set.Ioo a b) ↔ b ≤ a := by
  refine ⟨fun h => le_of_not_gt fun hab => ?_, by simp_all⟩
  have := h.closure_eq
  rw [closure_Ioo hab.ne, Icc_eq_Ioo_same_iff] at this
  exact this hab.le

end DenselyOrdered
