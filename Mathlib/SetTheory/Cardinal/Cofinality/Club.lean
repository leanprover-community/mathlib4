/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.SetTheory.Cardinal.Cofinality.Enum
public import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal

/-!
# Club sets and stationary sets

A subset of a well-ordered type `α` is called a **club set** when it is closed in the order topology
and cofinal. If `α` has no maximum, then an equivalent condition is that `α` is closed and
unbounded; hence the name.

A **stationary set** is a set which intersects all club sets.

## Implementation notes

To avoid importing topology in the ordinals, we spell out the closure property using `DirSupClosed`.
For any type equipped with the Scott-Hausdorff topology (which includes well-orders with the order
topology), `DirSupClosed s` and `IsClosed s` are equivalent predicates.
-/

public section

universe u v

open Cardinal Order Ordinal Set

variable {α : Type v} {s t : Set α} {x : α} [LinearOrder α]

/-! ### Club sets -/

/-- A club set is closed under suprema and cofinal. -/
structure IsClub {α : Type*} [LinearOrder α] (s : Set α) where
  /-- Club sets are closed under suprema. If `α` is a well-order with the order topology, this
  condition is equivalent to `IsClosed s`. -/
  dirSupClosed : DirSupClosed s
  /-- Club sets are cofinal. If `α` has no maximum, this condition is equivalent to `¬ BddAbove s`.
  See `not_bddAbove_iff_isCofinal`. -/
  isCofinal : IsCofinal s

namespace IsClub

@[simp]
theorem of_isEmpty [IsEmpty α] {s : Set α} : IsClub s :=
  ⟨.of_isEmpty, .of_isEmpty⟩

@[simp]
protected theorem univ : IsClub (α := α) .univ :=
  ⟨.univ, .univ⟩

protected theorem nonempty [Nonempty α] (hs : IsClub s) : s.Nonempty :=
  hs.isCofinal.nonempty

theorem _root_.isClub_empty_iff : IsClub (α := α) ∅ ↔ IsEmpty α :=
  ⟨fun h ↦ isCofinal_empty_iff.1 h.isCofinal, fun _ ↦ .of_isEmpty⟩

protected theorem union (hs : IsClub s) (ht : IsClub t) : IsClub (s ∪ t) :=
  ⟨hs.dirSupClosed.union ht.dirSupClosed, hs.isCofinal.mono Set.subset_union_left⟩

theorem isLUB_mem (hs : IsClub s) (ht : t ⊆ s) (ht₀ : t.Nonempty) (hx : IsLUB t x) : x ∈ s :=
  hs.dirSupClosed ht ht₀ (.of_linearOrder _) hx

theorem csSup_mem {α} [ConditionallyCompleteLinearOrder α] {s t : Set α}
    (hs : IsClub s) (ht : t ⊆ s) (ht₀ : t.Nonempty) (ht₁ : BddAbove t) : sSup t ∈ s :=
  hs.isLUB_mem ht ht₀ (isLUB_csSup ht₀ ht₁)

theorem ciSup_mem {α} [ConditionallyCompleteLinearOrder α] {ι} {f : ι → α} [Nonempty ι]
    {s : Set α} (hs : IsClub s) (ht : .range f ⊆ s) (ht' : BddAbove (.range f)) : ⨆ i, f i ∈ s :=
  hs.csSup_mem ht (Set.range_nonempty _) ht'

theorem sInter_of_orderTop {s : Set (Set α)} [OrderTop α] (hs : ∀ x ∈ s, IsClub x) :
    IsClub (⋂₀ s) := by
  refine ⟨.sInter fun x hx ↦ (hs x hx).dirSupClosed, ?_⟩
  rw [isCofinal_iff_top_mem, mem_sInter]
  exact fun x hx ↦ (hs x hx).isCofinal.top_mem

theorem iInter_of_orderTop {ι : Type*} {f : ι → Set α} [OrderTop α] (hs : ∀ i, IsClub (f i)) :
    IsClub (⋂ i, f i) := by
  rw [← sInter_range]
  exact .sInter_of_orderTop (by simpa)

theorem sInter_of_cof_le_one {s : Set (Set α)} (hα : cof α ≤ 1) (hs : ∀ x ∈ s, IsClub x) :
    IsClub (⋂₀ s) := by
  cases isEmpty_or_nonempty α; · simp
  cases topOrderOrNoTopOrder α
  · exact .sInter_of_orderTop hs
  · cases one_lt_cof.not_ge hα

theorem iInter_of_cof_le_one {ι : Type*} {f : ι → Set α} (hα : cof α ≤ 1) (hs : ∀ i, IsClub (f i)) :
    IsClub (⋂ i, f i) := by
  rw [← sInter_range]
  exact .sInter_of_cof_le_one hα (by simpa)

section WellFoundedLT
variable [WellFoundedLT α]

attribute [local instance]
  WellFoundedLT.toOrderBot WellFoundedLT.conditionallyCompleteLinearOrderBot

protected theorem sInter {s : Set (Set α)} (hα : cof α ≠ ℵ₀) (hsα : #s < cof α)
    (hs : ∀ x ∈ s, IsClub x) : IsClub (⋂₀ s) := by
  cases isEmpty_or_nonempty α; · simp
  obtain hα | hα := hα.lt_or_gt
  · exact .sInter_of_cof_le_one (cof_lt_aleph0_iff.1 hα) hs
  refine ⟨.sInter fun x hx ↦ (hs x hx).dirSupClosed, fun a ↦ ?_⟩
  choose f hf using fun x : s ↦ (hs _ x.2).isCofinal
  let g : ℕ → α := Nat.rec a fun _ IH ↦ sSup (.range (f · IH))
  have hg : BddAbove (.range g) := by
    refine .of_not_isCofinal fun hg ↦ (cof_le hg).not_gt (hα.trans_le' ?_)
    simpa using mk_range_le_lift (f := g)
  refine ⟨_, fun t ht ↦ ?_, le_csSup hg ⟨0, rfl⟩⟩
  apply (hs t ht).isLUB_mem (t := .range fun n ↦ f ⟨t, ht⟩ (g n)) _ (range_nonempty _)
  · refine ⟨?_, fun b hb ↦ csSup_le' ?_⟩ <;> rintro _ ⟨n, rfl⟩
    · apply (le_csSup (.of_not_isCofinal _) _).trans (le_csSup hg ⟨n + 1, rfl⟩)
      · exact fun hg' ↦ (cof_le hg').not_gt (mk_range_le.trans_lt hsα)
      · use ⟨t, ht⟩
    · exact (hf ⟨t, ht⟩ _).2.trans <| hb ⟨_, rfl⟩
  · grind

protected theorem iInter {ι : Type u} {f : ι → Set α} (hα : cof α ≠ ℵ₀)
    (hι : Cardinal.lift.{v} #ι < Cardinal.lift.{u} (cof α)) (hf : ∀ i, IsClub (f i)) :
    IsClub (⋂ i, f i) := by
  rw [← sInter_range]
  refine IsClub.sInter hα ?_ (by simpa)
  rw [← Cardinal.lift_lt]
  exact mk_range_le_lift.trans_lt hι

theorem sInter_of_countable {s : Set (Set α)} (hα : cof α ≠ ℵ₀) (hsα : s.Countable)
    (hs : ∀ x ∈ s, IsClub x) : IsClub (⋂₀ s) := by
  obtain hα | hα := hα.lt_or_gt
  · apply IsClub.sInter_of_cof_le_one _ hs
    rwa [← Order.cof_lt_aleph0_iff]
  · apply IsClub.sInter hα.ne' (hα.trans_le' _) hs
    rwa [le_aleph0_iff_set_countable]

theorem iInter_of_countable {ι : Sort*} {f : ι → Set α} [Countable ι] (hα : cof α ≠ ℵ₀)
    (hf : ∀ i, IsClub (f i)) : IsClub (⋂ i, f i) := by
  rw [← sInter_range]
  apply IsClub.sInter_of_countable hα (countable_range f)
  simpa

protected theorem inter (hα : cof α ≠ ℵ₀) (hs : IsClub s) (ht : IsClub t) : IsClub (s ∩ t) := by
  simpa [hs, ht] using IsClub.sInter_of_countable (s := {s, t}) hα

/-- Club sets are closed under diagonal intersections. -/
protected theorem diag [IsRegularCardinalOrder α] {f : α → Set α} (hα : cof α ≠ ℵ₀)
    (hf : ∀ a, IsClub (f a)) : IsClub {a | ∀ b < a, a ∈ f b} where
  dirSupClosed t ht ht₀ _ a ha b hb := by
    obtain ⟨c, hc, hbc, -⟩ := ha.exists_between hb
    apply (hf b).isLUB_mem _ ⟨c, _⟩ (ha.inter_Ici_of_mem hc) <;> grind
  isCofinal a := by
    obtain hα | hα := hα.lt_or_gt
    · rw [Order.cof_lt_aleph0_iff, cof_eq_cardinalMk, le_one_iff_subsingleton] at hα
      use a
      simp
    have : Nonempty α := ⟨a⟩
    have := (noTopOrder_iff_noMaxOrder α).1 <| one_lt_cof_iff.1 (one_lt_aleph0.trans hα)
    have (b : α) : ∃ c ∈ ⋂₀ (f '' Set.Iio b), b < c := by
      obtain ⟨b', hb'⟩ := exists_gt b
      have ⟨c, hc, hbc⟩ :=
        (IsClub.sInter (s := f '' Set.Iio b) hα.ne' (mk_image_le.trans_lt ?_) ?_).isCofinal b'
      · exact ⟨c, hc, hb'.trans_le hbc⟩
      · simp
      · simp [hf]
    choose g hg using this
    have hgm : StrictMono fun n ↦ g^[n] a := by
      apply strictMono_of_lt_add_one fun n _ ↦ ?_
      rw [← n.succ_eq_add_one, g.iterate_succ_apply']
      exact (hg _).2
    have hg' : IsLUB (.range fun n ↦ g^[n] a) (⨆ n, g^[n] a) := by
      refine isLUB_ciSup (.of_not_isCofinal fun h ↦ ?_)
      apply (Order.cof_le h).not_gt (hα.trans_le' _)
      simpa using mk_range_le_lift (f := fun n ↦ g^[n] a)
    refine ⟨⨆ n, g^[n] a, fun b hb ↦ ?_, hg'.1 ⟨0, rfl⟩⟩
    obtain ⟨_, ⟨n, rfl⟩, hb, hn⟩ := hg'.exists_between hb
    apply (hf b).isLUB_mem _ _ (hg'.inter_Ici_of_mem ⟨n + 1, rfl⟩)
    · rintro _ ⟨⟨m, rfl⟩, hm⟩
      rw [Set.mem_Ici, hgm.le_iff_le, Nat.add_one_le_iff] at hm
      cases m with
      | zero => contradiction
      | succ m =>
        simp_rw [g.iterate_succ_apply']
        rw [Nat.lt_add_one_iff] at hm
        simp_rw [Set.sInter_image, Set.mem_iInter] at hg
        exact (hg _).1 _ (hb.trans_le <| hgm.monotone hm)
    · use g^[n + 1] a; simp [- Function.iterate_succ]

theorem _root_.Order.IsNormal.isClub_range {f : α → α} (hf : IsNormal f) : IsClub (.range f) :=
  ⟨hf.dirSupClosed_range, fun x ↦ ⟨_, ⟨x, rfl⟩, hf.strictMono.le_apply⟩⟩

theorem _root_.Order.IsNormal.isClub_fixedPoints {f : α → α} (hα : cof α ≠ ℵ₀) (hf : IsNormal f) :
    IsClub f.fixedPoints := by
  cases isEmpty_or_nonempty α; · simp
  refine ⟨fun s hs hs₀ _ a ha ↦ (hf.map_isLUB ha hs₀).unique ?_, fun a ↦ ?_⟩
  · rwa [image_congr hs, image_id']
  · cases topOrderOrNoTopOrder α with
    | inl => use ⊤; simpa using! hf.strictMono.id_le ⊤
    | inr h =>
      rw [noTopOrder_iff_noMaxOrder] at h
      suffices BddAbove (.range fun n ↦ f^[n] a) from
        ⟨_, hf.iSup_iterate_mem_fixedPoints a this, le_csSup this ⟨0, rfl⟩⟩
      refine .of_not_isCofinal fun h ↦ (cof_le h).not_gt
        ((aleph0_le_cof.lt_of_ne' hα).trans_le' ?_)
      simpa using mk_range_le_lift (f := fun n : ℕ ↦ f^[n] a)

end WellFoundedLT
end IsClub

/-! ### Stationary sets -/

/-- A set is called stationary when it intersects all club sets. -/
@[expose]
def IsStationary (s : Set α) : Prop :=
  ∀ ⦃t⦄, IsClub t → (s ∩ t).Nonempty

theorem not_isStationary_iff : ¬ IsStationary s ↔ ∃ t, IsClub t ∧ Disjoint s t := by
  simp [IsStationary, disjoint_iff, not_nonempty_iff_eq_empty]

@[gcongr]
theorem IsStationary.mono (hs : IsStationary s) (h : s ⊆ t) : IsStationary t :=
  fun _u hu ↦ (hs hu).mono (inter_subset_inter_left _ h)

theorem IsStationary.nonempty (hs : IsStationary s) : s.Nonempty := by
  simpa using hs .univ

theorem isStationary_univ_iff : IsStationary (.univ (α := α)) ↔ Nonempty α := by
  simp [IsStationary, ← not_imp_not (b := IsClub _), not_nonempty_iff_eq_empty,
    isClub_empty_iff]

@[simp]
protected theorem IsStationary.univ [Nonempty α] : IsStationary (.univ (α := α)) :=
  isStationary_univ_iff.2 ‹_›

@[simp]
theorem not_isStationary_empty : ¬ IsStationary (∅ : Set α) := by
  intro h
  simpa using h .univ

@[simp]
theorem not_isStationary_of_isEmpty [IsEmpty α] : ¬ IsStationary s :=
  s.eq_empty_of_isEmpty ▸ not_isStationary_empty

theorem IsStationary.of_not_isCofinal_compl (hs : ¬ IsCofinal sᶜ) : IsStationary s := by
  intro t ht
  obtain ⟨a, ha⟩ := not_isCofinal_iff.1 hs
  obtain ⟨b, hb, hb'⟩ := ht.isCofinal a
  refine ⟨b, ?_, hb⟩
  contrapose! ha
  exact ⟨b, ha, hb'⟩

theorem isStationary_sUnion_iff_of_cof_le_one {s : Set (Set α)} (hα : cof α ≤ 1) :
    IsStationary (⋃₀ s) ↔ ∃ x ∈ s, IsStationary x where
  mp h := by
    contrapose! h
    simp_rw [not_isStationary_iff] at h ⊢
    choose f hf hxf using h
    refine ⟨⋂ x : s, f _ x.2, ?_, ?_⟩
    · apply IsClub.iInter_of_cof_le_one hα
      simpa
    · rw [disjoint_sUnion_left]
      exact fun x hx ↦ (hxf _ hx).mono_right (iInter_subset _ ⟨x, hx⟩)
  mpr := fun ⟨x, hxs, hx⟩ ↦ hx.mono (subset_sUnion_of_mem hxs)

theorem isStationary_iUnion_iff_of_cof_le_one {ι : Sort*} {f : ι → Set α} (hα : cof α ≤ 1) :
    IsStationary (⋃ i, f i) ↔ ∃ i, IsStationary (f i) := by
  rw [← sUnion_range, isStationary_sUnion_iff_of_cof_le_one hα]
  simp

theorem isStationary_sUnion_iff_of_orderTop [OrderTop α] {s : Set (Set α)} :
    IsStationary (⋃₀ s) ↔ ∃ x ∈ s, IsStationary x :=
  isStationary_sUnion_iff_of_cof_le_one (by simp)

theorem isStationary_iUnion_iff_of_orderTop [OrderTop α] {ι : Sort*} {f : ι → Set α} :
    IsStationary (⋃ i, f i) ↔ ∃ i, IsStationary (f i) :=
  isStationary_iUnion_iff_of_cof_le_one (by simp)

section WellFoundedLT
variable [WellFoundedLT α]

theorem IsClub.isStationary [Nonempty α] (hα : cof α ≠ ℵ₀) (hs : IsClub s) : IsStationary s :=
  fun _ ht ↦ (hs.inter hα ht).nonempty

theorem isStationary_sUnion_iff {s : Set (Set α)} (hα : cof α ≠ ℵ₀) (hsα : #s < cof α) :
    IsStationary (⋃₀ s) ↔ ∃ x ∈ s, IsStationary x where
  mp h := by
    contrapose! h
    simp_rw [not_isStationary_iff] at h ⊢
    choose f hf hxf using h
    refine ⟨⋂ x : s, f _ x.2, ?_, ?_⟩
    · apply IsClub.iInter hα <;> simpa
    · rw [disjoint_sUnion_left]
      exact fun x hx ↦ (hxf _ hx).mono_right (iInter_subset _ ⟨x, hx⟩)
  mpr := fun ⟨x, hxs, hx⟩ ↦ hx.mono (subset_sUnion_of_mem hxs)

theorem isStationary_iUnion_iff {ι : Type u} {f : ι → Set α} (hα : cof α ≠ ℵ₀)
    (hι : lift.{v} #ι < lift.{u} (cof α)) : IsStationary (⋃ i, f i) ↔ ∃ i, IsStationary (f i) := by
  rw [← sUnion_range, isStationary_sUnion_iff hα]
  · simp
  · rw [← Cardinal.lift_lt]
    exact mk_range_le_lift.trans_lt hι

theorem isStationary_sUnion_iff_of_countable {s : Set (Set α)} (hα : cof α ≠ ℵ₀)
    (hsα : s.Countable) : IsStationary (⋃₀ s) ↔ ∃ x ∈ s, IsStationary x := by
  obtain hα | hα := hα.lt_or_gt
  · apply isStationary_sUnion_iff_of_cof_le_one
    rwa [← Order.cof_lt_aleph0_iff]
  · apply isStationary_sUnion_iff hα.ne' (hα.trans_le' _)
    rwa [le_aleph0_iff_set_countable]

theorem isStationary_iUnion_iff_of_countable {ι : Sort*} {f : ι → Set α} [Countable ι]
    (hα : cof α ≠ ℵ₀) : IsStationary (⋃ i, f i) ↔ ∃ i, IsStationary (f i) := by
  rw [← sUnion_range, isStationary_sUnion_iff_of_countable hα (countable_range f)]
  simp

theorem isStationary_union_iff (hα : cof α ≠ ℵ₀) :
    IsStationary (s ∪ t) ↔ IsStationary s ∨ IsStationary t := by
  simpa using isStationary_sUnion_iff_of_countable (s := {s, t}) hα

/-- **Fodor's lemma**, or the **pressing down lemma**: if `α` has the order type of a regular
cardinal, `s` is a stationary set, and `f : α → α` is a regressive function on `s`, there exists
some stationary subset of `s` which is constant on `f`. -/
theorem exists_isStationary_preimage_singleton [IsRegularCardinalOrder α] {f : α → α}
    (hα : cof α ≠ ℵ₀) (hs : IsStationary s) (hf : ∀ x ∈ s, f x < x) :
    ∃ a, IsStationary (s ∩ f ⁻¹' {a}) := by
  unfold IsStationary
  by_contra!
  choose g hg using this
  simp_rw [Set.eq_empty_iff_forall_notMem] at hg
  obtain ⟨a, hs, ha⟩ := hs <| .diag hα fun a ↦ (hg a).1
  apply (hg (f a)).2 a
  grind

end WellFoundedLT
