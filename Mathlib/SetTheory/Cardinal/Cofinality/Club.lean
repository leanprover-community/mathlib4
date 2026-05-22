/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal

/-!
# Club sets

A subset of a well-ordered type `α` is called a club set when it is closed in the order topology and
cofinal. If `α` has no maximum, then an equivalent condition is that `α` is closed and unbounded;
hence the name.

## Implementation notes

To avoid importing topology in the ordinals, we spell out the closure property using `DirSupClosed`.
For any type equipped with the Scott-Hausdorff topology (which includes well-orders with the order
topology), `DirSupClosed s` and `IsClosed s` are equivalent predicates.
-/

public section

universe u v

open Cardinal Order Ordinal

/-- A club set is closed under suprema and cofinal. -/
structure IsClub {α : Type*} [LinearOrder α] (s : Set α) where
  /-- Club sets are closed under suprema. If `α` is a well-order with the order topology, this
  condition is equivalent to `IsClosed s`. -/
  dirSupClosed : DirSupClosed s
  /-- Club sets are cofinal. If `α` has no maximum, this condition is equivalent to `¬ BddAbove s`.
  See `not_bddAbove_iff_isCofinal`. -/
  isCofinal : IsCofinal s

variable {α : Type v} {s t : Set α} {x : α} [LinearOrder α]

@[simp]
theorem IsClub.of_isEmpty [IsEmpty α] {s : Set α} : IsClub s :=
  ⟨.of_isEmpty, .of_isEmpty⟩

@[simp]
theorem IsClub.univ : IsClub (α := α) .univ :=
  ⟨.univ, .univ⟩

protected theorem IsClub.nonempty [Nonempty α] (hs : IsClub s) : s.Nonempty :=
  hs.isCofinal.nonempty

theorem isClub_empty_iff : IsClub (α := α) ∅ ↔ IsEmpty α :=
  ⟨fun h ↦ isCofinal_empty_iff.1 h.isCofinal, fun _ ↦ .of_isEmpty⟩

theorem IsClub.union (hs : IsClub s) (ht : IsClub t) : IsClub (s ∪ t) :=
  ⟨hs.dirSupClosed.union ht.dirSupClosed, hs.isCofinal.mono Set.subset_union_left⟩

theorem IsClub.isLUB_mem (hs : IsClub s) (ht : t ⊆ s) (ht₀ : t.Nonempty) (hx : IsLUB t x) : x ∈ s :=
  hs.dirSupClosed ht ht₀ (.of_linearOrder _) hx

theorem IsClub.csSup_mem {α} [ConditionallyCompleteLinearOrder α] {s t : Set α}
    (hs : IsClub s) (ht : t ⊆ s) (ht₀ : t.Nonempty) (ht₁ : BddAbove t) : sSup t ∈ s :=
  hs.isLUB_mem ht ht₀ (isLUB_csSup ht₀ ht₁)

theorem IsClub.sInter_of_orderTop {s : Set (Set α)} [OrderTop α]
    (hs : ∀ x ∈ s, IsClub x) : IsClub (⋂₀ s) := by
  refine ⟨.sInter fun x hx ↦ (hs x hx).dirSupClosed, ?_⟩
  rw [isCofinal_iff_top_mem, Set.mem_sInter]
  exact fun x hx ↦ (hs x hx).isCofinal.top_mem

theorem IsClub.iInter_of_orderTop {ι : Type*} {f : ι → Set α} [OrderTop α]
    (hs : ∀ i, IsClub (f i)) : IsClub (⋂ i, f i) := by
  rw [← Set.sInter_range]
  exact .sInter_of_orderTop (by simpa)

theorem IsClub.sInter_of_cof_le_one {s : Set (Set α)} (hα : cof α ≤ 1)
    (hs : ∀ x ∈ s, IsClub x) : IsClub (⋂₀ s) := by
  cases isEmpty_or_nonempty α; · simp
  cases topOrderOrNoTopOrder α
  · exact .sInter_of_orderTop hs
  · cases one_lt_cof.not_ge hα

theorem IsClub.iInter_of_cof_le_one {ι : Type*} {f : ι → Set α} (hα : cof α ≤ 1)
    (hs : ∀ i, IsClub (f i)) : IsClub (⋂ i, f i) := by
  rw [← Set.sInter_range]
  exact .sInter_of_cof_le_one hα (by simpa)

section WellFoundedLT

variable [WellFoundedLT α]

attribute [local instance]
  WellFoundedLT.toOrderBot WellFoundedLT.conditionallyCompleteLinearOrderBot

theorem IsClub.sInter {s : Set (Set α)} (hα : cof α ≠ ℵ₀) (hsα : #s < cof α)
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
  apply (hs t ht).isLUB_mem (t := .range fun n ↦ f ⟨t, ht⟩ (g n)) _ (Set.range_nonempty _)
  · refine ⟨?_, fun b hb ↦ csSup_le' ?_⟩ <;> rintro _ ⟨n, rfl⟩
    · apply (le_csSup (.of_not_isCofinal _) _).trans (le_csSup hg ⟨n + 1, rfl⟩)
      · exact fun hg' ↦ (cof_le hg').not_gt (mk_range_le.trans_lt hsα)
      · use ⟨t, ht⟩
    · exact (hf ⟨t, ht⟩ _).2.trans <| hb ⟨_, rfl⟩
  · grind

theorem IsClub.iInter {ι : Type u} {f : ι → Set α} (hα : cof α ≠ ℵ₀)
    (hι : Cardinal.lift.{v} #ι < Cardinal.lift.{u} (cof α)) (hf : ∀ i, IsClub (f i)) :
    IsClub (⋂ i, f i) := by
  rw [← Set.sInter_range]
  refine IsClub.sInter hα ?_ (by simpa)
  rw [← Cardinal.lift_lt]
  exact mk_range_le_lift.trans_lt hι

theorem IsClub.inter {s t : Set α} (hα : cof α ≠ ℵ₀) (hs : IsClub s) (ht : IsClub t) :
    IsClub (s ∩ t) := by
  rw [← Set.sInter_pair]
  have H : ∀ x ∈ ({s, t} : Set _), IsClub x := by simpa [hs]
  obtain hα | hα' := hα.lt_or_gt
  · rw [Order.cof_lt_aleph0_iff] at hα
    exact .sInter_of_cof_le_one hα H
  · exact .sInter hα (hα'.trans_le' <| by simp) H

theorem Order.IsNormal.isClub_range {f : α → α} (hf : IsNormal f) : IsClub (.range f) :=
  ⟨hf.dirSupClosed_range, fun x ↦ ⟨_, ⟨x, rfl⟩, hf.strictMono.le_apply⟩⟩

theorem Order.IsNormal.isClub_fixedPoints {f : α → α} (hα : cof α ≠ ℵ₀) (hf : IsNormal f) :
    IsClub f.fixedPoints := by
  cases isEmpty_or_nonempty α; · simp
  refine ⟨fun s hs hs₀ _ a ha ↦ (hf.map_isLUB ha hs₀).unique ?_, fun a ↦ ?_⟩
  · rwa [Set.image_congr hs, Set.image_id']
  · cases topOrderOrNoTopOrder α with
    | inl => use ⊤; simpa using hf.strictMono.id_le ⊤
    | inr h =>
      rw [noTopOrder_iff_noMaxOrder] at h
      suffices BddAbove (.range fun n ↦ f^[n] a) from
        ⟨_, hf.iSup_iterate_mem_fixedPoints a this, le_csSup this ⟨0, rfl⟩⟩
      refine .of_not_isCofinal fun h ↦ (cof_le h).not_gt
        ((aleph0_le_cof.lt_of_ne' hα).trans_le' ?_)
      simpa using mk_range_le_lift (f := fun n : ℕ ↦ f^[n] a)

end WellFoundedLT

/-! ### Stationary sets -/

/-- A set is called stationary when it intersects all club sets. -/
@[expose]
def IsStationary (s : Set α) : Prop :=
  ∀ ⦃t⦄, IsClub t → (s ∩ t).Nonempty

@[gcongr]
theorem IsStationary.mono (hs : IsStationary s) (h : s ⊆ t) : IsStationary t :=
  fun _u hu ↦ (hs hu).mono (Set.inter_subset_inter_left _ h)

theorem IsStationary.nonempty (hs : IsStationary s) : s.Nonempty := by
  simpa using hs .univ

theorem isStationary_univ_iff : IsStationary (.univ (α := α)) ↔ Nonempty α := by
  simp [IsStationary, ← not_imp_not (b := IsClub _), Set.not_nonempty_iff_eq_empty,
    isClub_empty_iff]

@[simp]
theorem IsStationary.univ [Nonempty α] : IsStationary (.univ (α := α)) :=
  isStationary_univ_iff.2 ‹_›

@[simp]
theorem not_isStationary_empty : ¬ IsStationary (∅ : Set α) := by
  intro h
  simpa using h .univ

theorem IsClub.isStationary [Nonempty α] [WellFoundedLT α] (hα : cof α ≠ ℵ₀) (hs : IsClub s) :
    IsStationary s :=
  fun _ ht ↦ (hs.inter hα ht).nonempty

/-- Non-stationary sets form an ideal. -/
theorem not_isStationary_union [WellFoundedLT α] (hα : cof α ≠ ℵ₀)
    (hs : ¬ IsStationary s) (ht : ¬ IsStationary t) : ¬ IsStationary (s ∪ t) := by
  simp_rw [IsStationary, not_forall, Set.not_nonempty_iff_eq_empty] at hs ht ⊢
  obtain ⟨u, hu, hsu⟩ := hs
  obtain ⟨v, hv, htv⟩ := ht
  refine ⟨_, hu.inter hα hv, ?_⟩
  grind

theorem IsStationary.of_not_isCofinal_compl (hs : ¬ IsCofinal (sᶜ)) : IsStationary s := by
  intro t ht
  obtain ⟨a, ha⟩ := not_isCofinal_iff.1 hs
  obtain ⟨b, hb, hb'⟩ := ht.isCofinal a
  refine ⟨b, ?_, hb⟩
  contrapose! ha
  exact ⟨b, ha, hb'⟩

theorem isStationary_iff_not_isCofinal_compl [WellFoundedLT α] (hα : cof α ≤ ℵ₀) :
    IsStationary s ↔ ¬ IsCofinal (sᶜ) where
  mp hs h := by
    obtain ⟨t, hts, ht, htα⟩ := ord_cof_eq_of_isCofinal h
    have ht' := dirSupClosed_of_type_le_omega0 ht (htα.trans_le ?_)
    · cases hs ⟨ht', ht⟩
      grind
    · simpa using ord_mono hα
  mpr := .of_not_isCofinal_compl
