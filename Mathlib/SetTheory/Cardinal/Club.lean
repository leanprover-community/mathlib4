/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.SetTheory.Cardinal.Cofinality
public import Mathlib.Order.DirSupClosed

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

@[expose] public section

universe u v

open Cardinal Order

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
theorem IsClub.of_isEmpty [IsEmpty α] (s : Set α) : IsClub s :=
  ⟨.of_isEmpty s, .of_isEmpty s⟩

@[simp]
theorem IsClub.univ : IsClub (.univ (α := α)) :=
  ⟨.univ, .univ⟩

-- Depends on #37304.
proof_wanted IsClub.union (hs : IsClub s) (ht : IsClub t) : IsClub (s ∪ t)

theorem IsClub.isLUB_mem (hs : IsClub s) (ht : t ⊆ s) (ht₀ : t.Nonempty) (hx : IsLUB t x) : x ∈ s :=
  hs.dirSupClosed ht ht₀ (Std.Total.directedOn _) hx

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
  · rw [cof_lt_aleph0_iff] at hα
    exact .sInter_of_cof_le_one hα H
  · exact .sInter hα (hα'.trans_le' <| by simp) H

theorem IsNormal.isClub_fixedPoints {f : α → α} (hα : cof α ≠ ℵ₀) (hf : IsNormal f) :
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
