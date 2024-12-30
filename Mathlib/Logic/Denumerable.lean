theorem ofNat_surjective : Surjective (ofNat s)
  | ⟨x, hx⟩ => by
    set t : List s :=
      ((List.range x).filter fun y => y ∈ s).pmap
        (fun (y : ℕ) (hy : y ∈ s) => ⟨y, hy⟩)
        (by intros a ha; simpa using (List.mem_filter.mp ha).2) with ht
    have hmt : ∀ {y : s}, y ∈ t ↔ y < ⟨x, hx⟩ := by
      simp [List.mem_filter, Subtype.ext_iff_val, ht]
    cases' hmax : List.maximum t with m
    · refine ⟨0, le_antisymm bot_le (le_of_not_gt fun h => List.not_mem_nil (⊥ : s) ?_)⟩
      rwa [← List.maximum_eq_bot.1 hmax, hmt]
    have wf : ↑m < x := by simpa using hmt.mp (List.maximum_mem hmax)
    rcases ofNat_surjective m with ⟨a, rfl⟩
    refine ⟨a + 1, le_antisymm (succ_le_of_lt wf) ?_⟩
    exact le_succ_of_forall_lt_le fun z hz => List.le_maximum_of_mem (hmt.2 hz) hmax
  termination_by n => n.val
