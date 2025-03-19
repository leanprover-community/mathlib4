import Mathlib.Data.Nat.Count

variable {p} [DecidablePred p] {a b : ℕ}

lemma count_lt_count_iff_exists : (a.count p < b.count p) ↔ ∃ x : Set.Ico a b, p x := by
  refine ⟨fun h ↦ ?_, fun ⟨⟨x, ha, hb⟩, hx⟩ ↦ ?_⟩
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt (Nat.lt_of_count_lt_count h)
    rw [hk, add_assoc, Nat.count_add] at h
    have := Nat.lt_add_right_iff_pos.mp h
    obtain ⟨t, _, pat⟩ := Nat.exists_of_count_ne <| Nat.ne_zero_of_lt this
    exact ⟨⟨a + t, by simp, by rwa [hk, add_assoc _ k, add_lt_add_iff_left a]⟩, pat⟩
  · sorry

lemma count_lt_count_iff_exists_finset : (a.count p < b.count p) ↔ ∃ S : Finset (Set.Ico a b), S.card = y ∧ ∀ p x := by
  sorry
