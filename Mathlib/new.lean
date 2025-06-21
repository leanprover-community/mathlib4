import Mathlib

lemma WithBot.WithTop.coe_biSup {α : Type*} {ι : Type*} {s : Set ι} (hs : s.Nonempty)
    [CompleteLinearOrder α] {f : ι → (WithTop α)} :
    ⨆ i ∈ s, f i = ⨆ i ∈ s, (f i : WithBot (WithTop α)) := by
  rcases hs with ⟨j, hj⟩
  have : Nonempty ι := Nonempty.intro j
  refine le_antisymm ((WithBot.coe_iSup (OrderTop.bddAbove _)).trans_le <|
    iSup_le_iff.mpr (fun i ↦ ?_)) <| iSup_le_iff.mpr <| fun _ ↦ iSup_le_iff.mpr <|
      fun hi ↦ WithBot.coe_le_coe.mpr (le_biSup _ hi)
  by_cases h : i ∈ s
  · simp only [iSup_pos h]
    apply le_biSup _ h
  · simpa [iSup_neg h] using le_trans (by simp) (le_biSup _ hj)
