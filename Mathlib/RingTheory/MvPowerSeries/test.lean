import Mathlib

lemma tendsto_sup'_antidiagonal_cofinite
    {M R : Type*} [AddMonoid M] [Finset.HasAntidiagonal M] {f : M × M → R}
    [LinearOrder R] {F : Filter R} (hf : Tendsto f cofinite F) :
    Tendsto (fun a ↦ (Finset.antidiagonal a).sup' (Finset.nonempty_antidiagonal _) f)
      cofinite F := by
  intro U hU
  refine ((((hf hU).image Prod.fst)).add ((hf hU).image Prod.snd)).subset ?_
  simp only [Set.subset_def, Set.mem_compl_iff, Set.mem_preimage]
  intro x hx
  obtain ⟨i, hi, e⟩ := Finset.exists_mem_eq_sup' (Finset.nonempty_antidiagonal x) f
  obtain rfl : i.1 + i.2 = x := by simpa using hi
  exact Set.add_mem_add (by simpa using ⟨i.2, e ▸ hx⟩) (by simpa using ⟨i.1, e ▸ hx⟩)
