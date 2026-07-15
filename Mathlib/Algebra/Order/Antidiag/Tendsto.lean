/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Finite
public import Mathlib.Algebra.Order.Antidiag.Prod
public import Mathlib.Order.Filter.Cofinite

/-!
# Antidiagonal tendsto

`tendsto_sup'_antidiagonal_cofinite`: If a function `f : M × M → R` on a Finset `M`, that has the
  antidiagonal propertry,  tends to to a filter `F` under the cofinite filter then so does the
  function assigning to `x : M` its supremum of its antidiagonal.
-/

@[expose] public section

namespace Finset.HasAntidiagonal

open Filter

variable {M R : Type*} [AddMonoid M] [HasAntidiagonal M] {f : M × M → R} [LinearOrder R]
  {F : Filter R}

lemma tendsto_sup'_antidiagonal_cofinite (hf : Tendsto f cofinite F) : Tendsto
    (fun a ↦ (Finset.antidiagonal a).sup' (nonempty_antidiagonal _) f) cofinite F := by
  intro U hU
  refine ((((hf hU).image Prod.fst)).add ((hf hU).image Prod.snd)).subset ?_
  simp only [Set.subset_def, Set.mem_compl_iff, Set.mem_preimage]
  intro x hx
  obtain ⟨i, hi, e⟩ := Finset.exists_mem_eq_sup' (nonempty_antidiagonal x) f
  obtain rfl : i.1 + i.2 = x := by simpa using hi
  exact Set.add_mem_add (by simpa using ⟨i.2, e ▸ hx⟩) (by simpa using ⟨i.1, e ▸ hx⟩)

end Finset.HasAntidiagonal
