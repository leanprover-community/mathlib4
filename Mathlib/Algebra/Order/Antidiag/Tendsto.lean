/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Finite
public import Mathlib.Algebra.Order.Antidiag.Prod
public import Mathlib.Order.Filter.TendstoCofinite

/-!
# Antidiagonal tendsto

`Finset.HasAntidiagonal.tendsto_sup'_antidiagonal_cofinite`:
  If a function `f : M × M → R` on a Finset `M`, that has the antidiagonal propertry,
  tends to a filter `F` under the cofinite filter then so does
  the function assigning to `x : M` its supremum of its antidiagonal.

`Finset.HasMulAntidiagonal.tendstoCofinite_mul`:
  When a magma satisfies the `HasMulAntidiagonal` property, its multiplication map has
  finite fibers.

-/

public section

open Filter

namespace Finset.HasAntidiagonal

variable {M R : Type*} [AddZeroClass M] [HasAntidiagonal M] {f : M × M → R} [LinearOrder R]
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

namespace Finset.HasMulAntidiagonal

variable {N : Type*} [Mul N] [HasMulAntidiagonal N]

/-- When a magma satisfies the `HasMulAntidiagonal` property, its multiplication map has
finite fibers.

For the reverse implication, see `Filter.TendstoCofinite.hasMulAntidiagonal`. -/
@[to_additive /-- When an additive magma satisfies the `HasMulAntidiagonal` property,
its addition map has finite fibers.

For the reverse implication, see `Filter.TendstoCofinite.hasAntidiagonal`-/]
instance tendstoCofinite_mul : TendstoCofinite fun (p : N × N) ↦ p.1 * p.2 := by
  simp [tendstoCofinite_iff_finite_preimage_singleton, ← coe_mulAntidiagonal_eq_preimage_singleton]

end Finset.HasMulAntidiagonal
