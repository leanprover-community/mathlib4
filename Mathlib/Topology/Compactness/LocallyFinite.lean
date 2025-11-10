/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/

import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Compactness.Compact

/-!
# Compact sets and compact spaces and locally finite functions
-/

open Set

variable {X ι : Type*} [TopologicalSpace X] {s : Set X}

namespace LocallyFinite

/-- If `s` is a compact set in a topological space `X` and `f : ι → Set X` is a locally finite
family of sets, then `f i ∩ s` is nonempty only for a finitely many `i`. -/
theorem finite_nonempty_inter_compact {f : ι → Set X}
    (hf : LocallyFinite f) (hs : IsCompact s) : { i | (f i ∩ s).Nonempty }.Finite := by
  choose U hxU hUf using hf
  rcases hs.elim_nhds_subcover U fun x _ => hxU x with ⟨t, -, hsU⟩
  refine (t.finite_toSet.biUnion fun x _ => hUf x).subset ?_
  rintro i ⟨x, hx⟩
  rcases mem_iUnion₂.1 (hsU hx.2) with ⟨c, hct, hcx⟩
  exact mem_biUnion hct ⟨x, hx.1, hcx⟩

/-- If `X` is a compact space, then a locally finite family of sets of `X` can have only finitely
many nonempty elements. -/
theorem finite_nonempty_of_compact [CompactSpace X] {f : ι → Set X}
    (hf : LocallyFinite f) : { i | (f i).Nonempty }.Finite := by
  simpa only [inter_univ] using hf.finite_nonempty_inter_compact isCompact_univ

/-- If `X` is a compact space, then a locally finite family of nonempty sets of `X` can have only
finitely many elements, `Set.Finite` version. -/
theorem finite_of_compact [CompactSpace X] {f : ι → Set X}
    (hf : LocallyFinite f) (hne : ∀ i, (f i).Nonempty) : (univ : Set ι).Finite := by
  simpa only [hne] using hf.finite_nonempty_of_compact

/-- If `X` is a compact space, then a locally finite family of nonempty sets of `X` can have only
finitely many elements, `Fintype` version. -/
noncomputable def fintypeOfCompact [CompactSpace X] {f : ι → Set X}
    (hf : LocallyFinite f) (hne : ∀ i, (f i).Nonempty) : Fintype ι :=
  fintypeOfFiniteUniv (hf.finite_of_compact hne)

end LocallyFinite
