/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Algebra.BigOperators.Finprod

/-!
# Lemmas about group actions on big operators

Note that analogous lemmas for `Module`s like `Finset.sum_smul` appear in other files.
-/


variable {α β γ : Type*}

section

variable [AddMonoid β] [DistribSMul α β]

theorem List.smul_sum {r : α} {l : List β} : r • l.sum = (l.map (r • ·)).sum :=
  map_list_sum (DistribSMul.toAddMonoidHom β r) l

end

section

variable [Monoid α] [Monoid β] [MulDistribMulAction α β]

theorem List.smul_prod {r : α} {l : List β} : r • l.prod = (l.map (r • ·)).prod :=
  map_list_prod (MulDistribMulAction.toMonoidHom β r) l

end

section

variable [AddCommMonoid β] [DistribSMul α β]

theorem Multiset.smul_sum {r : α} {s : Multiset β} : r • s.sum = (s.map (r • ·)).sum :=
  (DistribSMul.toAddMonoidHom β r).map_multiset_sum s

theorem Finset.smul_sum {r : α} {f : γ → β} {s : Finset γ} :
    (r • ∑ x ∈ s, f x) = ∑ x ∈ s, r • f x :=
  map_sum (DistribSMul.toAddMonoidHom β r) f s

end

section

variable [Monoid α] [CommMonoid β] [MulDistribMulAction α β]

theorem Multiset.smul_prod {r : α} {s : Multiset β} : r • s.prod = (s.map (r • ·)).prod :=
  (MulDistribMulAction.toMonoidHom β r).map_multiset_prod s

theorem Finset.smul_prod {r : α} {f : γ → β} {s : Finset γ} :
    (r • ∏ x ∈ s, f x) = ∏ x ∈ s, r • f x :=
  map_prod (MulDistribMulAction.toMonoidHom β r) f s

theorem smul_finprod {ι : Sort*} [Finite ι] {f : ι → β} (r : α) :
    r • ∏ᶠ x : ι, f x = ∏ᶠ x : ι, r • (f x) := by
  cases nonempty_fintype (PLift ι)
  simp only [finprod_eq_prod_plift_of_mulSupport_subset (s := Finset.univ) (by simp),
    finprod_eq_prod_of_fintype, Finset.smul_prod]

end
