/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Algebra.Module.Basic

#align_import group_theory.group_action.big_operators from "leanprover-community/mathlib"@"008205aa645b3f194c1da47025c5f110c8406eab"

/-!
# Lemmas about group actions on big operators

Note that analogous lemmas for `Module`s like `Finset.sum_smul` appear in other files.
-/


variable {α β γ : Type*}

open BigOperators

section

variable [AddMonoid β] [DistribSMul α β]

theorem List.smul_sum {r : α} {l : List β} : r • l.sum = (l.map ((· • ·) r)).sum :=
  (DistribSMul.toAddMonoidHom β r).map_list_sum l
#align list.smul_sum List.smul_sum

end

section

variable [Monoid α] [Monoid β] [MulDistribMulAction α β]

theorem List.smul_prod {r : α} {l : List β} : r • l.prod = (l.map ((· • ·) r)).prod :=
  (MulDistribMulAction.toMonoidHom β r).map_list_prod l
#align list.smul_prod List.smul_prod

end

section

variable [AddCommMonoid β]

theorem Multiset.smul_sum [DistribSMul α β] {r : α} {s : Multiset β} :
    r • s.sum = (s.map ((· • ·) r)).sum :=
  (DistribSMul.toAddMonoidHom β r).map_multiset_sum s
#align multiset.smul_sum Multiset.smul_sum

theorem Finset.smul_sum [DistribSMul α β] {r : α} {f : γ → β} {s : Finset γ} :
    (r • ∑ x in s, f x) = ∑ x in s, r • f x :=
  (DistribSMul.toAddMonoidHom β r).map_sum f s
#align finset.smul_sum Finset.smul_sum

theorem Multiset.sum_smul [Semiring α] [Module α β] {r : β} {s : Multiset α} :
    s.sum • r = (s.map (. • r)).sum :=
  ((smulAddHom α β).flip <| r).map_multiset_sum s

theorem Finset.sum_smul [Semiring α] [Module α β] {r : β} {f : γ → α} {s : Finset γ} :
    (∑ x in s, f x) • r = ∑ x in s, f x • r :=
  ((smulAddHom α β).flip <| r).map_sum f s

end

section

variable [Monoid α] [CommMonoid β] [MulDistribMulAction α β]

theorem Multiset.smul_prod {r : α} {s : Multiset β} : r • s.prod = (s.map ((· • ·) r)).prod :=
  (MulDistribMulAction.toMonoidHom β r).map_multiset_prod s
#align multiset.smul_prod Multiset.smul_prod

theorem Finset.smul_prod {r : α} {f : γ → β} {s : Finset γ} :
    (r • ∏ x in s, f x) = ∏ x in s, r • f x :=
  (MulDistribMulAction.toMonoidHom β r).map_prod f s
#align finset.smul_prod Finset.smul_prod

end
