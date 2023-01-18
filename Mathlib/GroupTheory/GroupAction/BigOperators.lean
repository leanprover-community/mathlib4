/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module group_theory.group_action.big_operators
! leanprover-community/mathlib commit 008205aa645b3f194c1da47025c5f110c8406eab
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.BigOperators.Basic
import Mathbin.Data.Finset.Basic
import Mathbin.Data.Multiset.Basic
import Mathbin.GroupTheory.GroupAction.Defs

/-!
# Lemmas about group actions on big operators

Note that analogous lemmas for `module`s like `finset.sum_smul` appear in other files.
-/


variable {α β γ : Type _}

open BigOperators

section

variable [AddMonoid β] [DistribSMul α β]

theorem List.smul_sum {r : α} {l : List β} : r • l.Sum = (l.map ((· • ·) r)).Sum :=
  (DistribSMul.toAddMonoidHom β r).map_list_sum l
#align list.smul_sum List.smul_sum

end

section

variable [Monoid α] [Monoid β] [MulDistribMulAction α β]

theorem List.smul_prod {r : α} {l : List β} : r • l.Prod = (l.map ((· • ·) r)).Prod :=
  (MulDistribMulAction.toMonoidHom β r).map_list_prod l
#align list.smul_prod List.smul_prod

end

section

variable [AddCommMonoid β] [DistribSMul α β]

theorem Multiset.smul_sum {r : α} {s : Multiset β} : r • s.Sum = (s.map ((· • ·) r)).Sum :=
  (DistribSMul.toAddMonoidHom β r).map_multiset_sum s
#align multiset.smul_sum Multiset.smul_sum

theorem Finset.smul_sum {r : α} {f : γ → β} {s : Finset γ} :
    (r • ∑ x in s, f x) = ∑ x in s, r • f x :=
  (DistribSMul.toAddMonoidHom β r).map_sum f s
#align finset.smul_sum Finset.smul_sum

end

section

variable [Monoid α] [CommMonoid β] [MulDistribMulAction α β]

theorem Multiset.smul_prod {r : α} {s : Multiset β} : r • s.Prod = (s.map ((· • ·) r)).Prod :=
  (MulDistribMulAction.toMonoidHom β r).map_multiset_prod s
#align multiset.smul_prod Multiset.smul_prod

theorem Finset.smul_prod {r : α} {f : γ → β} {s : Finset γ} :
    (r • ∏ x in s, f x) = ∏ x in s, r • f x :=
  (MulDistribMulAction.toMonoidHom β r).map_prod f s
#align finset.smul_prod Finset.smul_prod

end

