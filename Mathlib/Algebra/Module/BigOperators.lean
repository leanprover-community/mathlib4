/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yury Kudryashov, Yaël Dillies
-/
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.Module.Defs
import Mathlib.Data.Fintype.BigOperators

/-!
# Finite sums over modules over a ring
-/

variable {ι κ α β R M : Type*}

section AddCommMonoid

variable [Semiring R] [AddCommMonoid M] [Module R M]

theorem List.sum_smul {l : List R} {x : M} : l.sum • x = (l.map fun r ↦ r • x).sum :=
  map_list_sum ((smulAddHom R M).flip x) l

theorem Multiset.sum_smul {l : Multiset R} {x : M} : l.sum • x = (l.map fun r ↦ r • x).sum :=
  ((smulAddHom R M).flip x).map_multiset_sum l

theorem Multiset.sum_smul_sum {s : Multiset R} {t : Multiset M} :
    s.sum • t.sum = ((s ×ˢ t).map fun p : R × M ↦ p.fst • p.snd).sum := by
  induction' s using Multiset.induction with a s ih
  · simp
  · simp [add_smul, ih, ← Multiset.smul_sum]

theorem Finset.sum_smul {f : ι → R} {s : Finset ι} {x : M} :
    (∑ i ∈ s, f i) • x = ∑ i ∈ s, f i • x := map_sum ((smulAddHom R M).flip x) f s

lemma Finset.sum_smul_sum (s : Finset α) (t : Finset β) {f : α → R} {g : β → M} :
    (∑ i ∈ s, f i) • ∑ j ∈ t, g j = ∑ i ∈ s, ∑ j ∈ t, f i • g j := by
  simp_rw [sum_smul, ← smul_sum]

lemma Fintype.sum_smul_sum [Fintype α] [Fintype β] (f : α → R) (g : β → M) :
    (∑ i, f i) • ∑ j, g j = ∑ i, ∑ j, f i • g j := Finset.sum_smul_sum _ _

end AddCommMonoid

open Finset

theorem Finset.cast_card [NonAssocSemiring R] (s : Finset α) : (#s : R) = ∑ _ ∈ s, 1 := by
  rw [Finset.sum_const, Nat.smul_one_eq_cast]

namespace Fintype
variable [DecidableEq ι] [Fintype ι] [AddCommMonoid α]

lemma sum_piFinset_apply (f : κ → α) (s : Finset κ) (i : ι) :
    ∑ g ∈ piFinset fun _ : ι ↦ s, f (g i) = #s ^ (card ι - 1) • ∑ b ∈ s, f b := by
  classical
  rw [Finset.sum_comp]
  simp only [eval_image_piFinset_const, card_filter_piFinset_const s, ite_smul, zero_smul, smul_sum,
    Finset.sum_ite_mem, inter_self]

end Fintype
