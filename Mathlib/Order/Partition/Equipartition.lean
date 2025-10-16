/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Set.Equitable
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Partition.Finpartition
import Mathlib.Tactic.ApplyFun

/-!
# Finite equipartitions

This file defines finite equipartitions, the partitions whose parts all are the same size up to a
difference of `1`.

## Main declarations

* `Finpartition.IsEquipartition`: Predicate for a `Finpartition` to be an equipartition.
* `Finpartition.IsEquipartition.exists_partPreservingEquiv`: part-preserving enumeration of a finset
  equipped with an equipartition. Indices of elements in the same part are congruent modulo
  the number of parts.
-/


open Finset Fintype

namespace Finpartition

variable {α : Type*} [DecidableEq α] {s t : Finset α} (P : Finpartition s)

/-- An equipartition is a partition whose parts are all the same size, up to a difference of `1`. -/
def IsEquipartition : Prop :=
  (P.parts : Set (Finset α)).EquitableOn card

theorem isEquipartition_iff_card_parts_eq_average :
    P.IsEquipartition ↔
      ∀ a : Finset α, a ∈ P.parts → #a = #s / #P.parts ∨ #a = #s / #P.parts + 1 := by
  simp_rw [IsEquipartition, Finset.equitableOn_iff, P.sum_card_parts]

variable {P}

lemma not_isEquipartition :
    ¬P.IsEquipartition ↔ ∃ a ∈ P.parts, ∃ b ∈ P.parts, #b + 1 < #a := Set.not_equitableOn

theorem _root_.Set.Subsingleton.isEquipartition (h : (P.parts : Set (Finset α)).Subsingleton) :
    P.IsEquipartition :=
  Set.Subsingleton.equitableOn h _

theorem IsEquipartition.card_parts_eq_average (hP : P.IsEquipartition) (ht : t ∈ P.parts) :
    #t = #s / #P.parts ∨ #t = #s / #P.parts + 1 :=
  P.isEquipartition_iff_card_parts_eq_average.1 hP _ ht

theorem IsEquipartition.card_part_eq_average_iff (hP : P.IsEquipartition) (ht : t ∈ P.parts) :
    #t = #s / #P.parts ↔ #t ≠ #s / #P.parts + 1 := by
  have a := hP.card_parts_eq_average ht
  cutsat

theorem IsEquipartition.average_le_card_part (hP : P.IsEquipartition) (ht : t ∈ P.parts) :
    #s / #P.parts ≤ #t := by
  rw [← P.sum_card_parts]
  exact Finset.EquitableOn.le hP ht

theorem IsEquipartition.card_part_le_average_add_one (hP : P.IsEquipartition) (ht : t ∈ P.parts) :
    #t ≤ #s / #P.parts + 1 := by
  rw [← P.sum_card_parts]
  exact Finset.EquitableOn.le_add_one hP ht

theorem IsEquipartition.filter_ne_average_add_one_eq_average (hP : P.IsEquipartition) :
    {p ∈ P.parts | ¬#p = #s / #P.parts + 1} = {p ∈ P.parts | #p = #s / #P.parts} := by
  ext p
  simp only [mem_filter, and_congr_right_iff]
  exact fun hp ↦ (hP.card_part_eq_average_iff hp).symm

/-- An equipartition of a finset with `n` elements into `k` parts has
`n % k` parts of size `n / k + 1`. -/
theorem IsEquipartition.card_large_parts_eq_mod (hP : P.IsEquipartition) :
    #{p ∈ P.parts | #p = #s / #P.parts + 1} = #s % #P.parts := by
  have z := P.sum_card_parts
  rw [← sum_filter_add_sum_filter_not (s := P.parts) (p := fun x ↦ #x = #s / #P.parts + 1),
    hP.filter_ne_average_add_one_eq_average, sum_const_nat (m := #s / #P.parts + 1) (by simp),
    sum_const_nat (m := #s / #P.parts) (by simp), ← hP.filter_ne_average_add_one_eq_average,
    mul_add, add_comm, ← add_assoc, ← add_mul, mul_one, add_comm #_,
    filter_card_add_filter_neg_card_eq_card, add_comm] at z
  rw [← add_left_inj, Nat.mod_add_div, z]

/-- An equipartition of a finset with `n` elements into `k` parts has
`n - n % k` parts of size `n / k`. -/
theorem IsEquipartition.card_small_parts_eq_mod (hP : P.IsEquipartition) :
    #{p ∈ P.parts | #p = #s / #P.parts} = #P.parts - #s % #P.parts := by
  conv_rhs =>
    arg 1
    rw [← filter_card_add_filter_neg_card_eq_card (p := fun p ↦ #p = #s / #P.parts + 1)]
  rw [hP.card_large_parts_eq_mod, add_tsub_cancel_left, hP.filter_ne_average_add_one_eq_average]

/-- There exists an enumeration of an equipartition's parts where
larger parts map to smaller numbers and vice versa. -/
theorem IsEquipartition.exists_partsEquiv (hP : P.IsEquipartition) :
    ∃ f : P.parts ≃ Fin #P.parts, ∀ t, #t.1 = #s / #P.parts + 1 ↔ f t < #s % #P.parts := by
  let el := {p ∈ P.parts | #p = #s / #P.parts + 1}.equivFin
  let es := {p ∈ P.parts | #p = #s / #P.parts}.equivFin
  simp_rw [mem_filter, hP.card_large_parts_eq_mod] at el
  simp_rw [mem_filter, hP.card_small_parts_eq_mod] at es
  let sneg :
      {x // x ∈ P.parts ∧ ¬#x = #s / #P.parts + 1} ≃ {x // x ∈ P.parts ∧ #x = #s / #P.parts} := by
    apply (Equiv.refl _).subtypeEquiv
    simp only [Equiv.refl_apply, and_congr_right_iff]
    exact fun _ ha ↦ by rw [hP.card_part_eq_average_iff ha, ne_eq]
  replace el : { x : P.parts // #x.1 = #s / #P.parts + 1 } ≃
      Fin (#s % #P.parts) := (Equiv.Set.sep ..).symm.trans el
  replace es : { x : P.parts // ¬#x.1 = #s / #P.parts + 1 } ≃
      Fin (#P.parts - #s % #P.parts) := (Equiv.Set.sep ..).symm.trans (sneg.trans es)
  let f := (Equiv.sumCompl _).symm.trans ((el.sumCongr es).trans finSumFinEquiv)
  use f.trans (finCongr (Nat.add_sub_of_le P.card_mod_card_parts_le))
  intro ⟨p, _⟩
  simp_rw [f, Equiv.trans_apply, Equiv.sumCongr_apply, finCongr_apply, Fin.coe_cast]
  by_cases hc : #p = #s / #P.parts + 1 <;> simp [hc]

/-- Given a finset equipartitioned into `k` parts, its elements can be enumerated such that
elements in the same part have congruent indices modulo `k`. -/
theorem IsEquipartition.exists_partPreservingEquiv (hP : P.IsEquipartition) : ∃ f : s ≃ Fin #s,
    ∀ a b : s, P.part a = P.part b ↔ f a % #P.parts = f b % #P.parts := by
  obtain ⟨f, hf⟩ := P.exists_enumeration
  obtain ⟨g, hg⟩ := hP.exists_partsEquiv
  let z := fun a ↦ #P.parts * (f a).2 + g (f a).1
  have gl := fun a ↦ (g (f a).1).2
  have less : ∀ a, z a < #s := fun a ↦ by
    rcases hP.card_parts_eq_average (f a).1.2 with (c | c)
    · calc
        _ < #P.parts * ((f a).2 + 1) := add_lt_add_left (gl a) _
        _ ≤ #P.parts * (#s / #P.parts) := mul_le_mul_left' (c ▸ (f a).2.2) _
        _ ≤ #P.parts * (#s / #P.parts) + #s % #P.parts := Nat.le_add_right ..
        _ = _ := Nat.div_add_mod ..
    · rw [← Nat.div_add_mod #s #P.parts]
      exact add_lt_add_of_le_of_lt (mul_le_mul_left' (by cutsat) _) ((hg (f a).1).mp c)
  let z' : s → Fin #s := fun a ↦ ⟨z a, less a⟩
  have bij : z'.Bijective := by
    refine (bijective_iff_injective_and_card z').mpr ⟨fun a b e ↦ ?_, by simp⟩
    simp_rw [z', z, Fin.mk.injEq, mul_comm #P.parts] at e
    haveI : NeZero #P.parts := ⟨((Nat.zero_le _).trans_lt (gl a)).ne'⟩
    change (#P.parts).divModEquiv.symm (_, _) = (#P.parts).divModEquiv.symm (_, _) at e
    simp only [Equiv.apply_eq_iff_eq, Prod.mk.injEq] at e
    apply_fun f
    exact Sigma.ext e.2 <| (Fin.heq_ext_iff (by rw [e.2])).mpr e.1
  use Equiv.ofBijective _ bij
  intro a b
  simp_rw [z', z, Equiv.ofBijective_apply, hf a b, Nat.mul_add_mod,
    Nat.mod_eq_of_lt (gl a), Nat.mod_eq_of_lt (gl b), Fin.val_eq_val, g.apply_eq_iff_eq]

/-! ### Discrete and indiscrete finpartitions -/


variable (s) -- [Decidable (a = ⊥)]

theorem bot_isEquipartition : (⊥ : Finpartition s).IsEquipartition :=
  Set.equitableOn_iff_exists_eq_eq_add_one.2 ⟨1, by simp⟩

theorem top_isEquipartition [Decidable (s = ⊥)] : (⊤ : Finpartition s).IsEquipartition :=
  Set.Subsingleton.isEquipartition (parts_top_subsingleton _)

theorem indiscrete_isEquipartition {hs : s ≠ ∅} : (indiscrete hs).IsEquipartition := by
  rw [IsEquipartition, indiscrete_parts, coe_singleton]
  exact Set.equitableOn_singleton s _

end Finpartition
