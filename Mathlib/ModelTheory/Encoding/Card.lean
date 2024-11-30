/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.ModelTheory.Encoding.Basic
import Mathlib.ModelTheory.Card
import Mathlib.Computability.Encoding.Card
import Mathlib.Logic.Small.List
import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Cardinality of First-Order Syntax
## Main Results

- `FirstOrder.Language.Term.card_le` shows that the number of terms in `L.Term α` is at most
  `max ℵ₀ # (α ⊕ Σ i, L.Functions i)`.
- `FirstOrder.Language.BoundedFormula.card_le` shows that the number of bounded formulas in
  `Σ n, L.BoundedFormula α n` is at most
  `max ℵ₀ (Cardinal.lift.{max u v} #α + Cardinal.lift.{u'} L.card)`.

## TODO

- `Primcodable` instances for terms and formulas, based on the `encoding`s
- Computability facts about term and formula operations, to set up a computability approach to
  incompleteness

-/

universe u v w u'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}
variable {α : Type u'}

open FirstOrder Cardinal

open Computability List Structure Cardinal Fin

namespace Term


theorem card_le : #(L.Term α) ≤ max ℵ₀ #(α ⊕ (Σi, L.Functions i)) :=
  lift_le.1 (_root_.trans Term.encoding.card_le_card_list (lift_le.2 (mk_list_le_max _)))

theorem card_sigma : #(Σn, L.Term (α ⊕ (Fin n))) = max ℵ₀ #(α ⊕ (Σi, L.Functions i)) := by
  refine le_antisymm ?_ ?_
  · rw [mk_sigma]
    refine (sum_le_iSup_lift _).trans ?_
    rw [mk_nat, lift_aleph0, mul_eq_max_of_aleph0_le_left le_rfl, max_le_iff,
      ciSup_le_iff' (bddAbove_range _)]
    · refine ⟨le_max_left _ _, fun i => card_le.trans ?_⟩
      refine max_le (le_max_left _ _) ?_
      rw [← add_eq_max le_rfl, mk_sum, mk_sum, mk_sum, add_comm (Cardinal.lift #α), lift_add,
        add_assoc, lift_lift, lift_lift, mk_fin, lift_natCast]
      exact add_le_add_right (nat_lt_aleph0 _).le _
    · rw [← one_le_iff_ne_zero]
      refine _root_.trans ?_ (le_ciSup (bddAbove_range _) 1)
      rw [one_le_iff_ne_zero, mk_ne_zero_iff]
      exact ⟨var (Sum.inr 0)⟩
  · rw [max_le_iff, ← infinite_iff]
    refine ⟨Infinite.of_injective (fun i => ⟨i + 1, var (Sum.inr i)⟩) fun i j ij => ?_, ?_⟩
    · cases ij
      rfl
    · rw [Cardinal.le_def]
      refine ⟨⟨Sum.elim (fun i => ⟨0, var (Sum.inl i)⟩)
        fun F => ⟨1, func F.2 fun _ => var (Sum.inr 0)⟩, ?_⟩⟩
      rintro (a | a) (b | b) h
      · simp only [Sum.elim_inl, Sigma.mk.inj_iff, heq_eq_eq, var.injEq, Sum.inl.injEq, true_and]
          at h
        rw [h]
      · simp only [Sum.elim_inl, Sum.elim_inr, Sigma.mk.inj_iff, false_and, reduceCtorEq] at h
      · simp only [Sum.elim_inr, Sum.elim_inl, Sigma.mk.inj_iff, false_and, reduceCtorEq] at h
      · simp only [Sum.elim_inr, Sigma.mk.inj_iff, heq_eq_eq, func.injEq, true_and] at h
        rw [Sigma.ext_iff.2 ⟨h.1, h.2.1⟩]

instance [Encodable α] [Encodable (Σi, L.Functions i)] : Encodable (L.Term α) :=
  Encodable.ofLeftInjection listEncode (fun l => (listDecode l).head?.join) fun t => by
    simp only
    rw [← flatMap_singleton listEncode, listDecode_encode_list]
    simp only [Option.join, head?_cons, Option.pure_def, Option.bind_eq_bind, Option.some_bind,
      id_eq]

instance [h1 : Countable α] [h2 : Countable (Σl, L.Functions l)] : Countable (L.Term α) := by
  refine mk_le_aleph0_iff.1 (card_le.trans (max_le_iff.2 ?_))
  simp only [le_refl, mk_sum, add_le_aleph0, lift_le_aleph0, true_and]
  exact ⟨Cardinal.mk_le_aleph0, Cardinal.mk_le_aleph0⟩

instance small [Small.{u} α] : Small.{u} (L.Term α) :=
  small_of_injective listEncode_injective

end Term

namespace BoundedFormula

theorem card_le : #(Σn, L.BoundedFormula α n) ≤
    max ℵ₀ (Cardinal.lift.{max u v} #α + Cardinal.lift.{u'} L.card) := by
  refine lift_le.1 (BoundedFormula.encoding.card_le_card_list.trans ?_)
  rw [encoding_Γ, mk_list_eq_max_mk_aleph0, lift_max, lift_aleph0, lift_max, lift_aleph0,
    max_le_iff]
  refine ⟨?_, le_max_left _ _⟩
  rw [mk_sum, Term.card_sigma, mk_sum, ← add_eq_max le_rfl, mk_sum, mk_nat]
  simp only [lift_add, lift_lift, lift_aleph0]
  rw [← add_assoc, add_comm, ← add_assoc, ← add_assoc, aleph0_add_aleph0, add_assoc,
    add_eq_max le_rfl, add_assoc, card, Symbols, mk_sum, lift_add, lift_lift, lift_lift]

end BoundedFormula

end Language

end FirstOrder
