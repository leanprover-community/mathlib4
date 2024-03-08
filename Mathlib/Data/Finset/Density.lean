/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset

/-!
# Density of a finite set

This defines the density of a `Finset` and provides induction principles for finsets.

## Main declarations

* `Finset.dens s`: Density of `s : Finset α` in `α`.

## Notation

If you need to specify the field the density is valued in, `dens[𝕜] s` is notation for
`(dens s : 𝕜)`. Note that no dot notation is allowed.
-/

open Function Multiset Nat

variable {𝕜 α β : Type*} [Fintype α]

namespace Finset
section Semifield
variable [Semifield 𝕜] {s t : Finset α} {a b : α}

/-- `dens s` is the number of elements of `s`, aka its density. -/
@[pp_dot] def dens (s : Finset α) : 𝕜 := s.card / Fintype.card α

@[inherit_doc dens] notation "dens[" 𝕜 "]" => @dens 𝕜

lemma dens_eq_card_div_card (s : Finset α) : dens[𝕜] s = s.card / Fintype.card α := rfl

@[simp] lemma dens_empty : dens[𝕜] (∅ : Finset α) = 0 := by simp [dens]

@[simp] lemma dens_singleton (a : α) : dens ({a} : Finset α) = (Fintype.card α : 𝕜)⁻¹ := by
  simp [dens]

@[simp]
lemma dens_cons (h : a ∉ s) : (s.cons a h).dens = dens s + (Fintype.card α : 𝕜)⁻¹ := by
  simp [dens, add_div]

@[simp]
lemma dens_disjUnion (s t : Finset α) (h) : dens[𝕜] (s.disjUnion t h) = dens s + dens t := by
  simp_rw [dens, card_disjUnion, Nat.cast_add, add_div]

section Lattice
variable [DecidableEq α]

lemma dens_union_add_dens_inter (s t : Finset α) :
    dens[𝕜] (s ∪ t) + dens (s ∩ t) = dens s + dens t := by
  simp_rw [dens, ← add_div, ← Nat.cast_add, card_union_add_card_inter]

lemma dens_inter_add_dens_union (s t : Finset α) :
    dens[𝕜] (s ∩ t) + dens (s ∪ t) = dens s + dens t := by rw [add_comm, dens_union_add_dens_inter]

@[simp] lemma dens_union_of_disjoint (h : Disjoint s t) : dens[𝕜] (s ∪ t) = dens s + dens t := by
  rw [← disjUnion_eq_union s t h, dens_disjUnion _ _ _]

lemma dens_sdiff_add_dens_eq_dens (h : s ⊆ t) : dens[𝕜] (t \ s) + dens s = dens t := by
  simp [dens, ← card_sdiff_add_card_eq_card h, add_div]

lemma dens_sdiff_add_dens (s t : Finset α) : dens[𝕜] (s \ t) + dens t = (s ∪ t).dens := by
  rw [← dens_union_of_disjoint sdiff_disjoint, sdiff_union_self_eq_union]

lemma dens_sdiff_comm [IsCancelAdd 𝕜] (h : card s = card t) : dens[𝕜] (s \ t) = dens (t \ s) :=
  add_left_injective (dens t) $ by
    simp_rw [dens_sdiff_add_dens, union_comm s, ← dens_sdiff_add_dens, dens, h]

@[simp]
lemma dens_sdiff_add_dens_inter (s t : Finset α) : dens[𝕜] (s \ t) + dens (s ∩ t) = dens s := by
  rw [← dens_union_of_disjoint (disjoint_sdiff_inter _ _), sdiff_union_inter]

@[simp]
lemma dens_inter_add_dens_sdiff (s t : Finset α) : dens[𝕜] (s ∩ t) + dens (s \ t) = dens s := by
  rw [add_comm, dens_sdiff_add_dens_inter]

lemma dens_filter_add_dens_filter_not_eq_dens
    (p : α → Prop) [DecidablePred p] [∀ x, Decidable (¬p x)] :
    dens[𝕜] (s.filter p) + dens (s.filter fun a ↦ ¬ p a) = dens s := by
  rw [← dens_union_of_disjoint (disjoint_filter_filter_neg ..), filter_union_filter_neg_eq]

end Lattice

section CharZero
variable [CharZero 𝕜]

@[simp] lemma dens_eq_zero : dens[𝕜] s = 0 ↔ s = ∅ := by
  simp (config := { contextual := true }) [dens, Fintype.card_eq_zero_iff, eq_empty_of_isEmpty]

lemma dens_ne_zero : dens[𝕜] s ≠ 0 ↔ s.Nonempty := dens_eq_zero.not.trans nonempty_iff_ne_empty.symm

protected alias ⟨_, Nonempty.dens_ne_zero⟩ := dens_ne_zero

variable [Nonempty α]

@[simp] lemma dens_univ : dens[𝕜] (univ : Finset α) = 1 := by simp [dens, card_univ]

@[simp] lemma dens_eq_one : dens[𝕜] s = 1 ↔ s = univ := by
  simp [dens, div_eq_one_iff_eq, card_eq_iff_eq_univ]

lemma dens_ne_one : dens[𝕜] s ≠ 1 ↔ s ≠ univ := dens_eq_one.not

end CharZero

end Semifield

section LinearOrderedSemifield
variable [LinearOrderedSemifield 𝕜] {s t : Finset α} {a b : α}

@[simp] lemma dens_nonneg : 0 ≤ dens[𝕜] s := by unfold dens; positivity

lemma dens_le_dens (h : s ⊆ t) : dens[𝕜] s ≤ dens t :=
  div_le_div_of_nonneg_right (mod_cast card_mono h) $ by positivity

lemma dens_lt_dens (h : s ⊂ t) : dens[𝕜] s < dens t :=
  div_lt_div_of_pos_right (mod_cast card_strictMono h) $ by
    cases isEmpty_or_nonempty α
    · simp [Subsingleton.elim s t, ssubset_irrfl] at h
    · positivity

@[mono] lemma dens_mono : Monotone (dens : Finset α → 𝕜) := fun _ _ ↦ dens_le_dens
@[mono] lemma dens_strictMono : StrictMono (dens : Finset α → 𝕜) := fun _ _ ↦ dens_lt_dens

lemma dens_map_le [Fintype β] (f : α ↪ β) : dens[𝕜] (s.map f) ≤ dens s := by
  cases isEmpty_or_nonempty α
  · simp [Subsingleton.elim s ∅]
  simp_rw [dens, card_map]
  gcongr
  · positivity
  · positivity
  · exact Fintype.card_le_of_injective _ f.2

section Lattice
variable [DecidableEq α]

lemma dens_union_le (s t : Finset α) : dens[𝕜] (s ∪ t) ≤ dens s + dens t :=
  dens_union_add_dens_inter (𝕜 := 𝕜) s t ▸ le_add_of_nonneg_right dens_nonneg

lemma dens_le_dens_sdiff_add_dens : dens[𝕜] s ≤ dens (s \ t) + dens t :=
  dens_sdiff_add_dens (𝕜 := 𝕜) s _ ▸ dens_le_dens (subset_union_left _ _)

variable [Sub 𝕜] [OrderedSub 𝕜]

lemma dens_sdiff (h : s ⊆ t) : dens[𝕜] (t \ s) = dens t - dens s :=
  eq_tsub_of_add_eq (dens_sdiff_add_dens_eq_dens h)

lemma le_dens_sdiff (s t : Finset α) : dens[𝕜] t - dens s ≤ dens (t \ s) :=
  tsub_le_iff_right.2 dens_le_dens_sdiff_add_dens

end Lattice

@[simp]
lemma dens_pos [CharZero 𝕜] : 0 < dens[𝕜] s ↔ s.Nonempty := dens_nonneg.gt_iff_ne.trans dens_ne_zero

protected alias ⟨_, Nonempty.dens_pos⟩ := dens_pos

end LinearOrderedSemifield
end Finset

open Finset
namespace Mathlib.Meta.Positivity
open Qq Lean Meta

/-- Positivity extension for `Finset.dens`: The density is always nonnegative, and positive if the
finset is nonempty. -/
@[positivity Finset.dens _]
def evalFinsetDens : PositivityExt where eval {u 𝕜} _ _ e := do
  match e with
  | ~q(@Finset.dens _ $α $instα $inst𝕜 $s) =>
    let p_pos : Option Q(0 < $e) := ← (do
      let some ps ← proveFinsetNonempty s | pure none
      let .some inst𝕜ordfield ← trySynthInstanceQ q(LinearOrderedSemifield $𝕜) | pure none
      let .some inst𝕜char ← trySynthInstanceQ q(CharZero $𝕜) | pure none
      assumeInstancesCommute
      return some q(@Nonempty.dens_pos $𝕜 $α $instα $inst𝕜ordfield $s $inst𝕜char $ps))
    -- Try to show that the density is positive
    if let some p_pos := p_pos then
      return .positive p_pos
    let p_nonneg : Option Q(0 ≤ $e) := ← (do
      let .some inst𝕜ordfield ← trySynthInstanceQ q(LinearOrderedSemifield $𝕜) | pure none
      assumeInstancesCommute
      return some q(@dens_nonneg $𝕜 $α $instα $inst𝕜ordfield $s))
    -- Try to show that the density is nonnegative
    if let some p_nonneg := p_nonneg then
      return .nonnegative p_nonneg
    -- Fall back to showing that the density is nonzero
    let inst𝕜char ← synthInstanceQ q(CharZero $𝕜)
    let some ps ← proveFinsetNonempty s | return .none
    assertInstancesCommute
    return .nonzero q(@Nonempty.dens_ne_zero $𝕜 $α $instα $inst𝕜 $s $inst𝕜char $ps)
  | _ => throwError "not Finset.dens"

variable {𝕜 α : Type*} [Fintype α] {s : Finset α}

example [LinearOrderedSemifield 𝕜] : 0 ≤ dens[𝕜] s := by positivity
example [LinearOrderedSemifield 𝕜] {s : Finset α} (hs : s.Nonempty) : 0 < dens[𝕜] s := by positivity
example [LinearOrderedSemifield 𝕜] [Nonempty α] : 0 < dens[𝕜] (univ : Finset α) := by positivity
example [PartialOrder 𝕜] [Semifield 𝕜] [CharZero 𝕜] {s : Finset α} (hs : s.Nonempty) :
    dens[𝕜] s ≠ 0 := by positivity
example [PartialOrder 𝕜] [Semifield 𝕜] [CharZero 𝕜] [Nonempty α] :
    dens[𝕜] (univ : Finset α) ≠ 0 := by positivity

end Mathlib.Meta.Positivity
