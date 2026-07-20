/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.Ordinals
public import Mathlib.SetTheory.ZFC.Constructible.BasicAxioms

/-!
# Constructible ordinal indices for stage histories

Every ambient ordinal has a canonical von Neumann code in `L`.  Packaging
that code once keeps the history and Replacement interfaces on `LCarrier`.
-/

@[expose] public section

universe u

namespace Constructible.Model

noncomputable section

/-- The canonical constructible carrier element coding an ordinal. -/
def ordinalLCarrier (alpha : Ordinal.{u}) : LCarrier.{u} :=
  ⟨alpha.toZFSet, ordinal_toZFSet_mem_L alpha⟩

@[simp]
theorem ordinalLCarrier_val (alpha : Ordinal.{u}) :
    (ordinalLCarrier alpha).1 = alpha.toZFSet :=
  rfl

theorem ordinalLCarrier_mem_ordinalLCarrier_iff
    (alpha beta : Ordinal.{u}) :
    (ordinalLCarrier beta).1 ∈ (ordinalLCarrier alpha).1 ↔ beta < alpha := by
  exact Ordinal.toZFSet_mem_toZFSet_iff

@[simp]
theorem ordinalLCarrier_zero :
    ordinalLCarrier (0 : Ordinal.{u}) = emptyLCarrier := by
  apply Subtype.ext
  exact Ordinal.toZFSet_zero

theorem ordinalLCarrier_succ_val (alpha : Ordinal.{u}) :
    (ordinalLCarrier (Order.succ alpha)).1 =
      insert (ordinalLCarrier alpha).1 (ordinalLCarrier alpha).1 := by
  rw [Order.succ_eq_add_one]
  change (alpha + 1).toZFSet = insert alpha.toZFSet alpha.toZFSet
  exact Ordinal.toZFSet_add_one alpha

theorem ordinalLCarrier_injective :
    Function.Injective (ordinalLCarrier : Ordinal.{u} → LCarrier.{u}) := by
  intro alpha beta h
  have hcodes : alpha.toZFSet = beta.toZFSet :=
    congrArg Subtype.val h
  exact Ordinal.toZFSet_injective hcodes

/-- Von Neumann successor is injective on all well-founded `ZFSet`s. -/
theorem insert_self_injective {x y : ZFSet.{u}}
    (h : insert x x = insert y y) : x = y := by
  have hrankSucc : Order.succ x.rank = Order.succ y.rank := by
    have hrank := congrArg ZFSet.rank h
    simpa only [ZFSet.rank_insert, max_eq_left (Order.le_succ x.rank),
      max_eq_left (Order.le_succ y.rank)] using hrank
  have hrank : x.rank = y.rank :=
    Order.succ_injective hrankSucc
  have hx : x ∈ insert y y := by
    rw [← h]
    exact ZFSet.mem_insert_iff.mpr (Or.inl rfl)
  rcases ZFSet.mem_insert_iff.mp hx with hxy | hxy
  · exact hxy
  · have hrankLt := ZFSet.rank_lt_of_mem hxy
    rw [hrank] at hrankLt
    exact (lt_irrefl _ hrankLt).elim

/-- The only predecessor whose von Neumann successor is the canonical code
of `alpha + 1` is the canonical code of `alpha`. -/
theorem ordinalLCarrier_successor_predecessor_iff
    (alpha : Ordinal.{u}) (predecessor : LCarrier.{u}) :
    (ordinalLCarrier (Order.succ alpha)).1 =
        insert predecessor.1 predecessor.1 ↔
      predecessor = ordinalLCarrier alpha := by
  constructor
  · intro h
    apply Subtype.ext
    apply insert_self_injective
    rw [← h, ordinalLCarrier_succ_val]
  · rintro rfl
    exact ordinalLCarrier_succ_val alpha

/-- A nonzero limit ordinal code is not the von Neumann successor of any
constructible set. -/
theorem ordinalLCarrier_limit_no_predecessor
    {limit : Ordinal.{u}} (hl : Order.IsSuccLimit limit) :
    ¬ ∃ predecessor : LCarrier.{u},
      (ordinalLCarrier limit).1 =
        insert predecessor.1 predecessor.1 := by
  rintro ⟨predecessor, hsuccessor⟩
  have hpredecessorMem : predecessor.1 ∈ limit.toZFSet := by
    rw [← ordinalLCarrier_val limit, hsuccessor]
    exact ZFSet.mem_insert_iff.mpr (Or.inl rfl)
  rcases Ordinal.mem_toZFSet_iff.mp hpredecessorMem with
    ⟨beta, _hbeta, hbetaCode⟩
  have hpredecessor : predecessor = ordinalLCarrier beta := by
    apply Subtype.ext
    exact hbetaCode.symm
  subst predecessor
  have hcodes : limit.toZFSet = (Order.succ beta).toZFSet := by
    calc
      limit.toZFSet = (ordinalLCarrier limit).1 := rfl
      _ = insert (ordinalLCarrier beta).1 (ordinalLCarrier beta).1 :=
        hsuccessor
      _ = (ordinalLCarrier (Order.succ beta)).1 :=
        (ordinalLCarrier_succ_val beta).symm
      _ = (Order.succ beta).toZFSet := rfl
  have hlimit : limit = Order.succ beta :=
    Ordinal.toZFSet_injective hcodes
  exact hl.succ_ne beta hlimit.symm

end

end Constructible.Model
