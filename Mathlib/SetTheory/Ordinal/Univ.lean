/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn, Violeta Hernández Palacios
-/
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Cardinal.Univ

/-!
# Universal ordinal

The universal ordinal `univ.{u, v}` is defined as the order type of `Ordinal.{u}` as a
`Ordinal.{v}`. This is the supremum of the order types of any `Small.{u}` types.

We also establish connections between `Ordinal.univ` and `Cardinal.univ`.
-/

universe u v w

open Cardinal Set

namespace Ordinal

/-- The ordinal `univ.{u, v}` is the order type of `Ordinal.{u}`, or equivalently `Cardinal.{u}`,
as an element of `Ordinal.{v}` (when `u < v`). -/
@[pp_with_univ, nolint checkUnivs]
def univ : Ordinal.{max (u + 1) v} :=
  lift.{v, u + 1} (@type Ordinal (· < ·) _)

theorem lift_type_ordinal : lift.{v} (@type Ordinal.{u} (· < ·) _) = univ.{u, v} :=
  rfl

@[simp]
theorem type_ordinal : @type Ordinal (· < ·) _ = univ.{u, u + 1} :=
  (lift_id _).symm

@[deprecated type_ordinal (since := "2024-10-20")]
theorem univ_id : univ.{u, u + 1} = @type Ordinal (· < ·) _ :=
  lift_id _

@[simp]
theorem lift_univ : lift.{w} univ.{u, v} = univ.{u, max v w} :=
  lift_lift _

theorem univ_umax : univ.{u, max (u + 1) v} = univ.{u, v} :=
  congr_fun lift_umax _

theorem lift_lt_univ (o : Ordinal) : lift.{max (u + 1) v, u} o < univ.{u, v} := by
  suffices ∀ o, lift.{max (u + 1) v, u} o ≤ univ.{u, v} by simpa using this (Order.succ o)
  refine fun o ↦ inductionOn o fun α r _ ↦ ?_
  rw [← lift_type_ordinal, ← lift_umax'.{u + 1, v}, lift_type_le.{u, u + 1, max (u + 1) v}]
  exact ⟨typein r⟩

/-- `Ordinal.lift` as a `PrincipalSeg` with top `univ`. -/
def liftPrincipalSeg : Ordinal.{v} <i Ordinal.{max u (v + 1)} := by
  refine ⟨liftInitialSeg.{max u (v + 1)}, univ.{v}, fun o ↦ ⟨fun ⟨a, ha⟩ ↦ ?_, fun h ↦ ?_⟩⟩
  · rw [← ha]
    exact lift_lt_univ _
  · rw [← lift_id o, ← o.type_lt, ← lift_type_ordinal, ← lift_umax'.{v + 1, u}, lift_type_lt] at h
    obtain ⟨f⟩ := h
    have := lift_typein_top f
    rw [typein_ordinal, lift_lift, type_lt, lift_id'.{v + 1, u}] at this
    rw [← this]
    exact Set.mem_range_self _

@[simp]
theorem liftPrincipalSeg_coe :
    (liftPrincipalSeg.{u, v} : Ordinal → Ordinal) = lift.{max u (v + 1)} :=
  rfl

@[simp]
theorem liftPrincipalSeg_top : (liftPrincipalSeg.{v, u}).top = univ.{u, v} :=
  rfl

theorem lt_univ {c} : c < univ.{u, v} ↔ c ∈ range lift.{max (u + 1) v, u} :=
  liftPrincipalSeg.mem_range_iff_rel.symm

@[simp]
theorem type_cardinal : @type Cardinal.{u} (· < ·) _ = univ.{u, u + 1} := by
  rw [← type_ordinal, Cardinal.aleph'.toRelIsoLT.ordinal_type_eq]

@[simp]
theorem _root_.Cardinal.mk_ordinal : #Ordinal = Cardinal.univ.{u, u + 1} := by
  rw [← mk_cardinal, Cardinal.aleph'.cardinal_eq]

@[simp]
theorem card_univ : card univ.{u, v} = Cardinal.univ.{u, v} := by
  rw [← lift_type_ordinal, ← lift_card, card_type, mk_ordinal, Cardinal.lift_univ,
    Cardinal.univ_umax.{u, v}]

@[simp]
theorem _root_.Cardinal.ord_univ : ord Cardinal.univ.{u, v} = Ordinal.univ.{u, v} := by
  apply le_antisymm
  · rw [← Ordinal.card_univ]
    exact ord_card_le _
  · refine le_of_forall_lt fun o h ↦ lt_ord.2 ?_
    obtain ⟨a, rfl⟩ := Ordinal.lt_univ.1 h
    rw [← Ordinal.lift_card]
    exact Cardinal.lift_lt_univ _

theorem isInitial_univ : IsInitial univ.{u, v} := by
  rw [IsInitial, card_univ, ord_univ]

end Ordinal
