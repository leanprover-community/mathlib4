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

open Cardinal


namespace Ordinal

/-- The ordinal `univ.{u, v}` is the order type of `Ordinal.{u}`, or equivalently `Cardinal.{u}`,
as an element of `Ordinal.{v}` (when `u < v`). -/
@[pp_with_univ, nolint checkUnivs]
def univ : Ordinal.{max (u + 1) v} :=
  lift.{v, u + 1} (@type Ordinal (· < ·) _)

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

theorem lift_type_ordinal : lift.{max (u + 1) v} (@type Ordinal.{u} (· < ·) _) = univ.{u, v} := by
  rw [type_ordinal, lift_univ, univ_umax.{u, v}]

@[simp]
theorem type_cardinal : @type Cardinal.{u} (· < ·) _ = univ.{u, u + 1} := by
  rw [← type_ordinal, Cardinal.aleph'.toRelIsoLT.ordinal_type_eq]

theorem lift_lt_univ (o : Ordinal) : lift.{max (u + 1) v, u} o < univ.{u, v} := by
  suffices ∀ o, lift.{max (u + 1) v, u} o ≤ univ.{u, v} by simpa using this (Order.succ o)
  refine fun o ↦ inductionOn o fun α r _ ↦ ?_
  rw [← lift_type_ordinal, lift_type_le.{u, u + 1, max (u + 1) v}]
  exact ⟨typein r⟩

/-- `Ordinal.lift` as a `PrincipalSeg` with top `univ`. -/
def liftPrincipalSeg : Ordinal.{v} <i Ordinal.{max u (v + 1)} := by
  refine ⟨liftInitialSeg.{max u (v + 1)}, univ.{v}, fun o ↦ ⟨fun ⟨a, ha⟩ ↦ ?_, fun h ↦ ?_⟩⟩
  · rw [← ha]
    exact lift_lt_univ _
  · rw [← o.type_lt]
    obtain (f | f) := InitialSeg.principalSeg_sum_initialSeg (α := o.toType) (β := Ordinal.{v})
      (· < ·) (· < ·)
    · apply Ordinal.mem_range_of_le_lift
      rw [← lift_id #c.out, lift_mk_le.{max u (v + 1)}]
      refine ⟨fun a ↦ equivShrink (Iio f.top) ⟨f a, f.lt_top a⟩, fun a b ↦ ?_⟩
      simp
    · have := lift_mk_le'.2 ⟨f.toEmbedding⟩
      rw [mk_cardinal, mk_out, lift_univ, lift_id', univ_umax] at this
      cases this.not_lt h
  /-
    refine fun b => inductionOn b ?_; intro β s _
    rw [univ, ← lift_umax]; constructor <;> intro h
    · cases' h with a e
      rw [← e]
      refine inductionOn a ?_
      intro α r _
      exact lift_type_lt.{u, u + 1, max (u + 1) v}.2 ⟨typein r⟩
    · rw [← lift_id (type s)] at h ⊢
      cases' lift_type_lt.{_,_,v}.1 h with f
      cases' f with f a hf
      exists a
      revert hf
      -- Porting note: apply inductionOn does not work, refine does
      refine inductionOn a ?_
      intro α r _ hf
      refine lift_type_eq.{u, max (u + 1) v, max (u + 1) v}.2
        ⟨(RelIso.ofSurjective (RelEmbedding.ofMonotone ?_ ?_) ?_).symm⟩
      · exact fun b => enum r ⟨f b, (hf _).1 ⟨_, rfl⟩⟩
      · refine fun a b h => (typein_lt_typein r).1 ?_
        rw [typein_enum, typein_enum]
        exact f.map_rel_iff.2 h
      · intro a'
        cases' (hf _).2 (typein_lt_type _ a') with b e
        exists b
        simp only [RelEmbedding.ofMonotone_coe]
        simp [e]⟩-/

#exit
@[deprecated liftPrincipalSeg (since := "2024-09-21")]
alias lift.principalSeg := liftPrincipalSeg

@[simp]
theorem liftPrincipalSeg_coe :
    (liftPrincipalSeg.{u, v} : Ordinal → Ordinal) = lift.{max (u + 1) v} :=
  rfl

set_option linter.deprecated false in
@[deprecated liftPrincipalSeg_coe (since := "2024-09-21")]
theorem lift.principalSeg_coe :
    (lift.principalSeg.{u, v} : Ordinal → Ordinal) = lift.{max (u + 1) v} :=
  rfl

@[simp]
theorem liftPrincipalSeg_top : (liftPrincipalSeg.{u, v}).top = univ.{u, v} :=
  rfl

set_option linter.deprecated false in
@[deprecated liftPrincipalSeg_top (since := "2024-09-21")]
theorem lift.principalSeg_top : (lift.principalSeg.{u, v}).top = univ.{u, v} :=
  rfl

theorem liftPrincipalSeg_top' : liftPrincipalSeg.{u, u + 1}.top = @type Ordinal (· < ·) _ := by
  simp only [liftPrincipalSeg_top, univ_id]

set_option linter.deprecated false in
@[deprecated liftPrincipalSeg_top (since := "2024-09-21")]
theorem lift.principalSeg_top' : lift.principalSeg.{u, u + 1}.top = @type Ordinal (· < ·) _ := by
  simp only [lift.principalSeg_top, univ_id]


@[simp]
theorem type_cardinal : @type Cardinal (· < ·) _ = Ordinal.univ.{u, u + 1} := by
  rw [Ordinal.univ_id]
  exact Quotient.sound ⟨aleph'.symm.toRelIsoLT⟩

@[simp]
theorem mk_cardinal : #Cardinal = univ.{u, u + 1} := by
  simpa only [card_type, card_univ] using congr_arg card type_cardinal

@[simp]
theorem card_univ : card univ.{u,v} = Cardinal.univ.{u,v} :=
  rfl


  #exit

@[simp]
theorem ord_univ : ord univ.{u, v} = Ordinal.univ.{u, v} := by
  refine le_antisymm (ord_card_le _) <| le_of_forall_lt fun o h => lt_ord.2 ?_
  have := liftPrincipalSeg.mem_range_of_rel_top (by simpa only [liftPrincipalSeg_coe] using h)
  rcases this with ⟨o, h'⟩
  rw [← h', liftPrincipalSeg_coe, ← lift_card]
  apply lift_lt_univ'

end Ordinal

namespace Cardinal


@[simp]
theorem mk_ordinal : #Ordinal = univ.{u, u + 1} := by
  rw [← mk_cardinal, Cardinal.aleph'.cardinal_eq]


@[simp]
theorem _root_.Ordinal.card_univ : card univ.{u, v} = Cardinal.univ.{u, v} := by
  rw [← lift_type_ordinal, ← lift_card, card_type, Cardinal.mk_ordinal, Cardinal.lift_univ,
    Cardinal.univ_umax.{u, v}]
