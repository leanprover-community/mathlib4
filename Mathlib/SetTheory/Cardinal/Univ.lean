/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Floris van Doorn
-/
import Mathlib.SetTheory.Cardinal.Basic

/-!
# Universal cardinal

The universal cardinal `univ.{u, v}` is defined as the cardinality of `Cardinal.{u}` as a
`Cardinal.{v}`. This is the supremum of the cardinalities of any `Small.{u}` types.
-/

assert_not_exists Ordinal

universe u v w

namespace Cardinal

/-- The cardinal `univ.{u, v}` is the cardinality of `Cardinal.{u}`, or equivalently `Ordinal.{u}`,
as an element of `Cardinal.{v}` (when `u < v`). -/
@[pp_with_univ, nolint checkUnivs]
def univ : Cardinal.{max (u + 1) v} :=
  lift.{v} #Cardinal.{u}

@[simp]
theorem mk_cardinal : #Cardinal = univ.{u, u + 1} :=
  (lift_id _).symm

@[deprecated mk_cardinal (since := "2024-10-20")]
theorem univ_id : univ.{u, u + 1} = #Cardinal :=
  lift_id _

@[simp]
theorem lift_univ : lift.{w} univ.{u, v} = univ.{u, max v w} :=
  lift_lift _

theorem univ_umax : univ.{u, max (u + 1) v} = univ.{u, v} :=
  congr_fun lift_umax _

theorem lift_mk_cardinal : lift.{max (u + 1) v} #Cardinal.{u} = univ.{u, v} := by
  rw [mk_cardinal, lift_univ, univ_umax.{u, v}]

theorem lift_lt_univ (c : Cardinal) : lift.{max (u + 1) v, u} c < univ.{u, v} := by
  suffices ∀ c, lift.{max (u + 1) v, u} c ≤ univ.{u, v} by simpa using this (Order.succ c)
  refine fun c ↦ inductionOn c fun α ↦ ?_
  rw [← lift_mk_cardinal, lift_mk_le.{max (u + 1) v}]
  exact nonempty_embedding_to_cardinal

@[deprecated (since := "2024-10-20")]
alias lift_lt_univ' := lift_lt_univ

theorem mem_range_lift_of_lt_univ {c : Cardinal} (h : c < univ.{u, v}) :
    c ∈ Set.range lift.{max (u + 1) v, u} := by
  rw [← c.mk_out]
  obtain (f | f) := InitialSeg.principalSeg_sum_initialSeg
    (@WellOrderingRel c.out) ((· < ·) : Cardinal.{u} → Cardinal.{u} → Prop)
  · apply mem_range_of_le_lift
    rw [← lift_id #c.out, lift_mk_le.{max (u + 1) v}]
    refine ⟨fun a ↦ equivShrink (Set.Iio f.top) ⟨f a, f.lt_top a⟩, fun a b ↦ ?_⟩
    simp
  · have := lift_mk_le'.2 ⟨f.toEmbedding⟩
    rw [mk_cardinal, mk_out, lift_univ, lift_id', univ_umax] at this
    cases this.not_lt h

/-- `Cardinal.lift` as a `PrincipalSeg` with top `univ`. -/
def liftPrincipalSeg : Cardinal.{u} <i Cardinal.{max (u + 1) v} := by
  refine ⟨liftInitialSeg.{max (u + 1) v}, univ.{u}, fun c ↦ inductionOn c fun α ↦
    ⟨?_, mem_range_lift_of_lt_univ⟩⟩
  rintro ⟨c, hc⟩
  rw [← hc]
  exact lift_lt_univ _

@[simp]
theorem ord_univ : ord univ.{u, v} = Ordinal.univ.{u, v} := by
  refine le_antisymm (ord_card_le _) <| le_of_forall_lt fun o h => lt_ord.2 ?_
  have := liftPrincipalSeg.mem_range_of_rel_top (by simpa only [liftPrincipalSeg_coe] using h)
  rcases this with ⟨o, h'⟩
  rw [← h', liftPrincipalSeg_coe, ← lift_card]
  apply lift_lt_univ'

theorem lt_univ {c} : c < univ.{u, u + 1} ↔ ∃ c', c = lift.{u + 1, u} c' :=
  ⟨fun h => by
    have := ord_lt_ord.2 h
    rw [ord_univ] at this
    cases' liftPrincipalSeg.mem_range_of_rel_top (by simpa only [liftPrincipalSeg_top]) with o e
    have := card_ord c
    rw [← e, liftPrincipalSeg_coe, ← lift_card] at this
    exact ⟨_, this.symm⟩, fun ⟨_, e⟩ => e.symm ▸ lift_lt_univ _⟩

theorem lt_univ' {c} : c < univ.{u, v} ↔ ∃ c', c = lift.{max (u + 1) v, u} c' :=
  ⟨fun h => by
    let ⟨a, h', e⟩ := lt_lift_iff.1 h
    rw [← univ_id] at h'
    rcases lt_univ.{u}.1 h' with ⟨c', rfl⟩
    exact ⟨c', by simp only [e.symm, lift_lift]⟩, fun ⟨_, e⟩ => e.symm ▸ lift_lt_univ' _⟩

theorem small_iff_lift_mk_lt_univ {α : Type u} :
    Small.{v} α ↔ Cardinal.lift.{v+1,_} #α < univ.{v, max u (v + 1)} := by
  rw [lt_univ']
  constructor
  · rintro ⟨β, e⟩
    exact ⟨#β, lift_mk_eq.{u, _, v + 1}.2 e⟩
  · rintro ⟨c, hc⟩
    exact ⟨⟨c.out, lift_mk_eq.{u, _, v + 1}.1 (hc.trans (congr rfl c.mk_out.symm))⟩⟩

end Cardinal
