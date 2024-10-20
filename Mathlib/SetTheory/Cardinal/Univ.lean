/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Floris van Doorn, Violeta Hernández Palacios
-/
import Mathlib.SetTheory.Cardinal.Basic

/-!
# Universal cardinal

The universal cardinal `univ.{u, v}` is defined as the cardinality of `Cardinal.{u}` as a
`Cardinal.{v}`. This is the supremum of the cardinalities of any `Small.{u}` types.
-/

assert_not_exists Ordinal

universe u v w

open Set

namespace Cardinal

/-- The cardinal `univ.{u, v}` is the cardinality of `Cardinal.{u}`, or equivalently `Ordinal.{u}`,
as an element of `Cardinal.{v}` (when `u < v`). It is an inaccessible cardinal. -/
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

@[deprecated lift_lt_univ (since := "2024-10-20")]
alias lift_lt_univ' := lift_lt_univ

/-- `Cardinal.lift` as a `PrincipalSeg` with top `univ`. -/
def liftPrincipalSeg : Cardinal.{v} <i Cardinal.{max u (v + 1)} := by
  refine ⟨liftInitialSeg.{max u (v + 1)}, univ.{v}, fun c ↦ ⟨fun ⟨a, ha⟩ ↦ ?_, fun h ↦ ?_⟩⟩
  · rw [← ha]
    exact lift_lt_univ _
  · rw [← c.mk_out]
    obtain (f | f) := InitialSeg.principalSeg_sum_initialSeg
      (@WellOrderingRel c.out) ((· < ·) : Cardinal.{v} → Cardinal.{v} → Prop)
    · apply mem_range_of_le_lift
      rw [← lift_id #c.out, lift_mk_le.{max u (v + 1)}]
      refine ⟨fun a ↦ equivShrink (Iio f.top) ⟨f a, f.lt_top a⟩, fun a b ↦ ?_⟩
      simp
    · have := lift_mk_le'.2 ⟨f.toEmbedding⟩
      rw [mk_cardinal, mk_out, lift_univ, lift_id', univ_umax] at this
      cases this.not_lt h

@[simp]
theorem liftPrincipalSeg_coe :
    (liftPrincipalSeg.{u, v} : Cardinal → Cardinal) = lift.{max u (v + 1)} :=
  rfl

@[simp]
theorem liftPrincipalSeg_top : (liftPrincipalSeg.{v, u}).top = univ.{u, v} :=
  rfl

theorem lt_univ {c} : c < univ.{u, v} ↔ c ∈ range lift.{max (u + 1) v, u} :=
  liftPrincipalSeg.mem_range_iff_rel.symm

@[deprecated lt_univ (since := "2024-10-20")]
alias lt_univ' := lt_univ

theorem small_iff_lift_mk_lt_univ {α : Type u} :
    Small.{v} α ↔ Cardinal.lift.{v + 1, u} #α < univ.{v, max u (v + 1)} := by
  rw [lt_univ]
  constructor
  · rintro ⟨β, ⟨e⟩⟩
    exact ⟨#β, lift_mk_eq.2 ⟨e.symm⟩⟩
  · rintro ⟨c, hc⟩
    exact ⟨⟨c.out, lift_mk_eq.{u, _, v + 1}.1 (hc.symm.trans (congr rfl c.mk_out.symm))⟩⟩

end Cardinal
