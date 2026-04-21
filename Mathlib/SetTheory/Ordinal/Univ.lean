/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn
-/
module

public import Mathlib.SetTheory.Ordinal.Basic

/-!
# Universal ordinal and cardinal

`Cardinal.univ` is the cardinality of the cardinals themselves. Likewise, `Ordinal.univ` is the
order type of the ordinals. These are related via `Cardinal.univ.ord = Ordinal.univ` and
`Ordinal.univ.card = Cardinal.univ`.

The cardinal `Cardinal.univ` is strongly inaccessible. This reflects the fact that in ZFC, the
cardinals form a proper class. See `IsInaccessible.univ` for a proof.

## Implementation notes

We actually define `Cardinal.univ` as the cardinality of `Ordinal`, rather than that of `Cardinal`.
This makes the basic API easier to set up. See `Cardinal.mk_cardinal` for a proof that
`Cardinal.univ = #Cardinal`.
-/

@[expose] public section

universe u v w

open Ordinal in
-- intended to be used with explicit universe parameters
/-- The ordinal `univ.{u, v}` is the order type of `Ordinal.{u}` or `Cardinal.{u}`, as an element of
`Ordinal.{v}` (when `u < v`). -/
@[pp_with_univ, nolint checkUnivs]
def Ordinal.univ : Ordinal.{max (u + 1) v} :=
  lift.{v, u + 1} (typeLT Ordinal)

open Cardinal in
-- intended to be used with explicit universe parameters
/-- The cardinal `univ.{u, v}` is the cardinality of `Ordinal.{u}` or `Cardinal.{u}`, as an element
of `Cardinal.{v}` (when `u < v`). -/
@[pp_with_univ, nolint checkUnivs]
def Cardinal.univ : Cardinal.{max (u + 1) v} :=
  lift.{v, u + 1} #Ordinal

/-! ### Universal ordinal -/

namespace Ordinal

@[simp]
theorem type_lt_ordinal : typeLT Ordinal = univ.{u, u + 1} :=
  (lift_id _).symm

@[deprecated type_lt_ordinal (since := "2026-03-20")]
theorem univ_id : univ.{u, u + 1} = typeLT Ordinal :=
  lift_id _

@[simp]
theorem lift_univ : lift.{w} univ.{u, v} = univ.{u, max v w} :=
  lift_lift _

theorem univ_umax : univ.{u, max (u + 1) v} = univ.{u, v} :=
  congr_fun lift_umax _

/-- Principal segment version of the lift operation on ordinals, embedding `Ordinal.{u}` in
`Ordinal.{v}` as a principal segment when `u < v`. -/
def liftPrincipalSeg : Ordinal.{u} <i Ordinal.{max (u + 1) v} :=
  ⟨liftInitialSeg.{max (u + 1) v, u}, univ.{u, v}, by
    refine fun b => inductionOn b ?_; intro β s _
    rw [univ, ← lift_umax]; constructor <;> intro h
    · obtain ⟨a, e⟩ := h
      rw [← e]
      refine inductionOn a ?_
      intro α r _
      exact lift_type_lt.{u, u + 1, max (u + 1) v}.2 ⟨typein r⟩
    · rw [← lift_id (type s)] at h ⊢
      obtain ⟨f⟩ := lift_type_lt.{_,_,v}.1 h
      obtain ⟨f, a, hf⟩ := f
      exists a
      induction a using inductionOn with | type α r
      refine lift_type_eq.{u, max (u + 1) v, max (u + 1) v}.2
        ⟨(RelIso.ofSurjective (RelEmbedding.ofMonotone ?_ ?_) ?_).symm⟩
      · exact fun b => enum r ⟨f b, (hf _).1 ⟨_, rfl⟩⟩
      · refine fun a b h => (typein_lt_typein r).1 ?_
        rw [typein_enum, typein_enum]
        exact f.map_rel_iff.2 h
      · intro a'
        obtain ⟨b, e⟩ := (hf _).2 (typein_lt_type _ a')
        exists b
        simp only [RelEmbedding.ofMonotone_coe]
        simp [e]⟩

@[simp]
theorem liftPrincipalSeg_coe :
    (liftPrincipalSeg.{u, v} : Ordinal → Ordinal) = lift.{max (u + 1) v} :=
  rfl

@[simp]
theorem liftPrincipalSeg_top : (liftPrincipalSeg.{u, v}).top = univ.{u, v} :=
  rfl

@[deprecated liftPrincipalSeg_top (since := "2026-03-20")]
theorem liftPrincipalSeg_top' : liftPrincipalSeg.{u, u + 1}.top = typeLT Ordinal := by
  simp

@[simp]
theorem card_univ : card univ.{u, v} = Cardinal.univ.{u, v} :=
  rfl

end Ordinal

/-! ### Universal cardinal -/

namespace Cardinal

theorem univ_id : univ.{u, u + 1} = #Ordinal :=
  lift_id _

@[simp]
theorem lift_univ : lift.{w} univ.{u, v} = univ.{u, max v w} :=
  lift_lift _

theorem univ_umax : univ.{u, max (u + 1) v} = univ.{u, v} :=
  congr_fun lift_umax _

theorem lift_lt_univ (c : Cardinal) : lift.{u + 1, u} c < univ.{u, u + 1} := by
  simpa only [Ordinal.liftPrincipalSeg_coe, lift_ord, lift_succ, ord_le, Order.succ_le_iff] using
    le_of_lt (Ordinal.liftPrincipalSeg.{u, u + 1}.lt_top (Order.succ c).ord)

theorem lift_lt_univ' (c : Cardinal) : lift.{max (u + 1) v, u} c < univ.{u, v} := by
  have := lift_lt.{_, max (u + 1) v}.2 (lift_lt_univ c)
  rw [lift_lift, lift_univ, univ_umax.{u, v}] at this
  exact this

theorem aleph0_lt_univ : ℵ₀ < univ.{u, v} := by
  simpa using lift_lt_univ' ℵ₀

theorem nat_lt_univ (n : ℕ) : n < univ.{u, v} := natCast_lt_aleph0.trans aleph0_lt_univ

theorem univ_pos : 0 < univ.{u, v} :=
  aleph0_pos.trans aleph0_lt_univ

theorem univ_ne_zero : univ.{u, v} ≠ 0 :=
  univ_pos.ne'

@[simp]
theorem ord_univ : ord univ.{u, v} = Ordinal.univ.{u, v} := by
  refine le_antisymm (ord_card_le _) <| le_of_forall_lt fun o h => lt_ord.2 ?_
  have := Ordinal.liftPrincipalSeg.mem_range_of_rel_top (by simpa using h)
  rcases this with ⟨o, h'⟩
  rw [← h', Ordinal.liftPrincipalSeg_coe, ← Ordinal.lift_card]
  apply lift_lt_univ'

theorem lt_univ {c} : c < univ.{u, u + 1} ↔ ∃ c', c = lift.{u + 1, u} c' :=
  ⟨fun h => by
    have := ord_lt_ord.2 h
    rw [ord_univ] at this
    obtain ⟨o, e⟩ := Ordinal.liftPrincipalSeg.mem_range_of_rel_top (by simpa)
    have := card_ord c
    rw [← e, Ordinal.liftPrincipalSeg_coe, ← Ordinal.lift_card] at this
    exact ⟨_, this.symm⟩, fun ⟨_, e⟩ => e.symm ▸ lift_lt_univ _⟩

theorem lt_univ' {c} : c < univ.{u, v} ↔ ∃ c', c = lift.{max (u + 1) v, u} c' :=
  ⟨fun h => by
    let ⟨a, h', e⟩ := lt_lift_iff.1 h
    rw [← univ_id] at h'
    rcases lt_univ.{u}.1 h' with ⟨c', rfl⟩
    exact ⟨c', by simp only [e.symm, lift_lift]⟩, fun ⟨_, e⟩ => e.symm ▸ lift_lt_univ' _⟩

theorem IsStrongLimit.univ : IsStrongLimit univ.{u, v} :=
  ⟨univ_ne_zero, fun c h ↦ let ⟨w, h⟩ := lt_univ'.1 h; lt_univ'.2 ⟨2 ^ w, by simp [h]⟩⟩

theorem small_iff_lift_mk_lt_univ {α : Type u} :
    Small.{v} α ↔ Cardinal.lift.{v + 1, _} #α < univ.{v, max u (v + 1)} := by
  rw [lt_univ']
  constructor
  · rintro ⟨β, e⟩
    exact ⟨#β, lift_mk_eq.{u, _, v + 1}.2 e⟩
  · rintro ⟨c, hc⟩
    exact ⟨⟨c.out, lift_mk_eq.{u, _, v + 1}.1 (hc.trans (congr rfl c.mk_out.symm))⟩⟩

end Cardinal
