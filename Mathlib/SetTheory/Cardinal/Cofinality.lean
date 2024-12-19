/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn, Violeta Hernández Palacios
-/
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Ordinal.FixedPoint

/-!
# Cofinality

This file contains the definition of cofinality of an ordinal number and regular cardinals

## Main Definitions

* `Ordinal.cof o` is the cofinality of the ordinal `o`.
  If `o` is the order type of the relation `<` on `α`, then `o.cof` is the smallest cardinality of a
  subset `s` of α that is *cofinal* in `α`, i.e. `∀ x : α, ∃ y ∈ s, ¬ y < x`.
* `Cardinal.IsStrongLimit c` means that `c` is a strong limit cardinal:
  `c ≠ 0 ∧ ∀ x < c, 2 ^ x < c`.
* `Cardinal.IsRegular c` means that `c` is a regular cardinal: `ℵ₀ ≤ c ∧ c.ord.cof = c`.
* `Cardinal.IsInaccessible c` means that `c` is strongly inaccessible:
  `ℵ₀ < c ∧ IsRegular c ∧ IsStrongLimit c`.

## Main Statements

* `Ordinal.infinite_pigeonhole_card`: the infinite pigeonhole principle
* `Cardinal.lt_power_cof`: A consequence of König's theorem stating that `c < c ^ c.ord.cof` for
  `c ≥ ℵ₀`
* `Cardinal.univ_inaccessible`: The type of ordinals in `Type u` form an inaccessible cardinal
  (in `Type v` with `v > u`). This shows (externally) that in `Type u` there are at least `u`
  inaccessible cardinals.

## Implementation Notes

* The cofinality is defined for ordinals.
  If `c` is a cardinal number, its cofinality is `c.ord.cof`.

## Tags

cofinality, regular cardinals, limits cardinals, inaccessible cardinals,
infinite pigeonhole principle
-/

noncomputable section

open Function Cardinal Set Order
open scoped Ordinal

universe u v w

variable {α : Type u} {β : Type v} {r : α → α → Prop} {s : β → β → Prop}

/-! ### Cofinality of orders -/

attribute [local instance] IsRefl.swap

namespace Order

/-- Cofinality of a reflexive order `≼`. This is the smallest cardinality
  of a subset `S : Set α` such that `∀ a, ∃ b ∈ S, a ≼ b`. -/
def cof (r : α → α → Prop) : Cardinal :=
  sInf { c | ∃ S : Set α, (∀ a, ∃ b ∈ S, r a b) ∧ #S = c }

/-- The set in the definition of `Order.cof` is nonempty. -/
private theorem cof_nonempty (r : α → α → Prop) [IsRefl α r] :
    { c | ∃ S : Set α, (∀ a, ∃ b ∈ S, r a b) ∧ #S = c }.Nonempty :=
  ⟨_, Set.univ, fun a => ⟨a, ⟨⟩, refl _⟩, rfl⟩

theorem cof_le (r : α → α → Prop) {S : Set α} (h : ∀ a, ∃ b ∈ S, r a b) : cof r ≤ #S :=
  csInf_le' ⟨S, h, rfl⟩

theorem le_cof [IsRefl α r] (c : Cardinal) :
    c ≤ cof r ↔ ∀ {S : Set α}, (∀ a, ∃ b ∈ S, r a b) → c ≤ #S := by
  rw [cof, le_csInf_iff'' (cof_nonempty r)]
  use fun H S h => H _ ⟨S, h, rfl⟩
  rintro H d ⟨S, h, rfl⟩
  exact H h

end Order

namespace RelIso

private theorem cof_le_lift [IsRefl β s] (f : r ≃r s) :
    Cardinal.lift.{v} (Order.cof r) ≤ Cardinal.lift.{u} (Order.cof s) := by
  rw [Order.cof, Order.cof, lift_sInf, lift_sInf, le_csInf_iff'' ((Order.cof_nonempty s).image _)]
  rintro - ⟨-, ⟨u, H, rfl⟩, rfl⟩
  apply csInf_le'
  refine ⟨_, ⟨f.symm '' u, fun a => ?_, rfl⟩, lift_mk_eq'.2 ⟨(f.symm.toEquiv.image u).symm⟩⟩
  rcases H (f a) with ⟨b, hb, hb'⟩
  refine ⟨f.symm b, mem_image_of_mem _ hb, f.map_rel_iff.1 ?_⟩
  rwa [RelIso.apply_symm_apply]

theorem cof_eq_lift [IsRefl β s] (f : r ≃r s) :
    Cardinal.lift.{v} (Order.cof r) = Cardinal.lift.{u} (Order.cof s) :=
  have := f.toRelEmbedding.isRefl
  (f.cof_le_lift).antisymm (f.symm.cof_le_lift)

theorem cof_eq {α β : Type u} {r : α → α → Prop} {s} [IsRefl β s] (f : r ≃r s) :
    Order.cof r = Order.cof s :=
  lift_inj.1 (f.cof_eq_lift)

@[deprecated cof_eq (since := "2024-10-22")]
theorem cof_le {α β : Type u} {r : α → α → Prop} {s} [IsRefl β s] (f : r ≃r s) :
    Order.cof r ≤ Order.cof s :=
  f.cof_eq.le

end RelIso

/-- Cofinality of a strict order `≺`. This is the smallest cardinality of a set `S : Set α` such
that `∀ a, ∃ b ∈ S, ¬ b ≺ a`. -/
@[deprecated Order.cof (since := "2024-10-22")]
def StrictOrder.cof (r : α → α → Prop) : Cardinal :=
  Order.cof (swap rᶜ)

/-- The set in the definition of `Order.StrictOrder.cof` is nonempty. -/
@[deprecated "No deprecation message was provided." (since := "2024-10-22")]
theorem StrictOrder.cof_nonempty (r : α → α → Prop) [IsIrrefl α r] :
    { c | ∃ S : Set α, Unbounded r S ∧ #S = c }.Nonempty :=
  @Order.cof_nonempty α _ (IsRefl.swap rᶜ)

/-! ### Cofinality of ordinals -/

namespace Ordinal

/-- Cofinality of an ordinal. This is the smallest cardinal of a subset `S` of the ordinal which is
unbounded, in the sense `∀ a, ∃ b ∈ S, a ≤ b`.

In particular, `cof 0 = 0` and `cof (succ o) = 1`. -/
def cof (o : Ordinal.{u}) : Cardinal.{u} :=
  o.liftOn (fun a ↦ Order.cof (swap a.rᶜ)) fun _ _ ⟨f⟩ ↦ f.compl.swap.cof_eq

theorem cof_type (r : α → α → Prop) [IsWellOrder α r] : (type r).cof = Order.cof (swap rᶜ) :=
  rfl

theorem cof_type_lt [LinearOrder α] [IsWellOrder α (· < ·)] :
    (@type α (· < ·) _).cof = @Order.cof α (· ≤ ·) := by
  rw [cof_type, compl_lt, swap_ge]

theorem cof_eq_cof_toType (o : Ordinal) : o.cof = @Order.cof o.toType (· ≤ ·) := by
  conv_lhs => rw [← type_toType o, cof_type_lt]

theorem le_cof_type [IsWellOrder α r] {c} : c ≤ cof (type r) ↔ ∀ S, Unbounded r S → c ≤ #S :=
  (le_csInf_iff'' (Order.cof_nonempty _)).trans
    ⟨fun H S h => H _ ⟨S, h, rfl⟩, by
      rintro H d ⟨S, h, rfl⟩
      exact H _ h⟩

theorem cof_type_le [IsWellOrder α r] {S : Set α} (h : Unbounded r S) : cof (type r) ≤ #S :=
  le_cof_type.1 le_rfl S h

theorem lt_cof_type [IsWellOrder α r] {S : Set α} : #S < cof (type r) → Bounded r S := by
  simpa using not_imp_not.2 cof_type_le

theorem cof_eq (r : α → α → Prop) [IsWellOrder α r] : ∃ S, Unbounded r S ∧ #S = cof (type r) :=
  csInf_mem (Order.cof_nonempty (swap rᶜ))

theorem ord_cof_eq (r : α → α → Prop) [IsWellOrder α r] :
    ∃ S, Unbounded r S ∧ type (Subrel r S) = (cof (type r)).ord := by
  let ⟨S, hS, e⟩ := cof_eq r
  let ⟨s, _, e'⟩ := Cardinal.ord_eq S
  let T : Set α := { a | ∃ aS : a ∈ S, ∀ b : S, s b ⟨_, aS⟩ → r b a }
  suffices Unbounded r T by
    refine ⟨T, this, le_antisymm ?_ (Cardinal.ord_le.2 <| cof_type_le this)⟩
    rw [← e, e']
    refine
      (RelEmbedding.ofMonotone
          (fun a : T =>
            (⟨a,
                let ⟨aS, _⟩ := a.2
                aS⟩ :
              S))
          fun a b h => ?_).ordinal_type_le
    rcases a with ⟨a, aS, ha⟩
    rcases b with ⟨b, bS, hb⟩
    change s ⟨a, _⟩ ⟨b, _⟩
    refine ((trichotomous_of s _ _).resolve_left fun hn => ?_).resolve_left ?_
    · exact asymm h (ha _ hn)
    · intro e
      injection e with e
      subst b
      exact irrefl _ h
  intro a
  have : { b : S | ¬r b a }.Nonempty :=
    let ⟨b, bS, ba⟩ := hS a
    ⟨⟨b, bS⟩, ba⟩
  let b := (IsWellFounded.wf : WellFounded s).min _ this
  have ba : ¬r b a := IsWellFounded.wf.min_mem _ this
  refine ⟨b, ⟨b.2, fun c => not_imp_not.1 fun h => ?_⟩, ba⟩
  rw [show ∀ b : S, (⟨b, b.2⟩ : S) = b by intro b; cases b; rfl]
  exact IsWellFounded.wf.not_lt_min _ this (IsOrderConnected.neg_trans h ba)

/-! ### Cofinality of suprema and least strict upper bounds -/


private theorem card_mem_cof {o} : ∃ (ι : _) (f : ι → Ordinal), lsub.{u, u} f = o ∧ #ι = o.card :=
  ⟨_, _, lsub_typein o, mk_toType o⟩

/-- The set in the `lsub` characterization of `cof` is nonempty. -/
theorem cof_lsub_def_nonempty (o) :
    { a : Cardinal | ∃ (ι : _) (f : ι → Ordinal), lsub.{u, u} f = o ∧ #ι = a }.Nonempty :=
  ⟨_, card_mem_cof⟩

theorem cof_eq_sInf_lsub (o : Ordinal.{u}) : cof o =
    sInf { a : Cardinal | ∃ (ι : Type u) (f : ι → Ordinal), lsub.{u, u} f = o ∧ #ι = a } := by
  refine le_antisymm (le_csInf (cof_lsub_def_nonempty o) ?_) (csInf_le' ?_)
  · rintro a ⟨ι, f, hf, rfl⟩
    rw [← type_toType o]
    refine
      (cof_type_le fun a => ?_).trans
        (@mk_le_of_injective _ _
          (fun s : typein ((· < ·) : o.toType → o.toType → Prop) ⁻¹' Set.range f =>
            Classical.choose s.prop)
          fun s t hst => by
          let H := congr_arg f hst
          rwa [Classical.choose_spec s.prop, Classical.choose_spec t.prop, typein_inj,
            Subtype.coe_inj] at H)
    have := typein_lt_self a
    simp_rw [← hf, lt_lsub_iff] at this
    cases' this with i hi
    refine ⟨enum (α := o.toType) (· < ·) ⟨f i, ?_⟩, ?_, ?_⟩
    · rw [type_toType, ← hf]
      apply lt_lsub
    · rw [mem_preimage, typein_enum]
      exact mem_range_self i
    · rwa [← typein_le_typein, typein_enum]
  · rcases cof_eq (α := o.toType) (· < ·) with ⟨S, hS, hS'⟩
    let f : S → Ordinal := fun s => typein LT.lt s.val
    refine ⟨S, f, le_antisymm (lsub_le fun i => typein_lt_self (o := o) i)
      (le_of_forall_lt fun a ha => ?_), by rwa [type_toType o] at hS'⟩
    rw [← type_toType o] at ha
    rcases hS (enum (· < ·) ⟨a, ha⟩) with ⟨b, hb, hb'⟩
    rw [← typein_le_typein, typein_enum] at hb'
    exact hb'.trans_lt (lt_lsub.{u, u} f ⟨b, hb⟩)

@[simp]
theorem lift_cof (o) : Cardinal.lift.{u, v} (cof o) = cof (Ordinal.lift.{u, v} o) := by
  refine inductionOn o fun α r _ ↦ ?_
  rw [← type_uLift, cof_type, cof_type, ← Cardinal.lift_id'.{v, u} (Order.cof _),
    ← Cardinal.lift_umax]
  apply RelIso.cof_eq_lift ⟨Equiv.ulift.symm, _⟩
  simp [swap]

theorem cof_le_card (o) : cof o ≤ card o := by
  rw [cof_eq_sInf_lsub]
  exact csInf_le' card_mem_cof

theorem cof_ord_le (c : Cardinal) : c.ord.cof ≤ c := by simpa using cof_le_card c.ord

theorem ord_cof_le (o : Ordinal.{u}) : o.cof.ord ≤ o :=
  (ord_le_ord.2 (cof_le_card o)).trans (ord_card_le o)

theorem exists_lsub_cof (o : Ordinal) :
    ∃ (ι : _) (f : ι → Ordinal), lsub.{u, u} f = o ∧ #ι = cof o := by
  rw [cof_eq_sInf_lsub]
  exact csInf_mem (cof_lsub_def_nonempty o)

theorem cof_lsub_le {ι} (f : ι → Ordinal) : cof (lsub.{u, u} f) ≤ #ι := by
  rw [cof_eq_sInf_lsub]
  exact csInf_le' ⟨ι, f, rfl, rfl⟩

theorem cof_lsub_le_lift {ι} (f : ι → Ordinal) :
    cof (lsub.{u, v} f) ≤ Cardinal.lift.{v, u} #ι := by
  rw [← mk_uLift.{u, v}]
  convert cof_lsub_le.{max u v} fun i : ULift.{v, u} ι => f i.down
  exact
    lsub_eq_of_range_eq.{u, max u v, max u v}
      (Set.ext fun x => ⟨fun ⟨i, hi⟩ => ⟨ULift.up.{v, u} i, hi⟩, fun ⟨i, hi⟩ => ⟨_, hi⟩⟩)

theorem le_cof_iff_lsub {o : Ordinal} {a : Cardinal} :
    a ≤ cof o ↔ ∀ {ι} (f : ι → Ordinal), lsub.{u, u} f = o → a ≤ #ι := by
  rw [cof_eq_sInf_lsub]
  exact
    (le_csInf_iff'' (cof_lsub_def_nonempty o)).trans
      ⟨fun H ι f hf => H _ ⟨ι, f, hf, rfl⟩, fun H b ⟨ι, f, hf, hb⟩ => by
        rw [← hb]
        exact H _ hf⟩

theorem lsub_lt_ord_lift {ι} {f : ι → Ordinal} {c : Ordinal}
    (hι : Cardinal.lift.{v, u} #ι < c.cof)
    (hf : ∀ i, f i < c) : lsub.{u, v} f < c :=
  lt_of_le_of_ne (lsub_le hf) fun h => by
    subst h
    exact (cof_lsub_le_lift.{u, v} f).not_lt hι

theorem lsub_lt_ord {ι} {f : ι → Ordinal} {c : Ordinal} (hι : #ι < c.cof) :
    (∀ i, f i < c) → lsub.{u, u} f < c :=
  lsub_lt_ord_lift (by rwa [(#ι).lift_id])

theorem cof_iSup_le_lift {ι} {f : ι → Ordinal} (H : ∀ i, f i < iSup f) :
    cof (iSup f) ≤ Cardinal.lift.{v, u} #ι := by
  rw [← Ordinal.sup] at *
  rw [← sup_eq_lsub_iff_lt_sup.{u, v}] at H
  rw [H]
  exact cof_lsub_le_lift f

set_option linter.deprecated false in
@[deprecated cof_iSup_le_lift (since := "2024-08-27")]
theorem cof_sup_le_lift {ι} {f : ι → Ordinal} (H : ∀ i, f i < sup.{u, v} f) :
    cof (sup.{u, v} f) ≤ Cardinal.lift.{v, u} #ι := by
  rw [← sup_eq_lsub_iff_lt_sup.{u, v}] at H
  rw [H]
  exact cof_lsub_le_lift f

theorem cof_iSup_le {ι} {f : ι → Ordinal} (H : ∀ i, f i < iSup f) :
    cof (iSup f) ≤ #ι := by
  rw [← (#ι).lift_id]
  exact cof_iSup_le_lift H

set_option linter.deprecated false in
@[deprecated cof_iSup_le (since := "2024-08-27")]
theorem cof_sup_le {ι} {f : ι → Ordinal} (H : ∀ i, f i < sup.{u, u} f) :
    cof (sup.{u, u} f) ≤ #ι := by
  rw [← (#ι).lift_id]
  exact cof_sup_le_lift H

theorem iSup_lt_ord_lift {ι} {f : ι → Ordinal} {c : Ordinal} (hι : Cardinal.lift.{v, u} #ι < c.cof)
    (hf : ∀ i, f i < c) : iSup f < c :=
  (sup_le_lsub.{u, v} f).trans_lt (lsub_lt_ord_lift hι hf)

set_option linter.deprecated false in
@[deprecated iSup_lt_ord_lift (since := "2024-08-27")]
theorem sup_lt_ord_lift {ι} {f : ι → Ordinal} {c : Ordinal} (hι : Cardinal.lift.{v, u} #ι < c.cof)
    (hf : ∀ i, f i < c) : sup.{u, v} f < c :=
  iSup_lt_ord_lift hι hf

theorem iSup_lt_ord {ι} {f : ι → Ordinal} {c : Ordinal} (hι : #ι < c.cof) :
    (∀ i, f i < c) → iSup f < c :=
  iSup_lt_ord_lift (by rwa [(#ι).lift_id])

set_option linter.deprecated false in
@[deprecated iSup_lt_ord (since := "2024-08-27")]
theorem sup_lt_ord {ι} {f : ι → Ordinal} {c : Ordinal} (hι : #ι < c.cof) :
    (∀ i, f i < c) → sup.{u, u} f < c :=
  sup_lt_ord_lift (by rwa [(#ι).lift_id])

theorem iSup_lt_lift {ι} {f : ι → Cardinal} {c : Cardinal}
    (hι : Cardinal.lift.{v, u} #ι < c.ord.cof)
    (hf : ∀ i, f i < c) : iSup f < c := by
  rw [← ord_lt_ord, iSup_ord (Cardinal.bddAbove_range _)]
  refine iSup_lt_ord_lift hι fun i => ?_
  rw [ord_lt_ord]
  apply hf

theorem iSup_lt {ι} {f : ι → Cardinal} {c : Cardinal} (hι : #ι < c.ord.cof) :
    (∀ i, f i < c) → iSup f < c :=
  iSup_lt_lift (by rwa [(#ι).lift_id])

theorem nfpFamily_lt_ord_lift {ι} {f : ι → Ordinal → Ordinal} {c} (hc : ℵ₀ < cof c)
    (hc' : Cardinal.lift.{v, u} #ι < cof c) (hf : ∀ (i), ∀ b < c, f i b < c) {a} (ha : a < c) :
    nfpFamily f a < c := by
  refine iSup_lt_ord_lift ((Cardinal.lift_le.2 (mk_list_le_max ι)).trans_lt ?_) fun l => ?_
  · rw [lift_max]
    apply max_lt _ hc'
    rwa [Cardinal.lift_aleph0]
  · induction' l with i l H
    · exact ha
    · exact hf _ _ H

theorem nfpFamily_lt_ord {ι} {f : ι → Ordinal → Ordinal} {c} (hc : ℵ₀ < cof c) (hc' : #ι < cof c)
    (hf : ∀ (i), ∀ b < c, f i b < c) {a} : a < c → nfpFamily.{u, u} f a < c :=
  nfpFamily_lt_ord_lift hc (by rwa [(#ι).lift_id]) hf

set_option linter.deprecated false in
@[deprecated nfpFamily_lt_ord_lift (since := "2024-10-14")]
theorem nfpBFamily_lt_ord_lift {o : Ordinal} {f : ∀ a < o, Ordinal → Ordinal} {c} (hc : ℵ₀ < cof c)
    (hc' : Cardinal.lift.{v, u} o.card < cof c) (hf : ∀ (i hi), ∀ b < c, f i hi b < c) {a} :
    a < c → nfpBFamily.{u, v} o f a < c :=
  nfpFamily_lt_ord_lift hc (by rwa [mk_toType]) fun _ => hf _ _

set_option linter.deprecated false in
@[deprecated nfpFamily_lt_ord (since := "2024-10-14")]
theorem nfpBFamily_lt_ord {o : Ordinal} {f : ∀ a < o, Ordinal → Ordinal} {c} (hc : ℵ₀ < cof c)
    (hc' : o.card < cof c) (hf : ∀ (i hi), ∀ b < c, f i hi b < c) {a} :
    a < c → nfpBFamily.{u, u} o f a < c :=
  nfpBFamily_lt_ord_lift hc (by rwa [o.card.lift_id]) hf

theorem nfp_lt_ord {f : Ordinal → Ordinal} {c} (hc : ℵ₀ < cof c) (hf : ∀ i < c, f i < c) {a} :
    a < c → nfp f a < c :=
  nfpFamily_lt_ord_lift hc (by simpa using Cardinal.one_lt_aleph0.trans hc) fun _ => hf

theorem exists_blsub_cof (o : Ordinal) :
    ∃ f : ∀ a < (cof o).ord, Ordinal, blsub.{u, u} _ f = o := by
  rcases exists_lsub_cof o with ⟨ι, f, hf, hι⟩
  rcases Cardinal.ord_eq ι with ⟨r, hr, hι'⟩
  rw [← @blsub_eq_lsub' ι r hr] at hf
  rw [← hι, hι']
  exact ⟨_, hf⟩

theorem le_cof_iff_blsub {b : Ordinal} {a : Cardinal} :
    a ≤ cof b ↔ ∀ {o} (f : ∀ a < o, Ordinal), blsub.{u, u} o f = b → a ≤ o.card :=
  le_cof_iff_lsub.trans
    ⟨fun H o f hf => by simpa using H _ hf, fun H ι f hf => by
      rcases Cardinal.ord_eq ι with ⟨r, hr, hι'⟩
      rw [← @blsub_eq_lsub' ι r hr] at hf
      simpa using H _ hf⟩

theorem cof_blsub_le_lift {o} (f : ∀ a < o, Ordinal) :
    cof (blsub.{u, v} o f) ≤ Cardinal.lift.{v, u} o.card := by
  rw [← mk_toType o]
  exact cof_lsub_le_lift _

theorem cof_blsub_le {o} (f : ∀ a < o, Ordinal) : cof (blsub.{u, u} o f) ≤ o.card := by
  rw [← o.card.lift_id]
  exact cof_blsub_le_lift f

theorem blsub_lt_ord_lift {o : Ordinal.{u}} {f : ∀ a < o, Ordinal} {c : Ordinal}
    (ho : Cardinal.lift.{v, u} o.card < c.cof) (hf : ∀ i hi, f i hi < c) : blsub.{u, v} o f < c :=
  lt_of_le_of_ne (blsub_le hf) fun h =>
    ho.not_le (by simpa [← iSup_ord, hf, h] using cof_blsub_le_lift.{u, v} f)

theorem blsub_lt_ord {o : Ordinal} {f : ∀ a < o, Ordinal} {c : Ordinal} (ho : o.card < c.cof)
    (hf : ∀ i hi, f i hi < c) : blsub.{u, u} o f < c :=
  blsub_lt_ord_lift (by rwa [o.card.lift_id]) hf

theorem cof_bsup_le_lift {o : Ordinal} {f : ∀ a < o, Ordinal} (H : ∀ i h, f i h < bsup.{u, v} o f) :
    cof (bsup.{u, v} o f) ≤ Cardinal.lift.{v, u} o.card := by
  rw [← bsup_eq_blsub_iff_lt_bsup.{u, v}] at H
  rw [H]
  exact cof_blsub_le_lift.{u, v} f

theorem cof_bsup_le {o : Ordinal} {f : ∀ a < o, Ordinal} :
    (∀ i h, f i h < bsup.{u, u} o f) → cof (bsup.{u, u} o f) ≤ o.card := by
  rw [← o.card.lift_id]
  exact cof_bsup_le_lift

theorem bsup_lt_ord_lift {o : Ordinal} {f : ∀ a < o, Ordinal} {c : Ordinal}
    (ho : Cardinal.lift.{v, u} o.card < c.cof) (hf : ∀ i hi, f i hi < c) : bsup.{u, v} o f < c :=
  (bsup_le_blsub f).trans_lt (blsub_lt_ord_lift ho hf)

theorem bsup_lt_ord {o : Ordinal} {f : ∀ a < o, Ordinal} {c : Ordinal} (ho : o.card < c.cof) :
    (∀ i hi, f i hi < c) → bsup.{u, u} o f < c :=
  bsup_lt_ord_lift (by rwa [o.card.lift_id])

/-! ### Basic results -/


@[simp]
theorem cof_zero : cof 0 = 0 := by
  refine LE.le.antisymm  ?_ (Cardinal.zero_le _)
  rw [← card_zero]
  exact cof_le_card 0

@[simp]
theorem cof_eq_zero {o} : cof o = 0 ↔ o = 0 :=
  ⟨inductionOn o fun _ r _ z =>
      let ⟨_, hl, e⟩ := cof_eq r
      type_eq_zero_iff_isEmpty.2 <|
        ⟨fun a =>
          let ⟨_, h, _⟩ := hl a
          (mk_eq_zero_iff.1 (e.trans z)).elim' ⟨_, h⟩⟩,
    fun e => by simp [e]⟩

theorem cof_ne_zero {o} : cof o ≠ 0 ↔ o ≠ 0 :=
  cof_eq_zero.not

@[simp]
theorem cof_succ (o) : cof (succ o) = 1 := by
  apply le_antisymm
  · refine inductionOn o fun α r _ => ?_
    change cof (type _) ≤ _
    rw [← (_ : #_ = 1)]
    · apply cof_type_le
      refine fun a => ⟨Sum.inr PUnit.unit, Set.mem_singleton _, ?_⟩
      rcases a with (a | ⟨⟨⟨⟩⟩⟩) <;> simp [EmptyRelation]
    · rw [Cardinal.mk_fintype, Set.card_singleton]
      simp
  · rw [← Cardinal.succ_zero, succ_le_iff]
    simpa [lt_iff_le_and_ne, Cardinal.zero_le] using fun h =>
      succ_ne_zero o (cof_eq_zero.1 (Eq.symm h))

@[simp]
theorem cof_eq_one_iff_is_succ {o} : cof.{u} o = 1 ↔ ∃ a, o = succ a :=
  ⟨inductionOn o fun α r _ z => by
      rcases cof_eq r with ⟨S, hl, e⟩; rw [z] at e
      cases' mk_ne_zero_iff.1 (by rw [e]; exact one_ne_zero) with a
      refine
        ⟨typein r a,
          Eq.symm <|
            Quotient.sound
              ⟨RelIso.ofSurjective (RelEmbedding.ofMonotone ?_ fun x y => ?_) fun x => ?_⟩⟩
      · apply Sum.rec <;> [exact Subtype.val; exact fun _ => a]
      · rcases x with (x | ⟨⟨⟨⟩⟩⟩) <;> rcases y with (y | ⟨⟨⟨⟩⟩⟩) <;>
          simp [Subrel, Order.Preimage, EmptyRelation]
        exact x.2
      · suffices r x a ∨ ∃ _ : PUnit.{u}, ↑a = x by
          convert this
          dsimp [RelEmbedding.ofMonotone]; simp
        rcases trichotomous_of r x a with (h | h | h)
        · exact Or.inl h
        · exact Or.inr ⟨PUnit.unit, h.symm⟩
        · rcases hl x with ⟨a', aS, hn⟩
          refine absurd h ?_
          convert hn
          change (a : α) = ↑(⟨a', aS⟩ : S)
          have := le_one_iff_subsingleton.1 (le_of_eq e)
          congr!,
    fun ⟨a, e⟩ => by simp [e]⟩

/-- A fundamental sequence for `a` is an increasing sequence of length `o = cof a` that converges at
    `a`. We provide `o` explicitly in order to avoid type rewrites. -/
def IsFundamentalSequence (a o : Ordinal.{u}) (f : ∀ b < o, Ordinal.{u}) : Prop :=
  o ≤ a.cof.ord ∧ (∀ {i j} (hi hj), i < j → f i hi < f j hj) ∧ blsub.{u, u} o f = a

namespace IsFundamentalSequence

variable {a o : Ordinal.{u}} {f : ∀ b < o, Ordinal.{u}}

protected theorem cof_eq (hf : IsFundamentalSequence a o f) : a.cof.ord = o :=
  hf.1.antisymm' <| by
    rw [← hf.2.2]
    exact (ord_le_ord.2 (cof_blsub_le f)).trans (ord_card_le o)

protected theorem strict_mono (hf : IsFundamentalSequence a o f) {i j} :
    ∀ hi hj, i < j → f i hi < f j hj :=
  hf.2.1

theorem blsub_eq (hf : IsFundamentalSequence a o f) : blsub.{u, u} o f = a :=
  hf.2.2

theorem ord_cof (hf : IsFundamentalSequence a o f) :
    IsFundamentalSequence a a.cof.ord fun i hi => f i (hi.trans_le (by rw [hf.cof_eq])) := by
  have H := hf.cof_eq
  subst H
  exact hf

theorem id_of_le_cof (h : o ≤ o.cof.ord) : IsFundamentalSequence o o fun a _ => a :=
  ⟨h, @fun _ _ _ _ => id, blsub_id o⟩

protected theorem zero {f : ∀ b < (0 : Ordinal), Ordinal} : IsFundamentalSequence 0 0 f :=
  ⟨by rw [cof_zero, ord_zero], @fun i _ hi => (Ordinal.not_lt_zero i hi).elim, blsub_zero f⟩

protected theorem succ : IsFundamentalSequence (succ o) 1 fun _ _ => o := by
  refine ⟨?_, @fun i j hi hj h => ?_, blsub_const Ordinal.one_ne_zero o⟩
  · rw [cof_succ, ord_one]
  · rw [lt_one_iff_zero] at hi hj
    rw [hi, hj] at h
    exact h.false.elim

protected theorem monotone (hf : IsFundamentalSequence a o f) {i j : Ordinal} (hi : i < o)
    (hj : j < o) (hij : i ≤ j) : f i hi ≤ f j hj := by
  rcases lt_or_eq_of_le hij with (hij | rfl)
  · exact (hf.2.1 hi hj hij).le
  · rfl

theorem trans {a o o' : Ordinal.{u}} {f : ∀ b < o, Ordinal.{u}} (hf : IsFundamentalSequence a o f)
    {g : ∀ b < o', Ordinal.{u}} (hg : IsFundamentalSequence o o' g) :
    IsFundamentalSequence a o' fun i hi =>
      f (g i hi) (by rw [← hg.2.2]; apply lt_blsub) := by
  refine ⟨?_, @fun i j _ _ h => hf.2.1 _ _ (hg.2.1 _ _ h), ?_⟩
  · rw [hf.cof_eq]
    exact hg.1.trans (ord_cof_le o)
  · rw [@blsub_comp.{u, u, u} o _ f (@IsFundamentalSequence.monotone _ _ f hf)]
    · exact hf.2.2
    · exact hg.2.2

protected theorem lt {a o : Ordinal} {s : Π p < o, Ordinal}
    (h : IsFundamentalSequence a o s) {p : Ordinal} (hp : p < o) : s p hp < a :=
  h.blsub_eq ▸ lt_blsub s p hp

end IsFundamentalSequence

/-- Every ordinal has a fundamental sequence. -/
theorem exists_fundamental_sequence (a : Ordinal.{u}) :
    ∃ f, IsFundamentalSequence a a.cof.ord f := by
  suffices h : ∃ o f, IsFundamentalSequence a o f by
    rcases h with ⟨o, f, hf⟩
    exact ⟨_, hf.ord_cof⟩
  rcases exists_lsub_cof a with ⟨ι, f, hf, hι⟩
  rcases ord_eq ι with ⟨r, wo, hr⟩
  haveI := wo
  let r' := Subrel r { i | ∀ j, r j i → f j < f i }
  let hrr' : r' ↪r r := Subrel.relEmbedding _ _
  haveI := hrr'.isWellOrder
  refine
    ⟨_, _, hrr'.ordinal_type_le.trans ?_, @fun i j _ h _ => (enum r' ⟨j, h⟩).prop _ ?_,
      le_antisymm (blsub_le fun i hi => lsub_le_iff.1 hf.le _) ?_⟩
  · rw [← hι, hr]
  · change r (hrr'.1 _) (hrr'.1 _)
    rwa [hrr'.2, @enum_lt_enum _ r']
  · rw [← hf, lsub_le_iff]
    intro i
    suffices h : ∃ i' hi', f i ≤ bfamilyOfFamily' r' (fun i => f i) i' hi' by
      rcases h with ⟨i', hi', hfg⟩
      exact hfg.trans_lt (lt_blsub _ _ _)
    by_cases h : ∀ j, r j i → f j < f i
    · refine ⟨typein r' ⟨i, h⟩, typein_lt_type _ _, ?_⟩
      rw [bfamilyOfFamily'_typein]
    · push_neg at h
      cases' wo.wf.min_mem _ h with hji hij
      refine ⟨typein r' ⟨_, fun k hkj => lt_of_lt_of_le ?_ hij⟩, typein_lt_type _ _, ?_⟩
      · by_contra! H
        exact (wo.wf.not_lt_min _ h ⟨IsTrans.trans _ _ _ hkj hji, H⟩) hkj
      · rwa [bfamilyOfFamily'_typein]

@[simp]
theorem cof_cof (a : Ordinal.{u}) : cof (cof a).ord = cof a := by
  cases' exists_fundamental_sequence a with f hf
  cases' exists_fundamental_sequence a.cof.ord with g hg
  exact ord_injective (hf.trans hg).cof_eq.symm

protected theorem IsNormal.isFundamentalSequence {f : Ordinal.{u} → Ordinal.{u}} (hf : IsNormal f)
    {a o} (ha : IsLimit a) {g} (hg : IsFundamentalSequence a o g) :
    IsFundamentalSequence (f a) o fun b hb => f (g b hb) := by
  refine ⟨?_, @fun i j _ _ h => hf.strictMono (hg.2.1 _ _ h), ?_⟩
  · rcases exists_lsub_cof (f a) with ⟨ι, f', hf', hι⟩
    rw [← hg.cof_eq, ord_le_ord, ← hι]
    suffices (lsub.{u, u} fun i => sInf { b : Ordinal | f' i ≤ f b }) = a by
      rw [← this]
      apply cof_lsub_le
    have H : ∀ i, ∃ b < a, f' i ≤ f b := fun i => by
      have := lt_lsub.{u, u} f' i
      rw [hf', ← IsNormal.blsub_eq.{u, u} hf ha, lt_blsub_iff] at this
      simpa using this
    refine (lsub_le fun i => ?_).antisymm (le_of_forall_lt fun b hb => ?_)
    · rcases H i with ⟨b, hb, hb'⟩
      exact lt_of_le_of_lt (csInf_le' hb') hb
    · have := hf.strictMono hb
      rw [← hf', lt_lsub_iff] at this
      cases' this with i hi
      rcases H i with ⟨b, _, hb⟩
      exact
        ((le_csInf_iff'' ⟨b, by exact hb⟩).2 fun c hc =>
          hf.strictMono.le_iff_le.1 (hi.trans hc)).trans_lt (lt_lsub _ i)
  · rw [@blsub_comp.{u, u, u} a _ (fun b _ => f b) (@fun i j _ _ h => hf.strictMono.monotone h) g
        hg.2.2]
    exact IsNormal.blsub_eq.{u, u} hf ha

theorem IsNormal.cof_eq {f} (hf : IsNormal f) {a} (ha : IsLimit a) : cof (f a) = cof a :=
  let ⟨_, hg⟩ := exists_fundamental_sequence a
  ord_injective (hf.isFundamentalSequence ha hg).cof_eq

theorem IsNormal.cof_le {f} (hf : IsNormal f) (a) : cof a ≤ cof (f a) := by
  rcases zero_or_succ_or_limit a with (rfl | ⟨b, rfl⟩ | ha)
  · rw [cof_zero]
    exact zero_le _
  · rw [cof_succ, Cardinal.one_le_iff_ne_zero, cof_ne_zero, ← Ordinal.pos_iff_ne_zero]
    exact (Ordinal.zero_le (f b)).trans_lt (hf.1 b)
  · rw [hf.cof_eq ha]

@[simp]
theorem cof_add (a b : Ordinal) : b ≠ 0 → cof (a + b) = cof b := fun h => by
  rcases zero_or_succ_or_limit b with (rfl | ⟨c, rfl⟩ | hb)
  · contradiction
  · rw [add_succ, cof_succ, cof_succ]
  · exact (isNormal_add_right a).cof_eq hb

theorem aleph0_le_cof {o} : ℵ₀ ≤ cof o ↔ IsLimit o := by
  rcases zero_or_succ_or_limit o with (rfl | ⟨o, rfl⟩ | l)
  · simp [not_zero_isLimit, Cardinal.aleph0_ne_zero]
  · simp [not_succ_isLimit, Cardinal.one_lt_aleph0]
  · simp only [l, iff_true]
    refine le_of_not_lt fun h => ?_
    cases' Cardinal.lt_aleph0.1 h with n e
    have := cof_cof o
    rw [e, ord_nat] at this
    cases n
    · simp at e
      simp [e, not_zero_isLimit] at l
    · rw [natCast_succ, cof_succ] at this
      rw [← this, cof_eq_one_iff_is_succ] at e
      rcases e with ⟨a, rfl⟩
      exact not_succ_isLimit _ l

@[simp]
theorem cof_preOmega {o : Ordinal} (ho : IsSuccPrelimit o) : (preOmega o).cof = o.cof := by
  by_cases h : IsMin o
  · simp [h.eq_bot]
  · exact isNormal_preOmega.cof_eq ⟨h, ho⟩

@[simp]
theorem cof_omega {o : Ordinal} (ho : o.IsLimit) : (ω_ o).cof = o.cof :=
  isNormal_omega.cof_eq ho

set_option linter.deprecated false in
@[deprecated cof_preOmega (since := "2024-10-22")]
theorem preAleph_cof {o : Ordinal} (ho : o.IsLimit) : (preAleph o).ord.cof = o.cof :=
  aleph'_isNormal.cof_eq ho

set_option linter.deprecated false in
@[deprecated cof_preOmega (since := "2024-10-22")]
theorem aleph'_cof {o : Ordinal} (ho : o.IsLimit) : (aleph' o).ord.cof = o.cof :=
  aleph'_isNormal.cof_eq ho

set_option linter.deprecated false in
@[deprecated cof_omega (since := "2024-10-22")]
theorem aleph_cof {o : Ordinal} (ho : o.IsLimit) : (ℵ_  o).ord.cof = o.cof :=
  aleph_isNormal.cof_eq ho

@[simp]
theorem cof_omega0 : cof ω = ℵ₀ :=
  (aleph0_le_cof.2 isLimit_omega0).antisymm' <| by
    rw [← card_omega0]
    apply cof_le_card

theorem cof_eq' (r : α → α → Prop) [IsWellOrder α r] (h : IsLimit (type r)) :
    ∃ S : Set α, (∀ a, ∃ b ∈ S, r a b) ∧ #S = cof (type r) :=
  let ⟨S, H, e⟩ := cof_eq r
  ⟨S, fun a =>
    let a' := enum r ⟨_, h.succ_lt (typein_lt_type r a)⟩
    let ⟨b, h, ab⟩ := H a'
    ⟨b, h,
      (IsOrderConnected.conn a b a' <|
            (typein_lt_typein r).1
              (by
                rw [typein_enum]
                exact lt_succ (typein _ _))).resolve_right
        ab⟩,
    e⟩

@[simp]
theorem cof_univ : cof univ.{u, v} = Cardinal.univ.{u, v} :=
  le_antisymm (cof_le_card _)
    (by
      refine le_of_forall_lt fun c h => ?_
      rcases lt_univ'.1 h with ⟨c, rfl⟩
      rcases @cof_eq Ordinal.{u} (· < ·) _ with ⟨S, H, Se⟩
      rw [univ, ← lift_cof, ← Cardinal.lift_lift.{u+1, v, u}, Cardinal.lift_lt, ← Se]
      refine lt_of_not_ge fun h => ?_
      cases' Cardinal.mem_range_lift_of_le h with a e
      refine Quotient.inductionOn a (fun α e => ?_) e
      cases' Quotient.exact e with f
      have f := Equiv.ulift.symm.trans f
      let g a := (f a).1
      let o := succ (iSup g)
      rcases H o with ⟨b, h, l⟩
      refine l (lt_succ_iff.2 ?_)
      rw [← show g (f.symm ⟨b, h⟩) = b by simp [g]]
      apply Ordinal.le_iSup)

/-! ### Infinite pigeonhole principle -/


/-- If the union of s is unbounded and s is smaller than the cofinality,
  then s has an unbounded member -/
theorem unbounded_of_unbounded_sUnion (r : α → α → Prop) [wo : IsWellOrder α r] {s : Set (Set α)}
    (h₁ : Unbounded r <| ⋃₀ s) (h₂ : #s < Order.cof (swap rᶜ)) : ∃ x ∈ s, Unbounded r x := by
  by_contra! h
  simp_rw [not_unbounded_iff] at h
  let f : s → α := fun x : s => wo.wf.sup x (h x.1 x.2)
  refine h₂.not_le (le_trans (csInf_le' ⟨range f, fun x => ?_, rfl⟩) mk_range_le)
  rcases h₁ x with ⟨y, ⟨c, hc, hy⟩, hxy⟩
  exact ⟨f ⟨c, hc⟩, mem_range_self _, fun hxz => hxy (Trans.trans (wo.wf.lt_sup _ hy) hxz)⟩

/-- If the union of s is unbounded and s is smaller than the cofinality,
  then s has an unbounded member -/
theorem unbounded_of_unbounded_iUnion {α β : Type u} (r : α → α → Prop) [wo : IsWellOrder α r]
    (s : β → Set α) (h₁ : Unbounded r <| ⋃ x, s x) (h₂ : #β < Order.cof (swap rᶜ)) :
    ∃ x : β, Unbounded r (s x) := by
  rw [← sUnion_range] at h₁
  rcases unbounded_of_unbounded_sUnion r h₁ (mk_range_le.trans_lt h₂) with ⟨_, ⟨x, rfl⟩, u⟩
  exact ⟨x, u⟩

/-- The infinite pigeonhole principle -/
theorem infinite_pigeonhole {β α : Type u} (f : β → α) (h₁ : ℵ₀ ≤ #β) (h₂ : #α < (#β).ord.cof) :
    ∃ a : α, #(f ⁻¹' {a}) = #β := by
  have : ∃ a, #β ≤ #(f ⁻¹' {a}) := by
    by_contra! h
    apply mk_univ.not_lt
    rw [← preimage_univ, ← iUnion_of_singleton, preimage_iUnion]
    exact
      mk_iUnion_le_sum_mk.trans_lt
        ((sum_le_iSup _).trans_lt <| mul_lt_of_lt h₁ (h₂.trans_le <| cof_ord_le _) (iSup_lt h₂ h))
  cases' this with x h
  refine ⟨x, h.antisymm' ?_⟩
  rw [le_mk_iff_exists_set]
  exact ⟨_, rfl⟩

/-- Pigeonhole principle for a cardinality below the cardinality of the domain -/
theorem infinite_pigeonhole_card {β α : Type u} (f : β → α) (θ : Cardinal) (hθ : θ ≤ #β)
    (h₁ : ℵ₀ ≤ θ) (h₂ : #α < θ.ord.cof) : ∃ a : α, θ ≤ #(f ⁻¹' {a}) := by
  rcases le_mk_iff_exists_set.1 hθ with ⟨s, rfl⟩
  cases' infinite_pigeonhole (f ∘ Subtype.val : s → α) h₁ h₂ with a ha
  use a; rw [← ha, @preimage_comp _ _ _ Subtype.val f]
  exact mk_preimage_of_injective _ _ Subtype.val_injective

theorem infinite_pigeonhole_set {β α : Type u} {s : Set β} (f : s → α) (θ : Cardinal)
    (hθ : θ ≤ #s) (h₁ : ℵ₀ ≤ θ) (h₂ : #α < θ.ord.cof) :
    ∃ (a : α) (t : Set β) (h : t ⊆ s), θ ≤ #t ∧ ∀ ⦃x⦄ (hx : x ∈ t), f ⟨x, h hx⟩ = a := by
  cases' infinite_pigeonhole_card f θ hθ h₁ h₂ with a ha
  refine ⟨a, { x | ∃ h, f ⟨x, h⟩ = a }, ?_, ?_, ?_⟩
  · rintro x ⟨hx, _⟩
    exact hx
  · refine
      ha.trans
        (ge_of_eq <|
          Quotient.sound ⟨Equiv.trans ?_ (Equiv.subtypeSubtypeEquivSubtypeExists _ _).symm⟩)
    simp only [coe_eq_subtype, mem_singleton_iff, mem_preimage, mem_setOf_eq]
    rfl
  rintro x ⟨_, hx'⟩; exact hx'

end Ordinal

/-! ### Regular and inaccessible cardinals -/


namespace Cardinal

open Ordinal

/-- A cardinal is a strong limit if it is not zero and it is
  closed under powersets. Note that `ℵ₀` is a strong limit by this definition. -/
def IsStrongLimit (c : Cardinal) : Prop :=
  c ≠ 0 ∧ ∀ x < c, (2^x) < c

theorem IsStrongLimit.ne_zero {c} (h : IsStrongLimit c) : c ≠ 0 :=
  h.1

theorem IsStrongLimit.two_power_lt {x c} (h : IsStrongLimit c) : x < c → (2^x) < c :=
  h.2 x

theorem isStrongLimit_aleph0 : IsStrongLimit ℵ₀ :=
  ⟨aleph0_ne_zero, fun x hx => by
    rcases lt_aleph0.1 hx with ⟨n, rfl⟩
    exact mod_cast nat_lt_aleph0 (2 ^ n)⟩

protected theorem IsStrongLimit.isSuccLimit {c} (H : IsStrongLimit c) : IsSuccLimit c := by
  rw [Cardinal.isSuccLimit_iff]
  exact ⟨H.ne_zero, isSuccPrelimit_of_succ_lt fun x h =>
    (succ_le_of_lt <| cantor x).trans_lt (H.two_power_lt h)⟩

protected theorem IsStrongLimit.isSuccPrelimit {c} (H : IsStrongLimit c) : IsSuccPrelimit c :=
  H.isSuccLimit.isSuccPrelimit

theorem IsStrongLimit.aleph0_le {c} (H : IsStrongLimit c) : ℵ₀ ≤ c :=
  aleph0_le_of_isSuccLimit H.isSuccLimit

set_option linter.deprecated false in
@[deprecated IsStrongLimit.isSuccLimit (since := "2024-09-17")]
theorem IsStrongLimit.isLimit {c} (H : IsStrongLimit c) : IsLimit c :=
  ⟨H.ne_zero, H.isSuccPrelimit⟩

theorem isStrongLimit_beth {o : Ordinal} (H : IsSuccPrelimit o) : IsStrongLimit (ℶ_ o) := by
  rcases eq_or_ne o 0 with (rfl | h)
  · rw [beth_zero]
    exact isStrongLimit_aleph0
  · refine ⟨beth_ne_zero o, fun a ha => ?_⟩
    rw [beth_limit] at ha
    · rcases exists_lt_of_lt_ciSup' ha with ⟨⟨i, hi⟩, ha⟩
      have := power_le_power_left two_ne_zero ha.le
      rw [← beth_succ] at this
      exact this.trans_lt (beth_lt.2 (H.succ_lt hi))
    · rw [isLimit_iff]
      exact ⟨h, H⟩

theorem mk_bounded_subset {α : Type*} (h : ∀ x < #α, (2^x) < #α) {r : α → α → Prop}
    [IsWellOrder α r] (hr : (#α).ord = type r) : #{ s : Set α // Bounded r s } = #α := by
  rcases eq_or_ne #α 0 with (ha | ha)
  · rw [ha]
    haveI := mk_eq_zero_iff.1 ha
    rw [mk_eq_zero_iff]
    constructor
    rintro ⟨s, hs⟩
    exact (not_unbounded_iff s).2 hs (unbounded_of_isEmpty s)
  have h' : IsStrongLimit #α := ⟨ha, h⟩
  have ha := h'.aleph0_le
  apply le_antisymm
  · have : { s : Set α | Bounded r s } = ⋃ i, 𝒫{ j | r j i } := setOf_exists _
    rw [← coe_setOf, this]
    refine mk_iUnion_le_sum_mk.trans ((sum_le_iSup (fun i => #(𝒫{ j | r j i }))).trans
      ((mul_le_max_of_aleph0_le_left ha).trans ?_))
    rw [max_eq_left]
    apply ciSup_le' _
    intro i
    rw [mk_powerset]
    apply (h'.two_power_lt _).le
    rw [coe_setOf, card_typein, ← lt_ord, hr]
    apply typein_lt_type
  · refine @mk_le_of_injective α _ (fun x => Subtype.mk {x} ?_) ?_
    · apply bounded_singleton
      rw [← hr]
      apply isLimit_ord ha
    · intro a b hab
      simpa [singleton_eq_singleton_iff] using hab

theorem mk_subset_mk_lt_cof {α : Type*} (h : ∀ x < #α, (2^x) < #α) :
    #{ s : Set α // #s < cof (#α).ord } = #α := by
  rcases eq_or_ne #α 0 with (ha | ha)
  · simp [ha]
  have h' : IsStrongLimit #α := ⟨ha, h⟩
  rcases ord_eq α with ⟨r, wo, hr⟩
  haveI := wo
  apply le_antisymm
  · conv_rhs => rw [← mk_bounded_subset h hr]
    apply mk_le_mk_of_subset
    intro s hs
    rw [hr] at hs
    exact lt_cof_type hs
  · refine @mk_le_of_injective α _ (fun x => Subtype.mk {x} ?_) ?_
    · rw [mk_singleton]
      exact one_lt_aleph0.trans_le (aleph0_le_cof.2 (isLimit_ord h'.aleph0_le))
    · intro a b hab
      simpa [singleton_eq_singleton_iff] using hab

/-- A cardinal is regular if it is infinite and it equals its own cofinality. -/
def IsRegular (c : Cardinal) : Prop :=
  ℵ₀ ≤ c ∧ c ≤ c.ord.cof

theorem IsRegular.aleph0_le {c : Cardinal} (H : c.IsRegular) : ℵ₀ ≤ c :=
  H.1

theorem IsRegular.cof_eq {c : Cardinal} (H : c.IsRegular) : c.ord.cof = c :=
  (cof_ord_le c).antisymm H.2

theorem IsRegular.cof_omega_eq {o : Ordinal} (H : (ℵ_ o).IsRegular) : (ω_ o).cof = ℵ_ o := by
  rw [← ord_aleph, H.cof_eq]

theorem IsRegular.pos {c : Cardinal} (H : c.IsRegular) : 0 < c :=
  aleph0_pos.trans_le H.1

theorem IsRegular.nat_lt {c : Cardinal} (H : c.IsRegular) (n : ℕ) : n < c :=
  lt_of_lt_of_le (nat_lt_aleph0 n) H.aleph0_le

theorem IsRegular.ord_pos {c : Cardinal} (H : c.IsRegular) : 0 < c.ord := by
  rw [Cardinal.lt_ord, card_zero]
  exact H.pos

theorem isRegular_cof {o : Ordinal} (h : o.IsLimit) : IsRegular o.cof :=
  ⟨aleph0_le_cof.2 h, (cof_cof o).ge⟩

theorem isRegular_aleph0 : IsRegular ℵ₀ :=
  ⟨le_rfl, by simp⟩

theorem isRegular_succ {c : Cardinal.{u}} (h : ℵ₀ ≤ c) : IsRegular (succ c) :=
  ⟨h.trans (le_succ c),
    succ_le_of_lt
      (by
        have αe := Cardinal.mk_out (succ c)
        set α := (succ c).out
        rcases ord_eq α with ⟨r, wo, re⟩
        have := isLimit_ord (h.trans (le_succ _))
        rw [← αe, re] at this ⊢
        rcases cof_eq' r this with ⟨S, H, Se⟩
        rw [← Se]
        apply lt_imp_lt_of_le_imp_le fun h => mul_le_mul_right' h c
        rw [mul_eq_self h, ← succ_le_iff, ← αe, ← sum_const']
        refine le_trans ?_ (sum_le_sum (fun (x : S) => card (typein r (x : α))) _ fun i => ?_)
        · simp only [← card_typein, ← mk_sigma]
          exact
            ⟨Embedding.ofSurjective (fun x => x.2.1) fun a =>
                let ⟨b, h, ab⟩ := H a
                ⟨⟨⟨_, h⟩, _, ab⟩, rfl⟩⟩
        · rw [← lt_succ_iff, ← lt_ord, ← αe, re]
          apply typein_lt_type)⟩

theorem isRegular_aleph_one : IsRegular ℵ₁ := by
  rw [← succ_aleph0]
  exact isRegular_succ le_rfl

theorem isRegular_preAleph_succ {o : Ordinal} (h : ω ≤ o) : IsRegular (preAleph (succ o)) := by
  rw [preAleph_succ]
  exact isRegular_succ (aleph0_le_preAleph.2 h)

set_option linter.deprecated false in
@[deprecated isRegular_preAleph_succ (since := "2024-10-22")]
theorem isRegular_aleph'_succ {o : Ordinal} (h : ω ≤ o) : IsRegular (aleph' (succ o)) := by
  rw [aleph'_succ]
  exact isRegular_succ (aleph0_le_aleph'.2 h)

theorem isRegular_aleph_succ (o : Ordinal) : IsRegular (ℵ_ (succ o)) := by
  rw [aleph_succ]
  exact isRegular_succ (aleph0_le_aleph o)

/-- A function whose codomain's cardinality is infinite but strictly smaller than its domain's
has a fiber with cardinality strictly great than the codomain.
-/
theorem infinite_pigeonhole_card_lt {β α : Type u} (f : β → α) (w : #α < #β) (w' : ℵ₀ ≤ #α) :
    ∃ a : α, #α < #(f ⁻¹' {a}) := by
  simp_rw [← succ_le_iff]
  exact
    Ordinal.infinite_pigeonhole_card f (succ #α) (succ_le_of_lt w) (w'.trans (lt_succ _).le)
      ((lt_succ _).trans_le (isRegular_succ w').2.ge)

/-- A function whose codomain's cardinality is infinite but strictly smaller than its domain's
has an infinite fiber.
-/
theorem exists_infinite_fiber {β α : Type u} (f : β → α) (w : #α < #β) (w' : Infinite α) :
    ∃ a : α, Infinite (f ⁻¹' {a}) := by
  simp_rw [Cardinal.infinite_iff] at w' ⊢
  cases' infinite_pigeonhole_card_lt f w w' with a ha
  exact ⟨a, w'.trans ha.le⟩

/-- If an infinite type `β` can be expressed as a union of finite sets,
then the cardinality of the collection of those finite sets
must be at least the cardinality of `β`.
-/
theorem le_range_of_union_finset_eq_top {α β : Type*} [Infinite β] (f : α → Finset β)
    (w : ⋃ a, (f a : Set β) = ⊤) : #β ≤ #(range f) := by
  have k : _root_.Infinite (range f) := by
    rw [infinite_coe_iff]
    apply mt (union_finset_finite_of_range_finite f)
    rw [w]
    exact infinite_univ
  by_contra h
  simp only [not_le] at h
  let u : ∀ b, ∃ a, b ∈ f a := fun b => by simpa using (w.ge : _) (Set.mem_univ b)
  let u' : β → range f := fun b => ⟨f (u b).choose, by simp⟩
  have v' : ∀ a, u' ⁻¹' {⟨f a, by simp⟩} ≤ f a := by
    rintro a p m
    simp? [u']  at m says simp only [mem_preimage, mem_singleton_iff, Subtype.mk.injEq, u'] at m
    rw [← m]
    apply fun b => (u b).choose_spec
  obtain ⟨⟨-, ⟨a, rfl⟩⟩, p⟩ := exists_infinite_fiber u' h k
  exact (@Infinite.of_injective _ _ p (inclusion (v' a)) (inclusion_injective _)).false

theorem lsub_lt_ord_lift_of_isRegular {ι} {f : ι → Ordinal} {c} (hc : IsRegular c)
    (hι : Cardinal.lift.{v, u} #ι < c) : (∀ i, f i < c.ord) → Ordinal.lsub.{u, v} f < c.ord :=
  lsub_lt_ord_lift (by rwa [hc.cof_eq])

theorem lsub_lt_ord_of_isRegular {ι} {f : ι → Ordinal} {c} (hc : IsRegular c) (hι : #ι < c) :
    (∀ i, f i < c.ord) → Ordinal.lsub f < c.ord :=
  lsub_lt_ord (by rwa [hc.cof_eq])

theorem iSup_lt_ord_lift_of_isRegular {ι} {f : ι → Ordinal} {c} (hc : IsRegular c)
    (hι : Cardinal.lift.{v, u} #ι < c) : (∀ i, f i < c.ord) → iSup f < c.ord :=
  iSup_lt_ord_lift (by rwa [hc.cof_eq])

set_option linter.deprecated false in
@[deprecated iSup_lt_ord_lift_of_isRegular (since := "2024-08-27")]
theorem sup_lt_ord_lift_of_isRegular {ι} {f : ι → Ordinal} {c} (hc : IsRegular c)
    (hι : Cardinal.lift.{v, u} #ι < c) : (∀ i, f i < c.ord) → Ordinal.sup.{u, v} f < c.ord :=
  iSup_lt_ord_lift_of_isRegular hc hι

theorem iSup_lt_ord_of_isRegular {ι} {f : ι → Ordinal} {c} (hc : IsRegular c) (hι : #ι < c) :
    (∀ i, f i < c.ord) → iSup f < c.ord :=
  iSup_lt_ord (by rwa [hc.cof_eq])

set_option linter.deprecated false in
@[deprecated iSup_lt_ord_of_isRegular (since := "2024-08-27")]
theorem sup_lt_ord_of_isRegular {ι} {f : ι → Ordinal} {c} (hc : IsRegular c) (hι : #ι < c) :
    (∀ i, f i < c.ord) → Ordinal.sup f < c.ord :=
  iSup_lt_ord_of_isRegular hc hι

theorem blsub_lt_ord_lift_of_isRegular {o : Ordinal} {f : ∀ a < o, Ordinal} {c} (hc : IsRegular c)
    (ho : Cardinal.lift.{v, u} o.card < c) :
    (∀ i hi, f i hi < c.ord) → Ordinal.blsub.{u, v} o f < c.ord :=
  blsub_lt_ord_lift (by rwa [hc.cof_eq])

theorem blsub_lt_ord_of_isRegular {o : Ordinal} {f : ∀ a < o, Ordinal} {c} (hc : IsRegular c)
    (ho : o.card < c) : (∀ i hi, f i hi < c.ord) → Ordinal.blsub o f < c.ord :=
  blsub_lt_ord (by rwa [hc.cof_eq])

theorem bsup_lt_ord_lift_of_isRegular {o : Ordinal} {f : ∀ a < o, Ordinal} {c} (hc : IsRegular c)
    (hι : Cardinal.lift.{v, u} o.card < c) :
    (∀ i hi, f i hi < c.ord) → Ordinal.bsup.{u, v} o f < c.ord :=
  bsup_lt_ord_lift (by rwa [hc.cof_eq])

theorem bsup_lt_ord_of_isRegular {o : Ordinal} {f : ∀ a < o, Ordinal} {c} (hc : IsRegular c)
    (hι : o.card < c) : (∀ i hi, f i hi < c.ord) → Ordinal.bsup o f < c.ord :=
  bsup_lt_ord (by rwa [hc.cof_eq])

theorem iSup_lt_lift_of_isRegular {ι} {f : ι → Cardinal} {c} (hc : IsRegular c)
    (hι : Cardinal.lift.{v, u} #ι < c) : (∀ i, f i < c) → iSup.{max u v + 1, u + 1} f < c :=
  iSup_lt_lift.{u, v} (by rwa [hc.cof_eq])

theorem iSup_lt_of_isRegular {ι} {f : ι → Cardinal} {c} (hc : IsRegular c) (hι : #ι < c) :
    (∀ i, f i < c) → iSup f < c :=
  iSup_lt (by rwa [hc.cof_eq])

theorem sum_lt_lift_of_isRegular {ι : Type u} {f : ι → Cardinal} {c : Cardinal} (hc : IsRegular c)
    (hι : Cardinal.lift.{v, u} #ι < c) (hf : ∀ i, f i < c) : sum f < c :=
  (sum_le_iSup_lift _).trans_lt <| mul_lt_of_lt hc.1 hι (iSup_lt_lift_of_isRegular hc hι hf)

theorem sum_lt_of_isRegular {ι : Type u} {f : ι → Cardinal} {c : Cardinal} (hc : IsRegular c)
    (hι : #ι < c) : (∀ i, f i < c) → sum f < c :=
  sum_lt_lift_of_isRegular.{u, u} hc (by rwa [lift_id])

@[simp]
theorem card_lt_of_card_iUnion_lt {ι : Type u} {α : Type u} {t : ι → Set α} {c : Cardinal}
    (h : #(⋃ i, t i) < c) (i : ι) : #(t i) < c :=
  lt_of_le_of_lt (Cardinal.mk_le_mk_of_subset <| subset_iUnion _ _) h

@[simp]
theorem card_iUnion_lt_iff_forall_of_isRegular {ι : Type u} {α : Type u} {t : ι → Set α}
    {c : Cardinal} (hc : c.IsRegular) (hι : #ι < c) : #(⋃ i, t i) < c ↔ ∀ i, #(t i) < c := by
  refine ⟨card_lt_of_card_iUnion_lt, fun h ↦ ?_⟩
  apply lt_of_le_of_lt (Cardinal.mk_sUnion_le _)
  apply Cardinal.mul_lt_of_lt hc.aleph0_le
    (lt_of_le_of_lt Cardinal.mk_range_le hι)
  apply Cardinal.iSup_lt_of_isRegular hc (lt_of_le_of_lt Cardinal.mk_range_le hι)
  simpa

theorem card_lt_of_card_biUnion_lt {α β : Type u} {s : Set α} {t : ∀ a ∈ s, Set β} {c : Cardinal}
    (h : #(⋃ a ∈ s, t a ‹_›) < c) (a : α) (ha : a ∈ s) : # (t a ha) < c := by
  rw [biUnion_eq_iUnion] at h
  have := card_lt_of_card_iUnion_lt h
  simp_all only [iUnion_coe_set,
    Subtype.forall]

theorem card_biUnion_lt_iff_forall_of_isRegular {α β : Type u} {s : Set α} {t : ∀ a ∈ s, Set β}
    {c : Cardinal} (hc : c.IsRegular) (hs : #s < c) :
    #(⋃ a ∈ s, t a ‹_›) < c ↔ ∀ a (ha : a ∈ s), # (t a ha) < c := by
  rw [biUnion_eq_iUnion, card_iUnion_lt_iff_forall_of_isRegular hc hs, SetCoe.forall']

theorem nfpFamily_lt_ord_lift_of_isRegular {ι} {f : ι → Ordinal → Ordinal} {c} (hc : IsRegular c)
    (hι : Cardinal.lift.{v, u} #ι < c) (hc' : c ≠ ℵ₀) (hf : ∀ (i), ∀ b < c.ord, f i b < c.ord) {a}
    (ha : a < c.ord) : nfpFamily f a < c.ord := by
  apply nfpFamily_lt_ord_lift _ _ hf ha <;> rw [hc.cof_eq]
  · exact lt_of_le_of_ne hc.1 hc'.symm
  · exact hι

theorem nfpFamily_lt_ord_of_isRegular {ι} {f : ι → Ordinal → Ordinal} {c} (hc : IsRegular c)
    (hι : #ι < c) (hc' : c ≠ ℵ₀) {a} (hf : ∀ (i), ∀ b < c.ord, f i b < c.ord) :
    a < c.ord → nfpFamily.{u, u} f a < c.ord :=
  nfpFamily_lt_ord_lift_of_isRegular hc (by rwa [lift_id]) hc' hf

set_option linter.deprecated false in
@[deprecated nfpFamily_lt_ord_lift_of_isRegular (since := "2024-10-14")]
theorem nfpBFamily_lt_ord_lift_of_isRegular {o : Ordinal} {f : ∀ a < o, Ordinal → Ordinal} {c}
    (hc : IsRegular c) (ho : Cardinal.lift.{v, u} o.card < c) (hc' : c ≠ ℵ₀)
    (hf : ∀ (i hi), ∀ b < c.ord, f i hi b < c.ord) {a} :
    a < c.ord → nfpBFamily.{u, v} o f a < c.ord :=
  nfpFamily_lt_ord_lift_of_isRegular hc (by rwa [mk_toType]) hc' fun _ => hf _ _

set_option linter.deprecated false in
@[deprecated nfpFamily_lt_ord_of_isRegular (since := "2024-10-14")]
theorem nfpBFamily_lt_ord_of_isRegular {o : Ordinal} {f : ∀ a < o, Ordinal → Ordinal} {c}
    (hc : IsRegular c) (ho : o.card < c) (hc' : c ≠ ℵ₀)
    (hf : ∀ (i hi), ∀ b < c.ord, f i hi b < c.ord) {a} :
    a < c.ord → nfpBFamily.{u, u} o f a < c.ord :=
  nfpBFamily_lt_ord_lift_of_isRegular hc (by rwa [lift_id]) hc' hf

theorem nfp_lt_ord_of_isRegular {f : Ordinal → Ordinal} {c} (hc : IsRegular c) (hc' : c ≠ ℵ₀)
    (hf : ∀ i < c.ord, f i < c.ord) {a} : a < c.ord → nfp f a < c.ord :=
  nfp_lt_ord
    (by
      rw [hc.cof_eq]
      exact lt_of_le_of_ne hc.1 hc'.symm)
    hf

theorem derivFamily_lt_ord_lift {ι : Type u} {f : ι → Ordinal → Ordinal} {c} (hc : IsRegular c)
    (hι : lift.{v} #ι < c) (hc' : c ≠ ℵ₀) (hf : ∀ i, ∀ b < c.ord, f i b < c.ord) {a} :
    a < c.ord → derivFamily f a < c.ord := by
  have hω : ℵ₀ < c.ord.cof := by
    rw [hc.cof_eq]
    exact lt_of_le_of_ne hc.1 hc'.symm
  induction a using limitRecOn with
  | H₁ =>
    rw [derivFamily_zero]
    exact nfpFamily_lt_ord_lift hω (by rwa [hc.cof_eq]) hf
  | H₂ b hb =>
    intro hb'
    rw [derivFamily_succ]
    exact
      nfpFamily_lt_ord_lift hω (by rwa [hc.cof_eq]) hf
        ((isLimit_ord hc.1).succ_lt (hb ((lt_succ b).trans hb')))
  | H₃ b hb H =>
    intro hb'
    -- TODO: generalize the universes of the lemmas in this file so we don't have to rely on bsup
    have : ⨆ a : Iio b, _ = _ :=
      iSup_eq_bsup.{max u v, max u v} (f := fun x (_ : x < b) ↦ derivFamily f x)
    rw [derivFamily_limit f hb, this]
    exact
      bsup_lt_ord_of_isRegular.{u, v} hc (ord_lt_ord.1 ((ord_card_le b).trans_lt hb')) fun o' ho' =>
        H o' ho' (ho'.trans hb')

theorem derivFamily_lt_ord {ι} {f : ι → Ordinal → Ordinal} {c} (hc : IsRegular c) (hι : #ι < c)
    (hc' : c ≠ ℵ₀) (hf : ∀ (i), ∀ b < c.ord, f i b < c.ord) {a} :
    a < c.ord → derivFamily.{u, u} f a < c.ord :=
  derivFamily_lt_ord_lift hc (by rwa [lift_id]) hc' hf

set_option linter.deprecated false in
@[deprecated derivFamily_lt_ord_lift (since := "2024-10-14")]
theorem derivBFamily_lt_ord_lift {o : Ordinal} {f : ∀ a < o, Ordinal → Ordinal} {c}
    (hc : IsRegular c) (hι : Cardinal.lift.{v, u} o.card < c) (hc' : c ≠ ℵ₀)
    (hf : ∀ (i hi), ∀ b < c.ord, f i hi b < c.ord) {a} :
    a < c.ord → derivBFamily.{u, v} o f a < c.ord :=
  derivFamily_lt_ord_lift hc (by rwa [mk_toType]) hc' fun _ => hf _ _

set_option linter.deprecated false in
@[deprecated derivFamily_lt_ord (since := "2024-10-14")]
theorem derivBFamily_lt_ord {o : Ordinal} {f : ∀ a < o, Ordinal → Ordinal} {c} (hc : IsRegular c)
    (hι : o.card < c) (hc' : c ≠ ℵ₀) (hf : ∀ (i hi), ∀ b < c.ord, f i hi b < c.ord) {a} :
    a < c.ord → derivBFamily.{u, u} o f a < c.ord :=
  derivBFamily_lt_ord_lift hc (by rwa [lift_id]) hc' hf

theorem deriv_lt_ord {f : Ordinal.{u} → Ordinal} {c} (hc : IsRegular c) (hc' : c ≠ ℵ₀)
    (hf : ∀ i < c.ord, f i < c.ord) {a} : a < c.ord → deriv f a < c.ord :=
  derivFamily_lt_ord_lift hc
    (by simpa using Cardinal.one_lt_aleph0.trans (lt_of_le_of_ne hc.1 hc'.symm)) hc' fun _ => hf

/-- A cardinal is inaccessible if it is an uncountable regular strong limit cardinal. -/
def IsInaccessible (c : Cardinal) :=
  ℵ₀ < c ∧ IsRegular c ∧ IsStrongLimit c

theorem IsInaccessible.mk {c} (h₁ : ℵ₀ < c) (h₂ : c ≤ c.ord.cof) (h₃ : ∀ x < c, (2^x) < c) :
    IsInaccessible c :=
  ⟨h₁, ⟨h₁.le, h₂⟩, (aleph0_pos.trans h₁).ne', h₃⟩

-- Lean's foundations prove the existence of ℵ₀ many inaccessible cardinals
theorem univ_inaccessible : IsInaccessible univ.{u, v} :=
  IsInaccessible.mk (by simpa using lift_lt_univ' ℵ₀) (by simp) fun c h => by
    rcases lt_univ'.1 h with ⟨c, rfl⟩
    rw [← lift_two_power]
    apply lift_lt_univ'

theorem lt_power_cof {c : Cardinal.{u}} : ℵ₀ ≤ c → c < (c^cof c.ord) :=
  Cardinal.inductionOn c fun α h => by
    rcases ord_eq α with ⟨r, wo, re⟩
    have := isLimit_ord h
    rw [re] at this ⊢
    rcases cof_eq' r this with ⟨S, H, Se⟩
    have := sum_lt_prod (fun a : S => #{ x // r x a }) (fun _ => #α) fun i => ?_
    · simp only [Cardinal.prod_const, Cardinal.lift_id, ← Se, ← mk_sigma, power_def] at this ⊢
      refine lt_of_le_of_lt ?_ this
      refine ⟨Embedding.ofSurjective ?_ ?_⟩
      · exact fun x => x.2.1
      · exact fun a =>
          let ⟨b, h, ab⟩ := H a
          ⟨⟨⟨_, h⟩, _, ab⟩, rfl⟩
    · have := typein_lt_type r i
      rwa [← re, lt_ord] at this

theorem lt_cof_power {a b : Cardinal} (ha : ℵ₀ ≤ a) (b1 : 1 < b) : a < cof (b^a).ord := by
  have b0 : b ≠ 0 := (zero_lt_one.trans b1).ne'
  apply lt_imp_lt_of_le_imp_le (power_le_power_left <| power_ne_zero a b0)
  rw [← power_mul, mul_eq_self ha]
  exact lt_power_cof (ha.trans <| (cantor' _ b1).le)

end Cardinal

section Omega1

namespace Ordinal

open Cardinal
open scoped Ordinal

-- TODO: generalize universes, and use ω₁.
lemma iSup_sequence_lt_omega1 {α : Type u} [Countable α]
    (o : α → Ordinal.{max u v}) (ho : ∀ n, o n < (aleph 1).ord) :
    iSup o < (aleph 1).ord := by
  apply iSup_lt_ord_lift _ ho
  rw [Cardinal.isRegular_aleph_one.cof_eq]
  exact lt_of_le_of_lt mk_le_aleph0 aleph0_lt_aleph_one

end Ordinal

end Omega1

namespace Ordinal

theorem isLimit_of_not_isRegular_aleph {o : Ordinal} (h : ¬((aleph o).IsRegular)) :
    o.IsLimit := by
  have ho : o ≠ 0 := fun h0 ↦ False.elim <| (aleph_zero ▸ h0 ▸ h) isRegular_aleph0
  contrapose! h
  obtain ⟨p, rfl⟩ := ((zero_or_succ_or_limit o).resolve_left ho).resolve_right h
  exact isRegular_aleph_succ p

theorem ord_cof_pos {o : Ordinal} : 0 < o.cof.ord ↔ 0 < o := by
  constructor
  · exact fun h ↦ Ordinal.pos_iff_ne_zero.mpr fun h' ↦ (h' ▸ cof_zero ▸ ord_zero ▸ h).ne rfl
  · exact fun h ↦ Ordinal.pos_iff_ne_zero.mpr fun h' ↦ by
      rw [ord_eq_zero, cof_eq_zero] at h'
      exact h.ne h'.symm

end Ordinal
