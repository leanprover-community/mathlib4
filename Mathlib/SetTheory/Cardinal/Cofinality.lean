/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn, Violeta Hernández Palacios
-/
module

public import Mathlib.Order.Cofinal
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.SetTheory.Ordinal.FixedPoint

/-!
# Cofinality

This file contains the definition of cofinality of an order and an ordinal number.

## Main Definitions

* `Order.cof α` is the cofinality of a preorder. This is the smallest cardinality of a cofinal
  subset.
* `Ordinal.cof o` is the cofinality of the ordinal `o` when viewed as a linear order.

## Main Statements

* `Cardinal.lt_power_cof`: A consequence of König's theorem stating that `c < c ^ c.ord.cof` for
  `c ≥ ℵ₀`.

## Implementation Notes

* The cofinality is defined for ordinals.
  If `c` is a cardinal number, its cofinality is `c.ord.cof`.
-/

public noncomputable section

open Function Cardinal Set Order
open scoped Ordinal

universe u v w

variable {α γ : Type u} {β : Type v}

/-! ### Cofinality of orders -/

namespace Order
variable [Preorder α]

variable (α) in
/-- The cofinality of a preorder is the smallest cardinality of a cofinal subset. -/
def cof : Cardinal :=
  ⨅ s : {s : Set α // IsCofinal s}, #s

theorem cof_le {s : Set α} (h : IsCofinal s) : cof α ≤ #s :=
  ciInf_le' (ι := {s : Set α // IsCofinal s}) _ ⟨s, h⟩

theorem le_cof_iff {c : Cardinal} : c ≤ cof α ↔ ∀ s : Set α, IsCofinal s → c ≤ #s :=
  le_ciInf_iff'.trans (by simp)

@[deprecated (since := "2026-02-18")] alias le_cof := le_cof_iff

variable (α) in
theorem cof_eq : ∃ s : Set α, IsCofinal s ∧ #s = cof α := by
  obtain ⟨s, hs⟩ := ciInf_mem fun s : {s : Set α // IsCofinal s} ↦ #s
  exact ⟨s.1, s.2, hs⟩

variable (α) in
theorem cof_le_cardinalMk : cof α ≤ #α :=
  cof_le .univ |>.trans_eq mk_univ

theorem cof_eq_zero_iff : cof α = 0 ↔ IsEmpty α := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ by simp [cof]⟩
  obtain ⟨s, hs, hs'⟩ := cof_eq α
  simp_all [mk_eq_zero_iff, isCofinal_empty_iff]

@[simp]
theorem cof_eq_zero [h : IsEmpty α] : cof α = 0 :=
  cof_eq_zero_iff.2 h

theorem cof_ne_zero_iff : cof α ≠ 0 ↔ Nonempty α := by
  simpa using cof_eq_zero_iff.not

@[simp]
theorem cof_ne_zero [h : Nonempty α] : cof α ≠ 0 :=
  cof_ne_zero_iff.2 h

theorem cof_eq_one_iff : cof α = 1 ↔ ∃ x : α, IsTop x := by
  refine ⟨fun h ↦ ?_, fun ⟨t, ht⟩ ↦ ?_⟩
  · obtain ⟨s, hs, hs'⟩ := cof_eq α
    rw [h, mk_set_eq_one_iff] at hs'
    obtain ⟨t, rfl⟩ := hs'
    use t
    rwa [isCofinal_singleton_iff] at hs
  · apply le_antisymm
    · apply (cof_le (s := {t}) _).trans_eq (mk_singleton _)
      rwa [isCofinal_singleton_iff]
    · rw [one_le_iff_ne_zero, cof_ne_zero_iff]
      use t

@[simp]
theorem cof_eq_one [OrderTop α] : cof α = 1 :=
  cof_eq_one_iff.2 ⟨⊤, isTop_top⟩

end Order

section Congr
variable [Preorder α] [Preorder β] [Preorder γ]

theorem GaloisConnection.cof_le_lift {f : β → α} {g : α → β} (h : GaloisConnection f g) :
    Cardinal.lift.{u} (Order.cof β) ≤ Cardinal.lift.{v} (Order.cof α) := by
  simp_rw [Order.cof, lift_iInf, le_ciInf_iff']
  rintro ⟨s, hs⟩
  apply (csInf_le' _).trans (mk_image_le_lift (f := g))
  exact ⟨⟨g '' s, h.map_cofinal hs⟩, rfl⟩

theorem GaloisConnection.cof_le {f : γ → α} {g : α → γ} (h : GaloisConnection f g) :
    Order.cof γ ≤ Order.cof α := by
  simpa using h.cof_le_lift

theorem OrderIso.lift_cof_eq (f : α ≃o β) :
    Cardinal.lift.{v} (Order.cof α) = Cardinal.lift.{u} (Order.cof β) :=
  f.to_galoisConnection.cof_le_lift.antisymm (f.symm.to_galoisConnection.cof_le_lift)

theorem OrderIso.cof_eq (f : α ≃o γ) : Order.cof α = Order.cof γ := by
  simpa using f.lift_cof_eq

@[deprecated (since := "2026-02-18")] alias RelIso.cof_eq_lift := OrderIso.lift_cof_eq
@[deprecated (since := "2026-02-18")] alias RelIso.cof_eq := OrderIso.cof_eq

end Congr

/-- If the union of `s` is cofinal and `s` is smaller than the cofinality, then `s` has a cofinal
member. -/
theorem isCofinal_of_isCofinal_sUnion {α : Type*} [LinearOrder α] {s : Set (Set α)}
    (h₁ : IsCofinal (⋃₀ s)) (h₂ : #s < Order.cof α) : ∃ x ∈ s, IsCofinal x := by
  contrapose! h₂
  simp_rw [not_isCofinal_iff] at h₂
  choose f hf using h₂
  refine (cof_le (s := range fun x ↦ f x.1 x.2) fun a ↦ ?_).trans mk_range_le
  obtain ⟨b, ⟨t, ht, hb⟩, hab⟩ := h₁ a
  simpa using ⟨t, ht, hab.trans (hf t ht b hb).le⟩

/-- If the union of the `ι`-indexed family `s` is cofinal and `ι` is smaller than the cofinality,
then `s` has a cofinal member. -/
theorem isCofinal_of_isCofinal_iUnion {α : Type*} {ι} [LinearOrder α] {s : ι → Set α}
    (h₁ : IsCofinal (⋃ i, s i)) (h₂ : #ι < Order.cof α) : ∃ i, IsCofinal (s i) := by
  rw [← sUnion_range] at h₁
  obtain ⟨_, ⟨i, rfl⟩, h⟩ := isCofinal_of_isCofinal_sUnion h₁ (mk_range_le.trans_lt h₂)
  exact ⟨i, h⟩

/-! ### Cofinality of ordinals -/

-- TODO: generalize to `OrderType`
namespace Ordinal

/-- The cofinality on an ordinal is the `Order.cof` of any isomorphic linear order.

In particular, `cof 0 = 0` and `cof (succ o) = 1`. -/
def cof (o : Ordinal.{u}) : Cardinal.{u} :=
  o.liftOnWellOrder (fun α _ _ ↦ Order.cof α) fun _ _ _ _ _ _ h ↦
    let ⟨f⟩ := type_eq.1 h
    (OrderIso.ofRelIsoLT f).cof_eq

@[simp]
theorem cof_type (α : Type*) [LinearOrder α] [WellFoundedLT α] :
    (typeLT α).cof = Order.cof α :=
  liftOnWellOrder_type ..

@[deprecated (since := "2026-02-18")] alias cof_type_lt := cof_type

@[simp]
theorem cof_toType (o : Ordinal) : Order.cof o.ToType = o.cof := by
  conv_rhs => rw [← type_toType o, cof_type]

@[deprecated (since := "2026-02-18")] alias cof_eq_cof_toType := cof_toType
@[deprecated (since := "2026-02-18")] alias le_cof_type := le_cof_iff
@[deprecated (since := "2026-02-18")] alias cof_type_le := cof_le
@[deprecated (since := "2026-02-18")] alias lt_cof_type := cof_le
@[deprecated (since := "2026-02-18")] alias cof_eq := Order.cof_eq

@[simp]
theorem lift_cof (o : Ordinal.{u}) : Cardinal.lift.{v} (cof o) = cof (Ordinal.lift.{v} o) := by
  induction o using inductionOnWellOrder with | H α
  rw [cof_type, ← type_lt_ulift, cof_type, ← Cardinal.lift_id'.{u, v} (Order.cof (ULift _)),
    ← Cardinal.lift_umax, ← ULift.orderIso.lift_cof_eq]

theorem cof_le_card (o : Ordinal) : cof o ≤ card o := by
  induction o using inductionOnWellOrder with | H α
  simpa using cof_le_cardinalMk α

theorem cof_ord_le (c : Cardinal) : c.ord.cof ≤ c := by simpa using cof_le_card c.ord

theorem ord_cof_le (o : Ordinal) : o.cof.ord ≤ o :=
  (ord_le_ord.2 (cof_le_card o)).trans (ord_card_le o)

@[simp]
theorem cof_eq_zero {o} : cof o = 0 ↔ o = 0 := by
  rw [← cof_toType, cof_eq_zero_iff, isEmpty_toType_iff]

@[deprecated cof_eq_zero (since := "2026-02-18")]
theorem cof_ne_zero {o} : cof o ≠ 0 ↔ o ≠ 0 :=
  cof_eq_zero.not

@[simp]
theorem cof_zero : cof 0 = 0 :=
  cof_eq_zero.2 rfl

theorem cof_eq_one_iff {o} : cof o = 1 ↔ o ∈ range succ := by
  induction o using inductionOnWellOrder with | H α
  rw [cof_type, Order.cof_eq_one_iff, type_lt_mem_range_succ_iff]
  simp_rw [isTop_iff_isMax]

theorem cof_add_one (o) : cof (o + 1) = 1 :=
  cof_eq_one_iff.2 (mem_range_self o)

@[simp]
theorem cof_one : cof 1 = 1 := by
  simpa using cof_add_one 0

-- TODO: deprecate in favor of `cof_add_one`
theorem cof_succ (o) : cof (succ o) = 1 :=
  cof_add_one o

@[deprecated (since := "2026-02-18")] alias cof_eq_one_iff_is_succ := cof_eq_one_iff

theorem ord_cof_eq (α : Type*) [LinearOrder α] [WellFoundedLT α] :
    ∃ s : Set α, IsCofinal s ∧ typeLT s = (Order.cof α).ord := by
  obtain ⟨s, hs, hs'⟩ := Order.cof_eq α
  obtain ⟨r, hr, hr'⟩ := ord_eq s
  have ht := hs.trans (isCofinal_setOf_imp_lt r)
  refine ⟨_, ht, (ord_le.2 (cof_le ht)).antisymm' ?_⟩
  rw [← hs', hr', type_le_iff']
  refine ⟨.ofMonotone (fun x ↦ ⟨x.1, ?_⟩) fun x y hxy ↦ ?_⟩
  · grind
  · apply (trichotomous_of r _ _).resolve_right
    rintro (_ | hxy')
    · simp_all [Subtype.coe_inj]
    · obtain ⟨x, z, hz, rfl⟩ := x
      exact (hz _ hxy').asymm hxy

/-! ### Cofinality of suprema and least strict upper bounds -/

-- TODO: use `⨆ i, succ (f i)` instead of `lsub`

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
      (cof_le fun a => ?_).trans
        (@mk_le_of_injective _ _
          (fun s : typein ((· < ·) : o.ToType → o.ToType → Prop) ⁻¹' Set.range f =>
            Classical.choose s.prop)
          fun s t hst => by
          let H := congr_arg f hst
          rwa [Classical.choose_spec s.prop, Classical.choose_spec t.prop, typein_inj,
            Subtype.coe_inj] at H)
    have := typein_lt_self a
    simp_rw [← hf, lt_lsub_iff] at this
    obtain ⟨i, hi⟩ := this
    refine ⟨enum (α := o.ToType) (· < ·) ⟨f i, ?_⟩, ?_, ?_⟩
    · rw [type_toType, ← hf]
      apply lt_lsub
    · rw [mem_preimage, typein_enum]
      exact mem_range_self i
    · rwa [← not_lt, ← typein_le_typein, typein_enum]
  · rcases Order.cof_eq (α := o.ToType) with ⟨S, hS, hS'⟩
    let f : S → Ordinal := fun s => typein LT.lt s.val
    refine ⟨S, f, le_antisymm (lsub_le fun i => typein_lt_self (o := o) i)
      (le_of_forall_lt fun a ha => ?_), by rwa [cof_toType] at hS'⟩
    rw [← type_toType o] at ha
    rcases hS (enum (· < ·) ⟨a, ha⟩) with ⟨b, hb, hb'⟩
    rw [← not_lt, ← typein_le_typein, typein_enum] at hb'
    exact hb'.trans_lt (lt_lsub.{u, u} f ⟨b, hb⟩)

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
    exact (cof_lsub_le_lift.{u, v} f).not_gt hι

theorem lsub_lt_ord {ι} {f : ι → Ordinal} {c : Ordinal} (hι : #ι < c.cof) :
    (∀ i, f i < c) → lsub.{u, u} f < c :=
  lsub_lt_ord_lift (by rwa [(#ι).lift_id])

theorem cof_iSup_le_lift {ι} {f : ι → Ordinal} (H : ∀ i, f i < iSup f) :
    cof (iSup f) ≤ Cardinal.lift.{v, u} #ι := by
  rw [← iSup_eq_lsub_iff_lt_iSup] at H
  rw [H]
  exact cof_lsub_le_lift f

theorem cof_iSup_le {ι} {f : ι → Ordinal} (H : ∀ i, f i < iSup f) :
    cof (iSup f) ≤ #ι := by
  rw [← (#ι).lift_id]
  exact cof_iSup_le_lift H

theorem iSup_lt_ord_lift {ι} {f : ι → Ordinal} {c : Ordinal} (hι : Cardinal.lift.{v, u} #ι < c.cof)
    (hf : ∀ i, f i < c) : iSup f < c :=
  (iSup_le_lsub f).trans_lt (lsub_lt_ord_lift hι hf)

theorem iSup_lt_ord {ι} {f : ι → Ordinal} {c : Ordinal} (hι : #ι < c.cof) :
    (∀ i, f i < c) → iSup f < c :=
  iSup_lt_ord_lift (by rwa [(#ι).lift_id])

theorem iSup_lt_lift {ι} {f : ι → Cardinal} {c : Cardinal}
    (hι : Cardinal.lift.{v, u} #ι < c.ord.cof)
    (hf : ∀ i, f i < c) : iSup f < c := by
  rw [← ord_lt_ord, iSup_ord]
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
  · induction l with
    | nil => exact ha
    | cons i l H => exact hf _ _ H

theorem nfpFamily_lt_ord {ι} {f : ι → Ordinal → Ordinal} {c} (hc : ℵ₀ < cof c) (hc' : #ι < cof c)
    (hf : ∀ (i), ∀ b < c, f i b < c) {a} : a < c → nfpFamily.{u, u} f a < c :=
  nfpFamily_lt_ord_lift hc (by rwa [(#ι).lift_id]) hf

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
    ho.not_ge (by simpa [← iSup_ord, hf, h] using cof_blsub_le_lift.{u, v} f)

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

/-! ### Fundamental sequences -/

-- TODO: move stuff about fundamental sequences to their own file.

/-- A fundamental sequence for `a` is an increasing sequence of length `o = cof a` that converges at
    `a`. We provide `o` explicitly in order to avoid type rewrites. -/
@[expose]
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
  ⟨by rw [cof_zero, ord_zero], @fun i _ hi => (not_lt_zero hi).elim, blsub_zero f⟩

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
  let r' := Subrel r fun i ↦ ∀ j, r j i → f j < f i
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
    by_cases! h : ∀ j, r j i → f j < f i
    · refine ⟨typein r' ⟨i, h⟩, typein_lt_type _ _, ?_⟩
      rw [bfamilyOfFamily'_typein]
    · obtain ⟨hji, hij⟩ := wo.wf.min_mem _ h
      refine ⟨typein r' ⟨_, fun k hkj => lt_of_lt_of_le ?_ hij⟩, typein_lt_type _ _, ?_⟩
      · by_contra! H
        exact (wo.wf.not_lt_min _ h ⟨IsTrans.trans _ _ _ hkj hji, H⟩) hkj
      · rwa [bfamilyOfFamily'_typein]

@[simp]
theorem cof_cof (a : Ordinal.{u}) : cof (cof a).ord = cof a := by
  obtain ⟨f, hf⟩ := exists_fundamental_sequence a
  obtain ⟨g, hg⟩ := exists_fundamental_sequence a.cof.ord
  exact ord_injective (hf.trans hg).cof_eq.symm

theorem IsFundamentalSequence.of_isNormal {f : Ordinal.{u} → Ordinal.{u}} (hf : IsNormal f)
    {a o} (ha : IsSuccLimit a) {g} (hg : IsFundamentalSequence a o g) :
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
      obtain ⟨i, hi⟩ := this
      rcases H i with ⟨b, _, hb⟩
      exact
        ((le_csInf_iff'' ⟨b, by exact hb⟩).2 fun c hc =>
          hf.strictMono.le_iff_le.1 (hi.trans hc)).trans_lt (lt_lsub _ i)
  · rw [@blsub_comp.{u, u, u} a _ (fun b _ => f b) (@fun i j _ _ h => hf.strictMono.monotone h) g
        hg.2.2]
    exact IsNormal.blsub_eq.{u, u} hf ha

@[deprecated (since := "2025-12-25")]
alias IsNormal.isFundamentalSequence := IsFundamentalSequence.of_isNormal

theorem cof_eq_of_isNormal {f} (hf : IsNormal f) {a} (ha : IsSuccLimit a) : cof (f a) = cof a :=
  let ⟨_, hg⟩ := exists_fundamental_sequence a
  ord_injective (IsFundamentalSequence.of_isNormal hf ha hg).cof_eq

@[deprecated (since := "2025-12-25")]
alias IsNormal.cof_eq := cof_eq_of_isNormal

theorem cof_le_of_isNormal {f} (hf : IsNormal f) (a) : cof a ≤ cof (f a) := by
  rcases zero_or_succ_or_isSuccLimit a with (rfl | ⟨b, rfl⟩ | ha)
  · rw [cof_zero]
    exact zero_le _
  · rw [cof_succ, Cardinal.one_le_iff_ne_zero, cof_eq_zero.ne, ← pos_iff_ne_zero]
    exact (zero_le (f b)).trans_lt (hf.strictMono (lt_succ b))
  · rw [cof_eq_of_isNormal hf ha]

@[deprecated (since := "2025-12-25")]
alias IsNormal.cof_le := cof_le_of_isNormal

@[simp]
theorem cof_add (a b : Ordinal) : b ≠ 0 → cof (a + b) = cof b := fun h => by
  rcases zero_or_succ_or_isSuccLimit b with (rfl | ⟨c, rfl⟩ | hb)
  · contradiction
  · rw [add_succ, cof_succ, cof_succ]
  · exact cof_eq_of_isNormal (isNormal_add_right a) hb

theorem aleph0_le_cof {o} : ℵ₀ ≤ cof o ↔ IsSuccLimit o := by
  rcases zero_or_succ_or_isSuccLimit o with (rfl | ⟨o, rfl⟩ | l)
  · simp [Cardinal.aleph0_ne_zero]
  · simp
  · simp only [l, iff_true]
    refine le_of_not_gt fun h => ?_
    obtain ⟨n, e⟩ := Cardinal.lt_aleph0.1 h
    have := cof_cof o
    rw [e, ord_nat] at this
    cases n
    · apply l.ne_bot
      simpa using e
    · rw [natCast_succ, cof_succ] at this
      rw [← this, cof_eq_one_iff] at e
      rcases e with ⟨a, rfl⟩
      exact not_isSuccLimit_succ _ l

@[simp]
theorem cof_preOmega {o : Ordinal} (ho : IsSuccPrelimit o) : (preOmega o).cof = o.cof := by
  by_cases h : IsMin o
  · simp [h.eq_bot]
  · exact cof_eq_of_isNormal isNormal_preOmega ⟨h, ho⟩

@[simp]
theorem cof_omega {o : Ordinal} (ho : IsSuccLimit o) : (ω_ o).cof = o.cof :=
  cof_eq_of_isNormal isNormal_omega ho

@[simp]
theorem cof_omega0 : cof ω = ℵ₀ :=
  (aleph0_le_cof.2 isSuccLimit_omega0).antisymm' <| by
    rw [← card_omega0]
    apply cof_le_card

-- TODO: deprecate in favor of `Order.cof_eq`
theorem cof_eq' (r : α → α → Prop) [H : IsWellOrder α r] (h : IsSuccLimit (type r)) :
    ∃ S : Set α, (∀ a, ∃ b ∈ S, r a b) ∧ #S = cof (type r) := by
  classical
  let := linearOrderOfSTO r
  have : WellFoundedLT α := H.toIsWellFounded
  have : NoMaxOrder α := isSuccPrelimit_type_lt_iff.1 h.isSuccPrelimit
  obtain ⟨s, hs, hs'⟩ := Order.cof_eq α
  refine ⟨s, ?_, hs'⟩
  rwa [← not_bddAbove_iff_isCofinal, not_bddAbove_iff] at hs

@[simp]
theorem cof_univ : cof univ.{u, v} = Cardinal.univ.{u, v} :=
  le_antisymm (cof_le_card _)
    (by
      refine le_of_forall_lt fun c h => ?_
      rcases lt_univ'.1 h with ⟨c, rfl⟩
      rcases Order.cof_eq Ordinal.{u} with ⟨S, H, Se⟩
      rw [univ, ← lift_cof, ← Cardinal.lift_lift.{u + 1, v, u}, Cardinal.lift_lt, cof_type, ← Se]
      refine lt_of_not_ge fun h => ?_
      obtain ⟨a, e⟩ := Cardinal.mem_range_lift_of_le h
      refine Quotient.inductionOn a (fun α e => ?_) e
      obtain ⟨f⟩ := Quotient.exact e
      have f := Equiv.ulift.symm.trans f
      let g a := (f a).1
      let o := succ (iSup g)
      rcases H o with ⟨b, h, l⟩
      refine l.not_gt (lt_succ_iff.2 ?_)
      rw [← show g (f.symm ⟨b, h⟩) = b by simp [g]]
      apply Ordinal.le_iSup)

end Ordinal

namespace Cardinal
open Ordinal

/-! ### Results on sets -/

-- TODO: re-state this for a bundled well-order
theorem mk_bounded_subset {α : Type*} (h : ∀ x < #α, 2 ^ x < #α) {r : α → α → Prop}
    [IsWellOrder α r] (hr : (#α).ord = type r) : #{ s : Set α // Bounded r s } = #α := by
  rcases eq_or_ne #α 0 with (ha | ha)
  · rw [ha]
    haveI := mk_eq_zero_iff.1 ha
    rw [mk_eq_zero_iff]
    constructor
    rintro ⟨s, hs⟩
    exact (not_unbounded_iff s).2 hs (unbounded_of_isEmpty s)
  have h' : IsStrongLimit #α := ⟨ha, @h⟩
  have ha := h'.aleph0_le
  apply le_antisymm
  · have : { s : Set α | Bounded r s } = ⋃ i, 𝒫 { j | r j i } := setOf_exists _
    rw [← coe_setOf, this]
    refine mk_iUnion_le_sum_mk.trans ((sum_le_mk_mul_iSup (fun i => #(𝒫 { j | r j i }))).trans
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
      apply isSuccLimit_ord ha
    · intro a b hab
      simpa [singleton_eq_singleton_iff] using hab

theorem mk_subset_mk_lt_cof {α : Type*} (h : ∀ x < #α, 2 ^ x < #α) :
    #{ s : Set α // #s < cof (#α).ord } = #α := by
  rcases eq_or_ne #α 0 with (ha | ha)
  · simp [ha]
  have h' : IsStrongLimit #α := ⟨ha, @h⟩
  rcases ord_eq α with ⟨r, wo, hr⟩
  classical
  letI := linearOrderOfSTO r
  apply le_antisymm
  · conv_rhs => rw [← mk_bounded_subset h hr]
    apply mk_subtype_le_of_subset
    intro s hs
    rw [hr] at hs
    contrapose! hs
    rw [not_bounded_iff] at hs
    apply cof_le
    simp_rw [IsCofinal, ← not_lt]
    exact hs
  · refine @mk_le_of_injective α _ (fun x => Subtype.mk {x} ?_) ?_
    · rw [mk_singleton]
      exact one_lt_aleph0.trans_le (aleph0_le_cof.2 (isSuccLimit_ord h'.aleph0_le))
    · intro a b hab
      simpa [singleton_eq_singleton_iff] using hab

@[deprecated (since := "2026-02-25")]
alias unbounded_of_unbounded_sUnion := isCofinal_of_isCofinal_sUnion
@[deprecated (since := "2026-02-25")]
alias unbounded_of_unbounded_iUnion := isCofinal_of_isCofinal_iUnion

/-! ### Consequences of König's lemma -/

theorem lt_power_cof {c : Cardinal.{u}} : ℵ₀ ≤ c → c < c ^ c.ord.cof :=
  Cardinal.inductionOn c fun α h => by
    rcases ord_eq α with ⟨r, wo, re⟩
    have := isSuccLimit_ord h
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

theorem lt_cof_power {a b : Cardinal} (ha : ℵ₀ ≤ a) (b1 : 1 < b) : a < (b ^ a).ord.cof := by
  have b0 : b ≠ 0 := (zero_lt_one.trans b1).ne'
  apply lt_imp_lt_of_le_imp_le (power_le_power_left <| power_ne_zero a b0)
  rw [← power_mul, mul_eq_self ha]
  exact lt_power_cof (ha.trans <| (cantor' _ b1).le)

end Cardinal
