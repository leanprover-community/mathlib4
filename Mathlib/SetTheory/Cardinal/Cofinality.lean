/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn, Violeta Hernández Palacios
-/
import Mathlib.Order.Cofinal
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Ordinal.FixedPoint

/-!
# Cofinality

This file contains the definition of cofinality of an order and an ordinal number.

## Main Definitions

* `Ordinal.cof o` is the cofinality of the ordinal `o`.
  If `o` is the order type of the relation `<` on `α`, then `o.cof` is the smallest cardinality of a
  subset `s` of α that is *cofinal* in `α`, i.e. `∀ x : α, ∃ y ∈ s, ¬ y < x`.
* `Cardinal.IsRegular c` means that `c` is a regular cardinal: `ℵ₀ ≤ c ∧ c.ord.cof = c`.
* `Cardinal.IsInaccessible c` means that `c` is strongly inaccessible:
  `ℵ₀ < c ∧ IsRegular c ∧ IsStrongLimit c`.

## Main Statements

* `Cardinal.lt_power_cof`: A consequence of König's theorem stating that `c < c ^ c.ord.cof` for
  `c ≥ ℵ₀`.

## Implementation Notes

* The cofinality is defined for ordinals.
  If `c` is a cardinal number, its cofinality is `c.ord.cof`.
-/

noncomputable section

open Function Cardinal Set Order
open scoped Ordinal

universe u v

variable {α ι : Type u} {β : Type v} {a o o' : Ordinal.{u}}

/-! ### Cofinality of orders -/

namespace Order

/-- The of a preorder `α` is the smallest cardinality of an `IsCofinal` subset. -/
def cof (α : Type*) [Preorder α] : Cardinal :=
  ⨅ s : { s : Set α // IsCofinal s }, #s.1

theorem IsCofinal.cof_le [Preorder α] {s : Set α} (h : IsCofinal s) : cof α ≤ #s :=
  ciInf_le' _ (Subtype.mk s h)

theorem cof_le (α : Type*) [Preorder α] : cof α ≤ #α := by
  simpa using IsCofinal.univ.cof_le

theorem le_cof_iff [Preorder α] {c : Cardinal} :
    c ≤ cof α ↔ ∀ {s : Set α}, IsCofinal s → c ≤ #s := by
  rw [cof, le_ciInf_iff', Subtype.forall]

@[deprecated le_cof_iff (since := "2024-12-02")]
alias le_cof := le_cof_iff

theorem lt_cof [Preorder α] {s : Set α} : #s < cof α → ¬ IsCofinal s := by
  simpa using not_imp_not.2 IsCofinal.cof_le

/-- Any order has a cofinal subset whose cardinality is its cofinality. -/
theorem cof_eq (α : Type*) [Preorder α] : ∃ s : Set α, IsCofinal s ∧ cof α = #s := by
  obtain ⟨⟨s, hs⟩, h⟩ := ciInf_mem fun s : { s : Set α // IsCofinal s } ↦ #s.1
  exact ⟨s, hs, h.symm⟩

/-- Any well-order has a cofinal subset whose order type is its cofinality. -/
theorem ord_cof_eq (α : Type*) [LinearOrder α] [WellFoundedLT α] :
    ∃ s : Set α, IsCofinal s ∧ (Order.cof α).ord = typeLT s := by
  obtain ⟨s, hs, hα⟩ := cof_eq α
  obtain ⟨r, _, hr⟩ := ord_eq s
  have hr' := hs.trans (isCofinal_setOf_imp_lt r)
  refine ⟨_, hr', le_antisymm ?_ ?_⟩
  · rw [ord_le]
    exact hr'.cof_le
  · rw [hα, hr, Ordinal.type_le_iff']
    refine ⟨RelEmbedding.ofMonotone (inclusion ?_) ?_⟩
    · simp
    · rintro ⟨_, ⟨x, hx, rfl⟩⟩ ⟨_, ⟨y, _, rfl⟩⟩ h
      obtain h' | h' | h' := trichotomous_of r x y
      · exact h'
      · refine (h.ne ?_).elim
        rwa [Subtype.mk_eq_mk, Subtype.val_inj]
      · cases (hx _ h').not_lt h

end Order

namespace OrderIso

private theorem cof_le_lift [Preorder α] [Preorder β] (f : α ≃o β) :
    Cardinal.lift.{v} (Order.cof α) ≤ Cardinal.lift.{u} (Order.cof β) := by
  rw [Order.cof, Order.cof, lift_iInf, lift_iInf, le_ciInf_iff']
  exact fun ⟨s, hs⟩ ↦ csInf_le' ⟨⟨_, f.symm.map_cofinal hs⟩, mk_image_eq_lift _ _ f.symm.injective⟩

theorem cof_eq_lift [Preorder α] [Preorder β] (f : α ≃o β) :
    Cardinal.lift.{v} (Order.cof α) = Cardinal.lift.{u} (Order.cof β) :=
  have := f.toRelEmbedding.isRefl
  (f.cof_le_lift).antisymm (f.symm.cof_le_lift)

theorem cof_eq {α β : Type u} [Preorder α] [Preorder β] (f : α ≃o β) : Order.cof α = Order.cof β :=
  lift_inj.1 f.cof_eq_lift

end OrderIso

namespace Order

@[simp]
theorem cof_eq_zero [Preorder α] [IsEmpty α] : cof α = 0 := by
  rw [← le_zero_iff, ← mk_emptyCollection α]
  exact (IsCofinal.of_isEmpty (∅ : Set α)).cof_le

@[simp]
theorem cof_eq_zero_iff [Preorder α] : cof α = 0 ↔ IsEmpty α := by
  refine ⟨fun h ↦ ?_, fun h ↦ cof_eq_zero⟩
  obtain ⟨s, hs, hα⟩ := cof_eq α
  rw [hα, mk_eq_zero_iff, isEmpty_subtype, ← eq_empty_iff_forall_not_mem] at h
  rwa [h, isCofinal_empty_iff] at hs

@[simp]
theorem cof_ne_zero_iff [Preorder α] : cof α ≠ 0 ↔ Nonempty α := by
  simp [cof_eq_zero_iff.not]

@[simp]
theorem cof_ne_zero [Preorder α] [h : Nonempty α] : cof α ≠ 0 :=
  cof_ne_zero_iff.2 h

@[simp]
theorem cof_eq_one [Preorder α] [OrderTop α] : cof α = 1 := by
  apply le_antisymm
  · rw [← mk_singleton (⊤ : α)]
    exact IsCofinal.singleton_top.cof_le
  · rw [one_le_iff_ne_zero, cof_ne_zero_iff]
    exact top_nonempty α

theorem cof_eq_one_iff [Preorder α] : cof α = 1 ↔ Nonempty (OrderTop α) := by
  refine ⟨fun h ↦ ?_, fun ⟨h⟩ ↦ cof_eq_one⟩
  obtain ⟨s, hs, hα⟩ := cof_eq α
  rw [h, eq_comm, mk_set_eq_one_iff] at hα
  obtain ⟨x, rfl⟩ := hα
  refine ⟨@OrderTop.mk _ _ ⟨x⟩ ?_⟩
  simpa [IsCofinal] using hs

end Order

/-! ### Cofinality of ordinals -/

namespace Ordinal

variable [LinearOrder α] [WellFoundedLT α]

/-- The cofinality of an ordinal is the `Order.cof` of any well-order with a given order type. In
particular, `cof 0 = 0` and `cof (succ o) = 1`. -/
def cof (o : Ordinal.{u}) : Cardinal.{u} :=
  o.liftOnWellOrder (fun α _ _ ↦ Order.cof α) fun _ _ _ _ _ _ h ↦ by
    obtain ⟨e⟩ := typeLT_eq.1 h
    exact e.cof_eq

@[simp]
theorem cof_type (α : Type*) [LinearOrder α] [WellFoundedLT α] : (typeLT α).cof = Order.cof α :=
  liftOnWellOrder_type ..

@[simp]
theorem _root_.Order.cof_toType (o : Ordinal) : Order.cof o.toType = o.cof := by
  rw [← cof_type, type_toType]

@[deprecated cof_toType (since := "2024-12-02")]
theorem cof_eq_cof_toType (o : Ordinal) : o.cof = Order.cof o.toType :=
  (cof_toType o).symm

@[simp]
theorem _root_.Order.cof_Iio_ordinal (o : Ordinal.{u}) :
    Order.cof (Iio o) = Cardinal.lift.{u + 1} o.cof := by
  convert (enumIsoToType o).cof_eq_lift
  · rw [Cardinal.lift_id'.{u, u + 1}]
  · rw [cof_toType]

@[simp]
theorem lift_cof (o) : Cardinal.lift.{u, v} (cof o) = cof (Ordinal.lift.{u, v} o) := by
  refine inductionOnWellOrder o fun α _ _ ↦ ?_
  rw [← typeLT_uLift, cof_type, cof_type, ← Cardinal.lift_id'.{v, u} (Order.cof (ULift _)),
    ← Cardinal.lift_umax, OrderIso.uLift.cof_eq_lift]

theorem cof_le_card (o : Ordinal) : cof o ≤ card o := by
  rw [← cof_toType, ← mk_toType]
  exact cof_le _

theorem cof_ord_le (c : Cardinal) : c.ord.cof ≤ c := by
  simpa using cof_le_card c.ord

theorem ord_cof_le (o : Ordinal) : o.cof.ord ≤ o :=
  (ord_le_ord.2 (cof_le_card o)).trans (ord_card_le o)

@[simp]
protected theorem _root_.Order.cof_cof (α : Type*) [LinearOrder α] [WellFoundedLT α] :
    (Order.cof α).ord.cof = Order.cof α := by
  obtain ⟨s, hs, hα⟩ := ord_cof_eq α
  obtain ⟨t, ht, hα'⟩ := cof_eq s
  apply ((hs.trans ht).cof_le.trans_eq _).antisymm'
  · apply_fun card at hα
    simpa [hα] using cof_ord_le _
  · rw [mk_image_eq Subtype.val_injective, ← hα', hα, cof_type]

@[simp]
theorem cof_cof (o : Ordinal) : o.cof.ord.cof = o.cof := by
  rw [← cof_toType o, Order.cof_cof]

@[simp]
theorem cof_zero : cof 0 = 0 := by
  rw [← cof_toType, cof_eq_zero]

@[simp]
theorem cof_eq_zero : cof o = 0 ↔ o = 0 := by
  rw [← cof_toType, cof_eq_zero_iff, toType_empty_iff_eq_zero]

theorem cof_ne_zero : cof o ≠ 0 ↔ o ≠ 0 :=
  cof_eq_zero.not

@[simp]
theorem cof_succ (o : Ordinal) : cof (succ o) = 1 := by
  rw [← cof_toType, cof_eq_one]

@[simp]
theorem cof_nat_succ (n : ℕ) : cof (n + 1) = 1 :=
  cof_succ n

@[simp]
theorem cof_eq_one : cof o = 1 ↔ ¬ IsSuccPrelimit o := by
  rw [← cof_toType, cof_eq_one_iff]
  sorry

@[simp]
theorem cof_le_one : cof o ≤ 1 ↔ ¬ IsLimit o := by
  sorry

theorem cof_le_one_of_cof_lt_aleph0 (h : cof o < ℵ₀) : cof o ≤ 1 := by
  obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.1 h
  apply_fun cof ∘ ord at hn
  cases n
  · suffices o = 0 by simp [this]
    simpa using hn
  · simp_rw [comp_apply, ord_nat, Nat.cast_succ, cof_nat_succ, cof_cof] at hn
    rw [hn]

-- TODO: Order.cof version
theorem aleph0_le_cof : ℵ₀ ≤ cof o ↔ IsLimit o := by
  obtain rfl | ⟨o, rfl⟩ | ho := zero_or_succ_or_limit o
  · simp
  · simp
  · simp_rw [ho, iff_true]
    refine le_of_not_lt fun h => ?_
    have := cof_le_one_of_cof_lt_aleph0 h
    rw [cof_le_one] at this
    contradiction

/-! ### Cofinality of suprema and least strict upper bounds -/

/-- The range of an indexed supremum is cofinal within the supremum. -/
theorem isCofinal_range_iSup {f : ι → Ordinal} (H : ∀ i, f i < ⨆ i, f i) :
    IsCofinal (range fun i ↦ enumIsoToType _ ⟨_, H i⟩) := by
  intro x
  have H' := ((enumIsoToType _).symm x).2
  rw [mem_Iio, lt_ciSup_iff'] at H'
  · obtain ⟨i, hi⟩ := H'
    use enumIsoToType _ ⟨_, H i⟩
    simpa [← (enumIsoToType _).symm.le_iff_le] using hi.le
  · use iSup f
    rintro _ ⟨i, rfl⟩
    exact (H i).le

theorem cof_iSup_le_lift {f : ι → Ordinal.{v}} (H : ∀ i, f i < ⨆ i, f i) :
    Cardinal.lift.{u} (cof (⨆ i, f i)) ≤ Cardinal.lift.{v} #ι := by
  rw [← cof_toType]
  exact (Cardinal.lift_le.2 (isCofinal_range_iSup H).cof_le).trans mk_range_le_lift

theorem cof_iSup_le {f : ι → Ordinal} (H : ∀ i, f i < ⨆ i, f i) : cof (⨆ i, f i) ≤ #ι := by
  simpa using cof_iSup_le_lift H

theorem cof_iSup_Iio_le {f : Iio a → Ordinal} (H : ∀ i, f i < ⨆ i, f i) :
    cof (⨆ i, f i) ≤ a.card := by
  convert cof_iSup_le_lift H
  rw [Cardinal.lift_id'.{u, u + 1}, mk_Iio_ordinal, Cardinal.lift_le]

theorem iSup_lt_of_lt_cof_lift {f : ι → Ordinal} {o : Ordinal.{v}} (H : ∀ i, f i < o)
    (h : Cardinal.lift.{v} #ι < Cardinal.lift.{u} o.cof) : ⨆ i, f i < o := by
  apply (ciSup_le' fun i ↦ (H i).le).lt_of_ne
  rintro rfl
  exact (cof_iSup_le_lift H).not_lt h

theorem iSup_lt_of_lt_cof {ι} {f : ι → Ordinal} (H : ∀ i, f i < o) (h : #ι < o.cof) :
    ⨆ i, f i < o := by
  apply iSup_lt_of_lt_cof_lift H
  simpa

theorem iSup_Iio_lt_of_lt_cof {f : Iio a → Ordinal} (H : ∀ i, f i < o) (h : a < o.cof.ord) :
    ⨆ i, f i < o := by
  apply iSup_lt_of_lt_cof_lift H
  rwa [Cardinal.lift_id'.{u, u + 1}, mk_Iio_ordinal, Cardinal.lift_lt, ← lt_ord]

/-! ### Fundamental sequences -/

/-- A fundamental sequence for an ordinal `a` is a strictly monotonic function from `Iio a.cof` to
`Iio a` with cofinal range. We provide `o = a.cof` explicitly to avoid type rewrites. -/
structure IsFundamentalSeq (f : Iio o → Iio a) : Prop where
  /-- This, alongside the other conditions, implies `o = a.cof.ord`. -/
  le_cof : o ≤ a.cof.ord
  /-- A fundamental sequence is strictly monotonic. -/
  strictMono : StrictMono f
  /-- A fundamental sequence has cofinal range. -/
  isCofinal_range : IsCofinal (range f)

namespace IsFundamentalSeq

variable {f : Iio o → Iio a}

theorem monotone (h : IsFundamentalSeq f) : Monotone f :=
  h.strictMono.monotone

theorem cof_eq (h : IsFundamentalSeq f) : o = a.cof.ord := by
  apply h.le_cof.antisymm
  have := h.isCofinal_range.cof_le.trans mk_range_le
  rwa [cof_Iio_ordinal, mk_Iio_ordinal, Cardinal.lift_le, ← ord_le] at this

theorem id_of_le_cof (h : o ≤ o.cof.ord) : IsFundamentalSeq (@id (Iio o)) :=
  ⟨h, strictMono_id, by simp⟩

/-- The empty sequence is a fundamental sequence for `0`. -/
protected theorem zero (f : Iio 0 → Iio 0) : IsFundamentalSeq f :=
  ⟨by simp, isEmptyElim, isEmptyElim⟩

/-- The sequence `{o}` is a fundamental sequence for `succ o`. -/
protected theorem succ : IsFundamentalSeq fun _ : Iio 1 ↦ ⟨o, lt_succ o⟩ := by
  refine ⟨?_, Subsingleton.strictMono _, ?_⟩ <;> simp

/-- The composition of fundamental sequences is a fundamental sequence. -/
theorem trans {g : Iio o' → Iio o} (hf : IsFundamentalSeq f) (hg : IsFundamentalSeq g) :
    IsFundamentalSeq (f ∘ g) := by
  refine ⟨?_, hf.strictMono.comp hg.strictMono, fun x ↦ ?_⟩
  · rw [hg.cof_eq, hf.cof_eq, cof_cof]
  · obtain ⟨_, ⟨y, rfl⟩, hx⟩ := hf.isCofinal_range x
    obtain ⟨_, ⟨z, rfl⟩, hy⟩ := hg.isCofinal_range y
    exact ⟨_, mem_range_self z, hx.trans (hf.monotone hy)⟩

protected theorem iSup (hf : IsFundamentalSeq f) (ho : IsLimit o) : ⨆ i, (f i).1 = a := by
  apply (ciSup_le' fun i ↦ (f i).2.le).antisymm
  apply le_of_forall_lt fun x hx ↦ ?_
  rw [lt_ciSup_iff']
  · obtain ⟨_, ⟨y, rfl⟩, hy⟩ := hf.isCofinal_range ⟨x, hx⟩
    exact ⟨⟨_, ho.succ_lt y.2⟩, hy.trans_lt (hf.strictMono (lt_succ y.1))⟩
  · use a
    rintro _ ⟨i, rfl⟩
    exact (f i).2.le

end IsFundamentalSeq

/-- Every ordinal has a fundamental sequence. -/
theorem exists_isFundamentalSeq (o : Ordinal) :
    ∃ f : Iio o.cof.ord → Iio o, IsFundamentalSeq f := by
  obtain ⟨s, hs, ho⟩ := ord_cof_eq o.toType
  rw [cof_toType] at ho
  rw [ho]
  let g := OrderIso.ofRelIsoLT (enum (α := s) (· < ·))
  refine ⟨fun x ↦ (enumIsoToType _).symm (g x), ho.ge, ?_, fun x ↦ ?_⟩
  · exact (OrderIso.strictMono _).comp g.strictMono
  · obtain ⟨y, hy, hx⟩ := hs (enumIsoToType o x)
    refine ⟨(enumIsoToType o).symm y, ⟨g.symm ⟨y, hy⟩, ?_⟩, ?_⟩ <;>
      simp [← o.enumIsoToType.le_iff_le, hx]

theorem IsNormal.cof_le {f : Ordinal → Ordinal} (hf : IsNormal f) : cof o ≤ cof (f o) := by
  obtain rfl | ⟨a, rfl⟩ | ho := zero_or_succ_or_limit o
  · simp
  · rw [cof_succ, Cardinal.one_le_iff_ne_zero, cof_ne_zero]
    exact (hf.strictMono (lt_succ a)).ne_bot
  · obtain ⟨g, hg⟩ := exists_isFundamentalSeq (f o)
    have H (x : Iio (f o)) : ∃ y : Iio o, x < f y := by simpa using (hf.limit_lt ho).1 x.2
    choose s hs using H
    have hs' : ⨆ i, (s (g i)).1 = o := by
      apply (ciSup_le' fun x ↦ (s (g x)).2.le).antisymm
      apply le_of_forall_lt fun x hx ↦ ?_
      rw [lt_ciSup_iff']
      · obtain ⟨_, ⟨y, rfl⟩, h : f x ≤ g y⟩ := hg.isCofinal_range ⟨f x, hf.strictMono hx⟩
        exact ⟨y, hf.lt_iff.1 <| h.trans_lt (hs (g y))⟩
      · use o
        rintro _ ⟨x, rfl⟩
        exact (s (g x)).2.le
    convert cof_iSup_Iio_le (f := fun x ↦ s (g x)) _ using 1
    · rw [hs']
    · rw [card_ord]
    · simpa only [hs'] using fun x ↦ (s (g x)).2

/-- If `g` is a fundamental sequence for `o` and `f` is normal, then `f ∘ g` is a fundamental
sequence for `f o`. -/
protected theorem IsNormal.isFundamentalSeq {f : Ordinal → Ordinal} (hf : IsNormal f)
    (ho : IsLimit o) {g : Iio a → Iio o} (hg : IsFundamentalSeq g) :
    IsFundamentalSeq fun x : Iio a ↦ ⟨f (g x), hf.strictMono (g x).2⟩ := by
  refine ⟨?_, fun x y h ↦ hf.strictMono (hg.strictMono h), fun x ↦ ?_⟩
  · rw [hg.cof_eq, ord_le_ord]
    exact hf.cof_le
  · obtain ⟨y, hy, hx⟩ := (hf.limit_lt ho).1 x.2
    obtain ⟨_, ⟨z, rfl⟩, hz⟩ := hg.isCofinal_range ⟨y, hy⟩
    exact ⟨_, mem_range_self z, hx.le.trans (hf.monotone hz)⟩

theorem IsNormal.cof_eq {f : Ordinal → Ordinal} (hf : IsNormal f) (ho : IsLimit o) :
    cof (f o) = cof o := by
  obtain ⟨g, hg⟩ := exists_isFundamentalSeq o
  exact (ord_injective (hf.isFundamentalSeq ho hg).cof_eq).symm

@[simp]
theorem cof_add {b : Ordinal} (h : b ≠ 0) : cof (a + b) = cof b := by
  obtain rfl | ⟨c, rfl⟩ | hb := zero_or_succ_or_limit b
  · contradiction
  · rw [add_succ, cof_succ, cof_succ]
  · exact (isNormal_add_right a).cof_eq hb

@[simp]
theorem cof_preOmega {o : Ordinal} (ho : o.IsLimit) : (preOmega o).cof = o.cof :=
  isNormal_preOmega.cof_eq ho

@[simp]
theorem cof_omega {o : Ordinal} (ho : o.IsLimit) : (ω_ o).cof = o.cof :=
  isNormal_omega.cof_eq ho

@[simp]
theorem cof_omega0 : cof ω = ℵ₀ := by
  apply (aleph0_le_cof.2 isLimit_omega0).antisymm'
  rw [← card_omega0]
  apply cof_le_card

@[simp]
theorem cof_univ : cof univ.{u, v} = Cardinal.univ.{u, v} := by
  apply le_antisymm (cof_le_card _)
  obtain ⟨s, hs, ho⟩ := cof_eq Ordinal.{u}
  rw [← not_bddAbove_iff_isCofinal, bddAbove_iff_small, small_iff_lift_mk_lt_univ,
    Cardinal.lift_id, ← ho, not_lt, ← Cardinal.lift_le.{v}, Cardinal.lift_univ,
    Cardinal.univ_umax] at hs
  rwa [card_univ, univ, ← lift_cof, cof_type]

end Ordinal

/-! ### Regular cardinals -/

namespace Cardinal
open Ordinal

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

theorem isRegular_succ {c : Cardinal.{u}} (h : ℵ₀ ≤ c) : IsRegular (succ c) := by
  refine ⟨h.trans (le_succ c), succ_le_of_lt ?_⟩
  obtain ⟨f, hf⟩ := exists_isFundamentalSeq (succ c).ord
  have := card_iSup_Iio_le_card_mul_iSup fun i ↦ (f i).1
  rw [Cardinal.lift_id, hf.iSup, card_ord, card_ord] at this
  · by_contra! hc
    have := this.trans (mul_le_mul' hc (ciSup_le' fun i ↦ card_le_iff.2 (f i).2))
    rw [mul_eq_self h, succ_le_iff] at this
    exact this.false
  · apply isLimit_ord
    rw [aleph0_le_cof]
    exact isLimit_ord (h.trans (le_succ _))

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

theorem isRegular_aleph_one : IsRegular ℵ₁ := by
  simpa using isRegular_aleph_succ 0

#exit

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

/-! ### Basic results -/

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

end Ordinal

namespace Cardinal
open Ordinal

/-! ### Results on sets -/

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

theorem mk_subset_mk_lt_cof {α : Type*} (h : ∀ x < #α, 2 ^ x < #α) :
    #{ s : Set α // #s < cof (#α).ord } = #α := by
  rcases eq_or_ne #α 0 with (ha | ha)
  · simp [ha]
  have h' : IsStrongLimit #α := ⟨ha, @h⟩
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

/-! ### Consequences of König's lemma -/

theorem lt_power_cof {c : Cardinal.{u}} : ℵ₀ ≤ c → c < c ^ c.ord.cof :=
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

theorem lt_cof_power {a b : Cardinal} (ha : ℵ₀ ≤ a) (b1 : 1 < b) : a < (b ^ a).ord.cof := by
  have b0 : b ≠ 0 := (zero_lt_one.trans b1).ne'
  apply lt_imp_lt_of_le_imp_le (power_le_power_left <| power_ne_zero a b0)
  rw [← power_mul, mul_eq_self ha]
  exact lt_power_cof (ha.trans <| (cantor' _ b1).le)

end Cardinal
