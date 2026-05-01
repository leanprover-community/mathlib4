/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn, Violeta Hernández Palacios
-/
module

public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.SetTheory.Cardinal.Cofinality.Basic
public import Mathlib.SetTheory.Ordinal.FixedPoint

/-!
# Cofinality of an ordinal

This file contains the definition of the cofinality `Ordinal.cof o` of an ordinal. This is the
cofinality of the ordinal `o` when viewed as a linear order.

## Main statements

* `Cardinal.lt_power_cof_ord`: A consequence of König's theorem stating that `c < c ^ c.ord.cof` for
  `c ≥ ℵ₀`.

## Implementation notes

* We do not separately define the cofinality of a cardinal. If `c` is a cardinal number, you can
  write its cofinality as `c.ord.cof`.
-/

public noncomputable section

open Function Cardinal Set Order
open scoped Ordinal

universe u v w

variable {α γ : Type u} {β : Type v}

theorem Order.cof_int : cof ℤ = ℵ₀ := by simp

/-! ### Cofinality of ordinals -/

-- TODO: generalize to `OrderType`
namespace Ordinal

/-- The cofinality on an ordinal is the `Order.cof` of any isomorphic linear order.

In particular, `cof 0 = 0` and `cof (succ o) = 1`. -/
def cof (o : Ordinal.{u}) : Cardinal.{u} :=
  o.liftOnWellOrder (fun α _ _ ↦ Order.cof α) fun _ _ _ _ _ _ h ↦
    let ⟨f⟩ := type_eq.1 h
    (OrderIso.ofRelIsoLT f).cof_congr

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
  cases o using inductionOnWellOrder with | type α
  rw [cof_type, ← type_lt_ulift, cof_type, ← Cardinal.lift_id'.{u, v} (Order.cof (ULift _)),
    ← Cardinal.lift_umax, ← ULift.orderIso.lift_cof_congr]

theorem _root_.Order.cof_Iio [LinearOrder α] [WellFoundedLT α] (x : α) :
    Order.cof (Iio x) = cof (typein (α := α) (· < ·) x) :=
  (cof_type _).symm

@[simp]
theorem cof_Iio (o : Ordinal.{u}) : Order.cof (Iio o) = cof (lift.{u + 1} o) := by
  rw [Order.cof_Iio, typein_ordinal]

theorem cof_le_card (o : Ordinal) : cof o ≤ card o := by
  simpa using cof_le_cardinalMk o.ToType

theorem cof_ord_le (c : Cardinal) : c.ord.cof ≤ c := by
  simpa using cof_le_card c.ord

theorem ord_cof_le (o : Ordinal) : o.cof.ord ≤ o :=
  (ord_le_ord.2 (cof_le_card o)).trans (ord_card_le o)

@[simp]
theorem cof_eq_zero {o} : cof o = 0 ↔ o = 0 := by
  rw [← cof_toType, cof_eq_zero_iff, isEmpty_toType_iff]

@[deprecated cof_eq_zero (since := "2026-02-18")]
theorem cof_ne_zero {o} : cof o ≠ 0 ↔ o ≠ 0 :=
  cof_eq_zero.not

@[simp]
theorem cof_pos {o} : 0 < cof o ↔ 0 < o := by
  simp [pos_iff_ne_zero]

@[simp]
theorem cof_zero : cof 0 = 0 :=
  cof_eq_zero.2 rfl

theorem cof_eq_one_iff {o} : cof o = 1 ↔ o ∈ range succ := by
  cases o using inductionOnWellOrder with | type α
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

theorem one_lt_cof_iff {o : Ordinal} : 1 < cof o ↔ IsSuccLimit o := by
  rw [← not_iff_not, not_lt, Cardinal.le_one_iff, isSuccLimit_iff,
    not_and_or, not_ne_iff, not_isSuccPrelimit_iff', cof_eq_zero, cof_eq_one_iff]

@[simp]
theorem cof_lt_aleph0_iff {o : Ordinal} : cof o < ℵ₀ ↔ cof o ≤ 1 := by
  simpa using Order.cof_lt_aleph0_iff (α := o.ToType)

@[simp]
theorem aleph0_le_cof_iff {o : Ordinal} : ℵ₀ ≤ cof o ↔ 1 < cof o := by
  simp [← not_lt]

@[deprecated one_lt_cof_iff (since := "2026-03-22")]
theorem aleph0_le_cof {o} : ℵ₀ ≤ cof o ↔ IsSuccLimit o := by
  rw [aleph0_le_cof_iff, one_lt_cof_iff]

/-- A countable limit ordinal has cofinality `ℵ₀`. -/
theorem cof_eq_aleph0_of_isSuccLimit {o : Ordinal} (ho : IsSuccLimit o) (ho' : o < ω₁) :
    cof o = ℵ₀ := by
  apply ((cof_le_card _).trans _).antisymm
  · rwa [aleph0_le_cof_iff, one_lt_cof_iff]
  · rwa [card_le_iff, succ_aleph0, ord_aleph]

@[simp]
theorem cof_omega0 : cof ω = ℵ₀ :=
  cof_eq_aleph0_of_isSuccLimit isSuccLimit_omega0 omega0_lt_omega_one

@[deprecated (since := "2026-02-18")] alias cof_eq_one_iff_is_succ := cof_eq_one_iff

theorem ord_cof_eq (α : Type*) [LinearOrder α] [WellFoundedLT α] :
    ∃ s : Set α, IsCofinal s ∧ typeLT s = (Order.cof α).ord := by
  obtain ⟨s, hs, hs'⟩ := Order.cof_eq α
  obtain ⟨r, hr, hr'⟩ := exists_ord_eq s
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

@[simp]
theorem _root_.Order.cof_ord_cof (α : Type*) [LinearOrder α] [WellFoundedLT α] :
    (Order.cof α).ord.cof = Order.cof α := by
  obtain ⟨s, hs, hs'⟩ := ord_cof_eq α
  rw [← hs', cof_type]
  apply le_antisymm
  · rw [← card_ord (Order.cof α), ← hs', card_type]
    exact cof_le_cardinalMk s
  · rw [le_cof_iff]
    exact fun t ht ↦ (cof_le (hs.trans ht)).trans_eq (mk_image_eq Subtype.val_injective)

@[simp]
theorem cof_ord_cof (o : Ordinal) : o.cof.ord.cof = o.cof := by
  simpa using Order.cof_ord_cof o.ToType

@[deprecated (since := "2026-03-21")] alias cof_cof := cof_ord_cof

/-! ### Cofinalities and suprema -/

section LinearOrder
variable [LinearOrder β] [LinearOrder γ]

theorem lift_cof_iSup_add_one [Small.{u} β] {f : β → Ordinal} (hf : StrictMono f) :
    Cardinal.lift.{v} (cof (⨆ i, f i + 1)) = Cardinal.lift.{u} (Order.cof β) := by
  have : StrictMono (β := Iio (⨆ i, f i + 1)) (fun i ↦ ⟨f i, ?_⟩) := fun x y h ↦ hf h
  · have := lift_cof_congr_of_strictMono this ?_
    · rw [← Cardinal.lift_inj.{_, max (u + 1) v}, Cardinal.lift_lift.{_, _, v},
        Cardinal.lift_umax.{_, u + 1}, Cardinal.lift_umax.{_, u + 1}, this]
      simp
    · intro ⟨b, hb⟩
      rw [mem_Iio, Ordinal.lt_iSup_add_one_iff] at hb
      obtain ⟨i, hi⟩ := hb
      exact ⟨_, Set.mem_range_self i, hi⟩
  · rw [mem_Iio]
    exact (lt_add_one _).trans_le <| le_ciSup bddAbove_of_small _

theorem cof_iSup_add_one {f : γ → Ordinal} (hf : StrictMono f) :
    cof (⨆ i, f i + 1) = Order.cof γ := by
  simpa using lift_cof_iSup_add_one hf

theorem lift_cof_iSup [Small.{u} β] [NoMaxOrder β] {f : β → Ordinal} (hf : StrictMono f) :
    Cardinal.lift.{v} (cof (⨆ i, f i)) = Cardinal.lift.{u} (Order.cof β) := by
  rw [← iSup_add_one hf, lift_cof_iSup_add_one hf]

theorem cof_iSup [NoMaxOrder γ] {f : γ → Ordinal} (hf : StrictMono f) :
    cof (⨆ i, f i) = Order.cof γ := by
  simpa using lift_cof_iSup hf

end LinearOrder

theorem cof_iSup_Iio_add_one {a} {f : Iio a → Ordinal} (hf : StrictMono f) :
    cof (⨆ i, f i + 1) = cof a := by
  simpa [← lift_cof] using lift_cof_iSup_add_one hf

theorem cof_iSup_Iio {a} {f : Iio a → Ordinal} (hf : StrictMono f) (ha : IsSuccPrelimit a) :
    cof (⨆ i, f i) = cof a := by
  rw [← iSup_Iio_add_one hf ha, cof_iSup_Iio_add_one hf]

theorem cof_map_of_isNormal {f} (hf : IsNormal f) {a} (ha : IsSuccLimit a) : cof (f a) = cof a := by
  rw [hf.apply_of_isSuccLimit ha, cof_iSup_Iio _ ha.isSuccPrelimit]
  exact hf.strictMono.comp <| Subtype.strictMono_coe _

@[deprecated (since := "2026-03-19")]
alias cof_eq_of_isNormal := cof_map_of_isNormal

@[deprecated (since := "2025-12-25")]
alias IsNormal.cof_eq := cof_eq_of_isNormal

theorem le_cof_map_of_isNormal {f} (hf : IsNormal f) (a) : cof a ≤ cof (f a) := by
  rcases zero_or_succ_or_isSuccLimit a with (rfl | ⟨b, rfl⟩ | ha)
  · rw [cof_zero]
    exact zero_le
  · rw [cof_succ, Cardinal.one_le_iff_ne_zero, cof_eq_zero.ne]
    exact (hf.strictMono (lt_succ b)).ne_zero
  · rw [cof_map_of_isNormal hf ha]

@[deprecated (since := "2026-03-19")]
alias cof_le_of_isNormal := le_cof_map_of_isNormal

@[deprecated (since := "2025-12-25")]
alias IsNormal.cof_le := le_cof_map_of_isNormal

theorem sSup_add_one_lt_of_lt_cof {s : Set Ordinal.{u}} {a : Ordinal.{u}}
    (ha : #s < (lift.{u + 1} a).cof) (hs : ∀ i ∈ s, i < a) : sSup ((· + 1) '' s) < a := by
  let f := OrderIso.ofRelIsoLT (enum (α := s) (· < ·))
  have : Small.{u} (Iio (typeLT s)) := by
    refine small_of_injective (β := Iio a) (f := fun x ↦ ⟨f x, hs _ (f x).2⟩) fun _ ↦ ?_
    simp [Subtype.val_inj]
  have : range (fun i ↦ (f i).1 + 1) = (· + 1) '' s := by
    convert range_comp (· + 1) (fun i ↦ (f i).1)
    rw [range_comp', f.range_eq]
    simp
  rw [← this, sSup_range]
  apply lt_of_le_of_ne
  · simp [hs]
  · rintro rfl
    rw [← lift_cof, ← Cardinal.lift_lt.{_, u + 2}, Cardinal.lift_lift,
      lift_cof_iSup_add_one fun _ ↦ by simp, cof_Iio, ← lift_cof, cof_type,
      Cardinal.lift_lift, Cardinal.lift_lt] at ha
    exact ha.not_ge (cof_le_cardinalMk _)

theorem sSup_lt_of_lt_cof {s : Set Ordinal.{u}} {a : Ordinal.{u}}
    (ha : #s < (lift.{u + 1} a).cof) (hs : ∀ i ∈ s, i < a) : sSup s < a :=
  (sSup_le_sSup_add_one s).trans_lt (sSup_add_one_lt_of_lt_cof ha hs)

theorem lift_iSup_add_one_lt_of_lt_cof {f : β → Ordinal.{u}} {a : Ordinal.{u}}
    (ha : Cardinal.lift.{u} #β < (lift.{v} a).cof) (hf : ∀ i, f i < a) : ⨆ i, f i + 1 < a := by
  rw [iSup, range_comp' (· + 1)]
  apply sSup_add_one_lt_of_lt_cof _ (by simpa)
  rw [← Cardinal.lift_lt.{_, v}]
  apply mk_range_le_lift.trans_lt
  rw [← Cardinal.lift_lt.{_, u + 1}] at ha
  simpa [← lift_cof] using ha

theorem iSup_add_one_lt_of_lt_cof {f : α → Ordinal.{u}} {a : Ordinal.{u}}
    (ha : #α < a.cof) (hf : ∀ i, f i < a) : ⨆ i, f i + 1 < a := by
  rw [← Cardinal.lift_lt.{_, u}, lift_cof] at ha
  simpa using lift_iSup_add_one_lt_of_lt_cof ha hf

theorem lift_iSup_lt_of_lt_cof {f : β → Ordinal.{u}} {a : Ordinal.{u}}
    (ha : Cardinal.lift.{u} #β < (lift.{v} a).cof) (hf : ∀ i, f i < a) : ⨆ i, f i < a :=
  (iSup_le_iSup_add_one f).trans_lt (lift_iSup_add_one_lt_of_lt_cof ha hf)

theorem iSup_lt_of_lt_cof {f : α → Ordinal.{u}} {a : Ordinal.{u}}
    (ha : #α < a.cof) (hf : ∀ i, f i < a) : ⨆ i, f i < a := by
  rw [← Cardinal.lift_lt.{_, u}, lift_cof] at ha
  simpa using lift_iSup_lt_of_lt_cof ha hf

theorem cof_lift_iSup_add_one_le [Small.{u} β] (f : β → Ordinal.{u}) :
    cof (lift.{v} (⨆ i, f i + 1)) ≤ Cardinal.lift.{u} (#β) := by
  by_contra! hf
  exact (lift_iSup_add_one_lt_of_lt_cof hf <| Ordinal.lt_iSup_add_one _).false

theorem cof_iSup_add_one_le (f : α → Ordinal.{u}) : cof (⨆ i, f i + 1) ≤ #α := by
  simpa using cof_lift_iSup_add_one_le f

theorem _root_.Cardinal.sSup_lt_of_lt_cof_ord {s : Set Cardinal.{u}} {a : Cardinal.{u}}
    (ha : #s < (Cardinal.lift.{u + 1} a).ord.cof) (hs : ∀ i ∈ s, i < a) : sSup s < a := by
  rw [← ord_lt_ord, sSup_ord]
  apply Ordinal.sSup_lt_of_lt_cof
  · simpa [mk_image_eq ord_injective]
  · simpa

theorem _root_.Cardinal.lift_iSup_lt_of_lt_cof_ord {f : β → Cardinal.{u}} {a : Cardinal.{u}}
    (ha : Cardinal.lift.{u} #β < a.lift.ord.cof) (hf : ∀ i, f i < a) : ⨆ i, f i < a := by
  rw [← ord_lt_ord, iSup_ord]
  apply Ordinal.lift_iSup_lt_of_lt_cof <;> simpa

theorem _root_.Cardinal.iSup_lt_of_lt_cof_ord {f : α → Cardinal.{u}} {a : Cardinal.{u}}
    (ha : #α < a.ord.cof) (hf : ∀ i, f i < a) : ⨆ i, f i < a := by
  rw [← ord_lt_ord, iSup_ord]
  apply Ordinal.iSup_lt_of_lt_cof <;> simpa

set_option linter.deprecated false in
/-- The set in the `lsub` characterization of `cof` is nonempty. -/
@[deprecated "to build an increasing function with limit o, use the fundamental sequence API."
(since := "2026-03-27")]
theorem cof_lsub_def_nonempty (o) :
    { a : Cardinal | ∃ (ι : _) (f : ι → Ordinal), lsub.{u, u} f = o ∧ #ι = a }.Nonempty :=
  ⟨_, ⟨_, _, lsub_typein o, mk_toType o⟩⟩

set_option linter.deprecated false in
@[deprecated "to build an increasing function with limit o, use the fundamental sequence API."
(since := "2026-03-27")]
theorem cof_eq_sInf_lsub (o : Ordinal.{u}) : cof o =
    sInf { a : Cardinal | ∃ (ι : Type u) (f : ι → Ordinal), lsub.{u, u} f = o ∧ #ι = a } := by
  refine le_antisymm (le_csInf (cof_lsub_def_nonempty o) ?_) (csInf_le' ?_)
  · rintro a ⟨ι, f, hf, rfl⟩
    rw [← hf]
    exact cof_iSup_add_one_le f
  · rcases Order.cof_eq (α := o.ToType) with ⟨S, hS, hS'⟩
    let f : S → Ordinal := fun s => typein LT.lt s.val
    refine ⟨S, f, le_antisymm (lsub_le fun i => typein_lt_self (o := o) i)
      (le_of_forall_lt fun a ha => ?_), by rwa [cof_toType] at hS'⟩
    rw [← type_toType o] at ha
    rcases hS (enum (· < ·) ⟨a, ha⟩) with ⟨b, hb, hb'⟩
    rw [← not_lt, ← typein_le_typein, typein_enum] at hb'
    exact hb'.trans_lt (lt_lsub.{u, u} f ⟨b, hb⟩)

set_option linter.deprecated false in
@[deprecated "to build an increasing function with limit o, use the fundamental sequence API."
(since := "2026-03-27")]
theorem exists_lsub_cof (o : Ordinal) :
    ∃ (ι : _) (f : ι → Ordinal), lsub.{u, u} f = o ∧ #ι = cof o := by
  rw [cof_eq_sInf_lsub]
  exact csInf_mem (cof_lsub_def_nonempty o)

set_option linter.deprecated false in
@[deprecated cof_iSup_add_one_le (since := "2026-03-22")]
theorem cof_lsub_le {ι} (f : ι → Ordinal) : cof (lsub.{u, u} f) ≤ #ι :=
  cof_iSup_add_one_le f

set_option linter.deprecated false in
@[deprecated cof_lift_iSup_add_one_le (since := "2026-03-22")]
theorem cof_lsub_le_lift {ι} (f : ι → Ordinal) :
    cof (lsub.{u, v} f) ≤ Cardinal.lift.{v, u} #ι := by
  rw [← lift_id'.{u} (lsub f), ← Cardinal.lift_umax.{u, v}]
  exact cof_lift_iSup_add_one_le _

set_option linter.deprecated false in
@[deprecated le_cof_iff (since := "2026-03-21")]
theorem le_cof_iff_lsub {o : Ordinal} {a : Cardinal} :
    a ≤ cof o ↔ ∀ {ι} (f : ι → Ordinal), lsub.{u, u} f = o → a ≤ #ι := by
  rw [cof_eq_sInf_lsub]
  exact
    (le_csInf_iff'' (cof_lsub_def_nonempty o)).trans
      ⟨fun H ι f hf => H _ ⟨ι, f, hf, rfl⟩, fun H b ⟨ι, f, hf, hb⟩ => by
        rw [← hb]
        exact H _ hf⟩

set_option linter.deprecated false in
@[deprecated lift_iSup_add_one_lt_of_lt_cof (since := "2026-03-22")]
theorem lsub_lt_ord_lift {ι} {f : ι → Ordinal} {c : Ordinal}
    (hι : Cardinal.lift.{v, u} #ι < c.cof)
    (hf : ∀ i, f i < c) : lsub.{u, v} f < c := by
  apply lift_iSup_add_one_lt_of_lt_cof _ hf
  rwa [Cardinal.lift_umax, c.lift_id']

set_option linter.deprecated false in
@[deprecated iSup_add_one_lt_of_lt_cof (since := "2026-03-22")]
theorem lsub_lt_ord {ι} {f : ι → Ordinal} {c : Ordinal} (hι : #ι < c.cof) :
    (∀ i, f i < c) → lsub.{u, u} f < c :=
  iSup_add_one_lt_of_lt_cof hι

@[deprecated lift_iSup_lt_of_lt_cof (since := "2026-03-22")]
theorem cof_iSup_le_lift {ι} {f : ι → Ordinal} (H : ∀ i, f i < iSup f) :
    cof (iSup f) ≤ Cardinal.lift.{v, u} #ι := by
  by_contra! hf
  apply (lift_iSup_lt_of_lt_cof _ H).false
  rwa [Cardinal.lift_umax, lift_id']

@[deprecated iSup_lt_of_lt_cof (since := "2026-03-22")]
theorem cof_iSup_le {ι} {f : ι → Ordinal} (H : ∀ i, f i < iSup f) :
    cof (iSup f) ≤ #ι := by
  by_contra! hf
  exact (iSup_lt_of_lt_cof hf H).false

@[deprecated lift_iSup_lt_of_lt_cof (since := "2026-03-22")]
theorem iSup_lt_ord_lift {ι} {f : ι → Ordinal} {c : Ordinal} (hι : Cardinal.lift.{v, u} #ι < c.cof)
    (hf : ∀ i, f i < c) : iSup f < c := by
  apply lift_iSup_lt_of_lt_cof _ hf
  rwa [Cardinal.lift_umax, lift_id']

@[deprecated (since := "2026-03-22")]
alias iSup_lt_ord := iSup_lt_of_lt_cof

@[deprecated lift_iSup_lt_of_lt_cof (since := "2026-03-22")]
theorem iSup_lt_lift {ι} {f : ι → Cardinal} {c : Cardinal}
    (hι : Cardinal.lift.{v, u} #ι < c.ord.cof)
    (hf : ∀ i, f i < c) : iSup f < c := by
  apply lift_iSup_lt_of_lt_cof_ord _ hf
  rwa [Cardinal.lift_umax, c.lift_id']

@[deprecated (since := "2026-03-22")]
alias iSup_lt := Cardinal.iSup_lt_of_lt_cof_ord

theorem nfpFamily_lt_ord_lift {ι} {f : ι → Ordinal → Ordinal} {c} (hc : ℵ₀ < cof c)
    (hc' : Cardinal.lift.{v, u} #ι < cof c) (hf : ∀ (i), ∀ b < c, f i b < c) {a} (ha : a < c) :
    nfpFamily f a < c := by
  refine lift_iSup_lt_of_lt_cof ?_ (fun l ↦ ?_)
  · rw [Cardinal.lift_umax, c.lift_id']
    apply (Cardinal.lift_le.2 (mk_list_le_max _)).trans_lt
    rw [Cardinal.lift_max]
    apply max_lt <;> simpa
  · induction l with
    | nil => exact ha
    | cons i l H => exact hf _ _ H

theorem nfpFamily_lt_ord {ι} {f : ι → Ordinal → Ordinal} {c} (hc : ℵ₀ < cof c) (hc' : #ι < cof c)
    (hf : ∀ (i), ∀ b < c, f i b < c) {a} : a < c → nfpFamily.{u, u} f a < c :=
  nfpFamily_lt_ord_lift hc (by rwa [(#ι).lift_id]) hf

theorem nfp_lt_ord {f : Ordinal → Ordinal} {c} (hc : ℵ₀ < cof c) (hf : ∀ i < c, f i < c) {a} :
    a < c → nfp f a < c :=
  nfpFamily_lt_ord_lift hc (by simpa using Cardinal.one_lt_aleph0.trans hc) fun _ => hf

set_option linter.deprecated false in
@[deprecated exists_lsub_cof (since := "2026-03-21")]
theorem exists_blsub_cof (o : Ordinal) :
    ∃ f : ∀ a < (cof o).ord, Ordinal, blsub.{u, u} _ f = o := by
  rcases exists_lsub_cof o with ⟨ι, f, hf, hι⟩
  rcases Cardinal.exists_ord_eq ι with ⟨r, hr, hι'⟩
  rw [← @blsub_eq_lsub' ι r hr] at hf
  rw [← hι, hι']
  exact ⟨_, hf⟩

set_option linter.deprecated false in
@[deprecated le_cof_iff (since := "2026-03-21")]
theorem le_cof_iff_blsub {b : Ordinal} {a : Cardinal} :
    a ≤ cof b ↔ ∀ {o} (f : ∀ a < o, Ordinal), blsub.{u, u} o f = b → a ≤ o.card :=
  le_cof_iff_lsub.trans
    ⟨fun H o f hf => by simpa using H _ hf, fun H ι f hf => by
      rcases Cardinal.exists_ord_eq ι with ⟨r, hr, hι'⟩
      rw [← @blsub_eq_lsub' ι r hr] at hf
      simpa using H _ hf⟩

set_option linter.deprecated false in
@[deprecated cof_lift_iSup_add_one_le (since := "2026-03-22")]
theorem cof_blsub_le_lift {o} (f : ∀ a < o, Ordinal) :
    cof (blsub.{u, v} o f) ≤ Cardinal.lift.{v, u} o.card := by
  rw [← mk_toType o]
  exact cof_lsub_le_lift _

set_option linter.deprecated false in
@[deprecated cof_iSup_add_one_le (since := "2026-03-22")]
theorem cof_blsub_le {o} (f : ∀ a < o, Ordinal) : cof (blsub.{u, u} o f) ≤ o.card := by
  rw [← o.card.lift_id]
  exact cof_blsub_le_lift f

set_option linter.deprecated false in
@[deprecated lift_iSup_add_one_lt_of_lt_cof (since := "2026-03-22")]
theorem blsub_lt_ord_lift {o : Ordinal.{u}} {f : ∀ a < o, Ordinal} {c : Ordinal}
    (ho : Cardinal.lift.{v, u} o.card < c.cof) (hf : ∀ i hi, f i hi < c) : blsub.{u, v} o f < c :=
  lt_of_le_of_ne (blsub_le hf) fun h =>
    ho.not_ge (by simpa [← iSup_ord, hf, h] using cof_blsub_le_lift.{u, v} f)

set_option linter.deprecated false in
@[deprecated iSup_add_one_lt_of_lt_cof (since := "2026-03-22")]
theorem blsub_lt_ord {o : Ordinal} {f : ∀ a < o, Ordinal} {c : Ordinal} (ho : o.card < c.cof)
    (hf : ∀ i hi, f i hi < c) : blsub.{u, u} o f < c :=
  blsub_lt_ord_lift (by rwa [o.card.lift_id]) hf

set_option linter.deprecated false in
@[deprecated lift_iSup_lt_of_lt_cof (since := "2026-03-22")]
theorem cof_bsup_le_lift {o : Ordinal} {f : ∀ a < o, Ordinal} (H : ∀ i h, f i h < bsup.{u, v} o f) :
    cof (bsup.{u, v} o f) ≤ Cardinal.lift.{v, u} o.card := by
  rw [← bsup_eq_blsub_iff_lt_bsup.{u, v}] at H
  rw [H]
  exact cof_blsub_le_lift.{u, v} f

set_option linter.deprecated false in
@[deprecated iSup_lt_of_lt_cof (since := "2026-03-22")]
theorem cof_bsup_le {o : Ordinal} {f : ∀ a < o, Ordinal} :
    (∀ i h, f i h < bsup.{u, u} o f) → cof (bsup.{u, u} o f) ≤ o.card := by
  rw [← o.card.lift_id]
  exact cof_bsup_le_lift

set_option linter.deprecated false in
@[deprecated lift_iSup_lt_of_lt_cof (since := "2026-03-22")]
theorem bsup_lt_ord_lift {o : Ordinal} {f : ∀ a < o, Ordinal} {c : Ordinal}
    (ho : Cardinal.lift.{v, u} o.card < c.cof) (hf : ∀ i hi, f i hi < c) : bsup.{u, v} o f < c :=
  (bsup_le_blsub f).trans_lt (blsub_lt_ord_lift ho hf)

set_option linter.deprecated false in
@[deprecated iSup_lt_of_lt_cof (since := "2026-03-22")]
theorem bsup_lt_ord {o : Ordinal} {f : ∀ a < o, Ordinal} {c : Ordinal} (ho : o.card < c.cof) :
    (∀ i hi, f i hi < c) → bsup.{u, u} o f < c :=
  bsup_lt_ord_lift (by rwa [o.card.lift_id])

/-! ### Cofinality arithmetic -/

@[simp]
theorem cof_add (a : Ordinal) {b : Ordinal} (hb : b ≠ 0) : cof (a + b) = cof b := by
  rcases zero_or_succ_or_isSuccLimit b with (rfl | ⟨c, rfl⟩ | hb)
  · contradiction
  · rw [succ_eq_add_one, ← add_assoc, cof_add_one, cof_add_one]
  · exact cof_map_of_isNormal (isNormal_add_right a) hb

@[simp]
theorem cof_mul {a b : Ordinal} (ha : a ≠ 0) (hb : IsSuccPrelimit b) : cof (a * b) = cof b := by
  by_cases hb' : IsMin b
  · simp [hb'.eq_bot]
  · exact cof_map_of_isNormal (isNormal_mul_right ha.pos) ⟨hb', hb⟩

@[simp]
theorem cof_preOmega {o : Ordinal} (ho : IsSuccPrelimit o) : (preOmega o).cof = o.cof := by
  by_cases h : IsMin o
  · simp [h.eq_bot]
  · exact cof_map_of_isNormal isNormal_preOmega ⟨h, ho⟩

@[simp]
theorem cof_omega {o : Ordinal} (ho : IsSuccLimit o) : (ω_ o).cof = o.cof :=
  cof_map_of_isNormal isNormal_omega ho

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
theorem cof_univ : cof univ.{u, v} = Cardinal.univ.{u, v} := by
  apply (cof_le_card _).antisymm
  simp_rw [univ, ← lift_cof, ← lift_card, Cardinal.lift_le, cof_type, card_type, le_cof_iff,
    ← not_bddAbove_iff_isCofinal]
  exact fun s hs ↦ mk_le_of_injective (enumOrdOrderIso s hs).injective

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
    exact (h'.two_power_lt (card_typein_lt _ hr)).le
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
  rcases exists_ord_eq α with ⟨r, wo, hr⟩
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
    · rw [mk_singleton, one_lt_cof_iff]
      exact isSuccLimit_ord h'.aleph0_le
    · intro a b hab
      simpa [singleton_eq_singleton_iff] using hab

@[deprecated (since := "2026-02-25")]
alias unbounded_of_unbounded_sUnion := isCofinal_of_isCofinal_sUnion
@[deprecated (since := "2026-02-25")]
alias unbounded_of_unbounded_iUnion := isCofinal_of_isCofinal_iUnion

/-! ### Consequences of König's lemma -/

theorem lt_power_cof_ord {c : Cardinal} (hc : ℵ₀ ≤ c) : c < c ^ c.ord.cof := by
  induction c using Cardinal.inductionOn with | mk α
  obtain ⟨_, _, hα⟩ := exists_ord_eq_type_lt α
  have : NoMaxOrder α := by
    rw [← isSuccPrelimit_type_lt_iff, ← hα]
    exact (isSuccLimit_ord hc).isSuccPrelimit
  obtain ⟨s, hs, hs'⟩ := ord_cof_eq α
  rw [hα, cof_type, ← card_ord (Order.cof _), ← hs', card_type, ← prod_const']
  refine (mk_iUnion_le_sum_mk.trans' ?_).trans_lt (sum_lt_prod _ _ fun i ↦ mk_Iio_lt i.1 hα)
  rw [← mk_univ, ← isCofinal_iff_iUnion_Iio_eq_univ.1 hs, iUnion_coe_set]

@[deprecated (since := "2026-03-30")]
alias lt_power_cof := lt_power_cof_ord

theorem lt_cof_ord_power {a b : Cardinal} (ha : ℵ₀ ≤ a) (hb : 1 < b) : a < (b ^ a).ord.cof := by
  apply lt_imp_lt_of_le_imp_le (power_le_power_left <| power_ne_zero a hb.ne_bot)
  rw [← power_mul, mul_eq_self ha]
  exact lt_power_cof_ord (ha.trans <| (cantor' _ hb).le)

@[deprecated (since := "2026-03-30")]
alias lt_cof_power := lt_cof_ord_power

end Cardinal
