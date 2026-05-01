/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn, Violeta Hernández Palacios
-/
module

public import Mathlib.SetTheory.Cardinal.Cofinality
public import Mathlib.SetTheory.Ordinal.FixedPoint

/-!
# Regular cardinals

This file defines regular and inaccessible cardinals.

## Main definitions

* `Cardinal.IsRegular c` means that `c` is a regular cardinal: `ℵ₀ ≤ c ∧ c.ord.cof = c`.
* `Cardinal.IsInaccessible c` means that `c` is strongly inaccessible:
  `ℵ₀ < c ∧ IsRegular c ∧ IsStrongLimit c`.

## TODO

* Define singular cardinals.
-/

@[expose] public section

universe u v

open Function Cardinal Set Order Ordinal

namespace Cardinal
variable {c : Cardinal}

/-! ### Regular cardinals -/

/-- A cardinal is regular if it is infinite and it equals its own cofinality. -/
structure IsRegular (c : Cardinal) : Prop where
  /-- A regular cardinal is infinite. -/
  aleph0_le : ℵ₀ ≤ c
  /-- A cardinal equals its own cofinality. See `IsRegular.cof_eq`. -/
  le_cof_ord : c ≤ c.ord.cof

theorem IsRegular.cof_ord {c : Cardinal} (H : c.IsRegular) : c.ord.cof = c :=
  (cof_ord_le c).antisymm H.2

@[deprecated (since := "2026-03-22")] alias IsRegular.cof_eq := IsRegular.cof_ord

theorem IsRegular.cof_omega_eq {o : Ordinal} (H : (ℵ_ o).IsRegular) : (ω_ o).cof = ℵ_ o := by
  rw [← ord_aleph, H.cof_ord]

theorem IsRegular.pos {c : Cardinal} (H : c.IsRegular) : 0 < c :=
  aleph0_pos.trans_le H.1

theorem IsRegular.nat_lt {c : Cardinal} (H : c.IsRegular) (n : ℕ) : n < c :=
  lt_of_lt_of_le natCast_lt_aleph0 H.aleph0_le

theorem IsRegular.ord_pos {c : Cardinal} (H : c.IsRegular) : 0 < c.ord := by
  rw [Cardinal.lt_ord, card_zero]
  exact H.pos

theorem isRegular_cof {o : Ordinal} (h : IsSuccLimit o) : IsRegular o.cof := by
  refine ⟨?_, (cof_ord_cof o).ge⟩
  rwa [aleph0_le_cof_iff, one_lt_cof_iff]

/-- If `c` is a regular cardinal, then `c.ord.ToType` has a least element. -/
lemma IsRegular.ne_zero {c : Cardinal} (H : c.IsRegular) : c ≠ 0 :=
  H.pos.ne'

theorem isRegular_aleph0 : IsRegular ℵ₀ :=
  ⟨le_rfl, by simp⟩

lemma fact_isRegular_aleph0 : Fact (IsRegular ℵ₀) where
  out := isRegular_aleph0

theorem isRegular_succ {c : Cardinal.{u}} (h : ℵ₀ ≤ c) : IsRegular (succ c) :=
  ⟨h.trans (le_succ c),
    succ_le_of_lt
      (by
        have αe := Cardinal.mk_out (succ c)
        set α := (succ c).out
        rcases exists_ord_eq α with ⟨r, wo, re⟩
        have := isSuccLimit_ord (h.trans (le_succ _))
        rw [← αe, re] at this ⊢
        rcases cof_eq' r this with ⟨S, H, Se⟩
        rw [← Se]
        apply lt_imp_lt_of_le_imp_le fun h => mul_le_mul_left h c
        rw [mul_eq_self h, ← succ_le_iff, ← αe, ← sum_const']
        refine le_trans ?_ (sum_le_sum (fun (x : S) => card (typein r (x : α))) _ fun i => ?_)
        · simp only [card_typein, ← mk_sigma]
          exact
            ⟨Embedding.ofSurjective (fun x => x.2.1) fun a =>
                let ⟨b, h, ab⟩ := H a
                ⟨⟨⟨_, h⟩, _, ab⟩, rfl⟩⟩
        · rw [← lt_succ_iff, ← lt_ord, ← αe, re]
          apply typein_lt_type)⟩

theorem isRegular_aleph_one : IsRegular ℵ₁ := by
  rw [← succ_aleph0]
  exact isRegular_succ le_rfl

@[simp]
theorem cof_omega_one : cof ω₁ = ℵ₁ := by
  simpa using isRegular_aleph_one.cof_omega_eq

/-- A countable supremum of countable ordinals is countable. -/
theorem _root_.Ordinal.iSup_lt_omega_one {α : Type*} [Countable α] {f : α → Ordinal} :
    (∀ i, f i < ω₁) → ⨆ i, f i < ω₁ :=
  Ordinal.lift_iSup_lt_of_lt_cof (by simp)

@[deprecated (since := "2026-03-23")]
alias iSup_sequence_lt_omega_one := Ordinal.iSup_lt_omega_one

@[deprecated (since := "2025-12-22")]
alias iSup_sequence_lt_omega1 := Ordinal.iSup_lt_omega_one

theorem isRegular_preAleph_add_one {o : Ordinal} (h : ω ≤ o) : IsRegular (preAleph (o + 1)) := by
  rw [← succ_preAleph]
  exact isRegular_succ (aleph0_le_preAleph.2 h)

@[deprecated isRegular_preAleph_add_one (since := "2026-03-23")]
theorem isRegular_preAleph_succ {o : Ordinal} (h : ω ≤ o) : IsRegular (preAleph (succ o)) :=
  isRegular_preAleph_add_one h

theorem cof_preOmega_add_one {o : Ordinal} (h : ω ≤ o) :
    (preOmega (o + 1)).cof = preAleph (o + 1) := by
  rw [← ord_preAleph, (isRegular_preAleph_add_one h).cof_ord]

theorem isRegular_aleph_add_one (o : Ordinal) : IsRegular (ℵ_ (o + 1)) := by
  rw [← succ_aleph]
  exact isRegular_succ (aleph0_le_aleph o)

@[deprecated isRegular_aleph_add_one (since := "2026-03-23")]
theorem isRegular_aleph_succ (o : Ordinal) : IsRegular (ℵ_ (succ o)) :=
  isRegular_aleph_add_one o

@[simp]
theorem cof_omega_add_one (o : Ordinal) : (ω_ (o + 1)).cof = ℵ_ (o + 1) :=
  (isRegular_aleph_add_one o).cof_omega_eq

lemma IsRegular.lift {κ : Cardinal.{v}} (h : κ.IsRegular) :
    (Cardinal.lift.{u} κ).IsRegular := by
  obtain ⟨h₁, h₂⟩ := h
  constructor
  · simpa
  · rwa [← Cardinal.lift_ord, ← Ordinal.lift_cof, lift_le]

@[simp]
lemma isRegular_lift_iff {κ : Cardinal.{v}} :
    (Cardinal.lift.{u} κ).IsRegular ↔ κ.IsRegular :=
  ⟨fun ⟨h₁, h₂⟩ ↦ ⟨by simpa using h₁, by simpa [← lift_le.{u, v}]⟩, fun h ↦ h.lift⟩

set_option linter.deprecated false in
@[deprecated lift_iSup_add_one_lt_of_lt_cof (since := "2026-03-22")]
theorem lsub_lt_ord_lift_of_isRegular {ι} {f : ι → Ordinal} {c} (hc : IsRegular c)
    (hι : Cardinal.lift.{v, u} #ι < c) (hf : ∀ i, f i < c.ord) : Ordinal.lsub.{u, v} f < c.ord := by
  apply lift_iSup_add_one_lt_of_lt_cof _ hf
  rwa [lift_umax, c.ord.lift_id', hc.cof_ord]

set_option linter.deprecated false in
@[deprecated iSup_add_one_lt_of_lt_cof (since := "2026-03-22")]
theorem lsub_lt_ord_of_isRegular {ι} {f : ι → Ordinal} {c} (hc : IsRegular c) (hι : #ι < c) :
    (∀ i, f i < c.ord) → Ordinal.lsub f < c.ord :=
  iSup_add_one_lt_of_lt_cof (by rwa [hc.cof_ord])

@[deprecated lift_iSup_lt_of_lt_cof (since := "2026-03-22")]
theorem iSup_lt_ord_lift_of_isRegular {ι} {f : ι → Ordinal} {c} (hc : IsRegular c)
    (hι : Cardinal.lift.{v, u} #ι < c) (hf : ∀ i, f i < c.ord) : iSup f < c.ord := by
  apply Ordinal.lift_iSup_lt_of_lt_cof _ hf
  rwa [lift_umax, Ordinal.lift_id', hc.cof_ord]

@[deprecated iSup_lt_of_lt_cof (since := "2026-03-22")]
theorem iSup_lt_ord_of_isRegular {ι} {f : ι → Ordinal} {c} (hc : IsRegular c) (hι : #ι < c) :
    (∀ i, f i < c.ord) → iSup f < c.ord :=
  Ordinal.iSup_lt_of_lt_cof (by rwa [hc.cof_ord])

set_option linter.deprecated false in
@[deprecated lift_iSup_add_one_lt_of_lt_cof (since := "2026-03-22")]
theorem blsub_lt_ord_lift_of_isRegular {o : Ordinal} {f : ∀ a < o, Ordinal} {c} (hc : IsRegular c)
    (ho : Cardinal.lift.{v, u} o.card < c) :
    (∀ i hi, f i hi < c.ord) → Ordinal.blsub.{u, v} o f < c.ord :=
  blsub_lt_ord_lift (by rwa [hc.cof_ord])

set_option linter.deprecated false in
@[deprecated lift_iSup_add_one_lt_of_lt_cof (since := "2026-03-22")]
theorem blsub_lt_ord_of_isRegular {o : Ordinal} {f : ∀ a < o, Ordinal} {c} (hc : IsRegular c)
    (ho : o.card < c) : (∀ i hi, f i hi < c.ord) → Ordinal.blsub o f < c.ord :=
  blsub_lt_ord (by rwa [hc.cof_ord])

set_option linter.deprecated false in
@[deprecated iSup_lt_ord_lift_of_isRegular (since := "2026-03-22")]
theorem bsup_lt_ord_lift_of_isRegular {o : Ordinal} {f : ∀ a < o, Ordinal} {c} (hc : IsRegular c)
    (hι : Cardinal.lift.{v, u} o.card < c) :
    (∀ i hi, f i hi < c.ord) → Ordinal.bsup.{u, v} o f < c.ord :=
  bsup_lt_ord_lift (by rwa [hc.cof_ord])

set_option linter.deprecated false in
@[deprecated lift_iSup_lt_of_lt_cof (since := "2026-03-22")]
theorem bsup_lt_ord_of_isRegular {o : Ordinal} {f : ∀ a < o, Ordinal} {c} (hc : IsRegular c)
    (hι : o.card < c) : (∀ i hi, f i hi < c.ord) → Ordinal.bsup o f < c.ord :=
  bsup_lt_ord (by rwa [hc.cof_ord])

@[deprecated lift_iSup_lt_of_lt_cof (since := "2026-03-22")]
theorem iSup_lt_lift_of_isRegular {ι} {f : ι → Cardinal} {c} (hc : IsRegular c)
    (hι : Cardinal.lift.{v, u} #ι < c) (hf : ∀ i, f i < c) : iSup f < c := by
  apply lift_iSup_lt_of_lt_cof_ord _ hf
  rwa [lift_umax, c.lift_id', hc.cof_ord]

@[deprecated iSup_lt_of_lt_cof (since := "2026-03-22")]
theorem iSup_lt_of_isRegular {ι} {f : ι → Cardinal} {c} (hc : IsRegular c) (hι : #ι < c) :
    (∀ i, f i < c) → iSup f < c :=
  iSup_lt_of_lt_cof_ord (by rwa [hc.cof_ord])

theorem sum_lt_lift_of_isRegular {ι : Type u} {f : ι → Cardinal} {c : Cardinal} (hc : IsRegular c)
    (hι : Cardinal.lift.{v, u} #ι < c) (hf : ∀ i, f i < c) : sum f < c := by
  apply (sum_le_lift_mk_mul_iSup _).trans_lt <|
    mul_lt_of_lt hc.1 hι (lift_iSup_lt_of_lt_cof_ord _ hf)
  rwa [lift_umax, c.lift_id', hc.cof_ord]

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
  apply Cardinal.mul_lt_of_lt hc.aleph0_le (mk_range_le.trans_lt hι)
  apply Cardinal.iSup_lt_of_lt_cof_ord (mk_range_le.trans_lt _)
  · simpa
  · rwa [hc.cof_ord]

theorem card_lt_of_card_biUnion_lt {α β : Type u} {s : Set α} {t : ∀ a ∈ s, Set β} {c : Cardinal}
    (h : #(⋃ a ∈ s, t a ‹_›) < c) (a : α) (ha : a ∈ s) : #(t a ha) < c := by
  rw [biUnion_eq_iUnion] at h
  have := card_lt_of_card_iUnion_lt h
  simp_all only [iUnion_coe_set, Subtype.forall]

theorem card_biUnion_lt_iff_forall_of_isRegular {α β : Type u} {s : Set α} {t : ∀ a ∈ s, Set β}
    {c : Cardinal} (hc : c.IsRegular) (hs : #s < c) :
    #(⋃ a ∈ s, t a ‹_›) < c ↔ ∀ a (ha : a ∈ s), #(t a ha) < c := by
  rw [biUnion_eq_iUnion, card_iUnion_lt_iff_forall_of_isRegular hc hs, SetCoe.forall']

theorem nfpFamily_lt_ord_lift_of_isRegular {ι} {f : ι → Ordinal → Ordinal} {c} (hc : IsRegular c)
    (hι : Cardinal.lift.{v, u} #ι < c) (hc' : c ≠ ℵ₀) (hf : ∀ (i), ∀ b < c.ord, f i b < c.ord) {a}
    (ha : a < c.ord) : nfpFamily f a < c.ord := by
  apply nfpFamily_lt_ord_lift _ _ hf ha <;> rw [hc.cof_ord]
  · exact lt_of_le_of_ne hc.1 hc'.symm
  · exact hι

theorem nfpFamily_lt_ord_of_isRegular {ι} {f : ι → Ordinal → Ordinal} {c} (hc : IsRegular c)
    (hι : #ι < c) (hc' : c ≠ ℵ₀) {a} (hf : ∀ (i), ∀ b < c.ord, f i b < c.ord) :
    a < c.ord → nfpFamily.{u, u} f a < c.ord :=
  nfpFamily_lt_ord_lift_of_isRegular hc (by rwa [lift_id]) hc' hf

theorem nfp_lt_ord_of_isRegular {f : Ordinal → Ordinal} {c} (hc : IsRegular c) (hc' : c ≠ ℵ₀)
    (hf : ∀ i < c.ord, f i < c.ord) {a} : a < c.ord → nfp f a < c.ord :=
  nfp_lt_ord (by rw [hc.cof_ord]; exact lt_of_le_of_ne hc.1 hc'.symm) hf

theorem derivFamily_lt_ord_lift {ι : Type u} {f : ι → Ordinal → Ordinal} {c} (hc : IsRegular c)
    (hι : lift.{v} #ι < c) (hc' : c ≠ ℵ₀) (hf : ∀ i, ∀ b < c.ord, f i b < c.ord) {a} :
    a < c.ord → derivFamily f a < c.ord := by
  have hω : ℵ₀ < c.ord.cof := by
    rw [hc.cof_ord]
    exact lt_of_le_of_ne hc.1 hc'.symm
  induction a using limitRecOn with
  | zero =>
    rw [derivFamily_zero]
    exact nfpFamily_lt_ord_lift hω (by rwa [hc.cof_ord]) hf
  | succ b hb =>
    intro hb'
    rw [derivFamily_succ]
    exact
      nfpFamily_lt_ord_lift hω (by rwa [hc.cof_ord]) hf
        ((isSuccLimit_ord hc.1).succ_lt (hb ((lt_succ b).trans hb')))
  | limit b hb H =>
    intro hb'
    rw [derivFamily_limit f hb]
    apply Ordinal.lift_iSup_lt_of_lt_cof
    · rwa [← lift_cof, hc.cof_ord, mk_Iio_ordinal, lift_lift, lift_lt, ← lt_ord]
    · exact fun i ↦ H i.1 i.2 <| i.2.trans hb'

theorem derivFamily_lt_ord {ι} {f : ι → Ordinal → Ordinal} {c} (hc : IsRegular c) (hι : #ι < c)
    (hc' : c ≠ ℵ₀) (hf : ∀ (i), ∀ b < c.ord, f i b < c.ord) {a} :
    a < c.ord → derivFamily.{u, u} f a < c.ord :=
  derivFamily_lt_ord_lift hc (by rwa [lift_id]) hc' hf

theorem deriv_lt_ord {f : Ordinal.{u} → Ordinal} {c} (hc : IsRegular c) (hc' : c ≠ ℵ₀)
    (hf : ∀ i < c.ord, f i < c.ord) {a} : a < c.ord → deriv f a < c.ord :=
  derivFamily_lt_ord_lift hc
    (by simpa using Cardinal.one_lt_aleph0.trans (lt_of_le_of_ne hc.1 hc'.symm)) hc' fun _ => hf

/-! ### Inaccessible cardinals -/

/-- A cardinal is inaccessible if it is an uncountable regular strong limit cardinal. -/
structure IsInaccessible (c : Cardinal) : Prop where
  /-- An inaccessible cardinal is uncountable. -/
  aleph0_lt : ℵ₀ < c
  /-- An inaccessible cardinal is equal to its own cofinality, see `IsInaccessible.isRegular`. -/
  le_cof_ord : c ≤ c.ord.cof
  /-- An inaccessible cardinal is a strong limit, see `IsInaccessible.isStrongLimit`. -/
  two_power_lt ⦃x⦄ : x < c → 2 ^ x < c

theorem IsInaccessible.nat_lt {c : Cardinal} (h : IsInaccessible c) (n : ℕ) : n < c :=
  natCast_lt_aleph0.trans h.1

theorem IsInaccessible.pos {c : Cardinal} (h : IsInaccessible c) : 0 < c :=
  aleph0_pos.trans h.1

theorem IsInaccessible.ne_zero {c : Cardinal} (h : IsInaccessible c) : c ≠ 0 :=
  h.pos.ne'

theorem IsInaccessible.isRegular {c : Cardinal} (h : IsInaccessible c) : IsRegular c :=
  ⟨h.aleph0_lt.le, h.le_cof_ord⟩

theorem IsInaccessible.isStrongLimit {c : Cardinal} (h : IsInaccessible c) : IsStrongLimit c :=
  ⟨h.ne_zero, h.two_power_lt⟩

theorem IsInaccessible.isSuccLimit {c : Cardinal} (h : IsInaccessible c) : IsSuccLimit c :=
  h.isStrongLimit.isSuccLimit

theorem isInaccessible_def {c : Cardinal} :
    IsInaccessible c ↔ ℵ₀ < c ∧ IsRegular c ∧ IsStrongLimit c where
  mp h := ⟨h.aleph0_lt, h.isRegular, h.isStrongLimit⟩
  mpr := fun ⟨h₁, h₂, h₃⟩ ↦ ⟨h₁, h₂.2, h₃.two_power_lt⟩

/-- Lean's foundations prove the existence of `v` inaccessibles in universe `v`. -/
theorem IsInaccessible.univ : IsInaccessible univ.{u, v} :=
  ⟨aleph0_lt_univ, by simp, IsStrongLimit.univ.two_power_lt⟩

theorem IsInaccessible.preBeth_ord (hc : IsInaccessible c) : preBeth c.ord = c := by
  apply (preBeth_strictMono.comp ord_strictMono).le_apply.antisymm'
  apply (isNormal_preBeth.le_iff_forall_le (isSuccLimit_ord hc.aleph0_lt.le)).2
  refine fun a ha ↦ le_of_lt ?_
  induction a using WellFoundedLT.induction with | ind a IH
  rw [preBeth]
  apply lift_iSup_lt_of_lt_cof_ord _ _
  · rwa [mk_Iio_ordinal, lift_lift, hc.isRegular.lift.cof_ord, lift_lt, ← lt_ord]
  · rintro ⟨b, hb⟩
    exact hc.isStrongLimit.two_power_lt <| IH _ hb (hb.trans ha)

theorem IsInaccessible.beth_ord (hc : IsInaccessible c) : ℶ_ c.ord = c := by
  rw [← preBeth_of_omega0_sq_le (le_of_lt _), hc.preBeth_ord]
  rw [lt_ord, pow_two, card_mul, card_omega0, aleph0_mul_aleph0]
  exact hc.aleph0_lt

theorem IsInaccessible.preAleph_ord (hc : IsInaccessible c) : preAleph c.ord = c :=
  ((preAleph_le_preBeth _).trans hc.preBeth_ord.le).antisymm
    (preAleph.strictMono.comp ord_strictMono).le_apply

theorem IsInaccessible.aleph_ord (hc : IsInaccessible c) : ℵ_ c.ord = c :=
  ((aleph_le_beth _).trans hc.beth_ord.le).antisymm (aleph.strictMono.comp ord_strictMono).le_apply

theorem IsInaccessible.preOmega_ord (hc : IsInaccessible c) : preOmega c.ord = c.ord := by
  rw [← ord_preAleph, hc.preAleph_ord]

theorem IsInaccessible.omega_ord (hc : IsInaccessible c) : ω_ c.ord = c.ord := by
  rw [← ord_aleph, hc.aleph_ord]

@[simp]
theorem preBeth_univ : preBeth Ordinal.univ.{u, v} = univ.{u, v} := by
  simpa using IsInaccessible.univ.preBeth_ord

@[simp]
theorem beth_univ : ℶ_ Ordinal.univ.{u, v} = univ.{u, v} := by
  simpa using IsInaccessible.univ.beth_ord

@[simp]
theorem preAleph_univ : preAleph Ordinal.univ.{u, v} = univ.{u, v} := by
  simpa using IsInaccessible.univ.preAleph_ord

@[simp]
theorem aleph_univ : ℵ_ Ordinal.univ.{u, v} = univ.{u, v} := by
  simpa using IsInaccessible.univ.aleph_ord

@[simp]
theorem _root_.Ordinal.preOmega_univ : preOmega Ordinal.univ.{u, v} = Ordinal.univ.{u, v} := by
  simpa using IsInaccessible.univ.preOmega_ord

@[simp]
theorem _root_.Ordinal.omega_univ : ω_ Ordinal.univ.{u, v} = Ordinal.univ.{u, v} := by
  simpa using IsInaccessible.univ.omega_ord

end Cardinal
