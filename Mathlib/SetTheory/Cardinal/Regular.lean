/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn, Violeta Hernández Palacios
-/
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.SetTheory.Ordinal.FixedPoint

/-!
# Regular cardinals

This file defines regular and inaccessible cardinals.

## Main definitions

* `Cardinal.IsRegular c` means that `c` is a regular cardinal: `ℵ₀ ≤ c ∧ c.ord.cof = c`.
* `Cardinal.IsInaccessible c` means that `c` is strongly inaccessible:
  `ℵ₀ < c ∧ IsRegular c ∧ IsStrongLimit c`.

## TODO

* Generalize the universes in the lemmas about `iSup`, by taking a `Small` assumption when necessary
  instead.
* Prove more theorems on inaccessible cardinals.
* Define singular cardinals.
-/

universe u v

open Function Cardinal Set Order Ordinal

namespace Cardinal

/-! ### Regular cardinals -/

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

theorem isRegular_cof {o : Ordinal} (h : IsSuccLimit o) : IsRegular o.cof :=
  ⟨aleph0_le_cof.2 h, (cof_cof o).ge⟩

/-- If `c` is a regular cardinal, then `c.ord.toType` has a least element. -/
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
        rcases ord_eq α with ⟨r, wo, re⟩
        have := isSuccLimit_ord (h.trans (le_succ _))
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

theorem isRegular_aleph_succ (o : Ordinal) : IsRegular (ℵ_ (succ o)) := by
  rw [aleph_succ]
  exact isRegular_succ (aleph0_le_aleph o)

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

theorem lsub_lt_ord_lift_of_isRegular {ι} {f : ι → Ordinal} {c} (hc : IsRegular c)
    (hι : Cardinal.lift.{v, u} #ι < c) : (∀ i, f i < c.ord) → Ordinal.lsub.{u, v} f < c.ord :=
  lsub_lt_ord_lift (by rwa [hc.cof_eq])

theorem lsub_lt_ord_of_isRegular {ι} {f : ι → Ordinal} {c} (hc : IsRegular c) (hι : #ι < c) :
    (∀ i, f i < c.ord) → Ordinal.lsub f < c.ord :=
  lsub_lt_ord (by rwa [hc.cof_eq])

theorem iSup_lt_ord_lift_of_isRegular {ι} {f : ι → Ordinal} {c} (hc : IsRegular c)
    (hι : Cardinal.lift.{v, u} #ι < c) : (∀ i, f i < c.ord) → iSup f < c.ord :=
  iSup_lt_ord_lift (by rwa [hc.cof_eq])

theorem iSup_lt_ord_of_isRegular {ι} {f : ι → Ordinal} {c} (hc : IsRegular c) (hι : #ι < c) :
    (∀ i, f i < c.ord) → iSup f < c.ord :=
  iSup_lt_ord (by rwa [hc.cof_eq])

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
  (sum_le_lift_mk_mul_iSup _).trans_lt <| mul_lt_of_lt hc.1 hι (iSup_lt_lift_of_isRegular hc hι hf)

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
  simp_all only [iUnion_coe_set, Subtype.forall]

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

theorem nfp_lt_ord_of_isRegular {f : Ordinal → Ordinal} {c} (hc : IsRegular c) (hc' : c ≠ ℵ₀)
    (hf : ∀ i < c.ord, f i < c.ord) {a} : a < c.ord → nfp f a < c.ord :=
  nfp_lt_ord (by rw [hc.cof_eq]; exact lt_of_le_of_ne hc.1 hc'.symm) hf

theorem derivFamily_lt_ord_lift {ι : Type u} {f : ι → Ordinal → Ordinal} {c} (hc : IsRegular c)
    (hι : lift.{v} #ι < c) (hc' : c ≠ ℵ₀) (hf : ∀ i, ∀ b < c.ord, f i b < c.ord) {a} :
    a < c.ord → derivFamily f a < c.ord := by
  have hω : ℵ₀ < c.ord.cof := by
    rw [hc.cof_eq]
    exact lt_of_le_of_ne hc.1 hc'.symm
  induction a using limitRecOn with
  | zero =>
    rw [derivFamily_zero]
    exact nfpFamily_lt_ord_lift hω (by rwa [hc.cof_eq]) hf
  | succ b hb =>
    intro hb'
    rw [derivFamily_succ]
    exact
      nfpFamily_lt_ord_lift hω (by rwa [hc.cof_eq]) hf
        ((isSuccLimit_ord hc.1).succ_lt (hb ((lt_succ b).trans hb')))
  | limit b hb H =>
    intro hb'
    -- TODO: generalize the universes of the lemmas in this file so we don't have to rely on bsup
    have : ⨆ a : Iio b, _ = _ := iSup_Iio_eq_bsup (f := fun x (_ : x < b) ↦ derivFamily f x)
    rw [derivFamily_limit f hb, this]
    exact
      bsup_lt_ord_of_isRegular.{u, v} hc (ord_lt_ord.1 ((ord_card_le b).trans_lt hb')) fun o' ho' =>
        H o' ho' (ho'.trans hb')

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
def IsInaccessible (c : Cardinal) : Prop :=
  ℵ₀ < c ∧ c ≤ c.ord.cof ∧ ∀ x < c, 2 ^ x < c

@[deprecated "use the default constructor for `IsInaccessible`" (since := "2025-07-01")]
theorem IsInaccessible.mk {c} (h₁ : ℵ₀ < c) (h₂ : c ≤ c.ord.cof) (h₃ : ∀ x < c, (2 ^ x) < c) :
    IsInaccessible c :=
  ⟨h₁, h₂, h₃⟩

theorem IsInaccessible.aleph0_lt {c : Cardinal} (h : IsInaccessible c) : ℵ₀ < c :=
  h.1

theorem IsInaccessible.nat_lt {c : Cardinal} (h : IsInaccessible c) (n : ℕ) : n < c :=
  (nat_lt_aleph0 n).trans h.1

theorem IsInaccessible.pos {c : Cardinal} (h : IsInaccessible c) : 0 < c :=
  aleph0_pos.trans h.1

theorem IsInaccessible.ne_zero {c : Cardinal} (h : IsInaccessible c) : c ≠ 0 :=
  h.pos.ne'

theorem IsInaccessible.isRegular {c : Cardinal} (h : IsInaccessible c) : IsRegular c :=
  ⟨h.aleph0_lt.le, h.2.1⟩

theorem IsInaccessible.isStrongLimit {c : Cardinal} (h : IsInaccessible c) : IsStrongLimit c :=
  ⟨h.ne_zero, h.2.2⟩

theorem isInaccessible_def {c : Cardinal} :
    IsInaccessible c ↔ ℵ₀ < c ∧ IsRegular c ∧ IsStrongLimit c where
  mp h := ⟨h.aleph0_lt, h.isRegular, h.isStrongLimit⟩
  mpr := fun ⟨h₁, h₂, h₃⟩ ↦ ⟨h₁, h₂.2, h₃.two_power_lt⟩

@[deprecated (since := "2025-08-20")] alias isInaccesible_def := isInaccessible_def

-- Lean's foundations prove the existence of ℵ₀ many inaccessible cardinals
theorem IsInaccessible.univ : IsInaccessible univ.{u, v} :=
  ⟨aleph0_lt_univ, by simp, IsStrongLimit.univ.two_power_lt⟩

@[deprecated IsInaccessible.univ (since := "2025-07-01")]
alias univ_inaccessible := IsInaccessible.univ

-- TODO: prove that `IsInaccessible o.card` implies `IsInaccessible (ℵ_ o)` and
-- `IsInaccessible (ℶ_ o)`

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
