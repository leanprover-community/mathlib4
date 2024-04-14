/-
Copyright (c) 2023 Kim Liesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Liesinger, Yaël Dillies
-/
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Order.Directed

/-!
# Monotone functions on intervals

This file shows many variants of the fact that a monotone function `f` sends an interval with
endpoints `a` and `b` to the interval with endpoints `f a` and `f b`.
-/

variable {α β : Type*} {f : α → β}

open Set

section Preorder
variable [Preorder α] [Preorder β] {a b : α}

lemma MonotoneOn.mapsTo_Ici (h : MonotoneOn f (Ici a)) : MapsTo f (Ici a) (Ici (f a)) :=
  fun _ _ ↦ by aesop

lemma MonotoneOn.mapsTo_Iic (h : MonotoneOn f (Iic b)) : MapsTo f (Iic b) (Iic (f b)) :=
  fun _ _ ↦ by aesop

lemma MonotoneOn.mapsTo_Icc (h : MonotoneOn f (Icc a b)) : MapsTo f (Icc a b) (Icc (f a) (f b)) :=
  fun _c hc ↦
    ⟨h (left_mem_Icc.2 <| hc.1.trans hc.2) hc hc.1, h hc (right_mem_Icc.2 <| hc.1.trans hc.2) hc.2⟩

lemma AntitoneOn.mapsTo_Ici (h : AntitoneOn f (Ici a)) : MapsTo f (Ici a) (Iic (f a)) :=
  fun _ _ ↦ by aesop

lemma AntitoneOn.mapsTo_Iic (h : AntitoneOn f (Iic b)) : MapsTo f (Iic b) (Ici (f b)) :=
  fun _ _ ↦ by aesop

lemma AntitoneOn.mapsTo_Icc (h : AntitoneOn f (Icc a b)) : MapsTo f (Icc a b) (Icc (f b) (f a)) :=
  fun _c hc ↦
    ⟨h hc (right_mem_Icc.2 <| hc.1.trans hc.2) hc.2, h (left_mem_Icc.2 <| hc.1.trans hc.2) hc hc.1⟩

lemma StrictMonoOn.mapsTo_Ioi (h : StrictMonoOn f (Ici a)) : MapsTo f (Ioi a) (Ioi (f a)) :=
  fun _c hc ↦ h le_rfl hc.le hc

lemma StrictMonoOn.mapsTo_Iio (h : StrictMonoOn f (Iic b)) : MapsTo f (Iio b) (Iio (f b)) :=
  fun _c hc ↦ h hc.le le_rfl hc

lemma StrictMonoOn.mapsTo_Ioo (h : StrictMonoOn f (Icc a b)) :
    MapsTo f (Ioo a b) (Ioo (f a) (f b)) :=
  fun _c hc ↦
    ⟨h (left_mem_Icc.2 (hc.1.trans hc.2).le) (Ioo_subset_Icc_self hc) hc.1,
     h (Ioo_subset_Icc_self hc) (right_mem_Icc.2 (hc.1.trans hc.2).le) hc.2⟩

lemma StrictAntiOn.mapsTo_Ioi (h : StrictAntiOn f (Ici a)) : MapsTo f (Ioi a) (Iio (f a)) :=
  fun _c hc ↦ h le_rfl hc.le hc

lemma StrictAntiOn.mapsTo_Iio (h : StrictAntiOn f (Iic b)) : MapsTo f (Iio b) (Ioi (f b)) :=
  fun _c hc ↦ h hc.le le_rfl hc

lemma StrictAntiOn.mapsTo_Ioo (h : StrictAntiOn f (Icc a b)) :
    MapsTo f (Ioo a b) (Ioo (f b) (f a)) :=
  fun _c hc ↦
    ⟨h (Ioo_subset_Icc_self hc) (right_mem_Icc.2 (hc.1.trans hc.2).le) hc.2,
     h (left_mem_Icc.2 (hc.1.trans hc.2).le) (Ioo_subset_Icc_self hc) hc.1⟩

lemma Monotone.mapsTo_Ici (h : Monotone f) : MapsTo f (Ici a) (Ici (f a)) :=
  (h.monotoneOn _).mapsTo_Ici

lemma Monotone.mapsTo_Iic (h : Monotone f) : MapsTo f (Iic b) (Iic (f b)) :=
  (h.monotoneOn _).mapsTo_Iic

lemma Monotone.mapsTo_Icc (h : Monotone f) : MapsTo f (Icc a b) (Icc (f a) (f b)) :=
  (h.monotoneOn _).mapsTo_Icc

lemma Antitone.mapsTo_Ici (h : Antitone f) : MapsTo f (Ici a) (Iic (f a)) :=
  (h.antitoneOn _).mapsTo_Ici

lemma Antitone.mapsTo_Iic (h : Antitone f) : MapsTo f (Iic b) (Ici (f b)) :=
  (h.antitoneOn _).mapsTo_Iic

lemma Antitone.mapsTo_Icc (h : Antitone f) : MapsTo f (Icc a b) (Icc (f b) (f a)) :=
  (h.antitoneOn _).mapsTo_Icc

lemma StrictMono.mapsTo_Ioi (h : StrictMono f) : MapsTo f (Ioi a) (Ioi (f a)) :=
  (h.strictMonoOn _).mapsTo_Ioi

lemma StrictMono.mapsTo_Iio (h : StrictMono f) : MapsTo f (Iio b) (Iio (f b)) :=
  (h.strictMonoOn _).mapsTo_Iio

lemma StrictMono.mapsTo_Ioo (h : StrictMono f) : MapsTo f (Ioo a b) (Ioo (f a) (f b)) :=
  (h.strictMonoOn _).mapsTo_Ioo

lemma StrictAnti.mapsTo_Ioi (h : StrictAnti f) : MapsTo f (Ioi a) (Iio (f a)) :=
  (h.strictAntiOn _).mapsTo_Ioi

lemma StrictAnti.mapsTo_Iio (h : StrictAnti f) : MapsTo f (Iio b) (Ioi (f b)) :=
  (h.strictAntiOn _).mapsTo_Iio

lemma StrictAnti.mapsTo_Ioo (h : StrictAnti f) : MapsTo f (Ioo a b) (Ioo (f b) (f a)) :=
  (h.strictAntiOn _).mapsTo_Ioo

lemma MonotoneOn.image_Ici_subset (h : MonotoneOn f (Ici a)) : f '' Ici a ⊆ Ici (f a) :=
  h.mapsTo_Ici.image_subset

lemma MonotoneOn.image_Iic_subset (h : MonotoneOn f (Iic b)) : f '' Iic b ⊆ Iic (f b) :=
  h.mapsTo_Iic.image_subset

lemma MonotoneOn.image_Icc_subset (h : MonotoneOn f (Icc a b)) : f '' Icc a b ⊆ Icc (f a) (f b) :=
  h.mapsTo_Icc.image_subset
#align monotone_on.image_Icc_subset MonotoneOn.image_Icc_subset

lemma AntitoneOn.image_Ici_subset (h : AntitoneOn f (Ici a)) : f '' Ici a ⊆ Iic (f a) :=
  h.mapsTo_Ici.image_subset

lemma AntitoneOn.image_Iic_subset (h : AntitoneOn f (Iic b)) : f '' Iic b ⊆ Ici (f b) :=
  h.mapsTo_Iic.image_subset

lemma AntitoneOn.image_Icc_subset (h : AntitoneOn f (Icc a b)) : f '' Icc a b ⊆ Icc (f b) (f a) :=
  h.mapsTo_Icc.image_subset
#align antitone_on.image_Icc_subset AntitoneOn.image_Icc_subset

lemma StrictMonoOn.image_Ioi_subset (h : StrictMonoOn f (Ici a)) : f '' Ioi a ⊆ Ioi (f a) :=
  h.mapsTo_Ioi.image_subset

lemma StrictMonoOn.image_Iio_subset (h : StrictMonoOn f (Iic b)) : f '' Iio b ⊆ Iio (f b) :=
  h.mapsTo_Iio.image_subset

lemma StrictMonoOn.image_Ioo_subset (h : StrictMonoOn f (Icc a b)) :
    f '' Ioo a b ⊆ Ioo (f a) (f b) := h.mapsTo_Ioo.image_subset

lemma StrictAntiOn.image_Ioi_subset (h : StrictAntiOn f (Ici a)) : f '' Ioi a ⊆ Iio (f a) :=
  h.mapsTo_Ioi.image_subset

lemma StrictAntiOn.image_Iio_subset (h : StrictAntiOn f (Iic b)) : f '' Iio b ⊆ Ioi (f b) :=
  h.mapsTo_Iio.image_subset

lemma StrictAntiOn.image_Ioo_subset (h : StrictAntiOn f (Icc a b)) :
    f '' Ioo a b ⊆ Ioo (f b) (f a) := h.mapsTo_Ioo.image_subset

lemma Monotone.image_Ici_subset (h : Monotone f) : f '' Ici a ⊆ Ici (f a) :=
  (h.monotoneOn _).image_Ici_subset

lemma Monotone.image_Iic_subset (h : Monotone f) : f '' Iic b ⊆ Iic (f b) :=
  (h.monotoneOn _).image_Iic_subset

lemma Monotone.image_Icc_subset (h : Monotone f) : f '' Icc a b ⊆ Icc (f a) (f b) :=
  (h.monotoneOn _).image_Icc_subset
#align monotone.image_Icc_subset Monotone.image_Icc_subset

lemma Antitone.image_Ici_subset (h : Antitone f) : f '' Ici a ⊆ Iic (f a) :=
  (h.antitoneOn _).image_Ici_subset

lemma Antitone.image_Iic_subset (h : Antitone f) : f '' Iic b ⊆ Ici (f b) :=
  (h.antitoneOn _).image_Iic_subset

lemma Antitone.image_Icc_subset (h : Antitone f) : f '' Icc a b ⊆ Icc (f b) (f a) :=
  (h.antitoneOn _).image_Icc_subset
#align antitone.image_Icc_subset Antitone.image_Icc_subset

lemma StrictMono.image_Ioi_subset (h : StrictMono f) : f '' Ioi a ⊆ Ioi (f a) :=
  (h.strictMonoOn _).image_Ioi_subset

lemma StrictMono.image_Iio_subset (h : StrictMono f) : f '' Iio b ⊆ Iio (f b) :=
  (h.strictMonoOn _).image_Iio_subset

lemma StrictMono.image_Ioo_subset (h : StrictMono f) : f '' Ioo a b ⊆ Ioo (f a) (f b) :=
  (h.strictMonoOn _).image_Ioo_subset

lemma StrictAnti.image_Ioi_subset (h : StrictAnti f) : f '' Ioi a ⊆ Iio (f a) :=
  (h.strictAntiOn _).image_Ioi_subset

lemma StrictAnti.image_Iio_subset (h : StrictAnti f) : f '' Iio b ⊆ Ioi (f b) :=
  (h.strictAntiOn _).image_Iio_subset

lemma StrictAnti.image_Ioo_subset (h : StrictAnti f) : f '' Ioo a b ⊆ Ioo (f b) (f a) :=
  (h.strictAntiOn _).image_Ioo_subset

end Preorder

section PartialOrder
variable [PartialOrder α] [Preorder β] {a b : α}

lemma StrictMonoOn.mapsTo_Ico (h : StrictMonoOn f (Icc a b)) :
    MapsTo f (Ico a b) (Ico (f a) (f b)) :=
  fun _c hc ↦ ⟨h.monotoneOn (left_mem_Icc.2 <| hc.1.trans hc.2.le) (Ico_subset_Icc_self hc) hc.1,
    h (Ico_subset_Icc_self hc) (right_mem_Icc.2 <| hc.1.trans hc.2.le) hc.2⟩

lemma StrictMonoOn.mapsTo_Ioc (h : StrictMonoOn f (Icc a b)) :
    MapsTo f (Ioc a b) (Ioc (f a) (f b)) :=
  fun _c hc ↦ ⟨h (left_mem_Icc.2 <| hc.1.le.trans hc.2) (Ioc_subset_Icc_self hc) hc.1,
    h.monotoneOn (Ioc_subset_Icc_self hc) (right_mem_Icc.2 <| hc.1.le.trans hc.2) hc.2⟩

lemma StrictAntiOn.mapsTo_Ico (h : StrictAntiOn f (Icc a b)) :
    MapsTo f (Ico a b) (Ioc (f b) (f a)) :=
  fun _c hc ↦ ⟨h (Ico_subset_Icc_self hc) (right_mem_Icc.2 <| hc.1.trans hc.2.le) hc.2,
    h.antitoneOn (left_mem_Icc.2 <| hc.1.trans hc.2.le) (Ico_subset_Icc_self hc) hc.1⟩

lemma StrictAntiOn.mapsTo_Ioc (h : StrictAntiOn f (Icc a b)) :
    MapsTo f (Ioc a b) (Ico (f b) (f a)) :=
  fun _c hc ↦ ⟨h.antitoneOn (Ioc_subset_Icc_self hc) (right_mem_Icc.2 <| hc.1.le.trans hc.2) hc.2,
    h (left_mem_Icc.2 <| hc.1.le.trans hc.2) (Ioc_subset_Icc_self hc) hc.1⟩

lemma StrictMono.mapsTo_Ico (h : StrictMono f) : MapsTo f (Ico a b) (Ico (f a) (f b)) :=
  (h.strictMonoOn _).mapsTo_Ico

lemma StrictMono.mapsTo_Ioc (h : StrictMono f) : MapsTo f (Ioc a b) (Ioc (f a) (f b)) :=
  (h.strictMonoOn _).mapsTo_Ioc

lemma StrictAnti.mapsTo_Ico (h : StrictAnti f) : MapsTo f (Ico a b) (Ioc (f b) (f a)) :=
  (h.strictAntiOn _).mapsTo_Ico

lemma StrictAnti.mapsTo_Ioc (h : StrictAnti f) : MapsTo f (Ioc a b) (Ico (f b) (f a)) :=
  (h.strictAntiOn _).mapsTo_Ioc

lemma StrictMonoOn.image_Ico_subset (h : StrictMonoOn f (Icc a b)) :
    f '' Ico a b ⊆ Ico (f a) (f b) := h.mapsTo_Ico.image_subset

lemma StrictMonoOn.image_Ioc_subset (h : StrictMonoOn f (Icc a b)) :
    f '' Ioc a b ⊆ Ioc (f a) (f b) :=
  h.mapsTo_Ioc.image_subset

lemma StrictAntiOn.image_Ico_subset (h : StrictAntiOn f (Icc a b)) :
    f '' Ico a b ⊆ Ioc (f b) (f a) := h.mapsTo_Ico.image_subset

lemma StrictAntiOn.image_Ioc_subset (h : StrictAntiOn f (Icc a b)) :
    f '' Ioc a b ⊆ Ico (f b) (f a) := h.mapsTo_Ioc.image_subset

lemma StrictMono.image_Ico_subset (h : StrictMono f) : f '' Ico a b ⊆ Ico (f a) (f b) :=
  (h.strictMonoOn _).image_Ico_subset

lemma StrictMono.image_Ioc_subset (h : StrictMono f) : f '' Ioc a b ⊆ Ioc (f a) (f b) :=
  (h.strictMonoOn _).image_Ioc_subset

lemma StrictAnti.image_Ico_subset (h : StrictAnti f) : f '' Ico a b ⊆ Ioc (f b) (f a) :=
  (h.strictAntiOn _).image_Ico_subset

lemma StrictAnti.image_Ioc_subset (h : StrictAnti f) : f '' Ioc a b ⊆ Ico (f b) (f a) :=
  (h.strictAntiOn _).image_Ioc_subset

end PartialOrder

namespace Set

variable [Preorder α] {p : α → Prop}

@[simp] lemma preimage_subtype_val_Ici (a : {x // p x}) : (↑) ⁻¹' (Ici a.1) = Ici a := rfl
@[simp] lemma preimage_subtype_val_Iic (a : {x // p x}) : (↑) ⁻¹' (Iic a.1) = Iic a := rfl
@[simp] lemma preimage_subtype_val_Ioi (a : {x // p x}) : (↑) ⁻¹' (Ioi a.1) = Ioi a := rfl
@[simp] lemma preimage_subtype_val_Iio (a : {x // p x}) : (↑) ⁻¹' (Iio a.1) = Iio a := rfl
@[simp] lemma preimage_subtype_val_Icc (a b : {x // p x}) : (↑) ⁻¹' (Icc a.1 b) = Icc a b := rfl
@[simp] lemma preimage_subtype_val_Ico (a b : {x // p x}) : (↑) ⁻¹' (Ico a.1 b) = Ico a b := rfl
@[simp] lemma preimage_subtype_val_Ioc (a b : {x // p x}) : (↑) ⁻¹' (Ioc a.1 b) = Ioc a b := rfl
@[simp] lemma preimage_subtype_val_Ioo (a b : {x // p x}) : (↑) ⁻¹' (Ioo a.1 b) = Ioo a b := rfl

theorem image_subtype_val_Icc_subset (a b : {x // p x}) :
    Subtype.val '' Icc a b ⊆ Icc a.val b.val :=
  image_subset_iff.mpr fun _ m => m

theorem image_subtype_val_Ico_subset (a b : {x // p x}) :
    Subtype.val '' Ico a b ⊆ Ico a.val b.val :=
  image_subset_iff.mpr fun _ m => m

theorem image_subtype_val_Ioc_subset (a b : {x // p x}) :
    Subtype.val '' Ioc a b ⊆ Ioc a.val b.val :=
  image_subset_iff.mpr fun _ m => m

theorem image_subtype_val_Ioo_subset (a b : {x // p x}) :
    Subtype.val '' Ioo a b ⊆ Ioo a.val b.val :=
  image_subset_iff.mpr fun _ m => m

theorem image_subtype_val_Iic_subset (a : {x // p x}) :
    Subtype.val '' Iic a ⊆ Iic a.val :=
  image_subset_iff.mpr fun _ m => m

theorem image_subtype_val_Iio_subset (a : {x // p x}) :
    Subtype.val '' Iio a ⊆ Iio a.val :=
  image_subset_iff.mpr fun _ m => m

theorem image_subtype_val_Ici_subset (a : {x // p x}) :
    Subtype.val '' Ici a ⊆ Ici a.val :=
  image_subset_iff.mpr fun _ m => m

theorem image_subtype_val_Ioi_subset (a : {x // p x}) :
    Subtype.val '' Ioi a ⊆ Ioi a.val :=
  image_subset_iff.mpr fun _ m => m

@[simp]
lemma image_subtype_val_Ici_Iic {a : α} (b : Ici a) : Subtype.val '' Iic b = Icc a b :=
  (Subtype.image_preimage_val (Ici a) (Iic b.1)).trans Ici_inter_Iic

@[simp]
lemma image_subtype_val_Ici_Iio {a : α} (b : Ici a) : Subtype.val '' Iio b = Ico a b :=
  (Subtype.image_preimage_val (Ici a) (Iio b.1)).trans Ici_inter_Iio

@[simp]
lemma image_subtype_val_Ici_Ici {a : α} (b : Ici a) : Subtype.val '' Ici b = Ici b.1 :=
  (Subtype.image_preimage_val (Ici a) (Ici b.1)).trans <| inter_eq_right.2 <| Ici_subset_Ici.2 b.2

@[simp]
lemma image_subtype_val_Ici_Ioi {a : α} (b : Ici a) : Subtype.val '' Ioi b = Ioi b.1 :=
  (Subtype.image_preimage_val (Ici a) (Ioi b.1)).trans <| inter_eq_right.2 <| Ioi_subset_Ici b.2

@[simp]
lemma image_subtype_val_Iic_Ici {a : α} (b : Iic a) : Subtype.val '' Ici b = Icc b.1 a :=
  (Subtype.image_preimage_val _ _).trans <| inter_comm _ _

@[simp]
lemma image_subtype_val_Iic_Ioi {a : α} (b : Iic a) : Subtype.val '' Ioi b = Ioc b.1 a :=
  (Subtype.image_preimage_val _ _).trans <| inter_comm _ _

@[simp]
lemma image_subtype_val_Iic_Iic {a : α} (b : Iic a) : Subtype.val '' Iic b = Iic b.1 :=
  image_subtype_val_Ici_Ici (α := αᵒᵈ) _

@[simp]
lemma image_subtype_val_Iic_Iio {a : α} (b : Iic a) : Subtype.val '' Iio b = Iio b.1 :=
  image_subtype_val_Ici_Ioi (α := αᵒᵈ) _

@[simp]
lemma image_subtype_val_Ioi_Ici {a : α} (b : Ioi a) : Subtype.val '' Ici b = Ici b.1 :=
  (Subtype.image_preimage_val (Ioi a) (Ici b.1)).trans <| inter_eq_right.2 <| Ici_subset_Ioi.2 b.2

@[simp]
lemma image_subtype_val_Ioi_Iic {a : α} (b : Ioi a) : Subtype.val '' Iic b = Ioc a b :=
  (Subtype.image_preimage_val (Ioi a) (Iic b.1)).trans Ioi_inter_Iic

@[simp]
lemma image_subtype_val_Ioi_Ioi {a : α} (b : Ioi a) : Subtype.val '' Ioi b = Ioi b.1 :=
  (Subtype.image_preimage_val (Ioi a) (Ioi b.1)).trans <| inter_eq_right.2 <| Ioi_subset_Ioi b.2.le

@[simp]
lemma image_subtype_val_Ioi_Iio {a : α} (b : Ioi a) : Subtype.val '' Iio b = Ioo a b :=
  (Subtype.image_preimage_val (Ioi a) (Iio b.1)).trans Ioi_inter_Iio

@[simp]
lemma image_subtype_val_Iio_Ici {a : α} (b : Iio a) : Subtype.val '' Ici b = Ico b.1 a :=
  (Subtype.image_preimage_val _ _).trans <| inter_comm _ _

@[simp]
lemma image_subtype_val_Iio_Iic {a : α} (b : Iio a) : Subtype.val '' Iic b = Iic b.1 :=
  image_subtype_val_Ioi_Ici (α := αᵒᵈ) _

@[simp]
lemma image_subtype_val_Iio_Ioi {a : α} (b : Iio a) : Subtype.val '' Ioi b = Ioo b.1 a :=
  (Subtype.image_preimage_val _ _).trans <| inter_comm _ _

@[simp]
lemma image_subtype_val_Iio_Iio {a : α} (b : Iio a) : Subtype.val '' Iio b = Iio b.1 :=
  image_subtype_val_Ioi_Ioi (α := αᵒᵈ) _

private lemma image_subtype_val_Ixx_Ixi {p q r : α → α → Prop} {a b : α} (c : {x // p a x ∧ q x b})
    (h : ∀ {x}, r c x → p a x) :
    Subtype.val '' {y : {x // p a x ∧ q x b} | r c.1 y.1} = {y : α | r c.1 y ∧ q y b} :=
  (Subtype.image_preimage_val {x | p a x ∧ q x b} {y | r c.1 y}).trans <| by
    ext; simp (config := { contextual := true }) [@and_comm (r _ _), h]

private lemma image_subtype_val_Ixx_Iix {p q r : α → α → Prop} {a b : α} (c : {x // p a x ∧ q x b})
    (h : ∀ {x}, r x c → q x b) :
    Subtype.val '' {y : {x // p a x ∧ q x b} | r y.1 c.1} = {y : α | p a y ∧ r y c.1} :=
  (Subtype.image_preimage_val {x | p a x ∧ q x b} {y | r y c.1}).trans <| by
    ext; simp (config := { contextual := true}) [h]

@[simp]
lemma image_subtype_val_Icc_Ici {a b : α} (c : Icc a b) : Subtype.val '' Ici c = Icc c.1 b :=
  image_subtype_val_Ixx_Ixi c c.2.1.trans

@[simp]
lemma image_subtype_val_Icc_Iic {a b : α} (c : Icc a b) : Subtype.val '' Iic c = Icc a c :=
  image_subtype_val_Ixx_Iix c (le_trans · c.2.2)

@[simp]
lemma image_subtype_val_Icc_Ioi {a b : α} (c : Icc a b) : Subtype.val '' Ioi c = Ioc c.1 b :=
  image_subtype_val_Ixx_Ixi c (c.2.1.trans <| le_of_lt ·)

@[simp]
lemma image_subtype_val_Icc_Iio {a b : α} (c : Icc a b) : Subtype.val '' Iio c = Ico a c :=
  image_subtype_val_Ixx_Iix c fun h ↦ (le_of_lt h).trans c.2.2

@[simp]
lemma image_subtype_val_Ico_Ici {a b : α} (c : Ico a b) : Subtype.val '' Ici c = Ico c.1 b :=
  image_subtype_val_Ixx_Ixi c c.2.1.trans

@[simp]
lemma image_subtype_val_Ico_Iic {a b : α} (c : Ico a b) : Subtype.val '' Iic c = Icc a c :=
  image_subtype_val_Ixx_Iix c (lt_of_le_of_lt · c.2.2)

@[simp]
lemma image_subtype_val_Ico_Ioi {a b : α} (c : Ico a b) : Subtype.val '' Ioi c = Ioo c.1 b :=
  image_subtype_val_Ixx_Ixi c (c.2.1.trans <| le_of_lt ·)

@[simp]
lemma image_subtype_val_Ico_Iio {a b : α} (c : Ico a b) : Subtype.val '' Iio c = Ico a c :=
  image_subtype_val_Ixx_Iix c (lt_trans · c.2.2)

@[simp]
lemma image_subtype_val_Ioc_Ici {a b : α} (c : Ioc a b) : Subtype.val '' Ici c = Icc c.1 b :=
  image_subtype_val_Ixx_Ixi c c.2.1.trans_le

@[simp]
lemma image_subtype_val_Ioc_Iic {a b : α} (c : Ioc a b) : Subtype.val '' Iic c = Ioc a c :=
  image_subtype_val_Ixx_Iix c (le_trans · c.2.2)

@[simp]
lemma image_subtype_val_Ioc_Ioi {a b : α} (c : Ioc a b) : Subtype.val '' Ioi c = Ioc c.1 b :=
  image_subtype_val_Ixx_Ixi c c.2.1.trans

@[simp]
lemma image_subtype_val_Ioc_Iio {a b : α} (c : Ioc a b) : Subtype.val '' Iio c = Ioo a c :=
  image_subtype_val_Ixx_Iix c fun h ↦ (le_of_lt h).trans c.2.2

@[simp]
lemma image_subtype_val_Ioo_Ici {a b : α} (c : Ioo a b) : Subtype.val '' Ici c = Ico c.1 b :=
  image_subtype_val_Ixx_Ixi c c.2.1.trans_le

@[simp]
lemma image_subtype_val_Ioo_Iic {a b : α} (c : Ioo a b) : Subtype.val '' Iic c = Ioc a c :=
  image_subtype_val_Ixx_Iix c (lt_of_le_of_lt · c.2.2)

@[simp]
lemma image_subtype_val_Ioo_Ioi {a b : α} (c : Ioo a b) : Subtype.val '' Ioi c = Ioo c.1 b :=
  image_subtype_val_Ixx_Ixi c c.2.1.trans

@[simp]
lemma image_subtype_val_Ioo_Iio {a b : α} (c : Ioo a b) : Subtype.val '' Iio c = Ioo a c :=
  image_subtype_val_Ixx_Iix c (lt_trans · c.2.2)

end Set

section Preorder
variable [Preorder α]

lemma directedOn_le_Iic (b : α) : DirectedOn (· ≤ ·) (Iic b) :=
  fun _x hx _y hy ↦ ⟨b, le_rfl, hx, hy⟩

lemma directedOn_le_Icc (a b : α) : DirectedOn (· ≤ ·) (Icc a b) :=
  fun _x hx _y hy ↦ ⟨b, right_mem_Icc.2 $ hx.1.trans hx.2, hx.2, hy.2⟩

lemma directedOn_le_Ioc (a b : α) : DirectedOn (· ≤ ·) (Ioc a b) :=
  fun _x hx _y hy ↦ ⟨b, right_mem_Ioc.2 $ hx.1.trans_le hx.2, hx.2, hy.2⟩

lemma directedOn_ge_Ici (a : α) : DirectedOn (· ≥ ·) (Ici a) :=
  fun _x hx _y hy ↦ ⟨a, le_rfl, hx, hy⟩

lemma directedOn_ge_Icc (a b : α) : DirectedOn (· ≥ ·) (Icc a b) :=
  fun _x hx _y hy ↦ ⟨a, left_mem_Icc.2 $ hx.1.trans hx.2, hx.1, hy.1⟩

lemma directedOn_ge_Ico (a b : α) : DirectedOn (· ≥ ·) (Ico a b) :=
  fun _x hx _y hy ↦ ⟨a, left_mem_Ico.2 $ hx.1.trans_lt hx.2, hx.1, hy.1⟩

end Preorder
