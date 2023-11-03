/-
Copyright (c) 2023 Kim Liesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Liesinger, Yaël Dillies
-/
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Data.Set.Function

/-!
# Monotone functions on intervals

This file shows many variants of the fact that a monotone function `f` sends an interval with
endpoints `a` and `b` to the interval with endpoints `f a` and `f b`.
-/

set_option autoImplicit true

variable {f : α → β}

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

lemma AntitoneOn.image_Ici_subset (h : AntitoneOn f (Ici a)) : f '' Ici a ⊆ Iic (f a) :=
  h.mapsTo_Ici.image_subset

lemma AntitoneOn.image_Iic_subset (h : AntitoneOn f (Iic b)) : f '' Iic b ⊆ Ici (f b) :=
  h.mapsTo_Iic.image_subset

lemma AntitoneOn.image_Icc_subset (h : AntitoneOn f (Icc a b)) : f '' Icc a b ⊆ Icc (f b) (f a) :=
  h.mapsTo_Icc.image_subset

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

lemma Antitone.image_Ici_subset (h : Antitone f) : f '' Ici a ⊆ Iic (f a) :=
  (h.antitoneOn _).image_Ici_subset

lemma Antitone.image_Iic_subset (h : Antitone f) : f '' Iic b ⊆ Ici (f b) :=
  (h.antitoneOn _).image_Iic_subset

lemma Antitone.image_Icc_subset (h : Antitone f) : f '' Icc a b ⊆ Icc (f b) (f a) :=
  (h.antitoneOn _).image_Icc_subset

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
variable [PartialOrder α] [Preorder β]

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

end Set
