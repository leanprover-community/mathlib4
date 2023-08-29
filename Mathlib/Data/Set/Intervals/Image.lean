/-
Copyright (c) 2023 Kim Liesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Liesinger
-/
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Data.Set.Function

/-! ### Lemmas about monotone functions on intervals, and intervals in subtypes.
-/

set_option autoImplicit true

variable {f : α → β}

open Set

section
variable [Preorder α] [Preorder β]

theorem Monotone.mapsTo_Icc (h : Monotone f) :
    MapsTo f (Icc a b) (Icc (f a) (f b)) :=
  fun _ _ => by aesop
                -- 🎉 no goals

theorem StrictMono.mapsTo_Ioo (h : StrictMono f) :
    MapsTo f (Ioo a b) (Ioo (f a) (f b)) :=
  fun _ _ => by aesop
                -- 🎉 no goals

theorem Monotone.mapsTo_Ici  (h : Monotone f) :
    MapsTo f (Ici a) (Ici (f a)) :=
  fun _ _ => by aesop
                -- 🎉 no goals

theorem Monotone.mapsTo_Iic (h : Monotone f) :
    MapsTo f (Iic a) (Iic (f a)) :=
  fun _ _ => by aesop
                -- 🎉 no goals

theorem StrictMono.mapsTo_Ioi (h : StrictMono f) :
    MapsTo f (Ioi a) (Ioi (f a)) :=
  fun _ _ => by aesop
                -- 🎉 no goals

theorem StrictMono.mapsTo_Iio (h : StrictMono f) :
    MapsTo f (Iio a) (Iio (f a)) :=
  fun _ _ => by aesop
                -- 🎉 no goals

end

section
variable [PartialOrder α] [Preorder β]

theorem StrictMono.mapsTo_Ico (h : StrictMono f) :
    MapsTo f (Ico a b) (Ico (f a) (f b)) :=
  -- It makes me sad that `aesop` doesn't do this. There are clearly missing lemmas.
  fun _ m => ⟨h.monotone m.1, h m.2⟩

theorem StrictMono.mapsTo_Ioc (h : StrictMono f) :
    MapsTo f (Ioc a b) (Ioc (f a) (f b)) :=
  fun _ m => ⟨h m.1, h.monotone m.2⟩

end

section
variable [Preorder α] [Preorder β]

theorem Monotone.image_Icc_subset (h : Monotone f) :
    f '' Icc a b ⊆ Icc (f a) (f b) :=
  h.mapsTo_Icc.image_subset

theorem StrictMono.image_Ioo_subset (h : StrictMono f) :
    f '' Ioo a b ⊆ Ioo (f a) (f b) :=
  h.mapsTo_Ioo.image_subset

theorem Monotone.image_Ici_subset (h : Monotone f) :
    f '' Ici a ⊆ Ici (f a) :=
  h.mapsTo_Ici.image_subset

theorem Monotone.image_Iic_subset (h : Monotone f) :
    f '' Iic a ⊆ Iic (f a) :=
  h.mapsTo_Iic.image_subset

theorem StrictMono.image_Ioi_subset (h : StrictMono f) :
    f '' Ioi a ⊆ Ioi (f a) :=
  h.mapsTo_Ioi.image_subset

theorem StrictMono.image_Iio_subset (h : StrictMono f) :
    f '' Iio a ⊆ Iio (f a) :=
  h.mapsTo_Iio.image_subset

end

section
variable [PartialOrder α] [Preorder β]

theorem StrictMono.imageIco_subset (h : StrictMono f) :
    f '' Ico a b ⊆ Ico (f a) (f b) :=
  h.mapsTo_Ico.image_subset

theorem StrictMono.imageIoc_subset (h : StrictMono f) :
    f '' Ioc a b ⊆ Ioc (f a) (f b) :=
  h.mapsTo_Ioc.image_subset

end

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
