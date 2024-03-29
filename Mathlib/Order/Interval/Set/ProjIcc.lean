/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Patrick Massot
-/
import Mathlib.Data.Set.Function
import Mathlib.Order.Interval.Set.OrdConnected

#align_import data.set.intervals.proj_Icc from "leanprover-community/mathlib"@"4e24c4bfcff371c71f7ba22050308aa17815626c"

/-!
# Projection of a line onto a closed interval

Given a linearly ordered type `α`, in this file we define

* `Set.projIci (a : α)` to be the map `α → [a, ∞)` sending `(-∞, a]` to `a`, and each point
   `x ∈ [a, ∞)` to itself;
* `Set.projIic (b : α)` to be the map `α → (-∞, b[` sending `[b, ∞)` to `b`, and each point
   `x ∈ (-∞, b]` to itself;
* `Set.projIcc (a b : α) (h : a ≤ b)` to be the map `α → [a, b]` sending `(-∞, a]` to `a`, `[b, ∞)`
  to `b`, and each point `x ∈ [a, b]` to itself;
* `Set.IccExtend {a b : α} (h : a ≤ b) (f : Icc a b → β)` to be the extension of `f` to `α` defined
  as `f ∘ projIcc a b h`.
* `Set.IciExtend {a : α} (f : Ici a → β)` to be the extension of `f` to `α` defined
  as `f ∘ projIci a`.
* `Set.IicExtend {b : α} (f : Iic b → β)` to be the extension of `f` to `α` defined
  as `f ∘ projIic b`.

We also prove some trivial properties of these maps.
-/


variable {α β : Type*} [LinearOrder α]

open Function

namespace Set

/-- Projection of `α` to the closed interval `[a, ∞)`. -/
def projIci (a x : α) : Ici a := ⟨max a x, le_max_left _ _⟩
#align set.proj_Ici Set.projIci

/-- Projection of `α` to the closed interval `(-∞, b]`. -/
def projIic (b x : α) : Iic b := ⟨min b x, min_le_left _ _⟩
#align set.proj_Iic Set.projIic

/-- Projection of `α` to the closed interval `[a, b]`. -/
def projIcc (a b : α) (h : a ≤ b) (x : α) : Icc a b :=
  ⟨max a (min b x), le_max_left _ _, max_le h (min_le_left _ _)⟩
#align set.proj_Icc Set.projIcc

variable {a b : α} (h : a ≤ b) {x : α}

@[norm_cast]
theorem coe_projIci (a x : α) : (projIci a x : α) = max a x := rfl
#align set.coe_proj_Ici Set.coe_projIci

@[norm_cast]
theorem coe_projIic (b x : α) : (projIic b x : α) = min b x := rfl
#align set.coe_proj_Iic Set.coe_projIic

@[norm_cast]
theorem coe_projIcc (a b : α) (h : a ≤ b) (x : α) : (projIcc a b h x : α) = max a (min b x) := rfl
#align set.coe_proj_Icc Set.coe_projIcc

theorem projIci_of_le (hx : x ≤ a) : projIci a x = ⟨a, le_rfl⟩ := Subtype.ext <| max_eq_left hx
#align set.proj_Ici_of_le Set.projIci_of_le

theorem projIic_of_le (hx : b ≤ x) : projIic b x = ⟨b, le_rfl⟩ := Subtype.ext <| min_eq_left hx
#align set.proj_Iic_of_le Set.projIic_of_le

theorem projIcc_of_le_left (hx : x ≤ a) : projIcc a b h x = ⟨a, left_mem_Icc.2 h⟩ := by
  simp [projIcc, hx, hx.trans h]
#align set.proj_Icc_of_le_left Set.projIcc_of_le_left


theorem projIcc_of_right_le (hx : b ≤ x) : projIcc a b h x = ⟨b, right_mem_Icc.2 h⟩ := by
  simp [projIcc, hx, h]
#align set.proj_Icc_of_right_le Set.projIcc_of_right_le

@[simp]
theorem projIci_self (a : α) : projIci a a = ⟨a, le_rfl⟩ := projIci_of_le le_rfl
#align set.proj_Ici_self Set.projIci_self

@[simp]
theorem projIic_self (b : α) : projIic b b = ⟨b, le_rfl⟩ := projIic_of_le le_rfl
#align set.proj_Iic_self Set.projIic_self

@[simp]
theorem projIcc_left : projIcc a b h a = ⟨a, left_mem_Icc.2 h⟩ :=
  projIcc_of_le_left h le_rfl
#align set.proj_Icc_left Set.projIcc_left

@[simp]
theorem projIcc_right : projIcc a b h b = ⟨b, right_mem_Icc.2 h⟩ :=
  projIcc_of_right_le h le_rfl
#align set.proj_Icc_right Set.projIcc_right

theorem projIci_eq_self : projIci a x = ⟨a, le_rfl⟩ ↔ x ≤ a := by simp [projIci, Subtype.ext_iff]
#align set.proj_Ici_eq_self Set.projIci_eq_self

theorem projIic_eq_self : projIic b x = ⟨b, le_rfl⟩ ↔ b ≤ x := by simp [projIic, Subtype.ext_iff]
#align set.proj_Iic_eq_self Set.projIic_eq_self

theorem projIcc_eq_left (h : a < b) : projIcc a b h.le x = ⟨a, left_mem_Icc.mpr h.le⟩ ↔ x ≤ a := by
  simp [projIcc, Subtype.ext_iff, h.not_le]
#align set.proj_Icc_eq_left Set.projIcc_eq_left

theorem projIcc_eq_right (h : a < b) : projIcc a b h.le x = ⟨b, right_mem_Icc.2 h.le⟩ ↔ b ≤ x := by
  simp [projIcc, Subtype.ext_iff, max_min_distrib_left, h.le, h.not_le]
#align set.proj_Icc_eq_right Set.projIcc_eq_right

theorem projIci_of_mem (hx : x ∈ Ici a) : projIci a x = ⟨x, hx⟩ := by simpa [projIci]
#align set.proj_Ici_of_mem Set.projIci_of_mem

theorem projIic_of_mem (hx : x ∈ Iic b) : projIic b x = ⟨x, hx⟩ := by simpa [projIic]
#align set.proj_Iic_of_mem Set.projIic_of_mem

theorem projIcc_of_mem (hx : x ∈ Icc a b) : projIcc a b h x = ⟨x, hx⟩ := by
  simp [projIcc, hx.1, hx.2]
#align set.proj_Icc_of_mem Set.projIcc_of_mem

@[simp]
theorem projIci_coe (x : Ici a) : projIci a x = x := by cases x; apply projIci_of_mem
#align set.proj_Ici_coe Set.projIci_coe

@[simp]
theorem projIic_coe (x : Iic b) : projIic b x = x := by cases x; apply projIic_of_mem
#align set.proj_Iic_coe Set.projIic_coe

@[simp]
theorem projIcc_val (x : Icc a b) : projIcc a b h x = x := by
  cases x
  apply projIcc_of_mem
#align set.proj_Icc_coe Set.projIcc_val

theorem projIci_surjOn : SurjOn (projIci a) (Ici a) univ := fun x _ => ⟨x, x.2, projIci_coe x⟩
#align set.proj_Ici_surj_on Set.projIci_surjOn

theorem projIic_surjOn : SurjOn (projIic b) (Iic b) univ := fun x _ => ⟨x, x.2, projIic_coe x⟩
#align set.proj_Iic_surj_on Set.projIic_surjOn

theorem projIcc_surjOn : SurjOn (projIcc a b h) (Icc a b) univ := fun x _ =>
  ⟨x, x.2, projIcc_val h x⟩
#align set.proj_Icc_surj_on Set.projIcc_surjOn

theorem projIci_surjective : Surjective (projIci a) := fun x => ⟨x, projIci_coe x⟩
#align set.proj_Ici_surjective Set.projIci_surjective

theorem projIic_surjective : Surjective (projIic b) := fun x => ⟨x, projIic_coe x⟩
#align set.proj_Iic_surjective Set.projIic_surjective

theorem projIcc_surjective : Surjective (projIcc a b h) := fun x => ⟨x, projIcc_val h x⟩
#align set.proj_Icc_surjective Set.projIcc_surjective

@[simp]
theorem range_projIci : range (projIci a) = univ := projIci_surjective.range_eq
#align set.range_proj_Ici Set.range_projIci

@[simp]
theorem range_projIic : range (projIic a) = univ := projIic_surjective.range_eq
#align set.range_proj_Iic Set.range_projIic

@[simp]
theorem range_projIcc : range (projIcc a b h) = univ :=
  (projIcc_surjective h).range_eq
#align set.range_proj_Icc Set.range_projIcc

theorem monotone_projIci : Monotone (projIci a) := fun _ _ => max_le_max le_rfl
#align set.monotone_proj_Ici Set.monotone_projIci

theorem monotone_projIic : Monotone (projIic a) := fun _ _ => min_le_min le_rfl
#align set.monotone_proj_Iic Set.monotone_projIic

theorem monotone_projIcc : Monotone (projIcc a b h) := fun _ _ hxy =>
  max_le_max le_rfl <| min_le_min le_rfl hxy
#align set.monotone_proj_Icc Set.monotone_projIcc

theorem strictMonoOn_projIci : StrictMonoOn (projIci a) (Ici a) := fun x hx y hy hxy => by
  simpa only [projIci_of_mem, hx, hy]
#align set.strict_mono_on_proj_Ici Set.strictMonoOn_projIci

theorem strictMonoOn_projIic : StrictMonoOn (projIic b) (Iic b) := fun x hx y hy hxy => by
  simpa only [projIic_of_mem, hx, hy]
#align set.strict_mono_on_proj_Iic Set.strictMonoOn_projIic

theorem strictMonoOn_projIcc : StrictMonoOn (projIcc a b h) (Icc a b) := fun x hx y hy hxy => by
  simpa only [projIcc_of_mem, hx, hy]
#align set.strict_mono_on_proj_Icc Set.strictMonoOn_projIcc

/-- Extend a function `[a, ∞) → β` to a map `α → β`. -/
def IciExtend (f : Ici a → β) : α → β :=
  f ∘ projIci a
#align set.Ici_extend Set.IciExtend

/-- Extend a function `(-∞, b] → β` to a map `α → β`. -/
def IicExtend (f : Iic b → β) : α → β :=
  f ∘ projIic b
#align set.Iic_extend Set.IicExtend

/-- Extend a function `[a, b] → β` to a map `α → β`. -/
def IccExtend {a b : α} (h : a ≤ b) (f : Icc a b → β) : α → β :=
  f ∘ projIcc a b h
#align set.Icc_extend Set.IccExtend

theorem IciExtend_apply (f : Ici a → β) (x : α) : IciExtend f x = f ⟨max a x, le_max_left _ _⟩ :=
  rfl
#align set.Ici_extend_apply Set.IciExtend_apply

theorem IicExtend_apply (f : Iic b → β) (x : α) : IicExtend f x = f ⟨min b x, min_le_left _ _⟩ :=
  rfl
#align set.Iic_extend_apply Set.IicExtend_apply

theorem IccExtend_apply (h : a ≤ b) (f : Icc a b → β) (x : α) :
    IccExtend h f x = f ⟨max a (min b x), le_max_left _ _, max_le h (min_le_left _ _)⟩ := rfl
#align set.Icc_extend_apply Set.IccExtend_apply

@[simp]
theorem range_IciExtend (f : Ici a → β) : range (IciExtend f) = range f := by
  simp only [IciExtend, range_comp f, range_projIci, range_id', image_univ]
#align set.range_Ici_extend Set.range_IciExtend

@[simp]
theorem range_IicExtend (f : Iic b → β) : range (IicExtend f) = range f := by
  simp only [IicExtend, range_comp f, range_projIic, range_id', image_univ]
#align set.range_Iic_extend Set.range_IicExtend

@[simp]
theorem IccExtend_range (f : Icc a b → β) : range (IccExtend h f) = range f := by
  simp only [IccExtend, range_comp f, range_projIcc, image_univ]
#align set.Icc_extend_range Set.IccExtend_range

theorem IciExtend_of_le (f : Ici a → β) (hx : x ≤ a) : IciExtend f x = f ⟨a, le_rfl⟩ :=
  congr_arg f <| projIci_of_le hx
#align set.Ici_extend_of_le Set.IciExtend_of_le

theorem IicExtend_of_le (f : Iic b → β) (hx : b ≤ x) : IicExtend f x = f ⟨b, le_rfl⟩ :=
  congr_arg f <| projIic_of_le hx
#align set.Iic_extend_of_le Set.IicExtend_of_le

theorem IccExtend_of_le_left (f : Icc a b → β) (hx : x ≤ a) :
    IccExtend h f x = f ⟨a, left_mem_Icc.2 h⟩ :=
  congr_arg f <| projIcc_of_le_left h hx
#align set.Icc_extend_of_le_left Set.IccExtend_of_le_left

theorem IccExtend_of_right_le (f : Icc a b → β) (hx : b ≤ x) :
    IccExtend h f x = f ⟨b, right_mem_Icc.2 h⟩ :=
  congr_arg f <| projIcc_of_right_le h hx
#align set.Icc_extend_of_right_le Set.IccExtend_of_right_le

@[simp]
theorem IciExtend_self (f : Ici a → β) : IciExtend f a = f ⟨a, le_rfl⟩ :=
  IciExtend_of_le f le_rfl
#align set.Ici_extend_self Set.IciExtend_self

@[simp]
theorem IicExtend_self (f : Iic b → β) : IicExtend f b = f ⟨b, le_rfl⟩ :=
  IicExtend_of_le f le_rfl
#align set.Iic_extend_self Set.IicExtend_self

@[simp]
theorem IccExtend_left (f : Icc a b → β) : IccExtend h f a = f ⟨a, left_mem_Icc.2 h⟩ :=
  IccExtend_of_le_left h f le_rfl
#align set.Icc_extend_left Set.IccExtend_left

@[simp]
theorem IccExtend_right (f : Icc a b → β) : IccExtend h f b = f ⟨b, right_mem_Icc.2 h⟩ :=
  IccExtend_of_right_le h f le_rfl
#align set.Icc_extend_right Set.IccExtend_right

theorem IciExtend_of_mem (f : Ici a → β) (hx : x ∈ Ici a) : IciExtend f x = f ⟨x, hx⟩ :=
  congr_arg f <| projIci_of_mem hx
#align set.Ici_extend_of_mem Set.IciExtend_of_mem

theorem IicExtend_of_mem (f : Iic b → β) (hx : x ∈ Iic b) : IicExtend f x = f ⟨x, hx⟩ :=
  congr_arg f <| projIic_of_mem hx
#align set.Iic_extend_of_mem Set.IicExtend_of_mem

theorem IccExtend_of_mem (f : Icc a b → β) (hx : x ∈ Icc a b) : IccExtend h f x = f ⟨x, hx⟩ :=
  congr_arg f <| projIcc_of_mem h hx
#align set.Icc_extend_of_mem Set.IccExtend_of_mem

@[simp]
theorem IciExtend_coe (f : Ici a → β) (x : Ici a) : IciExtend f x = f x :=
  congr_arg f <| projIci_coe x
#align set.Ici_extend_coe Set.IciExtend_coe

@[simp]
theorem IicExtend_coe (f : Iic b → β) (x : Iic b) : IicExtend f x = f x :=
  congr_arg f <| projIic_coe x
#align set.Iic_extend_coe Set.IicExtend_coe

@[simp]
theorem IccExtend_val (f : Icc a b → β) (x : Icc a b) : IccExtend h f x = f x :=
  congr_arg f <| projIcc_val h x
#align set.Icc_extend_coe Set.IccExtend_val

/-- If `f : α → β` is a constant both on $(-∞, a]$ and on $[b, +∞)$, then the extension of this
function from $[a, b]$ to the whole line is equal to the original function. -/
theorem IccExtend_eq_self (f : α → β) (ha : ∀ x < a, f x = f a) (hb : ∀ x, b < x → f x = f b) :
    IccExtend h (f ∘ (↑)) = f := by
  ext x
  cases' lt_or_le x a with hxa hax
  · simp [IccExtend_of_le_left _ _ hxa.le, ha x hxa]
  · rcases le_or_lt x b with hxb | hbx
    · lift x to Icc a b using ⟨hax, hxb⟩
      rw [IccExtend_val, comp_apply]
    · simp [IccExtend_of_right_le _ _ hbx.le, hb x hbx]
#align set.Icc_extend_eq_self Set.IccExtend_eq_self

end Set

open Set

variable [Preorder β] {s t : Set α} {a b : α} (h : a ≤ b) {f : Icc a b → β}

protected theorem Monotone.IciExtend {f : Ici a → β} (hf : Monotone f) : Monotone (IciExtend f) :=
  hf.comp monotone_projIci
#align monotone.Ici_extend Monotone.IciExtend

protected theorem Monotone.IicExtend {f : Iic b → β} (hf : Monotone f) : Monotone (IicExtend f) :=
  hf.comp monotone_projIic
#align monotone.Iic_extend Monotone.IicExtend

protected theorem Monotone.IccExtend (hf : Monotone f) : Monotone (IccExtend h f) :=
  hf.comp <| monotone_projIcc h
#align monotone.Icc_extend Monotone.IccExtend

theorem StrictMono.strictMonoOn_IciExtend {f : Ici a → β} (hf : StrictMono f) :
    StrictMonoOn (IciExtend f) (Ici a) :=
  hf.comp_strictMonoOn strictMonoOn_projIci
#align strict_mono.strict_mono_on_Ici_extend StrictMono.strictMonoOn_IciExtend

theorem StrictMono.strictMonoOn_IicExtend {f : Iic b → β} (hf : StrictMono f) :
    StrictMonoOn (IicExtend f) (Iic b) :=
  hf.comp_strictMonoOn strictMonoOn_projIic
#align strict_mono.strict_mono_on_Iic_extend StrictMono.strictMonoOn_IicExtend

theorem StrictMono.strictMonoOn_IccExtend (hf : StrictMono f) :
    StrictMonoOn (IccExtend h f) (Icc a b) :=
  hf.comp_strictMonoOn (strictMonoOn_projIcc h)
#align strict_mono.strict_mono_on_Icc_extend StrictMono.strictMonoOn_IccExtend

protected theorem Set.OrdConnected.IciExtend {s : Set (Ici a)} (hs : s.OrdConnected) :
    {x | IciExtend (· ∈ s) x}.OrdConnected :=
  ⟨fun _ hx _ hy _ hz => hs.out hx hy ⟨max_le_max le_rfl hz.1, max_le_max le_rfl hz.2⟩⟩
#align set.ord_connected.Ici_extend Set.OrdConnected.IciExtend

protected theorem Set.OrdConnected.IicExtend {s : Set (Iic b)} (hs : s.OrdConnected) :
    {x | IicExtend (· ∈ s) x}.OrdConnected :=
  ⟨fun _ hx _ hy _ hz => hs.out hx hy ⟨min_le_min le_rfl hz.1, min_le_min le_rfl hz.2⟩⟩
#align set.ord_connected.Iic_extend Set.OrdConnected.IicExtend

protected theorem Set.OrdConnected.restrict (hs : s.OrdConnected) :
    {x | restrict t (· ∈ s) x}.OrdConnected :=
  ⟨fun _ hx _ hy _ hz => hs.out hx hy hz⟩
#align set.ord_connected.restrict Set.OrdConnected.restrict
