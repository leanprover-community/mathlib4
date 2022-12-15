/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Patrick Massot

! This file was ported from Lean 3 source module data.set.intervals.proj_Icc
! leanprover-community/mathlib commit aba57d4d3dae35460225919dcd82fe91355162f9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.Function
import Mathbin.Data.Set.Intervals.Basic

/-!
# Projection of a line onto a closed interval

Given a linearly ordered type `α`, in this file we define

* `set.proj_Icc (a b : α) (h : a ≤ b)` to be the map `α → [a, b]` sending `(-∞, a]` to `a`, `[b, ∞)`
  to `b`, and each point `x ∈ [a, b]` to itself;
* `set.Icc_extend {a b : α} (h : a ≤ b) (f : Icc a b → β)` to be the extension of `f` to `α` defined
  as `f ∘ proj_Icc a b h`.

We also prove some trivial properties of these maps.
-/


variable {α β : Type _} [LinearOrder α]

open Function

namespace Set

/-- Projection of `α` to the closed interval `[a, b]`. -/
def projIcc (a b : α) (h : a ≤ b) (x : α) : icc a b :=
  ⟨max a (min b x), le_max_left _ _, max_le h (min_le_left _ _)⟩
#align set.proj_Icc Set.projIcc

variable {a b : α} (h : a ≤ b) {x : α}

theorem proj_Icc_of_le_left (hx : x ≤ a) : projIcc a b h x = ⟨a, left_mem_Icc.2 h⟩ := by
  simp [proj_Icc, hx, hx.trans h]
#align set.proj_Icc_of_le_left Set.proj_Icc_of_le_left

@[simp]
theorem proj_Icc_left : projIcc a b h a = ⟨a, left_mem_Icc.2 h⟩ :=
  proj_Icc_of_le_left h le_rfl
#align set.proj_Icc_left Set.proj_Icc_left

theorem proj_Icc_of_right_le (hx : b ≤ x) : projIcc a b h x = ⟨b, right_mem_Icc.2 h⟩ := by
  simp [proj_Icc, hx, h]
#align set.proj_Icc_of_right_le Set.proj_Icc_of_right_le

@[simp]
theorem proj_Icc_right : projIcc a b h b = ⟨b, right_mem_Icc.2 h⟩ :=
  proj_Icc_of_right_le h le_rfl
#align set.proj_Icc_right Set.proj_Icc_right

theorem proj_Icc_eq_left (h : a < b) : projIcc a b h.le x = ⟨a, left_mem_Icc.mpr h.le⟩ ↔ x ≤ a := by
  refine' ⟨fun h' => _, proj_Icc_of_le_left _⟩
  simp_rw [Subtype.ext_iff_val, proj_Icc, max_eq_left_iff, min_le_iff, h.not_le, false_or_iff] at h'
  exact h'
#align set.proj_Icc_eq_left Set.proj_Icc_eq_left

theorem proj_Icc_eq_right (h : a < b) : projIcc a b h.le x = ⟨b, right_mem_Icc.mpr h.le⟩ ↔ b ≤ x :=
  by
  refine' ⟨fun h' => _, proj_Icc_of_right_le _⟩
  simp_rw [Subtype.ext_iff_val, proj_Icc] at h'
  have := ((max_choice _ _).resolve_left (by simp [h.ne', h'])).symm.trans h'
  exact min_eq_left_iff.mp this
#align set.proj_Icc_eq_right Set.proj_Icc_eq_right

theorem proj_Icc_of_mem (hx : x ∈ icc a b) : projIcc a b h x = ⟨x, hx⟩ := by
  simp [proj_Icc, hx.1, hx.2]
#align set.proj_Icc_of_mem Set.proj_Icc_of_mem

@[simp]
theorem proj_Icc_coe (x : icc a b) : projIcc a b h x = x := by
  cases x
  apply proj_Icc_of_mem
#align set.proj_Icc_coe Set.proj_Icc_coe

theorem proj_Icc_surj_on : SurjOn (projIcc a b h) (icc a b) univ := fun x _ =>
  ⟨x, x.2, proj_Icc_coe h x⟩
#align set.proj_Icc_surj_on Set.proj_Icc_surj_on

theorem proj_Icc_surjective : Surjective (projIcc a b h) := fun x => ⟨x, proj_Icc_coe h x⟩
#align set.proj_Icc_surjective Set.proj_Icc_surjective

@[simp]
theorem range_proj_Icc : range (projIcc a b h) = univ :=
  (proj_Icc_surjective h).range_eq
#align set.range_proj_Icc Set.range_proj_Icc

theorem monotone_proj_Icc : Monotone (projIcc a b h) := fun x y hxy =>
  max_le_max le_rfl <| min_le_min le_rfl hxy
#align set.monotone_proj_Icc Set.monotone_proj_Icc

theorem strict_mono_on_proj_Icc : StrictMonoOn (projIcc a b h) (icc a b) := fun x hx y hy hxy => by
  simpa only [proj_Icc_of_mem, hx, hy]
#align set.strict_mono_on_proj_Icc Set.strict_mono_on_proj_Icc

/-- Extend a function `[a, b] → β` to a map `α → β`. -/
def iccExtend {a b : α} (h : a ≤ b) (f : icc a b → β) : α → β :=
  f ∘ projIcc a b h
#align set.Icc_extend Set.iccExtend

@[simp]
theorem Icc_extend_range (f : icc a b → β) : range (iccExtend h f) = range f := by
  simp only [Icc_extend, range_comp f, range_proj_Icc, range_id']
#align set.Icc_extend_range Set.Icc_extend_range

theorem Icc_extend_of_le_left (f : icc a b → β) (hx : x ≤ a) :
    iccExtend h f x = f ⟨a, left_mem_Icc.2 h⟩ :=
  congr_arg f <| proj_Icc_of_le_left h hx
#align set.Icc_extend_of_le_left Set.Icc_extend_of_le_left

@[simp]
theorem Icc_extend_left (f : icc a b → β) : iccExtend h f a = f ⟨a, left_mem_Icc.2 h⟩ :=
  Icc_extend_of_le_left h f le_rfl
#align set.Icc_extend_left Set.Icc_extend_left

theorem Icc_extend_of_right_le (f : icc a b → β) (hx : b ≤ x) :
    iccExtend h f x = f ⟨b, right_mem_Icc.2 h⟩ :=
  congr_arg f <| proj_Icc_of_right_le h hx
#align set.Icc_extend_of_right_le Set.Icc_extend_of_right_le

@[simp]
theorem Icc_extend_right (f : icc a b → β) : iccExtend h f b = f ⟨b, right_mem_Icc.2 h⟩ :=
  Icc_extend_of_right_le h f le_rfl
#align set.Icc_extend_right Set.Icc_extend_right

theorem Icc_extend_of_mem (f : icc a b → β) (hx : x ∈ icc a b) : iccExtend h f x = f ⟨x, hx⟩ :=
  congr_arg f <| proj_Icc_of_mem h hx
#align set.Icc_extend_of_mem Set.Icc_extend_of_mem

@[simp]
theorem Icc_extend_coe (f : icc a b → β) (x : icc a b) : iccExtend h f x = f x :=
  congr_arg f <| proj_Icc_coe h x
#align set.Icc_extend_coe Set.Icc_extend_coe

end Set

open Set

variable [Preorder β] {a b : α} (h : a ≤ b) {f : icc a b → β}

theorem Monotone.Icc_extend (hf : Monotone f) : Monotone (iccExtend h f) :=
  hf.comp <| monotone_proj_Icc h
#align monotone.Icc_extend Monotone.Icc_extend

theorem StrictMono.strict_mono_on_Icc_extend (hf : StrictMono f) :
    StrictMonoOn (iccExtend h f) (icc a b) :=
  hf.comp_strict_mono_on (strict_mono_on_proj_Icc h)
#align strict_mono.strict_mono_on_Icc_extend StrictMono.strict_mono_on_Icc_extend
