/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Data.Finset.Option
import Mathlib.Data.PFun
import Mathlib.Data.Part

#align_import data.finset.pimage from "leanprover-community/mathlib"@"f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c"

/-!
# Image of a `Finset α` under a partially defined function

In this file we define `Part.toFinset` and `Finset.pimage`. We also prove some trivial lemmas about
these definitions.

## Tags

finite set, image, partial function
-/


variable {α β : Type*}

namespace Part

/-- Convert an `o : Part α` with decidable `Part.Dom o` to `Finset α`. -/
def toFinset (o : Part α) [Decidable o.Dom] : Finset α :=
  o.toOption.toFinset
#align part.to_finset Part.toFinset

@[simp]
theorem mem_toFinset {o : Part α} [Decidable o.Dom] {x : α} : x ∈ o.toFinset ↔ x ∈ o := by
  simp [toFinset]
#align part.mem_to_finset Part.mem_toFinset

@[simp]
theorem toFinset_none [Decidable (none : Part α).Dom] : none.toFinset = (∅ : Finset α) := by
  simp [toFinset]
#align part.to_finset_none Part.toFinset_none

@[simp]
theorem toFinset_some {a : α} [Decidable (some a).Dom] : (some a).toFinset = {a} := by
  simp [toFinset]
#align part.to_finset_some Part.toFinset_some

@[simp]
theorem coe_toFinset (o : Part α) [Decidable o.Dom] : (o.toFinset : Set α) = { x | x ∈ o } :=
  Set.ext fun _ => mem_toFinset
#align part.coe_to_finset Part.coe_toFinset

end Part

namespace Finset

variable [DecidableEq β] {f g : α →. β} [∀ x, Decidable (f x).Dom] [∀ x, Decidable (g x).Dom]
  {s t : Finset α} {b : β}

/-- Image of `s : Finset α` under a partially defined function `f : α →. β`. -/
def pimage (f : α →. β) [∀ x, Decidable (f x).Dom] (s : Finset α) : Finset β :=
  s.biUnion fun x => (f x).toFinset
#align finset.pimage Finset.pimage

@[simp]
theorem mem_pimage : b ∈ s.pimage f ↔ ∃ a ∈ s, b ∈ f a := by
  simp [pimage]
#align finset.mem_pimage Finset.mem_pimage

@[simp, norm_cast]
theorem coe_pimage : (s.pimage f : Set β) = f.image s :=
  Set.ext fun _ => mem_pimage
#align finset.coe_pimage Finset.coe_pimage

@[simp]
theorem pimage_some (s : Finset α) (f : α → β) [∀ x, Decidable (Part.some <| f x).Dom] :
    (s.pimage fun x => Part.some (f x)) = s.image f := by
  ext
  simp [eq_comm]
#align finset.pimage_some Finset.pimage_some

theorem pimage_congr (h₁ : s = t) (h₂ : ∀ x ∈ t, f x = g x) : s.pimage f = t.pimage g := by
  subst s
  ext y
  -- Porting note: `← exists_prop` required because `∃ x ∈ s, p x` is defined differently
  simp (config := { contextual := true }) only [mem_pimage, ← exists_prop, h₂]
#align finset.pimage_congr Finset.pimage_congr

/-- Rewrite `s.pimage f` in terms of `Finset.filter`, `Finset.attach`, and `Finset.image`. -/
theorem pimage_eq_image_filter : s.pimage f =
    (filter (fun x => (f x).Dom) s).attach.image
      fun x : { x // x ∈ filter (fun x => (f x).Dom) s } =>
        (f x).get (mem_filter.mp x.coe_prop).2 := by
  ext x
  simp [Part.mem_eq, And.exists]
  -- Porting note: `← exists_prop` required because `∃ x ∈ s, p x` is defined differently
  simp only [← exists_prop]
#align finset.pimage_eq_image_filter Finset.pimage_eq_image_filter

theorem pimage_union [DecidableEq α] : (s ∪ t).pimage f = s.pimage f ∪ t.pimage f :=
  coe_inj.1 <| by
  simp only [coe_pimage, coe_union, ← PFun.image_union]
#align finset.pimage_union Finset.pimage_union

@[simp]
theorem pimage_empty : pimage f ∅ = ∅ := by
  ext
  simp
#align finset.pimage_empty Finset.pimage_empty

theorem pimage_subset {t : Finset β} : s.pimage f ⊆ t ↔ ∀ x ∈ s, ∀ y ∈ f x, y ∈ t := by
  simp [subset_iff, @forall_swap _ β]
#align finset.pimage_subset Finset.pimage_subset

@[mono]
theorem pimage_mono (h : s ⊆ t) : s.pimage f ⊆ t.pimage f :=
  pimage_subset.2 fun x hx _ hy => mem_pimage.2 ⟨x, h hx, hy⟩
#align finset.pimage_mono Finset.pimage_mono

theorem pimage_inter [DecidableEq α] : (s ∩ t).pimage f ⊆ s.pimage f ∩ t.pimage f := by
  simp only [← coe_subset, coe_pimage, coe_inter, PFun.image_inter]
#align finset.pimage_inter Finset.pimage_inter

end Finset
