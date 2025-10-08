/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Data.Finset.Option
import Mathlib.Data.PFun
import Mathlib.Data.Part

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

@[simp]
theorem mem_toFinset {o : Part α} [Decidable o.Dom] {x : α} : x ∈ o.toFinset ↔ x ∈ o := by
  simp [toFinset]

@[simp]
theorem toFinset_none [Decidable (none : Part α).Dom] : none.toFinset = (∅ : Finset α) := by
  simp [toFinset]

@[simp]
theorem toFinset_some {a : α} [Decidable (some a).Dom] : (some a).toFinset = {a} := by
  simp [toFinset]

@[simp]
theorem coe_toFinset (o : Part α) [Decidable o.Dom] : (o.toFinset : Set α) = { x | x ∈ o } :=
  Set.ext fun _ => mem_toFinset

end Part

namespace Finset

variable [DecidableEq β] {f g : α →. β} [∀ x, Decidable (f x).Dom] [∀ x, Decidable (g x).Dom]
  {s t : Finset α} {b : β}

/-- Image of `s : Finset α` under a partially defined function `f : α →. β`. -/
def pimage (f : α →. β) [∀ x, Decidable (f x).Dom] (s : Finset α) : Finset β :=
  s.biUnion fun x => (f x).toFinset

@[simp]
theorem mem_pimage : b ∈ s.pimage f ↔ ∃ a ∈ s, b ∈ f a := by
  simp [pimage]

@[simp, norm_cast]
theorem coe_pimage : (s.pimage f : Set β) = f.image s :=
  Set.ext fun _ => mem_pimage

@[simp]
theorem pimage_some (s : Finset α) (f : α → β) [∀ x, Decidable (Part.some <| f x).Dom] :
    (s.pimage fun x => Part.some (f x)) = s.image f := by
  ext
  simp [eq_comm]

theorem pimage_congr (h₁ : s = t) (h₂ : ∀ x ∈ t, f x = g x) : s.pimage f = t.pimage g := by
  aesop

/-- Rewrite `s.pimage f` in terms of `Finset.filter`, `Finset.attach`, and `Finset.image`. -/
theorem pimage_eq_image_filter : s.pimage f =
    {x ∈ s | (f x).Dom}.attach.image
      fun x : { x // x ∈ filter (fun x => (f x).Dom) s } =>
        (f x).get (mem_filter.mp x.coe_prop).2 := by
  aesop (add simp Part.mem_eq)

theorem pimage_union [DecidableEq α] : (s ∪ t).pimage f = s.pimage f ∪ t.pimage f :=
  coe_inj.1 <| by
  simp only [coe_pimage, coe_union, ← PFun.image_union]

@[simp]
theorem pimage_empty : pimage f ∅ = ∅ := by
  ext
  simp

theorem pimage_subset {t : Finset β} : s.pimage f ⊆ t ↔ ∀ x ∈ s, ∀ y ∈ f x, y ∈ t := by
  simp [subset_iff, @forall_swap _ β]

@[mono]
theorem pimage_mono (h : s ⊆ t) : s.pimage f ⊆ t.pimage f :=
  pimage_subset.2 fun x hx _ hy => mem_pimage.2 ⟨x, h hx, hy⟩

theorem pimage_inter [DecidableEq α] : (s ∩ t).pimage f ⊆ s.pimage f ∩ t.pimage f := by
  simp only [← coe_subset, coe_pimage, coe_inter, PFun.image_inter]

end Finset
