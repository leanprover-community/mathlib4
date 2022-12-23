/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov

! This file was ported from Lean 3 source module data.set.intervals.ord_connected
! leanprover-community/mathlib commit ba2245edf0c8bb155f1569fd9b9492a9b384cde6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.Intervals.UnorderedInterval
import Mathbin.Data.Set.Lattice

/-!
# Order-connected sets

We say that a set `s : set α` is `ord_connected` if for all `x y ∈ s` it includes the
interval `[x, y]`. If `α` is a `densely_ordered` `conditionally_complete_linear_order` with
the `order_topology`, then this condition is equivalent to `is_preconnected s`. If `α` is a
`linear_ordered_field`, then this condition is also equivalent to `convex α s`.

In this file we prove that intersection of a family of `ord_connected` sets is `ord_connected` and
that all standard intervals are `ord_connected`.
-/


open Interval

open OrderDual (toDual ofDual)

namespace Set

section Preorder

variable {α β : Type _} [Preorder α] [Preorder β] {s t : Set α}

/-- We say that a set `s : set α` is `ord_connected` if for all `x y ∈ s` it includes the
interval `[x, y]`. If `α` is a `densely_ordered` `conditionally_complete_linear_order` with
the `order_topology`, then this condition is equivalent to `is_preconnected s`. If `α` is a
`linear_ordered_field`, then this condition is also equivalent to `convex α s`.
-/
class OrdConnected (s : Set α) : Prop where
  out' ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s) : Icc x y ⊆ s
#align set.ord_connected Set.OrdConnected

theorem OrdConnected.out (h : OrdConnected s) : ∀ ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s), Icc x y ⊆ s :=
  h.1
#align set.ord_connected.out Set.OrdConnected.out

theorem ord_connected_def : OrdConnected s ↔ ∀ ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s), Icc x y ⊆ s :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩
#align set.ord_connected_def Set.ord_connected_def

/-- It suffices to prove `[x, y] ⊆ s` for `x y ∈ s`, `x ≤ y`. -/
theorem ord_connected_iff : OrdConnected s ↔ ∀ x ∈ s, ∀ y ∈ s, x ≤ y → Icc x y ⊆ s :=
  ord_connected_def.trans
    ⟨fun hs x hx y hy hxy => hs hx hy, fun H x hx y hy z hz => H x hx y hy (le_trans hz.1 hz.2) hz⟩
#align set.ord_connected_iff Set.ord_connected_iff

theorem ord_connected_of_Ioo {α : Type _} [PartialOrder α] {s : Set α}
    (hs : ∀ x ∈ s, ∀ y ∈ s, x < y → Ioo x y ⊆ s) : OrdConnected s := by
  rw [ord_connected_iff]
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with (rfl | hxy'); · simpa
  rw [← Ioc_insert_left hxy, ← Ioo_insert_right hxy']
  exact insert_subset.2 ⟨hx, insert_subset.2 ⟨hy, hs x hx y hy hxy'⟩⟩
#align set.ord_connected_of_Ioo Set.ord_connected_of_Ioo

theorem OrdConnected.preimage_mono {f : β → α} (hs : OrdConnected s) (hf : Monotone f) :
    OrdConnected (f ⁻¹' s) :=
  ⟨fun x hx y hy z hz => hs.out hx hy ⟨hf hz.1, hf hz.2⟩⟩
#align set.ord_connected.preimage_mono Set.OrdConnected.preimage_mono

theorem OrdConnected.preimage_anti {f : β → α} (hs : OrdConnected s) (hf : Antitone f) :
    OrdConnected (f ⁻¹' s) :=
  ⟨fun x hx y hy z hz => hs.out hy hx ⟨hf hz.2, hf hz.1⟩⟩
#align set.ord_connected.preimage_anti Set.OrdConnected.preimage_anti

protected theorem Icc_subset (s : Set α) [hs : OrdConnected s] {x y} (hx : x ∈ s) (hy : y ∈ s) :
    Icc x y ⊆ s :=
  hs.out hx hy
#align set.Icc_subset Set.Icc_subset

theorem OrdConnected.inter {s t : Set α} (hs : OrdConnected s) (ht : OrdConnected t) :
    OrdConnected (s ∩ t) :=
  ⟨fun x hx y hy => subset_inter (hs.out hx.1 hy.1) (ht.out hx.2 hy.2)⟩
#align set.ord_connected.inter Set.OrdConnected.inter

instance OrdConnected.inter' {s t : Set α} [OrdConnected s] [OrdConnected t] :
    OrdConnected (s ∩ t) :=
  OrdConnected.inter ‹_› ‹_›
#align set.ord_connected.inter' Set.OrdConnected.inter'

theorem OrdConnected.dual {s : Set α} (hs : OrdConnected s) :
    OrdConnected (OrderDual.ofDual ⁻¹' s) :=
  ⟨fun x hx y hy z hz => hs.out hy hx ⟨hz.2, hz.1⟩⟩
#align set.ord_connected.dual Set.OrdConnected.dual

theorem ord_connected_dual {s : Set α} : OrdConnected (OrderDual.ofDual ⁻¹' s) ↔ OrdConnected s :=
  ⟨fun h => by simpa only [ord_connected_def] using h.dual, fun h => h.dual⟩
#align set.ord_connected_dual Set.ord_connected_dual

theorem ord_connected_sInter {S : Set (Set α)} (hS : ∀ s ∈ S, OrdConnected s) :
    OrdConnected (⋂₀ S) :=
  ⟨fun x hx y hy => subset_sInter fun s hs => (hS s hs).out (hx s hs) (hy s hs)⟩
#align set.ord_connected_sInter Set.ord_connected_sInter

theorem ord_connected_Inter {ι : Sort _} {s : ι → Set α} (hs : ∀ i, OrdConnected (s i)) :
    OrdConnected (⋂ i, s i) :=
  ord_connected_sInter <| forall_range_iff.2 hs
#align set.ord_connected_Inter Set.ord_connected_Inter

instance ord_connected_Inter' {ι : Sort _} {s : ι → Set α} [∀ i, OrdConnected (s i)] :
    OrdConnected (⋂ i, s i) :=
  ord_connected_Inter ‹_›
#align set.ord_connected_Inter' Set.ord_connected_Inter'

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i hi) -/
theorem ord_connected_bInter {ι : Sort _} {p : ι → Prop} {s : ∀ (i : ι) (hi : p i), Set α}
    (hs : ∀ i hi, OrdConnected (s i hi)) : OrdConnected (⋂ (i) (hi), s i hi) :=
  ord_connected_Inter fun i => ord_connected_Inter <| hs i
#align set.ord_connected_bInter Set.ord_connected_bInter

theorem ord_connected_pi {ι : Type _} {α : ι → Type _} [∀ i, Preorder (α i)] {s : Set ι}
    {t : ∀ i, Set (α i)} (h : ∀ i ∈ s, OrdConnected (t i)) : OrdConnected (s.pi t) :=
  ⟨fun x hx y hy z hz i hi => (h i hi).out (hx i hi) (hy i hi) ⟨hz.1 i, hz.2 i⟩⟩
#align set.ord_connected_pi Set.ord_connected_pi

instance ord_connected_pi' {ι : Type _} {α : ι → Type _} [∀ i, Preorder (α i)] {s : Set ι}
    {t : ∀ i, Set (α i)} [h : ∀ i, OrdConnected (t i)] : OrdConnected (s.pi t) :=
  ord_connected_pi fun i hi => h i
#align set.ord_connected_pi' Set.ord_connected_pi'

@[instance]
theorem ord_connected_Ici {a : α} : OrdConnected (Ici a) :=
  ⟨fun x hx y hy z hz => le_trans hx hz.1⟩
#align set.ord_connected_Ici Set.ord_connected_Ici

@[instance]
theorem ord_connected_Iic {a : α} : OrdConnected (Iic a) :=
  ⟨fun x hx y hy z hz => le_trans hz.2 hy⟩
#align set.ord_connected_Iic Set.ord_connected_Iic

@[instance]
theorem ord_connected_Ioi {a : α} : OrdConnected (Ioi a) :=
  ⟨fun x hx y hy z hz => lt_of_lt_of_le hx hz.1⟩
#align set.ord_connected_Ioi Set.ord_connected_Ioi

@[instance]
theorem ord_connected_Iio {a : α} : OrdConnected (Iio a) :=
  ⟨fun x hx y hy z hz => lt_of_le_of_lt hz.2 hy⟩
#align set.ord_connected_Iio Set.ord_connected_Iio

@[instance]
theorem ord_connected_Icc {a b : α} : OrdConnected (Icc a b) :=
  ord_connected_Ici.inter ord_connected_Iic
#align set.ord_connected_Icc Set.ord_connected_Icc

@[instance]
theorem ord_connected_Ico {a b : α} : OrdConnected (Ico a b) :=
  ord_connected_Ici.inter ord_connected_Iio
#align set.ord_connected_Ico Set.ord_connected_Ico

@[instance]
theorem ord_connected_Ioc {a b : α} : OrdConnected (Ioc a b) :=
  ord_connected_Ioi.inter ord_connected_Iic
#align set.ord_connected_Ioc Set.ord_connected_Ioc

@[instance]
theorem ord_connected_Ioo {a b : α} : OrdConnected (Ioo a b) :=
  ord_connected_Ioi.inter ord_connected_Iio
#align set.ord_connected_Ioo Set.ord_connected_Ioo

@[instance]
theorem ord_connected_singleton {α : Type _} [PartialOrder α] {a : α} :
    OrdConnected ({a} : Set α) := by 
  rw [← Icc_self]
  exact ord_connected_Icc
#align set.ord_connected_singleton Set.ord_connected_singleton

@[instance]
theorem ord_connected_empty : OrdConnected (∅ : Set α) :=
  ⟨fun x => False.elim⟩
#align set.ord_connected_empty Set.ord_connected_empty

@[instance]
theorem ord_connected_univ : OrdConnected (univ : Set α) :=
  ⟨fun _ _ _ _ => subset_univ _⟩
#align set.ord_connected_univ Set.ord_connected_univ

/-- In a dense order `α`, the subtype from an `ord_connected` set is also densely ordered. -/
instance [DenselyOrdered α] {s : Set α} [hs : OrdConnected s] : DenselyOrdered s :=
  ⟨fun a b (h : (a : α) < b) =>
    let ⟨x, H⟩ := exists_between h
    ⟨⟨x, (hs.out a.2 b.2) (Ioo_subset_Icc_self H)⟩, H⟩⟩

@[instance]
theorem ord_connected_preimage {F : Type _} [OrderHomClass F α β] (f : F) {s : Set β}
    [hs : OrdConnected s] : OrdConnected (f ⁻¹' s) :=
  ⟨fun x hx y hy z hz => hs.out hx hy ⟨OrderHomClass.mono _ hz.1, OrderHomClass.mono _ hz.2⟩⟩
#align set.ord_connected_preimage Set.ord_connected_preimage

@[instance]
theorem ord_connected_image {E : Type _} [OrderIsoClass E α β] (e : E) {s : Set α}
    [hs : OrdConnected s] : OrdConnected (e '' s) := by
  erw [(e : α ≃o β).image_eq_preimage]
  apply ord_connected_preimage
#align set.ord_connected_image Set.ord_connected_image

@[instance]
theorem ord_connected_range {E : Type _} [OrderIsoClass E α β] (e : E) : OrdConnected (range e) :=
  by simp_rw [← image_univ, ord_connected_image e]
#align set.ord_connected_range Set.ord_connected_range

@[simp]
theorem dual_ord_connected_iff {s : Set α} : OrdConnected (of_dual ⁻¹' s) ↔ OrdConnected s := by
  simp_rw [ord_connected_def, to_dual.surjective.forall, dual_Icc, Subtype.forall']
  exact forall_swap
#align set.dual_ord_connected_iff Set.dual_ord_connected_iff

@[instance]
theorem dual_ord_connected {s : Set α} [OrdConnected s] : OrdConnected (of_dual ⁻¹' s) :=
  dual_ord_connected_iff.2 ‹_›
#align set.dual_ord_connected Set.dual_ord_connected

end Preorder

section LinearOrder

variable {α : Type _} [LinearOrder α] {s : Set α} {x : α}

@[instance]
theorem ord_connected_interval {a b : α} : OrdConnected [a, b] :=
  ord_connected_Icc
#align set.ord_connected_interval Set.ord_connected_interval

@[instance]
theorem ord_connected_interval_oc {a b : α} : OrdConnected (Ι a b) :=
  ord_connected_Ioc
#align set.ord_connected_interval_oc Set.ord_connected_interval_oc

theorem OrdConnected.interval_subset (hs : OrdConnected s) ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s) :
    [x, y] ⊆ s :=
  hs.out (min_rec' (· ∈ s) hx hy) (max_rec' (· ∈ s) hx hy)
#align set.ord_connected.interval_subset Set.OrdConnected.interval_subset

theorem OrdConnected.interval_oc_subset (hs : OrdConnected s) ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s) :
    Ι x y ⊆ s :=
  Ioc_subset_Icc_self.trans <| hs.interval_subset hx hy
#align set.ord_connected.interval_oc_subset Set.OrdConnected.interval_oc_subset

theorem ord_connected_iff_interval_subset :
    OrdConnected s ↔ ∀ ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s), [x, y] ⊆ s :=
  ⟨fun h => h.interval_subset, fun H => ⟨fun x hx y hy => Icc_subset_interval.trans <| H hx hy⟩⟩
#align set.ord_connected_iff_interval_subset Set.ord_connected_iff_interval_subset

theorem ord_connected_of_interval_subset_left (h : ∀ y ∈ s, [x, y] ⊆ s) : OrdConnected s :=
  ord_connected_iff_interval_subset.2 fun y hy z hz =>
    calc
      [y, z] ⊆ [y, x] ∪ [x, z] := interval_subset_interval_union_interval
      _ = [x, y] ∪ [x, z] := by rw [interval_swap]
      _ ⊆ s := union_subset (h y hy) (h z hz)
      
#align set.ord_connected_of_interval_subset_left Set.ord_connected_of_interval_subset_left

theorem ord_connected_iff_interval_subset_left (hx : x ∈ s) :
    OrdConnected s ↔ ∀ ⦃y⦄, y ∈ s → [x, y] ⊆ s :=
  ⟨fun hs => hs.interval_subset hx, ord_connected_of_interval_subset_left⟩
#align set.ord_connected_iff_interval_subset_left Set.ord_connected_iff_interval_subset_left

theorem ord_connected_iff_interval_subset_right (hx : x ∈ s) :
    OrdConnected s ↔ ∀ ⦃y⦄, y ∈ s → [y, x] ⊆ s := by
  simp_rw [ord_connected_iff_interval_subset_left hx, interval_swap]
#align set.ord_connected_iff_interval_subset_right Set.ord_connected_iff_interval_subset_right

end LinearOrder

end Set

