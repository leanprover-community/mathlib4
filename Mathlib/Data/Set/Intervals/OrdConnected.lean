/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov

! This file was ported from Lean 3 source module data.set.intervals.ord_connected
! leanprover-community/mathlib commit ba2245edf0c8bb155f1569fd9b9492a9b384cde6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Set.Intervals.UnorderedInterval
import Mathlib.Data.Set.Lattice

/-!
# Order-connected sets

We say that a set `s : Set α` is `OrdConnected` if for all `x y ∈ s` it includes the
interval `[[x, y]]`. If `α` is a `DenselyOrdered` `ConditionallyCompleteLinearOrder` with
the `OrderTopology`, then this condition is equivalent to `IsPreconnected s`. If `α` is a
`LinearOrderedField`, then this condition is also equivalent to `Convex α s`.

In this file we prove that intersection of a family of `OrdConnected` sets is `OrdConnected` and
that all standard intervals are `OrdConnected`.
-/

-- porting note: namespace `Interval` is not found, commented out following line
-- open Interval

open OrderDual (toDual ofDual)

namespace Set

section Preorder

variable {α β : Type _} [Preorder α] [Preorder β] {s t : Set α}

/-- We say that a set `s : Set α` is `OrdConnected` if for all `x y ∈ s` it includes the
interval `[[x, y]]`. If `α` is a `DenselyOrdered` `ConditionallyCompleteLinearOrder` with
the `OrderTopology`, then this condition is equivalent to `IsPreconnected s`. If `α` is a
`LinearOrderedField`, then this condition is also equivalent to `Convex α s`. -/
class OrdConnected (s : Set α) : Prop where
  -- porting note: added docstring
  /-- `s : set α` is `OrdConnected` if for all `x y ∈ s` it includes the interval `[[x, y]]`. -/
  out' ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s) : Icc x y ⊆ s
#align set.ord_connected Set.OrdConnected

theorem OrdConnected.out (h : OrdConnected s) : ∀ ⦃x⦄ (_ : x ∈ s) ⦃y⦄ (_ : y ∈ s), Icc x y ⊆ s :=
  h.1
#align set.ord_connected.out Set.OrdConnected.out

theorem OrdConnected_def : OrdConnected s ↔ ∀ ⦃x⦄ (_ : x ∈ s) ⦃y⦄ (_ : y ∈ s), Icc x y ⊆ s :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩
#align set.ord_connected_def Set.OrdConnected_def

/-- It suffices to prove `[[x, y]] ⊆ s` for `x y ∈ s`, `x ≤ y`. -/
theorem OrdConnected_iff : OrdConnected s ↔ ∀ x ∈ s, ∀ y ∈ s, x ≤ y → Icc x y ⊆ s :=
  OrdConnected_def.trans
    ⟨fun hs _ hx _ hy _ => hs hx hy, fun H x hx y hy _ hz => H x hx y hy (le_trans hz.1 hz.2) hz⟩
#align set.ord_connected_iff Set.OrdConnected_iff

theorem OrdConnected_of_Ioo {α : Type _} [PartialOrder α] {s : Set α}
    (hs : ∀ x ∈ s, ∀ y ∈ s, x < y → Ioo x y ⊆ s) : OrdConnected s := by
  rw [OrdConnected_iff]
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with (rfl | hxy'); · simpa
  rw [← Ioc_insert_left hxy, ← Ioo_insert_right hxy']
  exact insert_subset.2 ⟨hx, insert_subset.2 ⟨hy, hs x hx y hy hxy'⟩⟩
#align set.ord_connected_of_Ioo Set.OrdConnected_of_Ioo

theorem OrdConnected.preimage_mono {f : β → α} (hs : OrdConnected s) (hf : Monotone f) :
    OrdConnected (f ⁻¹' s) :=
  ⟨fun _ hx _ hy _ hz => hs.out hx hy ⟨hf hz.1, hf hz.2⟩⟩
#align set.ord_connected.preimage_mono Set.OrdConnected.preimage_mono

theorem OrdConnected.preimage_anti {f : β → α} (hs : OrdConnected s) (hf : Antitone f) :
    OrdConnected (f ⁻¹' s) :=
  ⟨fun _ hx _ hy _ hz => hs.out hy hx ⟨hf hz.2, hf hz.1⟩⟩
#align set.ord_connected.preimage_anti Set.OrdConnected.preimage_anti

protected theorem Icc_subset (s : Set α) [hs : OrdConnected s] {x y} (hx : x ∈ s) (hy : y ∈ s) :
    Icc x y ⊆ s :=
  hs.out hx hy
#align set.Icc_subset Set.Icc_subset

theorem OrdConnected.inter {s t : Set α} (hs : OrdConnected s) (ht : OrdConnected t) :
    OrdConnected (s ∩ t) :=
  ⟨fun _ hx _ hy => subset_inter (hs.out hx.1 hy.1) (ht.out hx.2 hy.2)⟩
#align set.ord_connected.inter Set.OrdConnected.inter

instance OrdConnected.inter' {s t : Set α} [OrdConnected s] [OrdConnected t] :
    OrdConnected (s ∩ t) :=
  OrdConnected.inter ‹_› ‹_›
#align set.ord_connected.inter' Set.OrdConnected.inter'

theorem OrdConnected.dual {s : Set α} (hs : OrdConnected s) :
    OrdConnected (OrderDual.ofDual ⁻¹' s) :=
  ⟨fun _ hx _ hy _ hz => hs.out hy hx ⟨hz.2, hz.1⟩⟩
#align set.ord_connected.dual Set.OrdConnected.dual

theorem OrdConnected_dual {s : Set α} : OrdConnected (OrderDual.ofDual ⁻¹' s) ↔ OrdConnected s :=
  ⟨fun h => by simpa only [OrdConnected_def] using h.dual, fun h => h.dual⟩
#align set.ord_connected_dual Set.OrdConnected_dual

theorem OrdConnected_interₛ {S : Set (Set α)} (hS : ∀ s ∈ S, OrdConnected s) :
    OrdConnected (⋂₀ S) :=
  ⟨fun _ hx _ hy => subset_interₛ fun s hs => (hS s hs).out (hx s hs) (hy s hs)⟩
#align set.ord_connected_sInter Set.OrdConnected_interₛ

theorem OrdConnected_interᵢ {ι : Sort _} {s : ι → Set α} (hs : ∀ i, OrdConnected (s i)) :
    OrdConnected (⋂ i, s i) :=
  OrdConnected_interₛ <| forall_range_iff.2 hs
#align set.ord_connected_Inter Set.OrdConnected_interᵢ

instance OrdConnected_interᵢ' {ι : Sort _} {s : ι → Set α} [∀ i, OrdConnected (s i)] :
    OrdConnected (⋂ i, s i) :=
  OrdConnected_interᵢ ‹_›
#align set.ord_connected_Inter' Set.OrdConnected_interᵢ'

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i hi) -/
theorem OrdConnected_binterᵢ  {ι : Sort _} {p : ι → Prop} {s : ∀ (i : ι) (_ : p i), Set α}
    (hs : ∀ i hi, OrdConnected (s i hi)) : OrdConnected (⋂ (i) (hi), s i hi) :=
  OrdConnected_interᵢ fun i => OrdConnected_interᵢ <| hs i
#align set.ord_connected_bInter Set.OrdConnected_binterᵢ

theorem OrdConnected_pi {ι : Type _} {α : ι → Type _} [∀ i, Preorder (α i)] {s : Set ι}
    {t : ∀ i, Set (α i)} (h : ∀ i ∈ s, OrdConnected (t i)) : OrdConnected (s.pi t) :=
  ⟨fun _ hx _ hy _ hz i hi => (h i hi).out (hx i hi) (hy i hi) ⟨hz.1 i, hz.2 i⟩⟩
#align set.ord_connected_pi Set.OrdConnected_pi

instance OrdConnected_pi' {ι : Type _} {α : ι → Type _} [∀ i, Preorder (α i)] {s : Set ι}
    {t : ∀ i, Set (α i)} [h : ∀ i, OrdConnected (t i)] : OrdConnected (s.pi t) :=
  OrdConnected_pi fun i _ => h i
#align set.ord_connected_pi' Set.OrdConnected_pi'

@[instance]
theorem OrdConnected_Ici {a : α} : OrdConnected (Ici a) :=
  ⟨fun _ hx _ _ _ hz => le_trans hx hz.1⟩
#align set.ord_connected_Ici Set.OrdConnected_Ici

@[instance]
theorem OrdConnected_Iic {a : α} : OrdConnected (Iic a) :=
  ⟨fun _ _ _ hy _ hz => le_trans hz.2 hy⟩
#align set.ord_connected_Iic Set.OrdConnected_Iic

@[instance]
theorem OrdConnected_Ioi {a : α} : OrdConnected (Ioi a) :=
  ⟨fun _ hx _ _ _ hz => lt_of_lt_of_le hx hz.1⟩
#align set.ord_connected_Ioi Set.OrdConnected_Ioi

@[instance]
theorem OrdConnected_Iio {a : α} : OrdConnected (Iio a) :=
  ⟨fun _ _ _ hy _ hz => lt_of_le_of_lt hz.2 hy⟩
#align set.OrdConnected_Iio Set.OrdConnected_Iio

@[instance]
theorem OrdConnected_Icc {a b : α} : OrdConnected (Icc a b) :=
  OrdConnected_Ici.inter OrdConnected_Iic
#align set.ord_connected_Icc Set.OrdConnected_Icc

@[instance]
theorem OrdConnected_Ico {a b : α} : OrdConnected (Ico a b) :=
  OrdConnected_Ici.inter OrdConnected_Iio
#align set.ord_connected_Ico Set.OrdConnected_Ico

@[instance]
theorem OrdConnected_Ioc {a b : α} : OrdConnected (Ioc a b) :=
  OrdConnected_Ioi.inter OrdConnected_Iic
#align set.ord_connected_Ioc Set.OrdConnected_Ioc

@[instance]
theorem OrdConnected_Ioo {a b : α} : OrdConnected (Ioo a b) :=
  OrdConnected_Ioi.inter OrdConnected_Iio
#align set.ord_connected_Ioo Set.OrdConnected_Ioo

@[instance]
theorem OrdConnected_singleton {α : Type _} [PartialOrder α] {a : α} :
    OrdConnected ({a} : Set α) := by
  rw [← Icc_self]
  exact OrdConnected_Icc
#align set.ord_connected_singleton Set.OrdConnected_singleton

@[instance]
theorem OrdConnected_empty : OrdConnected (∅ : Set α) :=
  ⟨fun _ => False.elim⟩
#align set.ord_connected_empty Set.OrdConnected_empty

@[instance]
theorem OrdConnected_univ : OrdConnected (univ : Set α) :=
  ⟨fun _ _ _ _ => subset_univ _⟩
#align set.ord_connected_univ Set.OrdConnected_univ

/-- In a dense order `α`, the subtype from an `OrdConnected` set is also densely ordered. -/
instance [DenselyOrdered α] {s : Set α} [hs : OrdConnected s] : DenselyOrdered s :=
  ⟨fun a b (h : (a : α) < b) =>
    let ⟨x, H⟩ := exists_between h
    ⟨⟨x, (hs.out a.2 b.2) (Ioo_subset_Icc_self H)⟩, H⟩⟩

@[instance]
theorem OrdConnected_preimage {F : Type _} [OrderHomClass F α β] (f : F) {s : Set β}
    [hs : OrdConnected s] : OrdConnected (f ⁻¹' s) :=
  ⟨fun _ hx _ hy _ hz => hs.out hx hy ⟨OrderHomClass.mono _ hz.1, OrderHomClass.mono _ hz.2⟩⟩
#align set.ord_connected_preimage Set.OrdConnected_preimage

@[instance]
theorem OrdConnected_image {E : Type _} [OrderIsoClass E α β] (e : E) {s : Set α}
    [hs : OrdConnected s] : OrdConnected (e '' s) := by
  erw [(e : α ≃o β).image_eq_preimage]
  apply OrdConnected_preimage (e : α ≃o β).symm
#align set.ord_connected_image Set.OrdConnected_image

-- porting note: split up `simp_rw [← image_univ, OrdConnected_image e]`, would not work otherwise
@[instance]
theorem OrdConnected_range {E : Type _} [OrderIsoClass E α β] (e : E) : OrdConnected (range e) := by
  simp_rw [← image_univ]
  exact OrdConnected_image (e : α ≃o β)
#align set.ord_connected_range Set.OrdConnected_range

@[simp]
theorem dual_OrdConnected_iff {s : Set α} : OrdConnected (ofDual ⁻¹' s) ↔ OrdConnected s := by
  simp_rw [OrdConnected_def, toDual.surjective.forall, dual_Icc, Subtype.forall']
  exact forall_swap
#align set.dual_ord_connected_iff Set.dual_OrdConnected_iff

@[instance]
theorem dual_OrdConnected {s : Set α} [OrdConnected s] : OrdConnected (ofDual ⁻¹' s) :=
  dual_OrdConnected_iff.2 ‹_›
#align set.dual_ord_connected Set.dual_OrdConnected

end Preorder

section LinearOrder

variable {α : Type _} [LinearOrder α] {s : Set α} {x : α}

@[instance]
theorem OrdConnected_interval {a b : α} : OrdConnected [[a, b]] :=
  OrdConnected_Icc
#align set.ord_connected_interval Set.OrdConnected_interval

@[instance]
theorem OrdConnected_interval_oc {a b : α} : OrdConnected (Ι a b) :=
  OrdConnected_Ioc
#align set.ord_connected_interval_oc Set.OrdConnected_interval_oc

theorem OrdConnected.interval_subset (hs : OrdConnected s) ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s) :
    [[x, y]] ⊆ s :=
  hs.out (min_rec' (· ∈ s) hx hy) (max_rec' (· ∈ s) hx hy)
#align set.ord_connected.interval_subset Set.OrdConnected.interval_subset

theorem OrdConnected.interval_oc_subset (hs : OrdConnected s) ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s) :
    Ι x y ⊆ s :=
  Ioc_subset_Icc_self.trans <| hs.interval_subset hx hy
#align set.ord_connected.interval_oc_subset Set.OrdConnected.interval_oc_subset

theorem OrdConnected_iff_interval_subset :
    OrdConnected s ↔ ∀ ⦃x⦄ (_ : x ∈ s) ⦃y⦄ (_ : y ∈ s), [[x, y]] ⊆ s :=
  ⟨fun h => h.interval_subset, fun H => ⟨fun _ hx _ hy => Icc_subset_interval.trans <| H hx hy⟩⟩
#align set.ord_connected_iff_interval_subset Set.OrdConnected_iff_interval_subset

theorem OrdConnected_of_interval_subset_left (h : ∀ y ∈ s, [[x, y]] ⊆ s) : OrdConnected s :=
  OrdConnected_iff_interval_subset.2 fun y hy z hz =>
    calc
      [[y, z]] ⊆ [[y, x]] ∪ [[x, z]] := interval_subset_interval_union_interval
      _ = [[x, y]] ∪ [[x, z]] := by rw [interval_swap]
      _ ⊆ s := union_subset (h y hy) (h z hz)
#align set.ord_connected_of_interval_subset_left Set.OrdConnected_of_interval_subset_left

theorem OrdConnected_iff_interval_subset_left (hx : x ∈ s) :
    OrdConnected s ↔ ∀ ⦃y⦄, y ∈ s → [[x, y]] ⊆ s :=
  ⟨fun hs => hs.interval_subset hx, OrdConnected_of_interval_subset_left⟩
#align set.ord_connected_iff_interval_subset_left Set.OrdConnected_iff_interval_subset_left

theorem OrdConnected_iff_interval_subset_right (hx : x ∈ s) :
    OrdConnected s ↔ ∀ ⦃y⦄, y ∈ s → [[y, x]] ⊆ s := by
  simp_rw [OrdConnected_iff_interval_subset_left hx, interval_swap]
#align set.ord_connected_iff_interval_subset_right Set.OrdConnected_iff_interval_subset_right
