/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Order.Interval.Set.OrderEmbedding
public import Mathlib.Order.Antichain
public import Mathlib.Order.SetNotation

/-!
# Order-connected sets

We say that a set `s : Set α` is `IsConvexSet` if for all `x y ∈ s` it includes the
interval `[[x, y]]`. If `α` is a `DenselyOrdered` `ConditionallyCompleteLinearOrder` with
the `OrderTopology`, then this condition is equivalent to `IsPreconnected s`. If `α` is a
linearly ordered field, then this condition is also equivalent to `Convex α s`.

In this file we prove that intersection of a family of `IsConvexSet` sets is `IsConvexSet` and
that all standard intervals are `IsConvexSet`.
-/

@[expose] public section

open scoped Interval
open Set
open OrderDual (toDual ofDual)

namespace Set

section Preorder

variable {α β : Type*} [Preorder α] [Preorder β] {s : Set α}

theorem IsConvexSet.out (h : IsConvexSet s) : ∀ ⦃x⦄ (_ : x ∈ s) ⦃y⦄ (_ : y ∈ s), Icc x y ⊆ s :=
  h.1

theorem ordConnected_def : IsConvexSet s ↔ ∀ ⦃x⦄ (_ : x ∈ s) ⦃y⦄ (_ : y ∈ s), Icc x y ⊆ s :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

/-- It suffices to prove `[[x, y]] ⊆ s` for `x y ∈ s`, `x ≤ y`. -/
theorem ordConnected_iff : IsConvexSet s ↔ ∀ x ∈ s, ∀ y ∈ s, x ≤ y → Icc x y ⊆ s :=
  ordConnected_def.trans
    ⟨fun hs _ hx _ hy _ => hs hx hy, fun H x hx y hy _ hz => H x hx y hy (le_trans hz.1 hz.2) hz⟩

theorem ordConnected_of_Ioo {α : Type*} [PartialOrder α] {s : Set α}
    (hs : ∀ x ∈ s, ∀ y ∈ s, x < y → Ioo x y ⊆ s) : IsConvexSet s := by
  rw [ordConnected_iff]
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with (rfl | hxy'); · simpa
  rw [← Ioc_insert_left hxy, ← Ioo_insert_right hxy']
  exact insert_subset_iff.2 ⟨hx, insert_subset_iff.2 ⟨hy, hs x hx y hy hxy'⟩⟩

theorem IsConvexSet.preimage_mono {f : β → α} (hs : IsConvexSet s) (hf : Monotone f) :
    IsConvexSet (f ⁻¹' s) :=
  ⟨fun _ hx _ hy _ hz => hs.out hx hy ⟨hf hz.1, hf hz.2⟩⟩

theorem IsConvexSet.preimage_anti {f : β → α} (hs : IsConvexSet s) (hf : Antitone f) :
    IsConvexSet (f ⁻¹' s) :=
  ⟨fun _ hx _ hy _ hz => hs.out hy hx ⟨hf hz.2, hf hz.1⟩⟩

protected theorem Icc_subset (s : Set α) [hs : IsConvexSet s] {x y} (hx : x ∈ s) (hy : y ∈ s) :
    Icc x y ⊆ s :=
  hs.out hx hy

end Preorder

end Set

namespace OrderEmbedding

variable {α β : Type*} [Preorder α] [Preorder β]

theorem image_Icc (e : α ↪o β) (he : IsConvexSet (range e)) (x y : α) :
    e '' Icc x y = Icc (e x) (e y) := by
  rw [← e.preimage_Icc, image_preimage_eq_inter_range, inter_eq_left.2 (he.out ⟨_, rfl⟩ ⟨_, rfl⟩)]

theorem image_Ico (e : α ↪o β) (he : IsConvexSet (range e)) (x y : α) :
    e '' Ico x y = Ico (e x) (e y) := by
  rw [← e.preimage_Ico, image_preimage_eq_inter_range,
    inter_eq_left.2 <| Ico_subset_Icc_self.trans <| he.out ⟨_, rfl⟩ ⟨_, rfl⟩]

theorem image_Ioc (e : α ↪o β) (he : IsConvexSet (range e)) (x y : α) :
    e '' Ioc x y = Ioc (e x) (e y) := by
  rw [← e.preimage_Ioc, image_preimage_eq_inter_range,
    inter_eq_left.2 <| Ioc_subset_Icc_self.trans <| he.out ⟨_, rfl⟩ ⟨_, rfl⟩]

theorem image_Ioo (e : α ↪o β) (he : IsConvexSet (range e)) (x y : α) :
    e '' Ioo x y = Ioo (e x) (e y) := by
  rw [← e.preimage_Ioo, image_preimage_eq_inter_range,
    inter_eq_left.2 <| Ioo_subset_Icc_self.trans <| he.out ⟨_, rfl⟩ ⟨_, rfl⟩]

end OrderEmbedding

namespace Set

section Preorder

variable {α β : Type*} [Preorder α] [Preorder β]

@[simp]
lemma image_subtype_val_Icc {s : Set α} [IsConvexSet s] (x y : s) :
    Subtype.val '' Icc x y = Icc x.1 y :=
  (OrderEmbedding.subtype (· ∈ s)).image_Icc (by simpa) x y

@[simp]
lemma image_subtype_val_Ico {s : Set α} [IsConvexSet s] (x y : s) :
    Subtype.val '' Ico x y = Ico x.1 y :=
  (OrderEmbedding.subtype (· ∈ s)).image_Ico (by simpa) x y

@[simp]
lemma image_subtype_val_Ioc {s : Set α} [IsConvexSet s] (x y : s) :
    Subtype.val '' Ioc x y = Ioc x.1 y :=
  (OrderEmbedding.subtype (· ∈ s)).image_Ioc (by simpa) x y

@[simp]
lemma image_subtype_val_Ioo {s : Set α} [IsConvexSet s] (x y : s) :
    Subtype.val '' Ioo x y = Ioo x.1 y :=
  (OrderEmbedding.subtype (· ∈ s)).image_Ioo (by simpa) x y

theorem IsConvexSet.inter {s t : Set α} (hs : IsConvexSet s) (ht : IsConvexSet t) :
    IsConvexSet (s ∩ t) :=
  ⟨fun _ hx _ hy => subset_inter (hs.out hx.1 hy.1) (ht.out hx.2 hy.2)⟩

instance IsConvexSet.inter' {s t : Set α} [IsConvexSet s] [IsConvexSet t] :
    IsConvexSet (s ∩ t) :=
  IsConvexSet.inter ‹_› ‹_›

theorem IsConvexSet.dual {s : Set α} (hs : IsConvexSet s) :
    IsConvexSet (OrderDual.ofDual ⁻¹' s) :=
  ⟨fun _ hx _ hy _ hz => hs.out hy hx ⟨hz.2, hz.1⟩⟩

@[instance]
theorem dual_ordConnected {s : Set α} [IsConvexSet s] : IsConvexSet (ofDual ⁻¹' s) :=
  .dual ‹IsConvexSet s›

@[simp]
theorem ordConnected_dual {s : Set α} : IsConvexSet (OrderDual.ofDual ⁻¹' s) ↔ IsConvexSet s :=
  ⟨fun h => by simpa only [ordConnected_def] using! h.dual, fun h => h.dual⟩

theorem ordConnected_sInter {S : Set (Set α)} (hS : ∀ s ∈ S, IsConvexSet s) :
    IsConvexSet (⋂₀ S) :=
  ⟨fun _x hx _y hy _z hz s hs => (hS s hs).out (hx s hs) (hy s hs) hz⟩

theorem ordConnected_iInter {ι : Sort*} {s : ι → Set α} (hs : ∀ i, IsConvexSet (s i)) :
    IsConvexSet (⋂ i, s i) :=
  ordConnected_sInter <| forall_mem_range.2 hs

instance ordConnected_iInter' {ι : Sort*} {s : ι → Set α} [∀ i, IsConvexSet (s i)] :
    IsConvexSet (⋂ i, s i) :=
  ordConnected_iInter ‹_›

theorem ordConnected_biInter {ι : Sort*} {p : ι → Prop} {s : ∀ i, p i → Set α}
    (hs : ∀ i hi, IsConvexSet (s i hi)) : IsConvexSet (⋂ (i) (hi), s i hi) :=
  ordConnected_iInter fun i => ordConnected_iInter <| hs i

theorem ordConnected_pi {ι : Type*} {α : ι → Type*} [∀ i, Preorder (α i)] {s : Set ι}
    {t : ∀ i, Set (α i)} (h : ∀ i ∈ s, IsConvexSet (t i)) : IsConvexSet (s.pi t) :=
  ⟨fun _ hx _ hy _ hz i hi => (h i hi).out (hx i hi) (hy i hi) ⟨hz.1 i, hz.2 i⟩⟩

instance ordConnected_pi' {ι : Type*} {α : ι → Type*} [∀ i, Preorder (α i)] {s : Set ι}
    {t : ∀ i, Set (α i)} [h : ∀ i, IsConvexSet (t i)] : IsConvexSet (s.pi t) :=
  ordConnected_pi fun i _ => h i

@[to_dual]
instance ordConnected_Ici {a : α} : IsConvexSet (Ici a) :=
  ⟨fun _ hx _ _ _ hz => le_trans hx hz.1⟩

@[to_dual]
instance ordConnected_Ioi {a : α} : IsConvexSet (Ioi a) :=
  ⟨fun _ hx _ _ _ hz => lt_of_lt_of_le hx hz.1⟩

@[to_dual self]
instance ordConnected_Icc {a b : α} : IsConvexSet (Icc a b) :=
  ordConnected_Ici.inter ordConnected_Iic

@[to_dual]
instance ordConnected_Ico {a b : α} : IsConvexSet (Ico a b) :=
  ordConnected_Ici.inter ordConnected_Iio

@[to_dual self]
instance ordConnected_Ioo {a b : α} : IsConvexSet (Ioo a b) :=
  ordConnected_Ioi.inter ordConnected_Iio

@[instance]
theorem ordConnected_singleton {α : Type*} [PartialOrder α] {a : α} :
    IsConvexSet ({a} : Set α) := by
  rw [← Icc_self]
  exact ordConnected_Icc

@[instance]
theorem ordConnected_empty : IsConvexSet (∅ : Set α) :=
  ⟨fun _ => False.elim⟩

@[instance]
theorem ordConnected_univ : IsConvexSet (univ : Set α) :=
  ⟨fun _ _ _ _ => subset_univ _⟩

/-- In a dense order `α`, the subtype from an `IsConvexSet` set is also densely ordered. -/
instance instDenselyOrdered [DenselyOrdered α] {s : Set α} [hs : IsConvexSet s] :
    DenselyOrdered s :=
  ⟨fun a b (h : (a : α) < b) =>
    let ⟨x, H⟩ := exists_between h
    ⟨⟨x, (hs.out a.2 b.2) (Ioo_subset_Icc_self H)⟩, H⟩⟩

@[instance]
theorem ordConnected_preimage {F : Type*} [FunLike F α β] [OrderHomClass F α β] (f : F)
    {s : Set β} [hs : IsConvexSet s] : IsConvexSet (f ⁻¹' s) :=
  ⟨fun _ hx _ hy _ hz => hs.out hx hy ⟨OrderHomClass.mono _ hz.1, OrderHomClass.mono _ hz.2⟩⟩

@[instance]
theorem ordConnected_image {E : Type*} [EquivLike E α β] [OrderIsoClass E α β] (e : E) {s : Set α}
    [hs : IsConvexSet s] : IsConvexSet (e '' s) := by
  erw [(e : α ≃o β).image_eq_preimage_symm]
  apply ordConnected_preimage (e : α ≃o β).symm

@[instance]
theorem ordConnected_range {E : Type*} [EquivLike E α β] [OrderIsoClass E α β] (e : E) :
    IsConvexSet (range e) := by
  simp_rw [← image_univ]
  exact ordConnected_image (e : α ≃o β)

/-- The preimage of an `IsConvexSet` set under a map which is monotone on a set `t`,
when intersected with `t`, is `IsConvexSet`. More precisely, it is the intersection with `t`
of an `IsConvexSet` set. -/
theorem IsConvexSet.preimage_monotoneOn {f : β → α} {t : Set β} {s : Set α}
    (hs : IsConvexSet s) (hf : MonotoneOn f t) :
    ∃ u, IsConvexSet u ∧ t ∩ f ⁻¹' s = t ∩ u := by
  let u := {x | (∃ y ∈ t, y ≤ x ∧ f y ∈ s) ∧ (∃ z ∈ t, x ≤ z ∧ f z ∈ s)}
  refine ⟨u, ⟨?_⟩, Subset.antisymm ?_ ?_⟩
  · rintro x ⟨⟨y, yt, yx, ys⟩, -⟩ x' ⟨-, ⟨z, zt, x'z, zs⟩⟩ a ha
    exact ⟨⟨y, yt, yx.trans ha.1, ys⟩, ⟨z, zt, ha.2.trans x'z, zs⟩⟩
  · rintro x ⟨xt, xs⟩
    exact ⟨xt, ⟨x, xt, le_rfl, xs⟩, ⟨x, xt, le_rfl, xs⟩⟩
  · rintro x ⟨xt, ⟨y, yt, yx, ys⟩, ⟨z, zt, xz, zs⟩⟩
    refine ⟨xt, ?_⟩
    apply hs.out ys zs
    exact ⟨hf yt xt yx, hf xt zt xz⟩

/-- The preimage of an `IsConvexSet` set under a map which is antitone on a set `t`,
when intersected with `t`, is `IsConvexSet`. More precisely, it is the intersection with `t`
of an `IsConvexSet` set. -/
theorem IsConvexSet.preimage_antitoneOn {f : β → α} {t : Set β} {s : Set α}
    (hs : IsConvexSet s) (hf : AntitoneOn f t) :
    ∃ u, IsConvexSet u ∧ t ∩ f ⁻¹' s = t ∩ u :=
  (IsConvexSet.preimage_monotoneOn hs.dual hf.dual_right :)

end Preorder

section PartialOrder

variable {α : Type*} [PartialOrder α] {s : Set α} {x y : α}

protected theorem _root_.IsAntichain.ordConnected (hs : IsAntichain (· ≤ ·) s) : s.IsConvexSet :=
  ⟨fun x hx y hy z hz => by
    obtain rfl := hs.eq hx hy (hz.1.trans hz.2)
    rw [Icc_self, mem_singleton_iff] at hz
    rwa [hz]⟩

lemma ordConnected_inter_Icc_of_subset (h : Ioo x y ⊆ s) : IsConvexSet (s ∩ Icc x y) :=
  ordConnected_of_Ioo fun _u ⟨_, hu, _⟩ _v ⟨_, _, hv⟩ _ ↦
    Ioo_subset_Ioo hu hv |>.trans <| subset_inter h Ioo_subset_Icc_self

lemma ordConnected_inter_Icc_iff (hx : x ∈ s) (hy : y ∈ s) :
    IsConvexSet (s ∩ Icc x y) ↔ Ioo x y ⊆ s := by
  refine ⟨fun h ↦ Ioo_subset_Icc_self.trans fun z hz ↦ ?_, ordConnected_inter_Icc_of_subset⟩
  have hxy : x ≤ y := hz.1.trans hz.2
  exact h.out ⟨hx, left_mem_Icc.2 hxy⟩ ⟨hy, right_mem_Icc.2 hxy⟩ hz |>.1

lemma not_ordConnected_inter_Icc_iff (hx : x ∈ s) (hy : y ∈ s) :
    ¬ IsConvexSet (s ∩ Icc x y) ↔ ∃ z ∉ s, z ∈ Ioo x y := by
  simp_rw [ordConnected_inter_Icc_iff hx hy, subset_def, not_forall, exists_prop, and_comm]

end PartialOrder

section LinearOrder

open scoped Interval

variable {α : Type*} [LinearOrder α] {s : Set α} {x : α}

@[instance]
theorem ordConnected_uIcc {a b : α} : IsConvexSet [[a, b]] :=
  ordConnected_Icc

@[instance]
theorem ordConnected_uIoc {a b : α} : IsConvexSet (Ι a b) :=
  ordConnected_Ioc

theorem IsConvexSet.uIcc_subset (hs : IsConvexSet s) ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s) :
    [[x, y]] ⊆ s :=
  hs.out (min_rec' (· ∈ s) hx hy) (max_rec' (· ∈ s) hx hy)

theorem IsConvexSet.uIoc_subset (hs : IsConvexSet s) ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s) :
    Ι x y ⊆ s :=
  Ioc_subset_Icc_self.trans <| hs.uIcc_subset hx hy

theorem ordConnected_iff_uIcc_subset :
    IsConvexSet s ↔ ∀ ⦃x⦄ (_ : x ∈ s) ⦃y⦄ (_ : y ∈ s), [[x, y]] ⊆ s :=
  ⟨fun h => h.uIcc_subset, fun H => ⟨fun _ hx _ hy => Icc_subset_uIcc.trans <| H hx hy⟩⟩

theorem ordConnected_of_uIcc_subset_left (h : ∀ y ∈ s, [[x, y]] ⊆ s) : IsConvexSet s :=
  ordConnected_iff_uIcc_subset.2 fun y hy z hz =>
    calc
      [[y, z]] ⊆ [[y, x]] ∪ [[x, z]] := uIcc_subset_uIcc_union_uIcc
      _ = [[x, y]] ∪ [[x, z]] := by rw [uIcc_comm]
      _ ⊆ s := union_subset (h y hy) (h z hz)

theorem ordConnected_iff_uIcc_subset_left (hx : x ∈ s) :
    IsConvexSet s ↔ ∀ ⦃y⦄, y ∈ s → [[x, y]] ⊆ s :=
  ⟨fun hs => hs.uIcc_subset hx, ordConnected_of_uIcc_subset_left⟩

theorem ordConnected_iff_uIcc_subset_right (hx : x ∈ s) :
    IsConvexSet s ↔ ∀ ⦃y⦄, y ∈ s → [[y, x]] ⊆ s := by
  simp_rw [ordConnected_iff_uIcc_subset_left hx, uIcc_comm]

@[simp]
theorem image_subtype_val_uIcc [IsConvexSet s] (a b : s) :
    Subtype.val '' [[a, b]] = [[a.1, b.1]] := by
  simp [uIcc, (Subtype.mono_coe (· ∈ s)).map_inf, (Subtype.mono_coe (· ∈ s)).map_sup]

@[simp]
theorem image_subtype_val_uIoc [IsConvexSet s] (a b : s) :
    Subtype.val '' uIoc a b = uIoc a.1 b.1 := by
  simp [uIoc, (Subtype.mono_coe (· ∈ s)).map_inf, (Subtype.mono_coe (· ∈ s)).map_sup]

@[simp]
theorem image_subtype_val_uIoo [IsConvexSet s] (a b : s) :
    Subtype.val '' uIoo a b = uIoo a.1 b.1 := by
  simp [uIoo, (Subtype.mono_coe (· ∈ s)).map_inf, (Subtype.mono_coe (· ∈ s)).map_sup]

end LinearOrder

end Set
