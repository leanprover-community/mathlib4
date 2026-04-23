/-
Copyright (c) 2022 Yaël Dillies, Sara Rousta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Sara Rousta
-/
module

public import Mathlib.Order.UpperLower.Principal
public import Mathlib.Order.Antichain
import Mathlib.Data.Set.Disjoint
import Mathlib.Data.Set.Insert
import Mathlib.Data.Set.Lattice
import Mathlib.Init
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Order.Minimal
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Tactic.Translate.ToDual
import Mathlib.Util.CompileInductive

/-!
# Upper and lower closures

Upper (lower) closures generalise principal upper (lower) sets to arbitrary included sets. Indeed,
they are equivalent to a union over principal upper (lower) sets, as shown in `coe_upperClosure`
(`coe_lowerClosure`).

## Main declarations

* `upperClosure`: The greatest upper set containing a set.
* `lowerClosure`: The least lower set containing a set.
-/

@[expose] public section

open OrderDual Set

variable {α β : Type*} {ι : Sort*}

section Preorder
variable [Preorder α] [Preorder β] {s t : Set α} {x : α}

/-- The greatest upper set containing a given set. -/
@[to_dual /-- The least lower set containing a given set. -/]
def upperClosure (s : Set α) : UpperSet α :=
  ⟨{ x | ∃ a ∈ s, a ≤ x }, fun _ _ hle h => h.imp fun _x hx => ⟨hx.1, hx.2.trans hle⟩⟩

@[to_dual (attr := simp)]
theorem mem_upperClosure : x ∈ upperClosure s ↔ ∃ a ∈ s, a ≤ x :=
  Iff.rfl

-- We do not tag this as `simp` to respect the abstraction.
@[to_dual (attr := norm_cast)]
theorem coe_upperClosure (s : Set α) : ↑(upperClosure s) = ⋃ a ∈ s, Ici a := by
  ext
  simp

@[to_dual]
instance instDecidablePredMemUpperClosure [DecidablePred (∃ a ∈ s, a ≤ ·)] :
    DecidablePred (· ∈ upperClosure s) := ‹DecidablePred _›

@[to_dual]
theorem subset_upperClosure : s ⊆ upperClosure s := fun x hx => ⟨x, hx, le_rfl⟩

@[to_dual lowerClosure_min]
theorem upperClosure_min (h : s ⊆ t) (ht : IsUpperSet t) : ↑(upperClosure s) ⊆ t :=
  fun _a ⟨_b, hb, hba⟩ => ht hba <| h hb

@[to_dual]
protected theorem IsUpperSet.upperClosure (hs : IsUpperSet s) : ↑(upperClosure s) = s :=
  (upperClosure_min Subset.rfl hs).antisymm subset_upperClosure

@[to_dual (attr := simp)]
protected theorem UpperSet.upperClosure (s : UpperSet α) : upperClosure (s : Set α) = s :=
  SetLike.coe_injective s.2.upperClosure

@[to_dual (attr := simp)]
theorem upperClosure_image (f : α ≃o β) :
    upperClosure (f '' s) = UpperSet.map f (upperClosure s) := by
  rw [← f.symm_symm, ← UpperSet.symm_map, f.symm_symm]
  ext
  simp only [SetLike.mem_coe]
  simp [f.le_symm_apply]

@[to_dual (attr := simp)]
theorem UpperSet.iInf_Ici (s : Set α) : ⨅ a ∈ s, UpperSet.Ici a = upperClosure s := by
  ext
  simp

@[to_dual (attr := simp) le_upperClosure]
lemma lowerClosure_le {t : LowerSet α} : lowerClosure s ≤ t ↔ s ⊆ t :=
  ⟨fun h ↦ subset_lowerClosure.trans <| LowerSet.coe_subset_coe.2 h,
    fun h ↦ lowerClosure_min h t.lower⟩

theorem gc_upperClosure_coe :
    GaloisConnection (toDual ∘ upperClosure : Set α → (UpperSet α)ᵒᵈ) ((↑) ∘ ofDual) :=
  fun _s _t ↦ le_upperClosure

theorem gc_lowerClosure_coe :
    GaloisConnection (lowerClosure : Set α → LowerSet α) (↑) := fun _s _t ↦ lowerClosure_le

/-- `upperClosure` forms a reversed Galois insertion with the coercion from upper sets to sets. -/
def giUpperClosureCoe :
    GaloisInsertion (toDual ∘ upperClosure : Set α → (UpperSet α)ᵒᵈ) ((↑) ∘ ofDual) where
  choice s hs := toDual (⟨s, fun a _b hab ha => hs ⟨a, ha, hab⟩⟩ : UpperSet α)
  gc := gc_upperClosure_coe
  le_l_u _ := subset_upperClosure
  choice_eq _s hs := ofDual.injective <| SetLike.coe_injective <| subset_upperClosure.antisymm hs

/-- `lowerClosure` forms a Galois insertion with the coercion from lower sets to sets. -/
def giLowerClosureCoe : GaloisInsertion (lowerClosure : Set α → LowerSet α) (↑) where
  choice s hs := ⟨s, fun a _b hba ha => hs ⟨a, ha, hba⟩⟩
  gc := gc_lowerClosure_coe
  le_l_u _ := subset_lowerClosure
  choice_eq _s hs := SetLike.coe_injective <| subset_lowerClosure.antisymm hs

theorem upperClosure_anti : Antitone (upperClosure : Set α → UpperSet α) :=
  gc_upperClosure_coe.monotone_l

theorem lowerClosure_mono : Monotone (lowerClosure : Set α → LowerSet α) :=
  gc_lowerClosure_coe.monotone_l

@[to_dual (attr := simp)]
theorem upperClosure_eq_top_iff : upperClosure s = ⊤ ↔ s = ∅ := by
  rw [eq_top_iff, le_upperClosure]; simp

@[to_dual (attr := simp)]
theorem upperClosure_empty : upperClosure (∅ : Set α) = ⊤ :=
  upperClosure_eq_top_iff.mpr rfl

@[to_dual (attr := simp)]
theorem upperClosure_singleton (a : α) : upperClosure ({a} : Set α) = UpperSet.Ici a := by
  ext
  simp

@[to_dual (attr := simp)]
theorem upperClosure_univ : upperClosure (univ : Set α) = ⊥ :=
  bot_unique subset_upperClosure

theorem upperClosure_union (s t : Set α) : upperClosure (s ∪ t) = upperClosure s ⊓ upperClosure t :=
  (@gc_upperClosure_coe α _).l_sup

@[to_dual existing (attr := simp)]
theorem lowerClosure_union (s t : Set α) : lowerClosure (s ∪ t) = lowerClosure s ⊔ lowerClosure t :=
  (@gc_lowerClosure_coe α _).l_sup

theorem upperClosure_iUnion (f : ι → Set α) : upperClosure (⋃ i, f i) = ⨅ i, upperClosure (f i) :=
  (@gc_upperClosure_coe α _).l_iSup

@[to_dual existing (attr := simp)]
theorem lowerClosure_iUnion (f : ι → Set α) : lowerClosure (⋃ i, f i) = ⨆ i, lowerClosure (f i) :=
  (@gc_lowerClosure_coe α _).l_iSup

@[to_dual (attr := simp)]
theorem upperClosure_sUnion (S : Set (Set α)) : upperClosure (⋃₀ S) = ⨅ s ∈ S, upperClosure s := by
  simp_rw [sUnion_eq_biUnion, upperClosure_iUnion]

theorem Set.OrdConnected.upperClosure_inter_lowerClosure (h : s.OrdConnected) :
    ↑(upperClosure s) ∩ ↑(lowerClosure s) = s :=
  (subset_inter subset_upperClosure subset_lowerClosure).antisymm'
    fun _a ⟨⟨_b, hb, hba⟩, _c, hc, hac⟩ => h.out hb hc ⟨hba, hac⟩

theorem ordConnected_iff_upperClosure_inter_lowerClosure :
    s.OrdConnected ↔ ↑(upperClosure s) ∩ ↑(lowerClosure s) = s := by
  refine ⟨Set.OrdConnected.upperClosure_inter_lowerClosure, fun h => ?_⟩
  rw [← h]
  exact (UpperSet.upper _).ordConnected.inter (LowerSet.lower _).ordConnected

@[to_dual (attr := simp)]
theorem lowerBounds_upperClosure : lowerBounds (upperClosure s : Set α) = lowerBounds s :=
  (lowerBounds_mono_set subset_upperClosure).antisymm
    fun _a ha _b ⟨_c, hc, hcb⟩ ↦ (ha hc).trans hcb

@[to_dual (attr := simp)]
theorem bddBelow_upperClosure : BddBelow (upperClosure s : Set α) ↔ BddBelow s := by
  simp_rw [BddBelow, lowerBounds_upperClosure]

@[to_dual]
protected alias ⟨BddBelow.of_upperClosure, BddBelow.upperClosure⟩ := bddBelow_upperClosure

@[to_dual (attr := simp) disjoint_lowerClosure_left]
lemma IsLowerSet.disjoint_upperClosure_left (ht : IsLowerSet t) :
    Disjoint ↑(upperClosure s) t ↔ Disjoint s t := by
  refine ⟨Disjoint.mono_left subset_upperClosure, ?_⟩
  simp only [disjoint_left, SetLike.mem_coe, mem_upperClosure, forall_exists_index, and_imp]
  exact fun h a b hb hba ha ↦ h hb <| ht hba ha

@[to_dual (attr := simp) disjoint_lowerClosure_right]
lemma IsLowerSet.disjoint_upperClosure_right (hs : IsLowerSet s) :
    Disjoint s (upperClosure t) ↔ Disjoint s t := by
  simpa only [disjoint_comm] using hs.disjoint_upperClosure_left

@[to_dual (attr := simp)]
lemma upperClosure_eq :
    ↑(upperClosure s) = s ↔ IsUpperSet s :=
  ⟨(· ▸ UpperSet.upper _), IsUpperSet.upperClosure⟩

end Preorder

section PartialOrder
variable [PartialOrder α] {s : Set α} {x : α}

lemma IsAntichain.minimal_mem_upperClosure_iff_mem (hs : IsAntichain (· ≤ ·) s) :
    Minimal (· ∈ upperClosure s) x ↔ x ∈ s := by
  simp only [upperClosure, UpperSet.mem_mk, mem_setOf_eq]
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨⟨x, h, rfl.le⟩, fun b ⟨a, has, hab⟩ hbx ↦ ?_⟩⟩
  · obtain ⟨a, has, hax⟩ := h.prop
    rwa [h.eq_of_ge ⟨a, has, rfl.le⟩ hax]
  rwa [← hs.eq has h (hab.trans hbx)]

lemma IsAntichain.maximal_mem_lowerClosure_iff_mem (hs : IsAntichain (· ≤ ·) s) :
    Maximal (· ∈ lowerClosure s) x ↔ x ∈ s :=
  hs.to_dual.minimal_mem_upperClosure_iff_mem

end PartialOrder

section LinearOrder

variable [LinearOrder α]

@[to_dual]
lemma upperClosure_eq_bot {s : Set α} (hs : ¬ BddBelow s) : upperClosure s = ⊥ :=
  le_bot_iff.mp fun x _ ↦ ⟨_, (not_bddBelow_iff.mp hs x).choose_spec.imp id le_of_lt⟩

@[to_dual]
lemma upperClosure_eq_bot_iff [NoMinOrder α] {s : Set α} : upperClosure s = ⊥ ↔ ¬ BddBelow s :=
  ⟨fun h₁ h₂ ↦ by simpa [h₁] using bddBelow_upperClosure.mpr h₂, upperClosure_eq_bot⟩

end LinearOrder

/-! ### Set Difference -/

namespace UpperSet
variable [Preorder α] {s : UpperSet α} {t : Set α} {a : α}

/-- The biggest upper subset of an upper set `s` disjoint from a set `t`. -/
@[to_dual /-- The biggest lower subset of a lower set `s` disjoint from a set `t`. -/]
def sdiff (s : UpperSet α) (t : Set α) : UpperSet α where
  carrier := s \ lowerClosure t
  upper' := s.upper.sdiff_of_isLowerSet (lowerClosure t).lower

/-- The biggest upper subset of an upper set `s` not containing an element `a`. -/
@[to_dual /-- The biggest lower subset of a lower set `s` not containing an element `a`. -/]
def erase (s : UpperSet α) (a : α) : UpperSet α where
  carrier := s \ LowerSet.Iic a
  upper' := s.upper.sdiff_of_isLowerSet (LowerSet.Iic a).lower

@[to_dual (attr := simp, norm_cast)]
lemma coe_sdiff (s : UpperSet α) (t : Set α) : s.sdiff t = (s : Set α) \ lowerClosure t := rfl

@[to_dual (attr := simp, norm_cast)]
lemma coe_erase (s : UpperSet α) (a : α) : s.erase a = (s : Set α) \ LowerSet.Iic a := rfl

@[to_dual (attr := simp)]
lemma sdiff_singleton (s : UpperSet α) (a : α) : s.sdiff {a} = s.erase a := by
  simp [sdiff, erase]

@[to_dual sdiff_le_left] lemma le_sdiff_left : s ≤ s.sdiff t := diff_subset
@[to_dual erase_le] lemma le_erase : s ≤ s.erase a := diff_subset

@[to_dual (attr := simp)]
protected lemma sdiff_eq_left : s.sdiff t = s ↔ Disjoint ↑s t := by
  simp [← SetLike.coe_set_eq]

@[to_dual (attr := simp)]
lemma erase_eq : s.erase a = s ↔ a ∉ s := by rw [← sdiff_singleton]; simp [-sdiff_singleton]

@[to_dual (attr := simp) sdiff_lt_left]
lemma lt_sdiff_left : s < s.sdiff t ↔ ¬ Disjoint ↑s t :=
  le_sdiff_left.lt_iff_ne'.trans UpperSet.sdiff_eq_left.not

@[to_dual (attr := simp) erase_lt]
lemma lt_erase : s < s.erase a ↔ a ∈ s := le_erase.lt_iff_ne'.trans erase_eq.not_left

@[to_dual (attr := simp)]
protected lemma sdiff_idem (s : UpperSet α) (t : Set α) : (s.sdiff t).sdiff t = s.sdiff t :=
  SetLike.coe_injective sdiff_idem

@[to_dual (attr := simp)]
lemma erase_idem (s : UpperSet α) (a : α) : (s.erase a).erase a = s.erase a :=
  SetLike.coe_injective sdiff_idem

@[to_dual]
lemma sdiff_inf_upperClosure (hts : t ⊆ s) (hst : ∀ b ∈ s, ∀ c ∈ t, b ≤ c → b ∈ t) :
    s.sdiff t ⊓ upperClosure t = s := by
  refine ge_antisymm (le_inf le_sdiff_left <| le_upperClosure.2 hts) fun a ha ↦ ?_
  obtain hat | hat := em (a ∈ t)
  · exact subset_union_right (subset_upperClosure hat)
  · refine subset_union_left ⟨ha, ?_⟩
    rintro ⟨b, hb, hab⟩
    exact hat <| hst _ ha _ hb hab

@[to_dual]
lemma upperClosure_inf_sdiff (hts : t ⊆ s) (hst : ∀ b ∈ s, ∀ c ∈ t, b ≤ c → b ∈ t) :
    upperClosure t ⊓ s.sdiff t = s := by rw [inf_comm, sdiff_inf_upperClosure hts hst]

@[to_dual]
lemma erase_inf_Ici (ha : a ∈ s) (has : ∀ b ∈ s, b ≤ a → b = a) : s.erase a ⊓ Ici a = s := by
  rw [← upperClosure_singleton, ← sdiff_singleton, sdiff_inf_upperClosure] <;> simpa

@[to_dual]
lemma Ici_inf_erase (ha : a ∈ s) (has : ∀ b ∈ s, b ≤ a → b = a) : Ici a ⊓ s.erase a = s := by
  rw [inf_comm, erase_inf_Ici ha has]

end UpperSet
