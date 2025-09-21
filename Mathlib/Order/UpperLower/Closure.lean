/-
Copyright (c) 2022 Yaël Dillies, Sara Rousta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Sara Rousta
-/
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Order.Minimal
import Mathlib.Order.UpperLower.Principal

/-!
# Upper and lower closures

Upper (lower) closures generalise principal upper (lower) sets to arbitrary included sets. Indeed,
they are equivalent to a union over principal upper (lower) sets, as shown in `coe_upperClosure`
(`coe_lowerClosure`).

## Main declarations

* `upperClosure`: The greatest upper set containing a set.
* `lowerClosure`: The least lower set containing a set.
-/

open OrderDual Set

variable {α β : Type*} {ι : Sort*}

section Preorder
variable [Preorder α] [Preorder β] {s t : Set α} {x : α}

/-- The greatest upper set containing a given set. -/
def upperClosure (s : Set α) : UpperSet α :=
  ⟨{ x | ∃ a ∈ s, a ≤ x }, fun _ _ hle h => h.imp fun _x hx => ⟨hx.1, hx.2.trans hle⟩⟩

/-- The least lower set containing a given set. -/
def lowerClosure (s : Set α) : LowerSet α :=
  ⟨{ x | ∃ a ∈ s, x ≤ a }, fun _ _ hle h => h.imp fun _x hx => ⟨hx.1, hle.trans hx.2⟩⟩

-- TODO: move `GaloisInsertion`s up, use them to prove lemmas

@[simp]
theorem mem_upperClosure : x ∈ upperClosure s ↔ ∃ a ∈ s, a ≤ x :=
  Iff.rfl

@[simp]
theorem mem_lowerClosure : x ∈ lowerClosure s ↔ ∃ a ∈ s, x ≤ a :=
  Iff.rfl

-- We do not tag those two as `simp` to respect the abstraction.
@[norm_cast]
theorem coe_upperClosure (s : Set α) : ↑(upperClosure s) = ⋃ a ∈ s, Ici a := by
  ext
  simp

@[norm_cast]
theorem coe_lowerClosure (s : Set α) : ↑(lowerClosure s) = ⋃ a ∈ s, Iic a := by
  ext
  simp

instance instDecidablePredMemUpperClosure [DecidablePred (∃ a ∈ s, a ≤ ·)] :
    DecidablePred (· ∈ upperClosure s) := ‹DecidablePred _›

instance instDecidablePredMemLowerClosure [DecidablePred (∃ a ∈ s, · ≤ a)] :
    DecidablePred (· ∈ lowerClosure s) := ‹DecidablePred _›

theorem subset_upperClosure : s ⊆ upperClosure s := fun x hx => ⟨x, hx, le_rfl⟩

theorem subset_lowerClosure : s ⊆ lowerClosure s := fun x hx => ⟨x, hx, le_rfl⟩

theorem upperClosure_min (h : s ⊆ t) (ht : IsUpperSet t) : ↑(upperClosure s) ⊆ t :=
  fun _a ⟨_b, hb, hba⟩ => ht hba <| h hb

theorem lowerClosure_min (h : s ⊆ t) (ht : IsLowerSet t) : ↑(lowerClosure s) ⊆ t :=
  fun _a ⟨_b, hb, hab⟩ => ht hab <| h hb

protected theorem IsUpperSet.upperClosure (hs : IsUpperSet s) : ↑(upperClosure s) = s :=
  (upperClosure_min Subset.rfl hs).antisymm subset_upperClosure

protected theorem IsLowerSet.lowerClosure (hs : IsLowerSet s) : ↑(lowerClosure s) = s :=
  (lowerClosure_min Subset.rfl hs).antisymm subset_lowerClosure

@[simp]
protected theorem UpperSet.upperClosure (s : UpperSet α) : upperClosure (s : Set α) = s :=
  SetLike.coe_injective s.2.upperClosure

@[simp]
protected theorem LowerSet.lowerClosure (s : LowerSet α) : lowerClosure (s : Set α) = s :=
  SetLike.coe_injective s.2.lowerClosure

@[simp]
theorem upperClosure_image (f : α ≃o β) :
    upperClosure (f '' s) = UpperSet.map f (upperClosure s) := by
  rw [← f.symm_symm, ← UpperSet.symm_map, f.symm_symm]
  ext
  simp [-UpperSet.symm_map, UpperSet.map, OrderIso.symm, ← f.le_symm_apply]

@[simp]
theorem lowerClosure_image (f : α ≃o β) :
    lowerClosure (f '' s) = LowerSet.map f (lowerClosure s) := by
  rw [← f.symm_symm, ← LowerSet.symm_map, f.symm_symm]
  ext
  simp [-LowerSet.symm_map, LowerSet.map, OrderIso.symm, ← f.symm_apply_le]

@[simp]
theorem UpperSet.iInf_Ici (s : Set α) : ⨅ a ∈ s, UpperSet.Ici a = upperClosure s := by
  ext
  simp

@[simp]
theorem LowerSet.iSup_Iic (s : Set α) : ⨆ a ∈ s, LowerSet.Iic a = lowerClosure s := by
  ext
  simp

@[simp] lemma lowerClosure_le {t : LowerSet α} : lowerClosure s ≤ t ↔ s ⊆ t :=
  ⟨fun h ↦ subset_lowerClosure.trans <| LowerSet.coe_subset_coe.2 h,
    fun h ↦ lowerClosure_min h t.lower⟩

@[simp] lemma le_upperClosure {s : UpperSet α} : s ≤ upperClosure t ↔ t ⊆ s :=
  ⟨fun h ↦ subset_upperClosure.trans <| UpperSet.coe_subset_coe.2 h,
    fun h ↦ upperClosure_min h s.upper⟩

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

@[simp]
theorem upperClosure_empty : upperClosure (∅ : Set α) = ⊤ :=
  (@gc_upperClosure_coe α).l_bot

@[simp]
theorem lowerClosure_empty : lowerClosure (∅ : Set α) = ⊥ :=
  (@gc_lowerClosure_coe α).l_bot

@[simp]
theorem upperClosure_singleton (a : α) : upperClosure ({a} : Set α) = UpperSet.Ici a := by
  ext
  simp

@[simp]
theorem lowerClosure_singleton (a : α) : lowerClosure ({a} : Set α) = LowerSet.Iic a := by
  ext
  simp

@[simp]
theorem upperClosure_univ : upperClosure (univ : Set α) = ⊥ :=
  bot_unique subset_upperClosure

@[simp]
theorem lowerClosure_univ : lowerClosure (univ : Set α) = ⊤ :=
  top_unique subset_lowerClosure

@[simp]
theorem upperClosure_eq_top_iff : upperClosure s = ⊤ ↔ s = ∅ :=
  (@gc_upperClosure_coe α _).l_eq_bot.trans subset_empty_iff

@[simp]
theorem lowerClosure_eq_bot_iff : lowerClosure s = ⊥ ↔ s = ∅ :=
  (@gc_lowerClosure_coe α _).l_eq_bot.trans subset_empty_iff

@[simp]
theorem upperClosure_union (s t : Set α) : upperClosure (s ∪ t) = upperClosure s ⊓ upperClosure t :=
  (@gc_upperClosure_coe α _).l_sup

@[simp]
theorem lowerClosure_union (s t : Set α) : lowerClosure (s ∪ t) = lowerClosure s ⊔ lowerClosure t :=
  (@gc_lowerClosure_coe α _).l_sup

@[simp]
theorem upperClosure_iUnion (f : ι → Set α) : upperClosure (⋃ i, f i) = ⨅ i, upperClosure (f i) :=
  (@gc_upperClosure_coe α _).l_iSup

@[simp]
theorem lowerClosure_iUnion (f : ι → Set α) : lowerClosure (⋃ i, f i) = ⨆ i, lowerClosure (f i) :=
  (@gc_lowerClosure_coe α _).l_iSup

@[simp]
theorem upperClosure_sUnion (S : Set (Set α)) : upperClosure (⋃₀ S) = ⨅ s ∈ S, upperClosure s := by
  simp_rw [sUnion_eq_biUnion, upperClosure_iUnion]

@[simp]
theorem lowerClosure_sUnion (S : Set (Set α)) : lowerClosure (⋃₀ S) = ⨆ s ∈ S, lowerClosure s := by
  simp_rw [sUnion_eq_biUnion, lowerClosure_iUnion]

theorem Set.OrdConnected.upperClosure_inter_lowerClosure (h : s.OrdConnected) :
    ↑(upperClosure s) ∩ ↑(lowerClosure s) = s :=
  (subset_inter subset_upperClosure subset_lowerClosure).antisymm'
    fun _a ⟨⟨_b, hb, hba⟩, _c, hc, hac⟩ => h.out hb hc ⟨hba, hac⟩

theorem ordConnected_iff_upperClosure_inter_lowerClosure :
    s.OrdConnected ↔ ↑(upperClosure s) ∩ ↑(lowerClosure s) = s := by
  refine ⟨Set.OrdConnected.upperClosure_inter_lowerClosure, fun h => ?_⟩
  rw [← h]
  exact (UpperSet.upper _).ordConnected.inter (LowerSet.lower _).ordConnected

@[simp]
theorem upperBounds_lowerClosure : upperBounds (lowerClosure s : Set α) = upperBounds s :=
  (upperBounds_mono_set subset_lowerClosure).antisymm
    fun _a ha _b ⟨_c, hc, hcb⟩ ↦ hcb.trans <| ha hc

@[simp]
theorem lowerBounds_upperClosure : lowerBounds (upperClosure s : Set α) = lowerBounds s :=
  (lowerBounds_mono_set subset_upperClosure).antisymm
    fun _a ha _b ⟨_c, hc, hcb⟩ ↦ (ha hc).trans hcb

@[simp]
theorem bddAbove_lowerClosure : BddAbove (lowerClosure s : Set α) ↔ BddAbove s := by
  simp_rw [BddAbove, upperBounds_lowerClosure]

@[simp]
theorem bddBelow_upperClosure : BddBelow (upperClosure s : Set α) ↔ BddBelow s := by
  simp_rw [BddBelow, lowerBounds_upperClosure]

protected alias ⟨BddAbove.of_lowerClosure, BddAbove.lowerClosure⟩ := bddAbove_lowerClosure

protected alias ⟨BddBelow.of_upperClosure, BddBelow.upperClosure⟩ := bddBelow_upperClosure

@[simp] lemma IsLowerSet.disjoint_upperClosure_left (ht : IsLowerSet t) :
    Disjoint ↑(upperClosure s) t ↔ Disjoint s t := by
  refine ⟨Disjoint.mono_left subset_upperClosure, ?_⟩
  simp only [disjoint_left, SetLike.mem_coe, mem_upperClosure, forall_exists_index, and_imp]
  exact fun h a b hb hba ha ↦ h hb <| ht hba ha

@[simp] lemma IsLowerSet.disjoint_upperClosure_right (hs : IsLowerSet s) :
    Disjoint s (upperClosure t) ↔ Disjoint s t := by
  simpa only [disjoint_comm] using hs.disjoint_upperClosure_left

@[simp] lemma IsUpperSet.disjoint_lowerClosure_left (ht : IsUpperSet t) :
    Disjoint ↑(lowerClosure s) t ↔ Disjoint s t := ht.toDual.disjoint_upperClosure_left

@[simp] lemma IsUpperSet.disjoint_lowerClosure_right (hs : IsUpperSet s) :
    Disjoint s (lowerClosure t) ↔ Disjoint s t := hs.toDual.disjoint_upperClosure_right

@[simp] lemma upperClosure_eq :
    ↑(upperClosure s) = s ↔ IsUpperSet s :=
  ⟨(· ▸ UpperSet.upper _), IsUpperSet.upperClosure⟩

@[simp] lemma lowerClosure_eq :
    ↑(lowerClosure s) = s ↔ IsLowerSet s :=
  @upperClosure_eq αᵒᵈ _ _

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

/-! ### Set Difference -/

namespace LowerSet
variable [Preorder α] {s : LowerSet α} {t : Set α} {a : α}

/-- The biggest lower subset of a lower set `s` disjoint from a set `t`. -/
def sdiff (s : LowerSet α) (t : Set α) : LowerSet α where
  carrier := s \ upperClosure t
  lower' := s.lower.sdiff_of_isUpperSet (upperClosure t).upper

/-- The biggest lower subset of a lower set `s` not containing an element `a`. -/
def erase (s : LowerSet α) (a : α) : LowerSet α where
  carrier := s \ UpperSet.Ici a
  lower' := s.lower.sdiff_of_isUpperSet (UpperSet.Ici a).upper

@[simp, norm_cast]
lemma coe_sdiff (s : LowerSet α) (t : Set α) : s.sdiff t = (s : Set α) \ upperClosure t := rfl

@[simp, norm_cast]
lemma coe_erase (s : LowerSet α) (a : α) : s.erase a = (s : Set α) \ UpperSet.Ici a := rfl

@[simp] lemma sdiff_singleton (s : LowerSet α) (a : α) : s.sdiff {a} = s.erase a := by
  simp [sdiff, erase]

lemma sdiff_le_left : s.sdiff t ≤ s := diff_subset
lemma erase_le : s.erase a ≤ s := diff_subset

@[simp] protected lemma sdiff_eq_left : s.sdiff t = s ↔ Disjoint ↑s t := by
  simp [← SetLike.coe_set_eq]

@[simp] lemma erase_eq : s.erase a = s ↔ a ∉ s := by rw [← sdiff_singleton]; simp [-sdiff_singleton]

@[simp] lemma sdiff_lt_left : s.sdiff t < s ↔ ¬ Disjoint ↑s t :=
  sdiff_le_left.lt_iff_ne.trans LowerSet.sdiff_eq_left.not

@[simp] lemma erase_lt : s.erase a < s ↔ a ∈ s := erase_le.lt_iff_ne.trans erase_eq.not_left

@[simp] protected lemma sdiff_idem (s : LowerSet α) (t : Set α) : (s.sdiff t).sdiff t = s.sdiff t :=
  SetLike.coe_injective sdiff_idem

@[simp] lemma erase_idem (s : LowerSet α) (a : α) : (s.erase a).erase a = s.erase a :=
  SetLike.coe_injective sdiff_idem

lemma sdiff_sup_lowerClosure (hts : t ⊆ s) (hst : ∀ b ∈ s, ∀ c ∈ t, c ≤ b → b ∈ t) :
    s.sdiff t ⊔ lowerClosure t = s := by
  refine le_antisymm (sup_le sdiff_le_left <| lowerClosure_le.2 hts) fun a ha ↦ ?_
  obtain hat | hat := em (a ∈ t)
  · exact subset_union_right (subset_lowerClosure hat)
  · refine subset_union_left ⟨ha, ?_⟩
    rintro ⟨b, hb, hba⟩
    exact hat <| hst _ ha _ hb hba

lemma lowerClosure_sup_sdiff (hts : t ⊆ s) (hst : ∀ b ∈ s, ∀ c ∈ t, c ≤ b → b ∈ t) :
    lowerClosure t ⊔ s.sdiff t = s := by rw [sup_comm, sdiff_sup_lowerClosure hts hst]

lemma erase_sup_Iic (ha : a ∈ s) (has : ∀ b ∈ s, a ≤ b → b = a) : s.erase a ⊔ Iic a = s := by
  rw [← lowerClosure_singleton, ← sdiff_singleton, sdiff_sup_lowerClosure] <;> simpa

lemma Iic_sup_erase (ha : a ∈ s) (has : ∀ b ∈ s, a ≤ b → b = a) : Iic a ⊔ s.erase a = s := by
  rw [sup_comm, erase_sup_Iic ha has]

end LowerSet

namespace UpperSet
variable [Preorder α] {s : UpperSet α} {t : Set α} {a : α}

/-- The biggest upper subset of a upper set `s` disjoint from a set `t`. -/
def sdiff (s : UpperSet α) (t : Set α) : UpperSet α where
  carrier := s \ lowerClosure t
  upper' := s.upper.sdiff_of_isLowerSet (lowerClosure t).lower

/-- The biggest upper subset of a upper set `s` not containing an element `a`. -/
def erase (s : UpperSet α) (a : α) : UpperSet α where
  carrier := s \ LowerSet.Iic a
  upper' := s.upper.sdiff_of_isLowerSet (LowerSet.Iic a).lower

@[simp, norm_cast]
lemma coe_sdiff (s : UpperSet α) (t : Set α) : s.sdiff t = (s : Set α) \ lowerClosure t := rfl

@[simp, norm_cast]
lemma coe_erase (s : UpperSet α) (a : α) : s.erase a = (s : Set α) \ LowerSet.Iic a := rfl

@[simp] lemma sdiff_singleton (s : UpperSet α) (a : α) : s.sdiff {a} = s.erase a := by
  simp [sdiff, erase]

lemma le_sdiff_left : s ≤ s.sdiff t := diff_subset
lemma le_erase : s ≤ s.erase a := diff_subset

@[simp] protected lemma sdiff_eq_left : s.sdiff t = s ↔ Disjoint ↑s t := by
  simp [← SetLike.coe_set_eq]

@[simp] lemma erase_eq : s.erase a = s ↔ a ∉ s := by rw [← sdiff_singleton]; simp [-sdiff_singleton]

@[simp] lemma lt_sdiff_left : s < s.sdiff t ↔ ¬ Disjoint ↑s t :=
  le_sdiff_left.lt_iff_ne'.trans UpperSet.sdiff_eq_left.not

@[simp] lemma lt_erase : s < s.erase a ↔ a ∈ s := le_erase.lt_iff_ne'.trans erase_eq.not_left

@[simp] protected lemma sdiff_idem (s : UpperSet α) (t : Set α) : (s.sdiff t).sdiff t = s.sdiff t :=
  SetLike.coe_injective sdiff_idem

@[simp] lemma erase_idem (s : UpperSet α) (a : α) : (s.erase a).erase a = s.erase a :=
  SetLike.coe_injective sdiff_idem

lemma sdiff_inf_upperClosure (hts : t ⊆ s) (hst : ∀ b ∈ s, ∀ c ∈ t, b ≤ c → b ∈ t) :
    s.sdiff t ⊓ upperClosure t = s := by
  refine ge_antisymm (le_inf le_sdiff_left <| le_upperClosure.2 hts) fun a ha ↦ ?_
  obtain hat | hat := em (a ∈ t)
  · exact subset_union_right (subset_upperClosure hat)
  · refine subset_union_left ⟨ha, ?_⟩
    rintro ⟨b, hb, hab⟩
    exact hat <| hst _ ha _ hb hab

lemma upperClosure_inf_sdiff (hts : t ⊆ s) (hst : ∀ b ∈ s, ∀ c ∈ t, b ≤ c → b ∈ t) :
    upperClosure t ⊓ s.sdiff t = s := by rw [inf_comm, sdiff_inf_upperClosure hts hst]

lemma erase_inf_Ici (ha : a ∈ s) (has : ∀ b ∈ s, b ≤ a → b = a) : s.erase a ⊓ Ici a = s := by
  rw [← upperClosure_singleton, ← sdiff_singleton, sdiff_inf_upperClosure] <;> simpa

lemma Ici_inf_erase (ha : a ∈ s) (has : ∀ b ∈ s, b ≤ a → b = a) : Ici a ⊓ s.erase a = s := by
  rw [inf_comm, erase_inf_Ici ha has]

end UpperSet
