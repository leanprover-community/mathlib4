/-
Copyright (c) 2022 Yaël Dillies, Sara Rousta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Sara Rousta
-/
module

public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Data.SetLike.Basic
public import Mathlib.Order.UpperLower.Basic

/-!
# The complete lattice structure on `UpperSet`/`LowerSet`

This file defines a completely distributive lattice structure on `UpperSet` and `LowerSet`,
pulled back across the canonical injection (`UpperSet.carrier`, `LowerSet.carrier`) into `Set α`.

## Notes

Upper sets are ordered by **reverse** inclusion. This convention is motivated by the fact that this
makes them order-isomorphic to lower sets and antichains, and matches the convention on `Filter`.
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

open OrderDual Set

variable {α β γ : Type*} {ι : Sort*} {κ : ι → Sort*}

namespace UpperSet

section LE

variable [LE α]

@[to_dual]
instance : SetLike (UpperSet α) α where
  coe := UpperSet.carrier
  coe_injective' s t h := by cases s; cases t; congr

/-- See Note [custom simps projection]. -/
@[to_dual /-- See Note [custom simps projection]. -/]
def Simps.coe (s : UpperSet α) : Set α := s

initialize_simps_projections UpperSet (carrier → coe, as_prefix coe)
initialize_simps_projections LowerSet (carrier → coe, as_prefix coe)

@[to_dual (attr := ext)]
theorem ext {s t : UpperSet α} : (s : Set α) = t → s = t :=
  SetLike.ext'

@[to_dual (attr := simp)]
theorem carrier_eq_coe (s : UpperSet α) : s.carrier = s :=
  rfl

@[to_dual (attr := simp)]
protected lemma upper (s : UpperSet α) : IsUpperSet (s : Set α) := s.upper'

@[to_dual (attr := simp, norm_cast)]
lemma coe_mk (s : Set α) (hs) : mk s hs = s := rfl

@[to_dual (attr := simp)]
lemma mem_mk {s : Set α} (hs) {a : α} : a ∈ mk s hs ↔ a ∈ s := Iff.rfl

variable {S : Set (UpperSet α)} {s t : UpperSet α} {a : α}

@[to_dual]
instance : Max (UpperSet α) :=
  ⟨fun s t => ⟨s ∩ t, s.upper.inter t.upper⟩⟩

@[to_dual]
instance : Min (UpperSet α) :=
  ⟨fun s t => ⟨s ∪ t, s.upper.union t.upper⟩⟩

@[to_dual]
instance : Top (UpperSet α) :=
  ⟨⟨∅, isUpperSet_empty⟩⟩

@[to_dual]
instance : Bot (UpperSet α) :=
  ⟨⟨univ, isUpperSet_univ⟩⟩

@[to_dual]
instance : SupSet (UpperSet α) :=
  ⟨fun S => ⟨⋂ s ∈ S, ↑s, isUpperSet_iInter₂ fun s _ => s.upper⟩⟩

@[to_dual]
instance : InfSet (UpperSet α) :=
  ⟨fun S => ⟨⋃ s ∈ S, ↑s, isUpperSet_iUnion₂ fun s _ => s.upper⟩⟩

instance : PartialOrder (UpperSet α) :=
  PartialOrder.lift _ (toDual.injective.comp SetLike.coe_injective)

instance completeLattice : CompleteLattice (UpperSet α) :=
  (toDual.injective.comp SetLike.coe_injective).completeLattice _
    .rfl .rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) rfl rfl

instance completelyDistribLattice : CompletelyDistribLattice (UpperSet α) :=
  .ofMinimalAxioms <|
    (toDual.injective.comp SetLike.coe_injective).completelyDistribLatticeMinimalAxioms .of _
      .rfl .rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) rfl rfl

@[to_dual existing]
instance _root_.LowerSet.instPartialOrder : PartialOrder (LowerSet α) :=
  PartialOrder.lift _ SetLike.coe_injective

@[to_dual existing]
instance _root_.LowerSet.completeLattice : CompleteLattice (LowerSet α) :=
  SetLike.coe_injective.completeLattice _
    .rfl .rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) rfl rfl

@[to_dual existing]
instance _root_.LowerSet.completelyDistribLattice : CompletelyDistribLattice (LowerSet α) :=
  .ofMinimalAxioms <| SetLike.coe_injective.completelyDistribLatticeMinimalAxioms .of _
    .rfl .rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) rfl rfl

@[to_dual]
instance : Inhabited (UpperSet α) :=
  ⟨⊥⟩

@[to_dual (attr := simp 1100, norm_cast)]
theorem coe_subset_coe : (s : Set α) ⊆ t ↔ t ≤ s :=
  Iff.rfl

@[to_dual (attr := simp 1100, norm_cast)]
lemma coe_ssubset_coe : (s : Set α) ⊂ t ↔ t < s := Iff.rfl

@[to_dual (attr := simp, norm_cast)]
theorem coe_top : ((⊤ : UpperSet α) : Set α) = ∅ :=
  rfl

@[to_dual (attr := simp, norm_cast)]
theorem coe_bot : ((⊥ : UpperSet α) : Set α) = univ :=
  rfl

@[to_dual (attr := simp, norm_cast)]
theorem coe_eq_univ : (s : Set α) = univ ↔ s = ⊥ := by simp [SetLike.ext'_iff]

@[to_dual (attr := simp, norm_cast)]
theorem coe_eq_empty : (s : Set α) = ∅ ↔ s = ⊤ := by simp [SetLike.ext'_iff]

@[to_dual (attr := simp, norm_cast)]
lemma coe_nonempty : (s : Set α).Nonempty ↔ s ≠ ⊤ :=
  nonempty_iff_ne_empty.trans coe_eq_empty.not

@[to_dual (attr := simp, norm_cast)]
theorem coe_sup (s t : UpperSet α) : (↑(s ⊔ t) : Set α) = (s : Set α) ∩ t :=
  rfl

@[to_dual (attr := simp, norm_cast)]
theorem coe_inf (s t : UpperSet α) : (↑(s ⊓ t) : Set α) = (s : Set α) ∪ t :=
  rfl

@[to_dual (attr := simp, norm_cast)]
theorem coe_sSup (S : Set (UpperSet α)) : (↑(sSup S) : Set α) = ⋂ s ∈ S, ↑s :=
  rfl

@[to_dual (attr := simp, norm_cast)]
theorem coe_sInf (S : Set (UpperSet α)) : (↑(sInf S) : Set α) = ⋃ s ∈ S, ↑s :=
  rfl

@[to_dual (attr := simp, norm_cast)]
theorem coe_iSup (f : ι → UpperSet α) : (↑(⨆ i, f i) : Set α) = ⋂ i, f i := by simp [iSup]

@[to_dual (attr := simp, norm_cast)]
theorem coe_iInf (f : ι → UpperSet α) : (↑(⨅ i, f i) : Set α) = ⋃ i, f i := by simp [iInf]

@[to_dual (attr := norm_cast)]
theorem coe_iSup₂ (f : ∀ i, κ i → UpperSet α) :
    (↑(⨆ (i) (j), f i j) : Set α) = ⋂ (i) (j), f i j := by simp

@[to_dual (attr := norm_cast)]
theorem coe_iInf₂ (f : ∀ i, κ i → UpperSet α) :
    (↑(⨅ (i) (j), f i j) : Set α) = ⋃ (i) (j), f i j := by simp

@[to_dual (attr := simp)]
theorem notMem_top : a ∉ (⊤ : UpperSet α) :=
  id

@[to_dual (attr := simp)]
theorem mem_bot : a ∈ (⊥ : UpperSet α) :=
  trivial

@[to_dual (attr := simp)]
theorem mem_sup_iff : a ∈ s ⊔ t ↔ a ∈ s ∧ a ∈ t :=
  Iff.rfl

@[to_dual (attr := simp)]
theorem mem_inf_iff : a ∈ s ⊓ t ↔ a ∈ s ∨ a ∈ t :=
  Iff.rfl

@[to_dual (attr := simp)]
theorem mem_sSup_iff : a ∈ sSup S ↔ ∀ s ∈ S, a ∈ s :=
  mem_iInter₂

@[to_dual (attr := simp)]
theorem mem_sInf_iff : a ∈ sInf S ↔ ∃ s ∈ S, a ∈ s :=
  mem_iUnion₂.trans <| by simp only [exists_prop, SetLike.mem_coe]

@[to_dual (attr := simp)]
theorem mem_iSup_iff {f : ι → UpperSet α} : (a ∈ ⨆ i, f i) ↔ ∀ i, a ∈ f i := by
  rw [← SetLike.mem_coe, coe_iSup]
  exact mem_iInter

@[to_dual (attr := simp)]
theorem mem_iInf_iff {f : ι → UpperSet α} : (a ∈ ⨅ i, f i) ↔ ∃ i, a ∈ f i := by
  rw [← SetLike.mem_coe, coe_iInf]
  exact mem_iUnion

@[to_dual]
theorem mem_iSup₂_iff {f : ∀ i, κ i → UpperSet α} : (a ∈ ⨆ (i) (j), f i j) ↔ ∀ i j, a ∈ f i j := by
  simp

@[to_dual]
theorem mem_iInf₂_iff {f : ∀ i, κ i → UpperSet α} : (a ∈ ⨅ (i) (j), f i j) ↔ ∃ i j, a ∈ f i j := by
  simp

@[to_dual (attr := simp, norm_cast)]
theorem codisjoint_coe : Codisjoint (s : Set α) t ↔ Disjoint s t := by
  simp [disjoint_iff, codisjoint_iff, SetLike.ext'_iff]

/-! ### Complement -/

/-- The complement of an upper set as a lower set. -/
@[to_dual /-- The complement of a lower set as an upper set. -/]
def compl (s : UpperSet α) : LowerSet α :=
  ⟨sᶜ, s.upper.compl⟩

@[to_dual (attr := simp)]
theorem coe_compl (s : UpperSet α) : (s.compl : Set α) = (↑s)ᶜ :=
  rfl

@[to_dual (attr := simp)]
theorem mem_compl_iff : a ∈ s.compl ↔ a ∉ s :=
  Iff.rfl

@[to_dual (attr := simp)]
nonrec theorem compl_compl (s : UpperSet α) : s.compl.compl = s :=
  UpperSet.ext <| compl_compl _

@[to_dual (attr := simp)]
theorem compl_le_compl : s.compl ≤ t.compl ↔ s ≤ t :=
  compl_subset_compl

@[to_dual (attr := simp)]
protected theorem compl_sup (s t : UpperSet α) : (s ⊔ t).compl = s.compl ⊔ t.compl :=
  LowerSet.ext compl_inf

@[to_dual (attr := simp)]
protected theorem compl_inf (s t : UpperSet α) : (s ⊓ t).compl = s.compl ⊓ t.compl :=
  LowerSet.ext compl_sup

@[to_dual (attr := simp)]
protected theorem compl_top : (⊤ : UpperSet α).compl = ⊤ :=
  LowerSet.ext compl_empty

@[to_dual (attr := simp)]
protected theorem compl_bot : (⊥ : UpperSet α).compl = ⊥ :=
  LowerSet.ext compl_univ

@[to_dual (attr := simp)]
protected theorem compl_sSup (S : Set (UpperSet α)) : (sSup S).compl = ⨆ s ∈ S, UpperSet.compl s :=
  LowerSet.ext <| by simp only [coe_compl, coe_sSup, compl_iInter₂, LowerSet.coe_iSup₂]

@[to_dual (attr := simp)]
protected theorem compl_sInf (S : Set (UpperSet α)) : (sInf S).compl = ⨅ s ∈ S, UpperSet.compl s :=
  LowerSet.ext <| by simp only [coe_compl, coe_sInf, compl_iUnion₂, LowerSet.coe_iInf₂]

@[to_dual (attr := simp)]
protected theorem compl_iSup (f : ι → UpperSet α) : (⨆ i, f i).compl = ⨆ i, (f i).compl :=
  LowerSet.ext <| by simp only [coe_compl, coe_iSup, compl_iInter, LowerSet.coe_iSup]

@[to_dual (attr := simp)]
protected theorem compl_iInf (f : ι → UpperSet α) : (⨅ i, f i).compl = ⨅ i, (f i).compl :=
  LowerSet.ext <| by simp only [coe_compl, coe_iInf, compl_iUnion, LowerSet.coe_iInf]

@[to_dual]
theorem compl_iSup₂ (f : ∀ i, κ i → UpperSet α) :
    (⨆ (i) (j), f i j).compl = ⨆ (i) (j), (f i j).compl := by simp

@[to_dual]
theorem compl_iInf₂ (f : ∀ i, κ i → UpperSet α) :
    (⨅ (i) (j), f i j).compl = ⨅ (i) (j), (f i j).compl := by simp

/-- Upper sets are order-isomorphic to lower sets under complementation. -/
@[simps]
def _root_.upperSetIsoLowerSet : UpperSet α ≃o LowerSet α where
  toFun := UpperSet.compl
  invFun := LowerSet.compl
  left_inv := UpperSet.compl_compl
  right_inv := LowerSet.compl_compl
  map_rel_iff' := UpperSet.compl_le_compl

end LE

section LinearOrder
variable [LinearOrder α]

@[to_dual none]
instance total_le : @Std.Total (UpperSet α) (· ≤ ·) := ⟨fun s t => t.upper.total s.upper⟩

noncomputable instance instLinearOrder : LinearOrder (UpperSet α) := by
  classical exact Lattice.toLinearOrder _

noncomputable instance instCompleteLinearOrder : CompleteLinearOrder (UpperSet α) :=
  { completelyDistribLattice, instLinearOrder with }

@[to_dual none]
instance _root_.LowerSet.total_le : @Std.Total (LowerSet α) (· ≤ ·) :=
  ⟨fun s t => s.lower.total t.lower⟩

@[to_dual existing]
noncomputable instance _root_.LowerSet.instLinearOrder : LinearOrder (LowerSet α) := by
  classical exact Lattice.toLinearOrder _

@[to_dual existing]
noncomputable instance _root_.LowerSet.instCompleteLinearOrder : CompleteLinearOrder (LowerSet α) :=
  { LowerSet.completelyDistribLattice, LowerSet.instLinearOrder with }

end LinearOrder

section Map

variable [Preorder α] [Preorder β] [Preorder γ]

variable {f : α ≃o β} {s t : UpperSet α} {a : α} {b : β}

/-- An order isomorphism of Preorders induces an order isomorphism of their upper sets. -/
@[to_dual (attr := simps)
/-- An order isomorphism of Preorders induces an order isomorphism of their lower sets. -/]
def map (f : α ≃o β) : UpperSet α ≃o UpperSet β where
  toFun s := ⟨f '' s, s.upper.image f⟩
  invFun t := ⟨f ⁻¹' t, t.upper.preimage f.monotone⟩
  left_inv _ := ext <| f.preimage_image _
  right_inv _ := ext <| f.image_preimage _
  map_rel_iff' := image_subset_image_iff f.injective

@[to_dual (attr := simp)]
theorem symm_map (f : α ≃o β) : (map f).symm = map f.symm := by
 ext; simp [map, OrderIso.symm_apply_eq]

@[to_dual (attr := simp)]
theorem mem_map : b ∈ map f s ↔ f.symm b ∈ s := by
  rw [← f.symm_symm, ← symm_map, f.symm_symm]
  rfl

@[to_dual (attr := simp)]
theorem map_refl : map (OrderIso.refl α) = OrderIso.refl _ := by
  ext
  simp

@[to_dual (attr := simp)]
theorem map_map (g : β ≃o γ) (f : α ≃o β) : map g (map f s) = map (f.trans g) s := by
  ext
  simp

variable (f s t)

@[to_dual (attr := simp, norm_cast)]
theorem coe_map : (map f s : Set β) = f '' s :=
  rfl

@[to_dual (attr := simp)]
theorem compl_map : (map f s).compl = LowerSet.map f s.compl :=
  SetLike.coe_injective (Set.image_compl_eq f.bijective).symm


end Map

end UpperSet
