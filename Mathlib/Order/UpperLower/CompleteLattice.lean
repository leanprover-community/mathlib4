/-
Copyright (c) 2022 Yaël Dillies, Sara Rousta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Sara Rousta
-/
import Mathlib.Data.Set.Lattice.Image
import Mathlib.Data.SetLike.Basic
import Mathlib.Order.UpperLower.Basic

/-!
# The complete lattice structure on `UpperSet`/`LowerSet`

This file defines a completely distributive lattice structure on `UpperSet` and `LowerSet`,
pulled back across the canonical injection (`UpperSet.carrier`, `LowerSet.carrier`) into `Set α`.

## Notes

Upper sets are ordered by **reverse** inclusion. This convention is motivated by the fact that this
makes them order-isomorphic to lower sets and antichains, and matches the convention on `Filter`.
-/

open OrderDual Set

variable {α β γ : Type*} {ι : Sort*} {κ : ι → Sort*}

section LE

variable [LE α]

namespace UpperSet

instance : SetLike (UpperSet α) α where
  coe := UpperSet.carrier
  coe_injective' s t h := by cases s; cases t; congr

/-- See Note [custom simps projection]. -/
def Simps.coe (s : UpperSet α) : Set α := s

initialize_simps_projections UpperSet (carrier → coe, as_prefix coe)

@[ext]
theorem ext {s t : UpperSet α} : (s : Set α) = t → s = t :=
  SetLike.ext'

@[simp]
theorem carrier_eq_coe (s : UpperSet α) : s.carrier = s :=
  rfl

@[simp] protected lemma upper (s : UpperSet α) : IsUpperSet (s : Set α) := s.upper'

@[simp, norm_cast] lemma coe_mk (s : Set α) (hs) : mk s hs = s := rfl
@[simp] lemma mem_mk {s : Set α} (hs) {a : α} : a ∈ mk s hs ↔ a ∈ s := Iff.rfl

end UpperSet

namespace LowerSet

instance : SetLike (LowerSet α) α where
  coe := LowerSet.carrier
  coe_injective' s t h := by cases s; cases t; congr

/-- See Note [custom simps projection]. -/
def Simps.coe (s : LowerSet α) : Set α := s

initialize_simps_projections LowerSet (carrier → coe, as_prefix coe)

@[ext]
theorem ext {s t : LowerSet α} : (s : Set α) = t → s = t :=
  SetLike.ext'

@[simp]
theorem carrier_eq_coe (s : LowerSet α) : s.carrier = s :=
  rfl

@[simp] protected lemma lower (s : LowerSet α) : IsLowerSet (s : Set α) := s.lower'

@[simp, norm_cast] lemma coe_mk (s : Set α) (hs) : mk s hs = s := rfl
@[simp] lemma mem_mk {s : Set α} (hs) {a : α} : a ∈ mk s hs ↔ a ∈ s := Iff.rfl

end LowerSet

namespace UpperSet

variable {S : Set (UpperSet α)} {s t : UpperSet α} {a : α}

instance : Max (UpperSet α) :=
  ⟨fun s t => ⟨s ∩ t, s.upper.inter t.upper⟩⟩

instance : Min (UpperSet α) :=
  ⟨fun s t => ⟨s ∪ t, s.upper.union t.upper⟩⟩

instance : Top (UpperSet α) :=
  ⟨⟨∅, isUpperSet_empty⟩⟩

instance : Bot (UpperSet α) :=
  ⟨⟨univ, isUpperSet_univ⟩⟩

instance : SupSet (UpperSet α) :=
  ⟨fun S => ⟨⋂ s ∈ S, ↑s, isUpperSet_iInter₂ fun s _ => s.upper⟩⟩

instance : InfSet (UpperSet α) :=
  ⟨fun S => ⟨⋃ s ∈ S, ↑s, isUpperSet_iUnion₂ fun s _ => s.upper⟩⟩

instance completeLattice : CompleteLattice (UpperSet α) :=
  (toDual.injective.comp SetLike.coe_injective).completeLattice _ (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl rfl

instance completelyDistribLattice : CompletelyDistribLattice (UpperSet α) :=
  .ofMinimalAxioms <|
    (toDual.injective.comp SetLike.coe_injective).completelyDistribLatticeMinimalAxioms .of _
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl rfl

instance : Inhabited (UpperSet α) :=
  ⟨⊥⟩

@[simp 1100, norm_cast]
theorem coe_subset_coe : (s : Set α) ⊆ t ↔ t ≤ s :=
  Iff.rfl

@[simp 1100, norm_cast] lemma coe_ssubset_coe : (s : Set α) ⊂ t ↔ t < s := Iff.rfl

@[simp, norm_cast]
theorem coe_top : ((⊤ : UpperSet α) : Set α) = ∅ :=
  rfl

@[simp, norm_cast]
theorem coe_bot : ((⊥ : UpperSet α) : Set α) = univ :=
  rfl

@[simp, norm_cast]
theorem coe_eq_univ : (s : Set α) = univ ↔ s = ⊥ := by simp [SetLike.ext'_iff]

@[simp, norm_cast]
theorem coe_eq_empty : (s : Set α) = ∅ ↔ s = ⊤ := by simp [SetLike.ext'_iff]

@[simp, norm_cast] lemma coe_nonempty : (s : Set α).Nonempty ↔ s ≠ ⊤ :=
  nonempty_iff_ne_empty.trans coe_eq_empty.not

@[simp, norm_cast]
theorem coe_sup (s t : UpperSet α) : (↑(s ⊔ t) : Set α) = (s : Set α) ∩ t :=
  rfl

@[simp, norm_cast]
theorem coe_inf (s t : UpperSet α) : (↑(s ⊓ t) : Set α) = (s : Set α) ∪ t :=
  rfl

@[simp, norm_cast]
theorem coe_sSup (S : Set (UpperSet α)) : (↑(sSup S) : Set α) = ⋂ s ∈ S, ↑s :=
  rfl

@[simp, norm_cast]
theorem coe_sInf (S : Set (UpperSet α)) : (↑(sInf S) : Set α) = ⋃ s ∈ S, ↑s :=
  rfl

@[simp, norm_cast]
theorem coe_iSup (f : ι → UpperSet α) : (↑(⨆ i, f i) : Set α) = ⋂ i, f i := by simp [iSup]

@[simp, norm_cast]
theorem coe_iInf (f : ι → UpperSet α) : (↑(⨅ i, f i) : Set α) = ⋃ i, f i := by simp [iInf]

@[norm_cast]
theorem coe_iSup₂ (f : ∀ i, κ i → UpperSet α) :
    (↑(⨆ (i) (j), f i j) : Set α) = ⋂ (i) (j), f i j := by simp

@[norm_cast]
theorem coe_iInf₂ (f : ∀ i, κ i → UpperSet α) :
    (↑(⨅ (i) (j), f i j) : Set α) = ⋃ (i) (j), f i j := by simp

@[simp]
theorem notMem_top : a ∉ (⊤ : UpperSet α) :=
  id

@[deprecated (since := "2025-05-23")] alias not_mem_top := notMem_top

@[simp]
theorem mem_bot : a ∈ (⊥ : UpperSet α) :=
  trivial

@[simp]
theorem mem_sup_iff : a ∈ s ⊔ t ↔ a ∈ s ∧ a ∈ t :=
  Iff.rfl

@[simp]
theorem mem_inf_iff : a ∈ s ⊓ t ↔ a ∈ s ∨ a ∈ t :=
  Iff.rfl

@[simp]
theorem mem_sSup_iff : a ∈ sSup S ↔ ∀ s ∈ S, a ∈ s :=
  mem_iInter₂

@[simp]
theorem mem_sInf_iff : a ∈ sInf S ↔ ∃ s ∈ S, a ∈ s :=
  mem_iUnion₂.trans <| by simp only [exists_prop, SetLike.mem_coe]

@[simp]
theorem mem_iSup_iff {f : ι → UpperSet α} : (a ∈ ⨆ i, f i) ↔ ∀ i, a ∈ f i := by
  rw [← SetLike.mem_coe, coe_iSup]
  exact mem_iInter

@[simp]
theorem mem_iInf_iff {f : ι → UpperSet α} : (a ∈ ⨅ i, f i) ↔ ∃ i, a ∈ f i := by
  rw [← SetLike.mem_coe, coe_iInf]
  exact mem_iUnion

theorem mem_iSup₂_iff {f : ∀ i, κ i → UpperSet α} : (a ∈ ⨆ (i) (j), f i j) ↔ ∀ i j, a ∈ f i j := by
  simp

theorem mem_iInf₂_iff {f : ∀ i, κ i → UpperSet α} : (a ∈ ⨅ (i) (j), f i j) ↔ ∃ i j, a ∈ f i j := by
  simp

@[simp, norm_cast]
theorem codisjoint_coe : Codisjoint (s : Set α) t ↔ Disjoint s t := by
  simp [disjoint_iff, codisjoint_iff, SetLike.ext'_iff]

end UpperSet

namespace LowerSet

variable {S : Set (LowerSet α)} {s t : LowerSet α} {a : α}

instance : Max (LowerSet α) :=
  ⟨fun s t => ⟨s ∪ t, fun _ _ h => Or.imp (s.lower h) (t.lower h)⟩⟩

instance : Min (LowerSet α) :=
  ⟨fun s t => ⟨s ∩ t, fun _ _ h => And.imp (s.lower h) (t.lower h)⟩⟩

instance : Top (LowerSet α) :=
  ⟨⟨univ, fun _ _ _ => id⟩⟩

instance : Bot (LowerSet α) :=
  ⟨⟨∅, fun _ _ _ => id⟩⟩

instance : SupSet (LowerSet α) :=
  ⟨fun S => ⟨⋃ s ∈ S, ↑s, isLowerSet_iUnion₂ fun s _ => s.lower⟩⟩

instance : InfSet (LowerSet α) :=
  ⟨fun S => ⟨⋂ s ∈ S, ↑s, isLowerSet_iInter₂ fun s _ => s.lower⟩⟩

instance completeLattice : CompleteLattice (LowerSet α) :=
  SetLike.coe_injective.completeLattice _ (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ => rfl) rfl rfl

instance completelyDistribLattice : CompletelyDistribLattice (LowerSet α) :=
  .ofMinimalAxioms <| SetLike.coe_injective.completelyDistribLatticeMinimalAxioms .of _
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl rfl

instance : Inhabited (LowerSet α) :=
  ⟨⊥⟩

@[norm_cast] lemma coe_subset_coe : (s : Set α) ⊆ t ↔ s ≤ t := Iff.rfl

@[norm_cast] lemma coe_ssubset_coe : (s : Set α) ⊂ t ↔ s < t := Iff.rfl

@[simp, norm_cast]
theorem coe_top : ((⊤ : LowerSet α) : Set α) = univ :=
  rfl

@[simp, norm_cast]
theorem coe_bot : ((⊥ : LowerSet α) : Set α) = ∅ :=
  rfl

@[simp, norm_cast]
theorem coe_eq_univ : (s : Set α) = univ ↔ s = ⊤ := by simp [SetLike.ext'_iff]

@[simp, norm_cast]
theorem coe_eq_empty : (s : Set α) = ∅ ↔ s = ⊥ := by simp [SetLike.ext'_iff]

@[simp, norm_cast] lemma coe_nonempty : (s : Set α).Nonempty ↔ s ≠ ⊥ :=
  nonempty_iff_ne_empty.trans coe_eq_empty.not

@[simp, norm_cast]
theorem coe_sup (s t : LowerSet α) : (↑(s ⊔ t) : Set α) = (s : Set α) ∪ t :=
  rfl

@[simp, norm_cast]
theorem coe_inf (s t : LowerSet α) : (↑(s ⊓ t) : Set α) = (s : Set α) ∩ t :=
  rfl

@[simp, norm_cast]
theorem coe_sSup (S : Set (LowerSet α)) : (↑(sSup S) : Set α) = ⋃ s ∈ S, ↑s :=
  rfl

@[simp, norm_cast]
theorem coe_sInf (S : Set (LowerSet α)) : (↑(sInf S) : Set α) = ⋂ s ∈ S, ↑s :=
  rfl

@[simp, norm_cast]
theorem coe_iSup (f : ι → LowerSet α) : (↑(⨆ i, f i) : Set α) = ⋃ i, f i := by
  simp_rw [iSup, coe_sSup, mem_range, iUnion_exists, iUnion_iUnion_eq']

@[simp, norm_cast]
theorem coe_iInf (f : ι → LowerSet α) : (↑(⨅ i, f i) : Set α) = ⋂ i, f i := by
  simp_rw [iInf, coe_sInf, mem_range, iInter_exists, iInter_iInter_eq']

@[norm_cast]
theorem coe_iSup₂ (f : ∀ i, κ i → LowerSet α) :
    (↑(⨆ (i) (j), f i j) : Set α) = ⋃ (i) (j), f i j := by simp

@[norm_cast]
theorem coe_iInf₂ (f : ∀ i, κ i → LowerSet α) :
    (↑(⨅ (i) (j), f i j) : Set α) = ⋂ (i) (j), f i j := by simp

@[simp]
theorem mem_top : a ∈ (⊤ : LowerSet α) :=
  trivial

@[simp]
theorem notMem_bot : a ∉ (⊥ : LowerSet α) :=
  id

@[deprecated (since := "2025-05-23")] alias not_mem_bot := notMem_bot

@[simp]
theorem mem_sup_iff : a ∈ s ⊔ t ↔ a ∈ s ∨ a ∈ t :=
  Iff.rfl

@[simp]
theorem mem_inf_iff : a ∈ s ⊓ t ↔ a ∈ s ∧ a ∈ t :=
  Iff.rfl

@[simp]
theorem mem_sSup_iff : a ∈ sSup S ↔ ∃ s ∈ S, a ∈ s :=
  mem_iUnion₂.trans <| by simp only [exists_prop, SetLike.mem_coe]

@[simp]
theorem mem_sInf_iff : a ∈ sInf S ↔ ∀ s ∈ S, a ∈ s :=
  mem_iInter₂

@[simp]
theorem mem_iSup_iff {f : ι → LowerSet α} : (a ∈ ⨆ i, f i) ↔ ∃ i, a ∈ f i := by
  rw [← SetLike.mem_coe, coe_iSup]
  exact mem_iUnion

@[simp]
theorem mem_iInf_iff {f : ι → LowerSet α} : (a ∈ ⨅ i, f i) ↔ ∀ i, a ∈ f i := by
  rw [← SetLike.mem_coe, coe_iInf]
  exact mem_iInter

theorem mem_iSup₂_iff {f : ∀ i, κ i → LowerSet α} : (a ∈ ⨆ (i) (j), f i j) ↔ ∃ i j, a ∈ f i j := by
  simp

theorem mem_iInf₂_iff {f : ∀ i, κ i → LowerSet α} : (a ∈ ⨅ (i) (j), f i j) ↔ ∀ i j, a ∈ f i j := by
  simp

@[simp, norm_cast]
theorem disjoint_coe : Disjoint (s : Set α) t ↔ Disjoint s t := by
  simp [disjoint_iff, SetLike.ext'_iff]

end LowerSet

/-! ### Complement -/

/-- The complement of a lower set as an upper set. -/
def UpperSet.compl (s : UpperSet α) : LowerSet α :=
  ⟨sᶜ, s.upper.compl⟩

/-- The complement of a lower set as an upper set. -/
def LowerSet.compl (s : LowerSet α) : UpperSet α :=
  ⟨sᶜ, s.lower.compl⟩

namespace UpperSet

variable {s t : UpperSet α} {a : α}

@[simp]
theorem coe_compl (s : UpperSet α) : (s.compl : Set α) = (↑s)ᶜ :=
  rfl

@[simp]
theorem mem_compl_iff : a ∈ s.compl ↔ a ∉ s :=
  Iff.rfl

@[simp]
nonrec theorem compl_compl (s : UpperSet α) : s.compl.compl = s :=
  UpperSet.ext <| compl_compl _

@[simp]
theorem compl_le_compl : s.compl ≤ t.compl ↔ s ≤ t :=
  compl_subset_compl

@[simp]
protected theorem compl_sup (s t : UpperSet α) : (s ⊔ t).compl = s.compl ⊔ t.compl :=
  LowerSet.ext compl_inf

@[simp]
protected theorem compl_inf (s t : UpperSet α) : (s ⊓ t).compl = s.compl ⊓ t.compl :=
  LowerSet.ext compl_sup

@[simp]
protected theorem compl_top : (⊤ : UpperSet α).compl = ⊤ :=
  LowerSet.ext compl_empty

@[simp]
protected theorem compl_bot : (⊥ : UpperSet α).compl = ⊥ :=
  LowerSet.ext compl_univ

@[simp]
protected theorem compl_sSup (S : Set (UpperSet α)) : (sSup S).compl = ⨆ s ∈ S, UpperSet.compl s :=
  LowerSet.ext <| by simp only [coe_compl, coe_sSup, compl_iInter₂, LowerSet.coe_iSup₂]

@[simp]
protected theorem compl_sInf (S : Set (UpperSet α)) : (sInf S).compl = ⨅ s ∈ S, UpperSet.compl s :=
  LowerSet.ext <| by simp only [coe_compl, coe_sInf, compl_iUnion₂, LowerSet.coe_iInf₂]

@[simp]
protected theorem compl_iSup (f : ι → UpperSet α) : (⨆ i, f i).compl = ⨆ i, (f i).compl :=
  LowerSet.ext <| by simp only [coe_compl, coe_iSup, compl_iInter, LowerSet.coe_iSup]

@[simp]
protected theorem compl_iInf (f : ι → UpperSet α) : (⨅ i, f i).compl = ⨅ i, (f i).compl :=
  LowerSet.ext <| by simp only [coe_compl, coe_iInf, compl_iUnion, LowerSet.coe_iInf]

theorem compl_iSup₂ (f : ∀ i, κ i → UpperSet α) :
    (⨆ (i) (j), f i j).compl = ⨆ (i) (j), (f i j).compl := by simp

theorem compl_iInf₂ (f : ∀ i, κ i → UpperSet α) :
    (⨅ (i) (j), f i j).compl = ⨅ (i) (j), (f i j).compl := by simp

end UpperSet

namespace LowerSet

variable {s t : LowerSet α} {a : α}

@[simp]
theorem coe_compl (s : LowerSet α) : (s.compl : Set α) = (↑s)ᶜ :=
  rfl

@[simp]
theorem mem_compl_iff : a ∈ s.compl ↔ a ∉ s :=
  Iff.rfl

@[simp]
nonrec theorem compl_compl (s : LowerSet α) : s.compl.compl = s :=
  LowerSet.ext <| compl_compl _

@[simp]
theorem compl_le_compl : s.compl ≤ t.compl ↔ s ≤ t :=
  compl_subset_compl

protected theorem compl_sup (s t : LowerSet α) : (s ⊔ t).compl = s.compl ⊔ t.compl :=
  UpperSet.ext compl_sup

protected theorem compl_inf (s t : LowerSet α) : (s ⊓ t).compl = s.compl ⊓ t.compl :=
  UpperSet.ext compl_inf

protected theorem compl_top : (⊤ : LowerSet α).compl = ⊤ :=
  UpperSet.ext compl_univ

protected theorem compl_bot : (⊥ : LowerSet α).compl = ⊥ :=
  UpperSet.ext compl_empty

protected theorem compl_sSup (S : Set (LowerSet α)) : (sSup S).compl = ⨆ s ∈ S, LowerSet.compl s :=
  UpperSet.ext <| by simp only [coe_compl, coe_sSup, compl_iUnion₂, UpperSet.coe_iSup₂]

protected theorem compl_sInf (S : Set (LowerSet α)) : (sInf S).compl = ⨅ s ∈ S, LowerSet.compl s :=
  UpperSet.ext <| by simp only [coe_compl, coe_sInf, compl_iInter₂, UpperSet.coe_iInf₂]

protected theorem compl_iSup (f : ι → LowerSet α) : (⨆ i, f i).compl = ⨆ i, (f i).compl :=
  UpperSet.ext <| by simp only [coe_compl, coe_iSup, compl_iUnion, UpperSet.coe_iSup]

protected theorem compl_iInf (f : ι → LowerSet α) : (⨅ i, f i).compl = ⨅ i, (f i).compl :=
  UpperSet.ext <| by simp only [coe_compl, coe_iInf, compl_iInter, UpperSet.coe_iInf]

@[simp]
theorem compl_iSup₂ (f : ∀ i, κ i → LowerSet α) :
    (⨆ (i) (j), f i j).compl = ⨆ (i) (j), (f i j).compl := by simp_rw [LowerSet.compl_iSup]

@[simp]
theorem compl_iInf₂ (f : ∀ i, κ i → LowerSet α) :
    (⨅ (i) (j), f i j).compl = ⨅ (i) (j), (f i j).compl := by simp_rw [LowerSet.compl_iInf]

end LowerSet

/-- Upper sets are order-isomorphic to lower sets under complementation. -/
@[simps]
def upperSetIsoLowerSet : UpperSet α ≃o LowerSet α where
  toFun := UpperSet.compl
  invFun := LowerSet.compl
  left_inv := UpperSet.compl_compl
  right_inv := LowerSet.compl_compl
  map_rel_iff' := UpperSet.compl_le_compl

end LE

section LinearOrder
variable [LinearOrder α]

instance UpperSet.inst_stdTotal_le : Std.Total (α := UpperSet α) (· ≤ ·) :=
  ⟨fun s t => t.upper.total s.upper⟩

instance LowerSet.inst_stdTotal_le : Std.Total (α := LowerSet α) (· ≤ ·) :=
  ⟨fun s t => s.lower.total t.lower⟩

noncomputable instance UpperSet.instLinearOrder : LinearOrder (UpperSet α) := by
  classical exact Lattice.toLinearOrder _

noncomputable instance LowerSet.instLinearOrder : LinearOrder (LowerSet α) := by
  classical exact Lattice.toLinearOrder _

noncomputable instance UpperSet.instCompleteLinearOrder : CompleteLinearOrder (UpperSet α) :=
  { completelyDistribLattice, instLinearOrder with }

noncomputable instance LowerSet.instCompleteLinearOrder : CompleteLinearOrder (LowerSet α) :=
  { completelyDistribLattice, instLinearOrder with }

end LinearOrder

section Map

variable [Preorder α] [Preorder β] [Preorder γ]

namespace UpperSet

variable {f : α ≃o β} {s t : UpperSet α} {a : α} {b : β}

/-- An order isomorphism of Preorders induces an order isomorphism of their upper sets. -/
def map (f : α ≃o β) : UpperSet α ≃o UpperSet β where
  toFun s := ⟨f '' s, s.upper.image f⟩
  invFun t := ⟨f ⁻¹' t, t.upper.preimage f.monotone⟩
  left_inv _ := ext <| f.preimage_image _
  right_inv _ := ext <| f.image_preimage _
  map_rel_iff' := image_subset_image_iff f.injective

@[simp]
theorem symm_map (f : α ≃o β) : (map f).symm = map f.symm :=
  DFunLike.ext _ _ fun s => ext <| by convert Set.preimage_equiv_eq_image_symm s f.toEquiv

@[simp]
theorem mem_map : b ∈ map f s ↔ f.symm b ∈ s := by
  rw [← f.symm_symm, ← symm_map, f.symm_symm]
  rfl

@[simp]
theorem map_refl : map (OrderIso.refl α) = OrderIso.refl _ := by
  ext
  simp

@[simp]
theorem map_map (g : β ≃o γ) (f : α ≃o β) : map g (map f s) = map (f.trans g) s := by
  ext
  simp

variable (f s t)

@[simp, norm_cast]
theorem coe_map : (map f s : Set β) = f '' s :=
  rfl

end UpperSet

namespace LowerSet

variable {f : α ≃o β} {s t : LowerSet α} {a : α}

/-- An order isomorphism of Preorders induces an order isomorphism of their lower sets. -/
def map (f : α ≃o β) : LowerSet α ≃o LowerSet β where
  toFun s := ⟨f '' s, s.lower.image f⟩
  invFun t := ⟨f ⁻¹' t, t.lower.preimage f.monotone⟩
  left_inv _ := SetLike.coe_injective <| f.preimage_image _
  right_inv _ := SetLike.coe_injective <| f.image_preimage _
  map_rel_iff' := image_subset_image_iff f.injective

@[simp]
theorem symm_map (f : α ≃o β) : (map f).symm = map f.symm :=
  DFunLike.ext _ _ fun s => ext <| by convert Set.preimage_equiv_eq_image_symm s f.toEquiv

@[simp]
theorem mem_map {f : α ≃o β} {b : β} : b ∈ map f s ↔ f.symm b ∈ s := by
  rw [← f.symm_symm, ← symm_map, f.symm_symm]
  rfl

@[simp]
theorem map_refl : map (OrderIso.refl α) = OrderIso.refl _ := by
  ext
  simp

@[simp]
theorem map_map (g : β ≃o γ) (f : α ≃o β) : map g (map f s) = map (f.trans g) s := by
  ext
  simp

variable (f s t)

@[simp, norm_cast]
theorem coe_map : (map f s : Set β) = f '' s :=
  rfl

end LowerSet

namespace UpperSet

@[simp]
theorem compl_map (f : α ≃o β) (s : UpperSet α) : (map f s).compl = LowerSet.map f s.compl :=
  SetLike.coe_injective (Set.image_compl_eq f.bijective).symm

end UpperSet

namespace LowerSet

@[simp]
theorem compl_map (f : α ≃o β) (s : LowerSet α) : (map f s).compl = UpperSet.map f s.compl :=
  SetLike.coe_injective (Set.image_compl_eq f.bijective).symm

end LowerSet

end Map
