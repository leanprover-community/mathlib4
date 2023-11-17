/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Order.Hom.Basic
import Mathlib.Logic.Equiv.Set
import Mathlib.Data.Set.Image

#align_import order.hom.set from "leanprover-community/mathlib"@"198161d833f2c01498c39c266b0b3dbe2c7a8c07"

/-!
# Order homomorphisms and sets
-/


open OrderDual

variable {F α β γ δ : Type*}

namespace OrderIso

section LE

variable [LE α] [LE β] [LE γ]

theorem range_eq (e : α ≃o β) : Set.range e = Set.univ :=
  e.surjective.range_eq
#align order_iso.range_eq OrderIso.range_eq

@[simp]
theorem symm_image_image (e : α ≃o β) (s : Set α) : e.symm '' (e '' s) = s :=
  e.toEquiv.symm_image_image s
#align order_iso.symm_image_image OrderIso.symm_image_image

@[simp]
theorem image_symm_image (e : α ≃o β) (s : Set β) : e '' (e.symm '' s) = s :=
  e.toEquiv.image_symm_image s
#align order_iso.image_symm_image OrderIso.image_symm_image

theorem image_eq_preimage (e : α ≃o β) (s : Set α) : e '' s = e.symm ⁻¹' s :=
  e.toEquiv.image_eq_preimage s
#align order_iso.image_eq_preimage OrderIso.image_eq_preimage

@[simp]
theorem preimage_symm_preimage (e : α ≃o β) (s : Set α) : e ⁻¹' (e.symm ⁻¹' s) = s :=
  e.toEquiv.preimage_symm_preimage s
#align order_iso.preimage_symm_preimage OrderIso.preimage_symm_preimage

@[simp]
theorem symm_preimage_preimage (e : α ≃o β) (s : Set β) : e.symm ⁻¹' (e ⁻¹' s) = s :=
  e.toEquiv.symm_preimage_preimage s
#align order_iso.symm_preimage_preimage OrderIso.symm_preimage_preimage

@[simp]
theorem image_preimage (e : α ≃o β) (s : Set β) : e '' (e ⁻¹' s) = s :=
  e.toEquiv.image_preimage s
#align order_iso.image_preimage OrderIso.image_preimage

@[simp]
theorem preimage_image (e : α ≃o β) (s : Set α) : e ⁻¹' (e '' s) = s :=
  e.toEquiv.preimage_image s
#align order_iso.preimage_image OrderIso.preimage_image

end LE

open Set

variable [Preorder α] [Preorder β] [Preorder γ]

/-- Order isomorphism between two equal sets. -/
def setCongr (s t : Set α) (h : s = t) :
    s ≃o t where
  toEquiv := Equiv.setCongr h
  map_rel_iff' := Iff.rfl
#align order_iso.set_congr OrderIso.setCongr

/-- Order isomorphism between `univ : Set α` and `α`. -/
def Set.univ : (Set.univ : Set α) ≃o α where
  toEquiv := Equiv.Set.univ α
  map_rel_iff' := Iff.rfl
#align order_iso.set.univ OrderIso.Set.univ

end OrderIso

/-- If a function `f` is strictly monotone on a set `s`, then it defines an order isomorphism
between `s` and its image. -/
protected noncomputable def StrictMonoOn.orderIso {α β} [LinearOrder α] [Preorder β] (f : α → β)
    (s : Set α) (hf : StrictMonoOn f s) :
    s ≃o f '' s where
  toEquiv := hf.injOn.bijOn_image.equiv _
  map_rel_iff' := hf.le_iff_le (Subtype.property _) (Subtype.property _)
#align strict_mono_on.order_iso StrictMonoOn.orderIso

namespace StrictMono

variable [LinearOrder α] [Preorder β]

variable (f : α → β) (h_mono : StrictMono f) (h_surj : Function.Surjective f)

/-- A strictly monotone function from a linear order is an order isomorphism between its domain and
its range. -/
@[simps! apply]
protected noncomputable def orderIso :
    α ≃o Set.range f where
  toEquiv := Equiv.ofInjective f h_mono.injective
  map_rel_iff' := h_mono.le_iff_le
#align strict_mono.order_iso StrictMono.orderIso
#align strict_mono.order_iso_apply StrictMono.orderIso_apply

/-- A strictly monotone surjective function from a linear order is an order isomorphism. -/
noncomputable def orderIsoOfSurjective : α ≃o β :=
  (h_mono.orderIso f).trans <|
    (OrderIso.setCongr _ _ h_surj.range_eq).trans OrderIso.Set.univ
#align strict_mono.order_iso_of_surjective StrictMono.orderIsoOfSurjective

@[simp]
theorem coe_orderIsoOfSurjective : (orderIsoOfSurjective f h_mono h_surj : α → β) = f :=
  rfl
#align strict_mono.coe_order_iso_of_surjective StrictMono.coe_orderIsoOfSurjective

@[simp]
theorem orderIsoOfSurjective_symm_apply_self (a : α) :
    (orderIsoOfSurjective f h_mono h_surj).symm (f a) = a :=
  (orderIsoOfSurjective f h_mono h_surj).symm_apply_apply _
#align strict_mono.order_iso_of_surjective_symm_apply_self StrictMono.orderIsoOfSurjective_symm_apply_self

theorem orderIsoOfSurjective_self_symm_apply (b : β) :
    f ((orderIsoOfSurjective f h_mono h_surj).symm b) = b :=
  (orderIsoOfSurjective f h_mono h_surj).apply_symm_apply _
#align strict_mono.order_iso_of_surjective_self_symm_apply StrictMono.orderIsoOfSurjective_self_symm_apply

end StrictMono

section BooleanAlgebra

variable (α) [BooleanAlgebra α]

/-- Taking complements as an order isomorphism to the order dual. -/
@[simps]
def OrderIso.compl : α ≃o αᵒᵈ where
  toFun := OrderDual.toDual ∘ HasCompl.compl
  invFun := HasCompl.compl ∘ OrderDual.ofDual
  left_inv := compl_compl
  right_inv := compl_compl (α := αᵒᵈ)
  map_rel_iff' := compl_le_compl_iff_le
#align order_iso.compl OrderIso.compl
#align order_iso.compl_symm_apply OrderIso.compl_symm_apply
#align order_iso.compl_apply OrderIso.compl_apply

theorem compl_strictAnti : StrictAnti (compl : α → α) :=
  (OrderIso.compl α).strictMono
#align compl_strict_anti compl_strictAnti

theorem compl_antitone : Antitone (compl : α → α) :=
  (OrderIso.compl α).monotone
#align compl_antitone compl_antitone

end BooleanAlgebra

section Set

variable {s t : Set α}

/-- Equivalent types have order-isomorphic types of subsets. --/
def Equiv.setOrderIso (e : α ≃ β) : Set α ≃o Set β where
  toEquiv := Equiv.Set.congr e
  map_rel_iff' := by simp

@[simp] theorem Equiv.setOrderIso_toEquiv (e : α ≃ β) :
    e.setOrderIso.toEquiv = Equiv.Set.congr e := rfl

@[simp] theorem Equiv.setOrderIso_apply (e : α ≃ β) (s : Set α) :
    e.setOrderIso s = e '' s := rfl

@[simp] theorem Equiv.setOrderIso_apply_symm (e : α ≃ β) (s : Set β) :
    e.setOrderIso.symm s = e.symm '' s := rfl

@[simp] theorem Equiv.setOrderIso_subset_iff (e : α ≃ β) :
    e.setOrderIso s ⊆ e.setOrderIso t ↔ s ⊆ t :=
  e.setOrderIso.map_rel_iff

@[simp] theorem Equiv.setOrderIso_symm_subset_iff (e : α ≃ β) {s t : Set β} :
    e.setOrderIso.symm s ⊆ e.setOrderIso.symm t ↔ s ⊆ t :=
  e.setOrderIso.symm.map_rel_iff

/-- An injection from `α` to `β` gives one from `Set α` to `Set β`.  -/
def Function.Embedding.setEmbedding (f : α ↪ β) : Set α ↪ Set β where
  toFun := Set.image f
  inj' := Set.image_injective.2 f.injective

@[simp] theorem Function.Embedding.setEmbedding_apply (f : α ↪ β) (s : Set α) :
    f.setEmbedding s = f '' s := rfl

/-- An injection from `α` to `β` gives an order embedding from `Set α` to `Set β`.  -/
def Function.Embedding.setOrderEmbedding (f : α ↪ β) : Set α ↪o Set β where
  toEmbedding := f.setEmbedding
  map_rel_iff' := fun {_} {_} ↦ Set.image_subset_image_iff f.injective

@[simp] theorem Function.Embedding.setOrderEmbedding_apply (f : α ↪ β) (s : Set α) :
    f.setOrderEmbedding s = f '' s := rfl

@[simp] theorem Function.Embedding.setOrderEmbedding_toEmbedding (f : α ↪ β) :
    f.setOrderEmbedding.toEmbedding = f.setEmbedding := rfl

/-- Given `s : Set α`, the natural order-embedding from `Set s` to `Set α`. -/
def Set.subtypeOrderEmbedding (s : Set α) : Set s ↪o Set α :=
  (Function.Embedding.subtype _).setOrderEmbedding

theorem Set.subtypeOrderEmbedding_apply (s : Set α) (t : Set s) :
    (s.subtypeOrderEmbedding t : Set α) = (fun (x : s) ↦ (x : α)) '' t := rfl

@[simp] theorem Set.mem_subtypeOrderEmbedding_iff (s : Set α) {x : α} {r : Set s} :
    x ∈ (s.subtypeOrderEmbedding r : Set α) ↔ ∃ (hx : x ∈ s), ⟨x,hx⟩ ∈ r := by
  simp [Set.subtypeOrderEmbedding]

@[simp] theorem Set.subtypeOrderEmbedding_subset_iff (s : Set α) {r r' : Set s} :
    (s.subtypeOrderEmbedding r : Set α) ⊆ s.subtypeOrderEmbedding r' ↔ r ⊆ r' :=
  s.subtypeOrderEmbedding.map_rel_iff'

/-- Given `s : Set α`, the type `Set s` is order-isomorphic to the type of subsets of `s`. -/
def Set.subtypeOrderIso (s : Set α) : Set s ≃o {t : Set α // t ⊆ s} where
  toFun r := ⟨(fun (x : s) ↦ (x : α)) '' r, by rintro _ ⟨⟨x,h⟩, _, rfl⟩; exact h⟩
  invFun r := (fun (x : s) ↦ (x : α)) ⁻¹' r
  left_inv := fun _ ↦ preimage_image_eq _ Subtype.val_injective
  right_inv := fun r ↦ by cases r; simpa
  map_rel_iff' := by simp [preimage_image_eq _ Subtype.val_injective]

theorem Set.subtypeOrderIso_apply (s : Set α) (t : Set s) :
    (s.subtypeOrderIso t : Set α) = (fun (x : s) ↦ (x : α)) '' t := rfl

theorem Set.subtypeOrderIso_apply_symm {s : Set α} (t : {r : Set α // r ⊆ s}) :
    s.subtypeOrderIso.symm t = (fun (x : s) ↦ (x : α)) ⁻¹' t := rfl

@[simp] theorem Set.subtypeOrderIso_subset_iff (s : Set α) {r r' : Set s} :
    (s.subtypeOrderIso r : Set α) ⊆ s.subtypeOrderIso r' ↔ r ⊆ r' :=
  s.subtypeOrderIso.map_rel_iff'

@[simp] theorem Set.subtypeOrderIso_symm_subset_iff (s : Set α) {r r' : {t : Set α // t ⊆ s}} :
    s.subtypeOrderIso.symm r ⊆ s.subtypeOrderIso.symm r' ↔ (r : Set α) ⊆ r' :=
  s.subtypeOrderIso.symm.map_rel_iff'

@[simp] theorem Set.mem_subtypeOrderIso_iff (s : Set α) {x : α} {r : Set s} :
    x ∈ (s.subtypeOrderIso r : Set α) ↔ ∃ (hx : x ∈ s), ⟨x,hx⟩ ∈ r := by
  simp [Set.subtypeOrderIso]

@[simp] theorem Set.mem_subtypeOrderIso_iff' (s : Set α) {x : α} {r : Set s} :
    x ∈ (s.subtypeOrderIso r : Set α) ↔ ∃ y, y ∈ r ∧ y = x := Iff.rfl

@[simp] theorem Set.mem_subtypeOrderIso_symm_iff (s : Set α) (x : s) (t : {t : Set α // t ⊆ s}) :
    x ∈ s.subtypeOrderIso.symm t ↔ (x : α) ∈ (t : Set α) := Iff.rfl

end Set
