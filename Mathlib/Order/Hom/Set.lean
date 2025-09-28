/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Logic.Equiv.Set
import Mathlib.Order.Hom.Basic
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Order.WellFounded
import Mathlib.Tactic.MinImports

/-!
# Order homomorphisms and sets
-/


open OrderDual Set

variable {α β : Type*}

namespace Set

/-- Sets on sum types are order-equivalent to pairs of sets on each summand. -/
def sumEquiv : Set (α ⊕ β) ≃o Set α × Set β where
  toFun s := (Sum.inl ⁻¹' s, Sum.inr ⁻¹' s)
  invFun s := Sum.inl '' s.1 ∪ Sum.inr '' s.2
  left_inv s := image_preimage_inl_union_image_preimage_inr s
  right_inv s := by
    simp [preimage_image_eq _ Sum.inl_injective, preimage_image_eq _ Sum.inr_injective]
  map_rel_iff' := by simp [subset_def]

end Set

namespace OrderIso

section LE

variable [LE α] [LE β]

theorem range_eq (e : α ≃o β) : Set.range e = Set.univ :=
  e.surjective.range_eq

@[simp]
theorem symm_image_image (e : α ≃o β) (s : Set α) : e.symm '' (e '' s) = s :=
  e.toEquiv.symm_image_image s

@[simp]
theorem image_symm_image (e : α ≃o β) (s : Set β) : e '' (e.symm '' s) = s :=
  e.toEquiv.image_symm_image s

theorem image_eq_preimage (e : α ≃o β) (s : Set α) : e '' s = e.symm ⁻¹' s :=
  e.toEquiv.image_eq_preimage s

@[simp]
theorem preimage_symm_preimage (e : α ≃o β) (s : Set α) : e ⁻¹' (e.symm ⁻¹' s) = s :=
  e.toEquiv.preimage_symm_preimage s

@[simp]
theorem symm_preimage_preimage (e : α ≃o β) (s : Set β) : e.symm ⁻¹' (e ⁻¹' s) = s :=
  e.toEquiv.symm_preimage_preimage s

@[simp]
theorem image_preimage (e : α ≃o β) (s : Set β) : e '' (e ⁻¹' s) = s :=
  e.toEquiv.image_preimage s

@[simp]
theorem preimage_image (e : α ≃o β) (s : Set α) : e ⁻¹' (e '' s) = s :=
  e.toEquiv.preimage_image s

end LE

open Set

variable [Preorder α]

/-- Order isomorphism between two equal sets. -/
@[simps! apply symm_apply]
def setCongr (s t : Set α) (h : s = t) :
    s ≃o t where
  toEquiv := Equiv.setCongr h
  map_rel_iff' := Iff.rfl

/-- Order isomorphism between `univ : Set α` and `α`. -/
def Set.univ : (Set.univ : Set α) ≃o α where
  toEquiv := Equiv.Set.univ α
  map_rel_iff' := Iff.rfl

end OrderIso

/-- We can regard an order embedding as an order isomorphism to its range. -/
@[simps! apply]
noncomputable def OrderEmbedding.orderIso [LE α] [LE β] {f : α ↪o β} :
    α ≃o Set.range f :=
  { Equiv.ofInjective _ f.injective with
    map_rel_iff' := f.map_rel_iff }

/-- If a function `f` is strictly monotone on a set `s`, then it defines an order isomorphism
between `s` and its image. -/
protected noncomputable def StrictMonoOn.orderIso {α β} [LinearOrder α] [Preorder β] (f : α → β)
    (s : Set α) (hf : StrictMonoOn f s) :
    s ≃o f '' s where
  toEquiv := hf.injOn.bijOn_image.equiv _
  map_rel_iff' := hf.le_iff_le (Subtype.property _) (Subtype.property _)

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

/-- A strictly monotone surjective function from a linear order is an order isomorphism. -/
noncomputable def orderIsoOfSurjective : α ≃o β :=
  (h_mono.orderIso f).trans <|
    (OrderIso.setCongr _ _ h_surj.range_eq).trans OrderIso.Set.univ

@[simp]
theorem coe_orderIsoOfSurjective : (orderIsoOfSurjective f h_mono h_surj : α → β) = f :=
  rfl

@[simp]
theorem orderIsoOfSurjective_symm_apply_self (a : α) :
    (orderIsoOfSurjective f h_mono h_surj).symm (f a) = a :=
  (orderIsoOfSurjective f h_mono h_surj).symm_apply_apply _

theorem orderIsoOfSurjective_self_symm_apply (b : β) :
    f ((orderIsoOfSurjective f h_mono h_surj).symm b) = b :=
  (orderIsoOfSurjective f h_mono h_surj).apply_symm_apply _

end StrictMono

/-- Two order embeddings on a well-order are equal provided that their ranges are equal. -/
lemma OrderEmbedding.range_inj [LinearOrder α] [WellFoundedLT α] [Preorder β] {f g : α ↪o β} :
    Set.range f = Set.range g ↔ f = g := by
  rw [f.strictMono.range_inj g.strictMono, DFunLike.coe_fn_eq]

namespace OrderIso

-- These results are also true whenever β is well-founded instead of α.
-- You can use `RelEmbedding.isWellFounded` to transfer the instance over.

instance subsingleton_of_wellFoundedLT [LinearOrder α] [WellFoundedLT α] [Preorder β] :
    Subsingleton (α ≃o β) := by
  refine ⟨fun f g ↦ ?_⟩
  rw [OrderIso.ext_iff, ← coe_toOrderEmbedding, ← coe_toOrderEmbedding, DFunLike.coe_fn_eq,
    ← OrderEmbedding.range_inj, coe_toOrderEmbedding, coe_toOrderEmbedding, range_eq, range_eq]

instance subsingleton_of_wellFoundedLT' [LinearOrder β] [WellFoundedLT β] [Preorder α] :
    Subsingleton (α ≃o β) := by
  refine ⟨fun f g ↦ ?_⟩
  change f.symm.symm = g.symm.symm
  rw [Subsingleton.elim f.symm]

instance unique_of_wellFoundedLT [LinearOrder α] [WellFoundedLT α] : Unique (α ≃o α) := Unique.mk' _

instance subsingleton_of_wellFoundedGT [LinearOrder α] [WellFoundedGT α] [Preorder β] :
    Subsingleton (α ≃o β) := by
  refine ⟨fun f g ↦ ?_⟩
  change f.dual.dual = g.dual.dual
  rw [Subsingleton.elim f.dual]

instance subsingleton_of_wellFoundedGT' [LinearOrder β] [WellFoundedGT β] [Preorder α] :
    Subsingleton (α ≃o β) := by
  refine ⟨fun f g ↦ ?_⟩
  change f.dual.dual = g.dual.dual
  rw [Subsingleton.elim f.dual]

instance unique_of_wellFoundedGT [LinearOrder α] [WellFoundedGT α] : Unique (α ≃o α) := Unique.mk' _

/-- An order isomorphism between lattices induces an order isomorphism between corresponding
interval sublattices. -/
protected def Iic [Lattice α] [Lattice β] (e : α ≃o β) (x : α) :
    Iic x ≃o Iic (e x) where
  toFun y := ⟨e y, (map_le_map_iff _).mpr y.property⟩
  invFun y := ⟨e.symm y, e.symm_apply_le.mpr y.property⟩
  left_inv y := by simp
  right_inv y := by simp
  map_rel_iff' := by simp

/-- An order isomorphism between lattices induces an order isomorphism between corresponding
interval sublattices. -/
protected def Ici [Lattice α] [Lattice β] (e : α ≃o β) (x : α) :
    Ici x ≃o Ici (e x) where
  toFun y := ⟨e y, (map_le_map_iff _).mpr y.property⟩
  invFun y := ⟨e.symm y, e.le_symm_apply.mpr y.property⟩
  left_inv y := by simp
  right_inv y := by simp
  map_rel_iff' := by simp

/-- An order isomorphism between lattices induces an order isomorphism between corresponding
interval sublattices. -/
protected def Icc [Lattice α] [Lattice β] (e : α ≃o β) (x y : α) :
    Icc x y ≃o Icc (e x) (e y) where
  toFun z := ⟨e z, by simp only [mem_Icc, map_le_map_iff]; exact z.property⟩
  invFun z := ⟨e.symm z, by simp only [mem_Icc, e.le_symm_apply, e.symm_apply_le]; exact z.property⟩
  left_inv y := by simp
  right_inv y := by simp
  map_rel_iff' := by simp

end OrderIso

section BooleanAlgebra

variable (α) [BooleanAlgebra α]

/-- Taking complements as an order isomorphism to the order dual. -/
@[simps!]
def OrderIso.compl : α ≃o αᵒᵈ where
  toFun := OrderDual.toDual ∘ HasCompl.compl
  invFun := HasCompl.compl ∘ OrderDual.ofDual
  left_inv := compl_compl
  right_inv := compl_compl (α := αᵒᵈ)
  map_rel_iff' := compl_le_compl_iff_le

theorem compl_strictAnti : StrictAnti (compl : α → α) :=
  (OrderIso.compl α).strictMono

theorem compl_antitone : Antitone (compl : α → α) :=
  (OrderIso.compl α).monotone

end BooleanAlgebra
