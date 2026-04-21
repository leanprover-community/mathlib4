/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Pi
public import Mathlib.Data.Finset.Sigma
public import Mathlib.Data.Set.Finite.Basic

/-!
# Preimage of a `Finset` under an injective map.
-/

@[expose] public section

assert_not_exists Finset.sum

open Set Function

universe u v w x

variable {α : Type u} {β : Type v} {ι : Sort w} {γ : Type x}

namespace Finset

section Preimage

/-- Preimage of `s : Finset β` under a map `f` injective on `f ⁻¹' s` as a `Finset`. -/
noncomputable def preimage (s : Finset β) (f : α → β) (hf : Set.InjOn f (f ⁻¹' ↑s)) : Finset α :=
  (s.finite_toSet.preimage hf).toFinset

@[simp]
theorem mem_preimage {f : α → β} {s : Finset β} {hf : Set.InjOn f (f ⁻¹' ↑s)} {x : α} :
    x ∈ preimage s f hf ↔ f x ∈ s :=
  Set.Finite.mem_toFinset _

@[simp, norm_cast]
theorem coe_preimage {f : α → β} (s : Finset β) (hf : Set.InjOn f (f ⁻¹' ↑s)) :
    (↑(preimage s f hf) : Set α) = f ⁻¹' ↑s :=
  Set.Finite.coe_toFinset _

@[simp]
theorem preimage_empty {f : α → β} : preimage ∅ f (by simp [InjOn]) = ∅ :=
  Finset.coe_injective (by simp)

@[simp]
theorem preimage_univ {f : α → β} [Fintype α] [Fintype β] (hf) : preimage univ f hf = univ :=
  Finset.coe_injective (by simp)

@[simp]
theorem disjoint_preimage {f : α → β} {s t : Finset β}
    {hs : Set.InjOn f (f ⁻¹' ↑s)} {ht : Set.InjOn f (f ⁻¹' ↑t)} (hd : Disjoint s t) :
    Disjoint (s.preimage f hs) (t.preimage f ht) := by
  grind [not_disjoint_iff, mem_preimage]

@[simp]
theorem preimage_inter [DecidableEq α] [DecidableEq β] {f : α → β} {s t : Finset β}
    (hs : Set.InjOn f (f ⁻¹' ↑s)) (ht : Set.InjOn f (f ⁻¹' ↑t)) :
    (preimage (s ∩ t) f fun _ hx₁ _ hx₂ =>
        hs (mem_of_mem_inter_left hx₁) (mem_of_mem_inter_left hx₂)) =
      preimage s f hs ∩ preimage t f ht :=
  Finset.coe_injective (by simp)

@[simp]
theorem preimage_union [DecidableEq α] [DecidableEq β] {f : α → β} {s t : Finset β} (hst) :
    preimage (s ∪ t) f hst =
      (preimage s f fun _ hx₁ _ hx₂ => hst (mem_union_left _ hx₁) (mem_union_left _ hx₂)) ∪
        preimage t f fun _ hx₁ _ hx₂ => hst (mem_union_right _ hx₁) (mem_union_right _ hx₂) :=
  Finset.coe_injective (by simp)

@[simp]
theorem preimage_compl' [DecidableEq α] [DecidableEq β] [Fintype α] [Fintype β] {f : α → β}
    (s : Finset β) (hfc : InjOn f (f ⁻¹' ↑sᶜ)) (hf : InjOn f (f ⁻¹' ↑s)) :
    preimage sᶜ f hfc = (preimage s f hf)ᶜ :=
  Finset.coe_injective (by simp)

-- Not `@[simp]` since `simp` can't figure out `hf`; `simp`-normal form is `preimage_compl'`.
theorem preimage_compl [DecidableEq α] [DecidableEq β] [Fintype α] [Fintype β] {f : α → β}
    (s : Finset β) (hf : Function.Injective f) :
    preimage sᶜ f hf.injOn = (preimage s f hf.injOn)ᶜ :=
  preimage_compl' _ _ _

@[simp]
lemma preimage_map (f : α ↪ β) (s : Finset α) : (s.map f).preimage f f.injective.injOn = s :=
  coe_injective <| by simp only [coe_preimage, coe_map, Set.preimage_image_eq _ f.injective]

theorem monotone_preimage {f : α → β} (h : Injective f) :
    Monotone fun s => preimage s f h.injOn := fun _ _ H _ hx =>
  mem_preimage.2 (H <| mem_preimage.1 hx)

theorem image_subset_iff_subset_preimage [DecidableEq β] {f : α → β} {s : Finset α} {t : Finset β}
    (hf : Set.InjOn f (f ⁻¹' ↑t)) : s.image f ⊆ t ↔ s ⊆ t.preimage f hf :=
  image_subset_iff.trans <| by simp only [subset_iff, mem_preimage]

theorem map_subset_iff_subset_preimage {f : α ↪ β} {s : Finset α} {t : Finset β} :
    s.map f ⊆ t ↔ s ⊆ t.preimage f f.injective.injOn := by
  classical rw [map_eq_image, image_subset_iff_subset_preimage]

lemma card_preimage (s : Finset β) (f : α → β) (hf) [DecidablePred (· ∈ Set.range f)] :
    (s.preimage f hf).card = {x ∈ s | x ∈ Set.range f}.card :=
  card_nbij f (by simp [Set.MapsTo]) (by simpa) (fun b hb ↦ by aesop)

theorem image_preimage [DecidableEq β] (f : α → β) (s : Finset β) [∀ x, Decidable (x ∈ Set.range f)]
    (hf : Set.InjOn f (f ⁻¹' ↑s)) : image f (preimage s f hf) = {x ∈ s | x ∈ Set.range f} :=
  Finset.coe_inj.1 <| by
    simp only [coe_image, coe_preimage, coe_filter, Set.image_preimage_eq_inter_range,
      ← Set.sep_mem_eq]; rfl

theorem image_eq_preimage_of_leftInvOn_injOn {α β : Type*} [DecidableEq β] {f : α → β}
    {g : β → α} {s : Finset α} (hgf : Set.LeftInvOn g f s) (ginj : Set.InjOn g (g ⁻¹' s)) :
    s.image f = s.preimage g ginj := by
  simp only [SetLike.ext'_iff, coe_preimage, coe_image]
  rw [Set.image_eq_preimage_of_leftInvOn_injOn hgf ginj]

theorem image_preimage_of_bij [DecidableEq β] (f : α → β) (s : Finset β)
    (hf : Set.BijOn f (f ⁻¹' ↑s) ↑s) : image f (preimage s f hf.injOn) = s :=
  Finset.coe_inj.1 <| by simpa using hf.image_eq

lemma preimage_subset_of_subset_image [DecidableEq β] {f : α → β} {s : Finset β} {t : Finset α}
    (hs : s ⊆ t.image f) {hf} : s.preimage f hf ⊆ t := by
  rw [← coe_subset, coe_preimage]; exact Set.preimage_subset (mod_cast hs) hf

theorem preimage_subset {f : α ↪ β} {s : Finset β} {t : Finset α} (hs : s ⊆ t.map f) :
    s.preimage f f.injective.injOn ⊆ t := fun _ h => (mem_map' f).1 (hs (mem_preimage.1 h))

theorem subset_map_iff {f : α ↪ β} {s : Finset β} {t : Finset α} :
    s ⊆ t.map f ↔ ∃ u ⊆ t, s = u.map f := by
  classical
  simp_rw [map_eq_image, subset_image_iff, eq_comm]

@[simp]
theorem sup_preimage_self {α β : Type*} [Nonempty α] [SemilatticeSup β] [OrderBot β]
    {s : Finset β} {f : α → β} (hf : Set.BijOn f (f ⁻¹' ↑s) s) :
    (preimage s f hf.2.1).sup f = s.sup id := by
  classical
  have hfinvs : ∀ x ∈ s, (f ∘ invFunOn f (f ⁻¹' ↑s)) x = id x := hf.invOn_invFunOn.2
  rw [← sup_congr (Eq.refl s) hfinvs, ← sup_image]
  congr
  exact (image_eq_preimage_of_leftInvOn_injOn hf.invOn_invFunOn.2 hf.2.1).symm

lemma sup_preimage_val_id [Lattice α] [OrderBot α] {P : α → Prop}
    (Psup : ∀ ⦃s t : α⦄, P s → P t → P (s ⊔ t)) (Pbot : P ⊥) {t : Finset α}
    (ht : ∀ x ∈ t, P x) :
    letI := Subtype.semilatticeSup Psup
    letI := Subtype.orderBot Pbot
    (t.preimage Subtype.val Subtype.val_injective.injOn).sup id =
      (⟨t.sup id, sup_induction Pbot (fun _ h _ => Psup h) ht⟩ : Subtype P) := by
  letI : OrderBot (Subtype P) := Subtype.orderBot Pbot
  ext
  simp only [sup_coe, id_eq]
  apply sup_preimage_self
  refine ⟨mapsTo_preimage _ _, injOn_of_injective Subtype.val_injective, ?_⟩
  intro x hx; simpa using ⟨hx, ht x hx⟩

theorem sigma_preimage_mk {β : α → Type*} [DecidableEq α] (s : Finset (Σ a, β a)) (t : Finset α) :
    t.sigma (fun a => s.preimage (Sigma.mk a) sigma_mk_injective.injOn) = {a ∈ s | a.1 ∈ t} := by
  ext x
  simp [and_comm]

theorem sigma_preimage_mk_of_subset {β : α → Type*} [DecidableEq α] (s : Finset (Σ a, β a))
    {t : Finset α} (ht : s.image Sigma.fst ⊆ t) :
    (t.sigma fun a => s.preimage (Sigma.mk a) sigma_mk_injective.injOn) = s := by
  rw [sigma_preimage_mk, filter_true_of_mem <| image_subset_iff.1 ht]

theorem sigma_image_fst_preimage_mk {β : α → Type*} [DecidableEq α] (s : Finset (Σ a, β a)) :
    ((s.image Sigma.fst).sigma fun a => s.preimage (Sigma.mk a) sigma_mk_injective.injOn) =
      s :=
  s.sigma_preimage_mk_of_subset (Subset.refl _)

@[simp] lemma preimage_inl (s : Finset (α ⊕ β)) :
    s.preimage Sum.inl Sum.inl_injective.injOn = s.toLeft := by
  ext x; simp

@[simp] lemma preimage_inr (s : Finset (α ⊕ β)) :
    s.preimage Sum.inr Sum.inr_injective.injOn = s.toRight := by
  ext x; simp

end Preimage
end Finset

namespace Equiv

/-- Given an equivalence `e : α ≃ β` and `s : Finset β`, restrict `e` to an equivalence
from `e ⁻¹' s` to `s`. -/
@[simps]
def restrictPreimageFinset (e : α ≃ β) (s : Finset β) : (s.preimage e e.injective.injOn) ≃ s where
  toFun a := ⟨e a, Finset.mem_preimage.1 a.2⟩
  invFun b := ⟨e.symm b, by simp⟩
  left_inv _ := by simp
  right_inv _ := by simp

end Equiv

set_option backward.isDefEq.respectTransparency false in
/-- Reindexing and then restricting to a `Finset` is the same as first restricting to the preimage
of this `Finset` and then reindexing. -/
lemma Finset.restrict_comp_piCongrLeft {π : β → Type*} (s : Finset β) (e : α ≃ β) :
    s.restrict ∘ ⇑(e.piCongrLeft π) =
    ⇑((e.restrictPreimageFinset s).piCongrLeft (fun b : s ↦ (π b))) ∘
    (s.preimage e e.injective.injOn).restrict := by
  ext x b
  simp only [comp_apply, restrict, Equiv.piCongrLeft_apply_eq_cast,
    Equiv.restrictPreimageFinset_symm_apply_coe]
