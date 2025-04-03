/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Data.Set.Finite

/-!
# Preimage of a `Finset` under an injective map.
-/

assert_not_exists Finset.sum

open Set Function

universe u v w x

variable {α : Type u} {β : Type v} {ι : Sort w} {γ : Type x}

namespace Finset

section Preimage

/-- Preimage of `s : Finset β` under a map `f` injective on `f ⁻¹' s` as a `Finset`.  -/
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
theorem preimage_inter [DecidableEq α] [DecidableEq β] {f : α → β} {s t : Finset β}
    (hs : Set.InjOn f (f ⁻¹' ↑s)) (ht : Set.InjOn f (f ⁻¹' ↑t)) :
    (preimage (s ∩ t) f fun x₁ hx₁ x₂ hx₂ =>
        hs (mem_of_mem_inter_left hx₁) (mem_of_mem_inter_left hx₂)) =
      preimage s f hs ∩ preimage t f ht :=
  Finset.coe_injective (by simp)

@[simp]
theorem preimage_union [DecidableEq α] [DecidableEq β] {f : α → β} {s t : Finset β} (hst) :
    preimage (s ∪ t) f hst =
      (preimage s f fun x₁ hx₁ x₂ hx₂ => hst (mem_union_left _ hx₁) (mem_union_left _ hx₂)) ∪
        preimage t f fun x₁ hx₁ x₂ hx₂ => hst (mem_union_right _ hx₁) (mem_union_right _ hx₂) :=
  Finset.coe_injective (by simp)

@[simp, nolint simpNF] -- Porting note: linter complains that LHS doesn't simplify
theorem preimage_compl [DecidableEq α] [DecidableEq β] [Fintype α] [Fintype β] {f : α → β}
    (s : Finset β) (hf : Function.Injective f) :
    preimage sᶜ f hf.injOn = (preimage s f hf.injOn)ᶜ :=
  Finset.coe_injective (by simp)

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

theorem image_preimage [DecidableEq β] (f : α → β) (s : Finset β) [∀ x, Decidable (x ∈ Set.range f)]
    (hf : Set.InjOn f (f ⁻¹' ↑s)) : image f (preimage s f hf) = s.filter fun x => x ∈ Set.range f :=
  Finset.coe_inj.1 <| by
    simp only [coe_image, coe_preimage, coe_filter, Set.image_preimage_eq_inter_range,
      ← Set.sep_mem_eq]; rfl

theorem image_preimage_of_bij [DecidableEq β] (f : α → β) (s : Finset β)
    (hf : Set.BijOn f (f ⁻¹' ↑s) ↑s) : image f (preimage s f hf.injOn) = s :=
  Finset.coe_inj.1 <| by simpa using hf.image_eq

theorem preimage_subset {f : α ↪ β} {s : Finset β} {t : Finset α} (hs : s ⊆ t.map f) :
    s.preimage f f.injective.injOn ⊆ t := fun _ h => (mem_map' f).1 (hs (mem_preimage.1 h))

theorem subset_map_iff {f : α ↪ β} {s : Finset β} {t : Finset α} :
    s ⊆ t.map f ↔ ∃ u ⊆ t, s = u.map f := by
  classical
  simp_rw [← coe_subset, coe_map, subset_image_iff, map_eq_image, eq_comm]

theorem sigma_preimage_mk {β : α → Type*} [DecidableEq α] (s : Finset (Σa, β a)) (t : Finset α) :
    (t.sigma fun a => s.preimage (Sigma.mk a) sigma_mk_injective.injOn) =
      s.filter fun a => a.1 ∈ t := by
  ext x
  simp [and_comm]

theorem sigma_preimage_mk_of_subset {β : α → Type*} [DecidableEq α] (s : Finset (Σa, β a))
    {t : Finset α} (ht : s.image Sigma.fst ⊆ t) :
    (t.sigma fun a => s.preimage (Sigma.mk a) sigma_mk_injective.injOn) = s := by
  rw [sigma_preimage_mk, filter_true_of_mem <| image_subset_iff.1 ht]

theorem sigma_image_fst_preimage_mk {β : α → Type*} [DecidableEq α] (s : Finset (Σa, β a)) :
    ((s.image Sigma.fst).sigma fun a => s.preimage (Sigma.mk a) sigma_mk_injective.injOn) =
      s :=
  s.sigma_preimage_mk_of_subset (Subset.refl _)

end Preimage
end Finset
