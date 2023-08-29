/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Data.Set.Finite
import Mathlib.Algebra.BigOperators.Basic

#align_import data.finset.preimage from "leanprover-community/mathlib"@"2445c98ae4b87eabebdde552593519b9b6dc350c"

/-!
# Preimage of a `Finset` under an injective map.
-/


open Set Function

open BigOperators

universe u v w x

variable {α : Type u} {β : Type v} {ι : Sort w} {γ : Type x}

namespace Finset

section Preimage

/-- Preimage of `s : Finset β` under a map `f` injective on `f ⁻¹' s` as a `Finset`.  -/
noncomputable def preimage (s : Finset β) (f : α → β) (hf : Set.InjOn f (f ⁻¹' ↑s)) : Finset α :=
  (s.finite_toSet.preimage hf).toFinset
#align finset.preimage Finset.preimage

@[simp]
theorem mem_preimage {f : α → β} {s : Finset β} {hf : Set.InjOn f (f ⁻¹' ↑s)} {x : α} :
    x ∈ preimage s f hf ↔ f x ∈ s :=
  Set.Finite.mem_toFinset _
#align finset.mem_preimage Finset.mem_preimage

@[simp, norm_cast]
theorem coe_preimage {f : α → β} (s : Finset β) (hf : Set.InjOn f (f ⁻¹' ↑s)) :
    (↑(preimage s f hf) : Set α) = f ⁻¹' ↑s :=
  Set.Finite.coe_toFinset _
#align finset.coe_preimage Finset.coe_preimage

@[simp]
theorem preimage_empty {f : α → β} : preimage ∅ f (by simp [InjOn]) = ∅ :=
                                                      -- 🎉 no goals
  Finset.coe_injective (by simp)
                           -- 🎉 no goals
#align finset.preimage_empty Finset.preimage_empty

@[simp]
theorem preimage_univ {f : α → β} [Fintype α] [Fintype β] (hf) : preimage univ f hf = univ :=
  Finset.coe_injective (by simp)
                           -- 🎉 no goals
#align finset.preimage_univ Finset.preimage_univ

@[simp]
theorem preimage_inter [DecidableEq α] [DecidableEq β] {f : α → β} {s t : Finset β}
    (hs : Set.InjOn f (f ⁻¹' ↑s)) (ht : Set.InjOn f (f ⁻¹' ↑t)) :
    (preimage (s ∩ t) f fun x₁ hx₁ x₂ hx₂ =>
        hs (mem_of_mem_inter_left hx₁) (mem_of_mem_inter_left hx₂)) =
      preimage s f hs ∩ preimage t f ht :=
  Finset.coe_injective (by simp)
                           -- 🎉 no goals
#align finset.preimage_inter Finset.preimage_inter

@[simp]
theorem preimage_union [DecidableEq α] [DecidableEq β] {f : α → β} {s t : Finset β} (hst) :
    preimage (s ∪ t) f hst =
      (preimage s f fun x₁ hx₁ x₂ hx₂ => hst (mem_union_left _ hx₁) (mem_union_left _ hx₂)) ∪
        preimage t f fun x₁ hx₁ x₂ hx₂ => hst (mem_union_right _ hx₁) (mem_union_right _ hx₂) :=
  Finset.coe_injective (by simp)
                           -- 🎉 no goals
#align finset.preimage_union Finset.preimage_union

@[simp, nolint simpNF] -- Porting note: linter complains that LHS doesn't simplify
theorem preimage_compl [DecidableEq α] [DecidableEq β] [Fintype α] [Fintype β] {f : α → β}
    (s : Finset β) (hf : Function.Injective f) :
    preimage sᶜ f (hf.injOn _) = (preimage s f (hf.injOn _))ᶜ :=
  Finset.coe_injective (by simp)
                           -- 🎉 no goals
#align finset.preimage_compl Finset.preimage_compl

theorem monotone_preimage {f : α → β} (h : Injective f) :
    Monotone fun s => preimage s f (h.injOn _) := fun _ _ H _ hx =>
  mem_preimage.2 (H <| mem_preimage.1 hx)
#align finset.monotone_preimage Finset.monotone_preimage

theorem image_subset_iff_subset_preimage [DecidableEq β] {f : α → β} {s : Finset α} {t : Finset β}
    (hf : Set.InjOn f (f ⁻¹' ↑t)) : s.image f ⊆ t ↔ s ⊆ t.preimage f hf :=
  image_subset_iff.trans <| by simp only [subset_iff, mem_preimage]
                               -- 🎉 no goals
#align finset.image_subset_iff_subset_preimage Finset.image_subset_iff_subset_preimage

theorem map_subset_iff_subset_preimage {f : α ↪ β} {s : Finset α} {t : Finset β} :
    s.map f ⊆ t ↔ s ⊆ t.preimage f (f.injective.injOn _) := by
  classical rw [map_eq_image, image_subset_iff_subset_preimage]
  -- 🎉 no goals
#align finset.map_subset_iff_subset_preimage Finset.map_subset_iff_subset_preimage

theorem image_preimage [DecidableEq β] (f : α → β) (s : Finset β) [∀ x, Decidable (x ∈ Set.range f)]
    (hf : Set.InjOn f (f ⁻¹' ↑s)) : image f (preimage s f hf) = s.filter fun x => x ∈ Set.range f :=
  Finset.coe_inj.1 <| by
    simp only [coe_image, coe_preimage, coe_filter, Set.image_preimage_eq_inter_range,
      ← Set.sep_mem_eq]; rfl
                         -- 🎉 no goals
#align finset.image_preimage Finset.image_preimage

theorem image_preimage_of_bij [DecidableEq β] (f : α → β) (s : Finset β)
    (hf : Set.BijOn f (f ⁻¹' ↑s) ↑s) : image f (preimage s f hf.injOn) = s :=
  Finset.coe_inj.1 <| by simpa using hf.image_eq
                         -- 🎉 no goals
#align finset.image_preimage_of_bij Finset.image_preimage_of_bij

theorem preimage_subset {f : α ↪ β} {s : Finset β} {t : Finset α} (hs : s ⊆ t.map f) :
    s.preimage f (f.injective.injOn _) ⊆ t := fun _ h => (mem_map' f).1 (hs (mem_preimage.1 h))
#align finset.preimage_subset Finset.preimage_subset

theorem subset_map_iff {f : α ↪ β} {s : Finset β} {t : Finset α} :
    s ⊆ t.map f ↔ ∃ (u : _) (_ : u ⊆ t), s = u.map f := by
  classical
    refine' ⟨fun h => ⟨_, preimage_subset h, _⟩, _⟩
    · rw [map_eq_image, image_preimage, filter_true_of_mem]
      exact fun x hx ↦ coe_map_subset_range _ _ (h hx)
    · rintro ⟨u, hut, rfl⟩
      exact map_subset_map.2 hut
#align finset.subset_map_iff Finset.subset_map_iff

theorem sigma_preimage_mk {β : α → Type*} [DecidableEq α] (s : Finset (Σa, β a)) (t : Finset α) :
    (t.sigma fun a => s.preimage (Sigma.mk a) <| sigma_mk_injective.injOn _) =
      s.filter fun a => a.1 ∈ t := by
  ext x
  -- ⊢ (x ∈ Finset.sigma t fun a => preimage s (Sigma.mk a) (_ : InjOn (Sigma.mk a) …
  simp [and_comm]
  -- 🎉 no goals
#align finset.sigma_preimage_mk Finset.sigma_preimage_mk

theorem sigma_preimage_mk_of_subset {β : α → Type*} [DecidableEq α] (s : Finset (Σa, β a))
    {t : Finset α} (ht : s.image Sigma.fst ⊆ t) :
    (t.sigma fun a => s.preimage (Sigma.mk a) <| sigma_mk_injective.injOn _) = s := by
  rw [sigma_preimage_mk, filter_true_of_mem <| image_subset_iff.1 ht]
  -- 🎉 no goals
#align finset.sigma_preimage_mk_of_subset Finset.sigma_preimage_mk_of_subset

theorem sigma_image_fst_preimage_mk {β : α → Type*} [DecidableEq α] (s : Finset (Σa, β a)) :
    ((s.image Sigma.fst).sigma fun a => s.preimage (Sigma.mk a) <| sigma_mk_injective.injOn _) =
      s :=
  s.sigma_preimage_mk_of_subset (Subset.refl _)
#align finset.sigma_image_fst_preimage_mk Finset.sigma_image_fst_preimage_mk

end Preimage

@[to_additive]
theorem prod_preimage' [CommMonoid β] (f : α → γ) [DecidablePred fun x => x ∈ Set.range f]
    (s : Finset γ) (hf : Set.InjOn f (f ⁻¹' ↑s)) (g : γ → β) :
    (∏ x in s.preimage f hf, g (f x)) = ∏ x in s.filter fun x => x ∈ Set.range f, g x := by
  haveI := Classical.decEq γ
  -- ⊢ ∏ x in preimage s f hf, g (f x) = ∏ x in filter (fun x => x ∈ Set.range f) s …
  calc
    (∏ x in preimage s f hf, g (f x)) = ∏ x in image f (preimage s f hf), g x :=
      Eq.symm <| prod_image <| by simpa only [mem_preimage, InjOn] using hf
    _ = ∏ x in s.filter fun x => x ∈ Set.range f, g x := by rw [image_preimage]
#align finset.prod_preimage' Finset.prod_preimage'
#align finset.sum_preimage' Finset.sum_preimage'

@[to_additive]
theorem prod_preimage [CommMonoid β] (f : α → γ) (s : Finset γ) (hf : Set.InjOn f (f ⁻¹' ↑s))
    (g : γ → β) (hg : ∀ x ∈ s, x ∉ Set.range f → g x = 1) :
    (∏ x in s.preimage f hf, g (f x)) = ∏ x in s, g x := by
  classical
    rw [prod_preimage', prod_filter_of_ne]
    exact fun x hx => Not.imp_symm (hg x hx)
#align finset.prod_preimage Finset.prod_preimage
#align finset.sum_preimage Finset.sum_preimage

@[to_additive]
theorem prod_preimage_of_bij [CommMonoid β] (f : α → γ) (s : Finset γ)
    (hf : Set.BijOn f (f ⁻¹' ↑s) ↑s) (g : γ → β) :
    (∏ x in s.preimage f hf.injOn, g (f x)) = ∏ x in s, g x :=
  prod_preimage _ _ hf.injOn g fun _ hs h_f => (h_f <| hf.subset_range hs).elim
#align finset.prod_preimage_of_bij Finset.prod_preimage_of_bij
#align finset.sum_preimage_of_bij Finset.sum_preimage_of_bij

end Finset
