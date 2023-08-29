/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Set.Image

#align_import data.set.sigma from "leanprover-community/mathlib"@"2258b40dacd2942571c8ce136215350c702dc78f"

/-!
# Sets in sigma types

This file defines `Set.sigma`, the indexed sum of sets.
-/

namespace Set

variable {ι ι' : Type*} {α β : ι → Type*} {s s₁ s₂ : Set ι} {t t₁ t₂ : ∀ i, Set (α i)}
  {u : Set (Σ i, α i)} {x : Σ i, α i} {i j : ι} {a : α i}

@[simp]
theorem range_sigmaMk (i : ι) : range (Sigma.mk i : α i → Sigma α) = Sigma.fst ⁻¹' {i} := by
  apply Subset.antisymm
  -- ⊢ range (Sigma.mk i) ⊆ Sigma.fst ⁻¹' {i}
  · rintro _ ⟨b, rfl⟩
    -- ⊢ { fst := i, snd := b } ∈ Sigma.fst ⁻¹' {i}
    simp
    -- 🎉 no goals
  · rintro ⟨x, y⟩ (rfl | _)
    -- ⊢ { fst := x, snd := y } ∈ range (Sigma.mk { fst := x, snd := y }.fst)
    exact mem_range_self y
    -- 🎉 no goals
#align set.range_sigma_mk Set.range_sigmaMk

theorem preimage_image_sigmaMk_of_ne (h : i ≠ j) (s : Set (α j)) :
    Sigma.mk i ⁻¹' (Sigma.mk j '' s) = ∅ := by
  ext x
  -- ⊢ x ∈ Sigma.mk i ⁻¹' (Sigma.mk j '' s) ↔ x ∈ ∅
  simp [h.symm]
  -- 🎉 no goals
#align set.preimage_image_sigma_mk_of_ne Set.preimage_image_sigmaMk_of_ne

theorem image_sigmaMk_preimage_sigmaMap_subset {β : ι' → Type*} (f : ι → ι')
    (g : ∀ i, α i → β (f i)) (i : ι) (s : Set (β (f i))) :
    Sigma.mk i '' (g i ⁻¹' s) ⊆ Sigma.map f g ⁻¹' (Sigma.mk (f i) '' s) :=
  image_subset_iff.2 fun x hx ↦ ⟨g i x, hx, rfl⟩
#align set.image_sigma_mk_preimage_sigma_map_subset Set.image_sigmaMk_preimage_sigmaMap_subset

theorem image_sigmaMk_preimage_sigmaMap {β : ι' → Type*} {f : ι → ι'} (hf : Function.Injective f)
    (g : ∀ i, α i → β (f i)) (i : ι) (s : Set (β (f i))) :
    Sigma.mk i '' (g i ⁻¹' s) = Sigma.map f g ⁻¹' (Sigma.mk (f i) '' s) := by
  refine' (image_sigmaMk_preimage_sigmaMap_subset f g i s).antisymm _
  -- ⊢ Sigma.map f g ⁻¹' (Sigma.mk (f i) '' s) ⊆ Sigma.mk i '' (g i ⁻¹' s)
  rintro ⟨j, x⟩ ⟨y, hys, hxy⟩
  -- ⊢ { fst := j, snd := x } ∈ Sigma.mk i '' (g i ⁻¹' s)
  simp only [hf.eq_iff, Sigma.map, Sigma.ext_iff] at hxy
  -- ⊢ { fst := j, snd := x } ∈ Sigma.mk i '' (g i ⁻¹' s)
  rcases hxy with ⟨rfl, hxy⟩; rw [heq_iff_eq] at hxy; subst y
  -- ⊢ { fst := i, snd := x } ∈ Sigma.mk i '' (g i ⁻¹' s)
                              -- ⊢ { fst := i, snd := x } ∈ Sigma.mk i '' (g i ⁻¹' s)
                                                      -- ⊢ { fst := i, snd := x } ∈ Sigma.mk i '' (g i ⁻¹' s)
  exact ⟨x, hys, rfl⟩
  -- 🎉 no goals
#align set.image_sigma_mk_preimage_sigma_map Set.image_sigmaMk_preimage_sigmaMap

/-- Indexed sum of sets. `s.sigma t` is the set of dependent pairs `⟨i, a⟩` such that `i ∈ s` and
`a ∈ t i`.-/
protected def Sigma (s : Set ι) (t : ∀ i, Set (α i)) : Set (Σi, α i) :=
  { x | x.1 ∈ s ∧ x.2 ∈ t x.1 }
#align set.sigma Set.Sigma

@[simp]
theorem mem_sigma_iff : x ∈ s.Sigma t ↔ x.1 ∈ s ∧ x.2 ∈ t x.1 :=
  Iff.rfl
#align set.mem_sigma_iff Set.mem_sigma_iff

theorem mk_sigma_iff : (⟨i, a⟩ : Σ i, α i) ∈ s.Sigma t ↔ i ∈ s ∧ a ∈ t i :=
  Iff.rfl
#align set.mk_sigma_iff Set.mk_sigma_iff

theorem mk_mem_sigma (hi : i ∈ s) (ha : a ∈ t i) : (⟨i, a⟩ : Σi, α i) ∈ s.Sigma t :=
  ⟨hi, ha⟩
#align set.mk_mem_sigma Set.mk_mem_sigma

theorem sigma_mono (hs : s₁ ⊆ s₂) (ht : ∀ i, t₁ i ⊆ t₂ i) : s₁.Sigma t₁ ⊆ s₂.Sigma t₂ := fun _ hx ↦
  ⟨hs hx.1, ht _ hx.2⟩
#align set.sigma_mono Set.sigma_mono

theorem sigma_subset_iff : s.Sigma t ⊆ u ↔ ∀ ⦃i⦄, i ∈ s → ∀ ⦃a⦄, a ∈ t i → (⟨i, a⟩ : Σi, α i) ∈ u :=
  ⟨fun h _ hi _ ha ↦ h <| mk_mem_sigma hi ha, fun h _ ha ↦ h ha.1 ha.2⟩
#align set.sigma_subset_iff Set.sigma_subset_iff

theorem forall_sigma_iff {p : (Σi, α i) → Prop} :
    (∀ x ∈ s.Sigma t, p x) ↔ ∀ ⦃i⦄, i ∈ s → ∀ ⦃a⦄, a ∈ t i → p ⟨i, a⟩ :=
  sigma_subset_iff
#align set.forall_sigma_iff Set.forall_sigma_iff

theorem exists_sigma_iff {p : (Σi, α i) → Prop} :
    (∃ x ∈ s.Sigma t, p x) ↔ ∃ i ∈ s, ∃ a ∈ t i, p ⟨i, a⟩ :=
  ⟨fun ⟨⟨i, a⟩, ha, h⟩ ↦ ⟨i, ha.1, a, ha.2, h⟩, fun ⟨i, hi, a, ha, h⟩ ↦ ⟨⟨i, a⟩, ⟨hi, ha⟩, h⟩⟩
#align set.exists_sigma_iff Set.exists_sigma_iff

@[simp]
theorem sigma_empty : (s.Sigma fun i ↦ (∅ : Set (α i))) = ∅ :=
  ext fun _ ↦ and_false_iff _
#align set.sigma_empty Set.sigma_empty

@[simp]
theorem empty_sigma : (∅ : Set ι).Sigma t = ∅ :=
  ext fun _ ↦ false_and_iff _
#align set.empty_sigma Set.empty_sigma

theorem univ_sigma_univ : ((@univ ι).Sigma fun _ ↦ @univ (α i)) = univ :=
  ext fun _ ↦ true_and_iff _
#align set.univ_sigma_univ Set.univ_sigma_univ

@[simp]
theorem sigma_univ : s.Sigma (fun _ ↦ univ : ∀ i, Set (α i)) = Sigma.fst ⁻¹' s :=
  ext fun _ ↦ and_true_iff _
#align set.sigma_univ Set.sigma_univ

@[simp]
theorem singleton_sigma : ({i} : Set ι).Sigma t = Sigma.mk i '' t i :=
  ext fun x ↦ by
    constructor
    -- ⊢ x ∈ Set.Sigma {i} t → x ∈ Sigma.mk i '' t i
    · obtain ⟨j, a⟩ := x
      -- ⊢ { fst := j, snd := a } ∈ Set.Sigma {i} t → { fst := j, snd := a } ∈ Sigma.mk …
      rintro ⟨rfl : j = i, ha⟩
      -- ⊢ { fst := j, snd := a✝ } ∈ Sigma.mk j '' t j
      exact mem_image_of_mem _ ha
      -- 🎉 no goals
    · rintro ⟨b, hb, rfl⟩
      -- ⊢ { fst := i, snd := b } ∈ Set.Sigma {i} t
      exact ⟨rfl, hb⟩
      -- 🎉 no goals
#align set.singleton_sigma Set.singleton_sigma

@[simp]
theorem sigma_singleton {a : ∀ i, α i} :
    (s.Sigma fun i ↦ ({a i} : Set (α i))) = (fun i ↦ Sigma.mk i <| a i) '' s := by
  ext ⟨x, y⟩
  -- ⊢ ({ fst := x, snd := y } ∈ Set.Sigma s fun i => {a i}) ↔ { fst := x, snd := y …
  simp [and_left_comm, eq_comm]
  -- 🎉 no goals
#align set.sigma_singleton Set.sigma_singleton

theorem singleton_sigma_singleton {a : ∀ i, α i} :
    (({i} : Set ι).Sigma fun i ↦ ({a i} : Set (α i))) = {⟨i, a i⟩} := by
  rw [sigma_singleton, image_singleton]
  -- 🎉 no goals
#align set.singleton_sigma_singleton Set.singleton_sigma_singleton

@[simp]
theorem union_sigma : (s₁ ∪ s₂).Sigma t = s₁.Sigma t ∪ s₂.Sigma t :=
  ext fun _ ↦ or_and_right
#align set.union_sigma Set.union_sigma

@[simp]
theorem sigma_union : (s.Sigma fun i ↦ t₁ i ∪ t₂ i) = s.Sigma t₁ ∪ s.Sigma t₂ :=
  ext fun _ ↦ and_or_left
#align set.sigma_union Set.sigma_union

theorem sigma_inter_sigma : s₁.Sigma t₁ ∩ s₂.Sigma t₂ = (s₁ ∩ s₂).Sigma fun i ↦ t₁ i ∩ t₂ i := by
  ext ⟨x, y⟩
  -- ⊢ { fst := x, snd := y } ∈ Set.Sigma s₁ t₁ ∩ Set.Sigma s₂ t₂ ↔ { fst := x, snd …
  simp [and_assoc, and_left_comm]
  -- 🎉 no goals
#align set.sigma_inter_sigma Set.sigma_inter_sigma

theorem insert_sigma : (insert i s).Sigma t = Sigma.mk i '' t i ∪ s.Sigma t := by
  rw [insert_eq, union_sigma, singleton_sigma]
  -- ⊢ α i
  exact a
  -- 🎉 no goals
#align set.insert_sigma Set.insert_sigma

theorem sigma_insert {a : ∀ i, α i} :
    (s.Sigma fun i ↦ insert (a i) (t i)) = (fun i ↦ ⟨i, a i⟩) '' s ∪ s.Sigma t := by
  simp_rw [insert_eq, sigma_union, sigma_singleton]
  -- 🎉 no goals
#align set.sigma_insert Set.sigma_insert

theorem sigma_preimage_eq {f : ι' → ι} {g : ∀ i, β i → α i} :
    ((f ⁻¹' s).Sigma fun i ↦ g (f i) ⁻¹' t (f i)) =
      (fun p : Σi, β (f i) ↦ Sigma.mk _ (g _ p.2)) ⁻¹' s.Sigma t :=
  rfl
#align set.sigma_preimage_eq Set.sigma_preimage_eq

theorem sigma_preimage_left {f : ι' → ι} :
    ((f ⁻¹' s).Sigma fun i ↦ t (f i)) = (fun p : Σi, α (f i) ↦ Sigma.mk _ p.2) ⁻¹' s.Sigma t :=
  rfl
#align set.sigma_preimage_left Set.sigma_preimage_left

theorem sigma_preimage_right {g : ∀ i, β i → α i} :
    (s.Sigma fun i ↦ g i ⁻¹' t i) = (fun p : Σi, β i ↦ Sigma.mk p.1 (g _ p.2)) ⁻¹' s.Sigma t :=
  rfl
#align set.sigma_preimage_right Set.sigma_preimage_right

theorem preimage_sigmaMap_sigma {α' : ι' → Type*} (f : ι → ι') (g : ∀ i, α i → α' (f i))
    (s : Set ι') (t : ∀ i, Set (α' i)) :
    Sigma.map f g ⁻¹' s.Sigma t = (f ⁻¹' s).Sigma fun i ↦ g i ⁻¹' t (f i) :=
  rfl
#align set.preimage_sigma_map_sigma Set.preimage_sigmaMap_sigma

@[simp]
theorem mk_preimage_sigma (hi : i ∈ s) : Sigma.mk i ⁻¹' s.Sigma t = t i :=
  ext fun _ ↦ and_iff_right hi
#align set.mk_preimage_sigma Set.mk_preimage_sigma

@[simp]
theorem mk_preimage_sigma_eq_empty (hi : i ∉ s) : Sigma.mk i ⁻¹' s.Sigma t = ∅ :=
  ext fun _ ↦ iff_of_false (hi ∘ And.left) id
#align set.mk_preimage_sigma_eq_empty Set.mk_preimage_sigma_eq_empty

theorem mk_preimage_sigma_eq_if [DecidablePred (· ∈ s)] :
    Sigma.mk i ⁻¹' s.Sigma t = if i ∈ s then t i else ∅ := by split_ifs <;> simp [*]
                                                              -- ⊢ Sigma.mk i ⁻¹' Set.Sigma s t = t i
                                                                            -- 🎉 no goals
                                                                            -- 🎉 no goals
#align set.mk_preimage_sigma_eq_if Set.mk_preimage_sigma_eq_if

theorem mk_preimage_sigma_fn_eq_if {β : Type*} [DecidablePred (· ∈ s)] (g : β → α i) :
    (fun b ↦ Sigma.mk i (g b)) ⁻¹' s.Sigma t = if i ∈ s then g ⁻¹' t i else ∅ :=
  ext fun _ ↦ by split_ifs <;> simp [*]
                 -- ⊢ x✝ ∈ (fun b => { fst := i, snd := g b }) ⁻¹' Set.Sigma s t ↔ x✝ ∈ g ⁻¹' t i
                               -- 🎉 no goals
                               -- 🎉 no goals
#align set.mk_preimage_sigma_fn_eq_if Set.mk_preimage_sigma_fn_eq_if

theorem sigma_univ_range_eq {f : ∀ i, α i → β i} :
    ((univ : Set ι).Sigma fun i ↦ range (f i)) = range fun x : Σi, α i ↦ ⟨x.1, f _ x.2⟩ :=
  ext <| by simp [range]
            -- 🎉 no goals
#align set.sigma_univ_range_eq Set.sigma_univ_range_eq

protected theorem Nonempty.sigma :
    s.Nonempty → (∀ i, (t i).Nonempty) → (s.Sigma t : Set _).Nonempty := fun ⟨i, hi⟩ h ↦
  let ⟨a, ha⟩ := h i
  ⟨⟨i, a⟩, hi, ha⟩
#align set.nonempty.sigma Set.Nonempty.sigma

theorem Nonempty.sigma_fst : (s.Sigma t : Set _).Nonempty → s.Nonempty := fun ⟨x, hx⟩ ↦ ⟨x.1, hx.1⟩
#align set.nonempty.sigma_fst Set.Nonempty.sigma_fst

theorem Nonempty.sigma_snd : (s.Sigma t : Set _).Nonempty → ∃ i ∈ s, (t i).Nonempty :=
  fun ⟨x, hx⟩ ↦ ⟨x.1, hx.1, x.2, hx.2⟩
#align set.nonempty.sigma_snd Set.Nonempty.sigma_snd

theorem sigma_nonempty_iff : (s.Sigma t : Set _).Nonempty ↔ ∃ i ∈ s, (t i).Nonempty :=
  ⟨Nonempty.sigma_snd, fun ⟨i, hi, a, ha⟩ ↦ ⟨⟨i, a⟩, hi, ha⟩⟩
#align set.sigma_nonempty_iff Set.sigma_nonempty_iff

theorem sigma_eq_empty_iff : s.Sigma t = ∅ ↔ ∀ i ∈ s, t i = ∅ :=
  not_nonempty_iff_eq_empty.symm.trans <|
    sigma_nonempty_iff.not.trans <| by
      simp only [not_nonempty_iff_eq_empty, not_and, not_exists]
      -- 🎉 no goals
#align set.sigma_eq_empty_iff Set.sigma_eq_empty_iff

theorem image_sigmaMk_subset_sigma_left {a : ∀ i, α i} (ha : ∀ i, a i ∈ t i) :
    (fun i ↦ Sigma.mk i (a i)) '' s ⊆ s.Sigma t :=
  image_subset_iff.2 fun _ hi ↦ ⟨hi, ha _⟩
#align set.image_sigma_mk_subset_sigma_left Set.image_sigmaMk_subset_sigma_left

theorem image_sigmaMk_subset_sigma_right (hi : i ∈ s) : Sigma.mk i '' t i ⊆ s.Sigma t :=
  image_subset_iff.2 fun _ ↦ And.intro hi
#align set.image_sigma_mk_subset_sigma_right Set.image_sigmaMk_subset_sigma_right

theorem sigma_subset_preimage_fst (s : Set ι) (t : ∀ i, Set (α i)) : s.Sigma t ⊆ Sigma.fst ⁻¹' s :=
  fun _ ↦ And.left
#align set.sigma_subset_preimage_fst Set.sigma_subset_preimage_fst

theorem fst_image_sigma_subset (s : Set ι) (t : ∀ i, Set (α i)) : Sigma.fst '' s.Sigma t ⊆ s :=
  image_subset_iff.2 fun _ ↦ And.left
#align set.fst_image_sigma_subset Set.fst_image_sigma_subset

theorem fst_image_sigma (s : Set ι) (ht : ∀ i, (t i).Nonempty) : Sigma.fst '' s.Sigma t = s :=
  (fst_image_sigma_subset _ _).antisymm fun i hi ↦
    let ⟨a, ha⟩ := ht i
    ⟨⟨i, a⟩, ⟨hi, ha⟩, rfl⟩
#align set.fst_image_sigma Set.fst_image_sigma

theorem sigma_diff_sigma : s₁.Sigma t₁ \ s₂.Sigma t₂ = s₁.Sigma (t₁ \ t₂) ∪ (s₁ \ s₂).Sigma t₁ :=
  ext fun x ↦ by
    by_cases h₁ : x.1 ∈ s₁ <;> by_cases h₂ : x.2 ∈ t₁ x.1 <;> simp [*, ← imp_iff_or_not]
    -- ⊢ x ∈ Set.Sigma s₁ t₁ \ Set.Sigma s₂ t₂ ↔ x ∈ Set.Sigma s₁ (t₁ \ t₂) ∪ Set.Sig …
                               -- ⊢ x ∈ Set.Sigma s₁ t₁ \ Set.Sigma s₂ t₂ ↔ x ∈ Set.Sigma s₁ (t₁ \ t₂) ∪ Set.Sig …
                               -- ⊢ x ∈ Set.Sigma s₁ t₁ \ Set.Sigma s₂ t₂ ↔ x ∈ Set.Sigma s₁ (t₁ \ t₂) ∪ Set.Sig …
                                                              -- 🎉 no goals
                                                              -- 🎉 no goals
                                                              -- 🎉 no goals
                                                              -- 🎉 no goals
#align set.sigma_diff_sigma Set.sigma_diff_sigma

end Set
