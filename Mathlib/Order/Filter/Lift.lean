/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Order.Filter.Bases
import Mathlib.Order.ConditionallyCompleteLattice.Basic

#align_import order.filter.lift from "leanprover-community/mathlib"@"8631e2d5ea77f6c13054d9151d82b83069680cb1"

/-!
# Lift filters along filter and set functions
-/

open Set Classical Filter Function

namespace Filter

variable {α β γ : Type*} {ι : Sort*}

section lift

/-- A variant on `bind` using a function `g` taking a set instead of a member of `α`.
This is essentially a push-forward along a function mapping each set to a filter. -/
protected def lift (f : Filter α) (g : Set α → Filter β) :=
  ⨅ s ∈ f, g s
#align filter.lift Filter.lift

variable {f f₁ f₂ : Filter α} {g g₁ g₂ : Set α → Filter β}

@[simp]
theorem lift_top (g : Set α → Filter β) : (⊤ : Filter α).lift g = g univ := by simp [Filter.lift]
                                                                               -- 🎉 no goals
#align filter.lift_top Filter.lift_top

-- porting note: use `∃ i, p i ∧ _` instead of `∃ i (hi : p i), _`
/-- If `(p : ι → Prop, s : ι → Set α)` is a basis of a filter `f`, `g` is a monotone function
`Set α → Filter γ`, and for each `i`, `(pg : β i → Prop, sg : β i → Set α)` is a basis
of the filter `g (s i)`, then `(λ (i : ι) (x : β i), p i ∧ pg i x, λ (i : ι) (x : β i), sg i x)`
is a basis of the filter `f.lift g`.

This basis is parametrized by `i : ι` and `x : β i`, so in order to formulate this fact using
`Filter.HasBasis` one has to use `Σ i, β i` as the index type, see `Filter.HasBasis.lift`.
This lemma states the corresponding `mem_iff` statement without using a sigma type. -/
theorem HasBasis.mem_lift_iff {ι} {p : ι → Prop} {s : ι → Set α} {f : Filter α}
    (hf : f.HasBasis p s) {β : ι → Type*} {pg : ∀ i, β i → Prop} {sg : ∀ i, β i → Set γ}
    {g : Set α → Filter γ} (hg : ∀ i, (g <| s i).HasBasis (pg i) (sg i)) (gm : Monotone g)
    {s : Set γ} : s ∈ f.lift g ↔ ∃ i, p i ∧ ∃ x, pg i x ∧ sg i x ⊆ s := by
  refine' (mem_biInf_of_directed _ ⟨univ, univ_sets _⟩).trans _
  -- ⊢ DirectedOn ((fun s => g s) ⁻¹'o fun x x_1 => x ≥ x_1) f.sets
  · intro t₁ ht₁ t₂ ht₂
    -- ⊢ ∃ z, z ∈ f.sets ∧ ((fun s => g s) ⁻¹'o fun x x_1 => x ≥ x_1) t₁ z ∧ ((fun s  …
    exact ⟨t₁ ∩ t₂, inter_mem ht₁ ht₂, gm <| inter_subset_left _ _, gm <| inter_subset_right _ _⟩
    -- 🎉 no goals
  · simp only [← (hg _).mem_iff]
    -- ⊢ (∃ i, i ∈ f.sets ∧ s ∈ g i) ↔ ∃ i, p i ∧ s ∈ g (s✝ i)
    exact hf.exists_iff fun t₁ t₂ ht H => gm ht H
    -- 🎉 no goals
#align filter.has_basis.mem_lift_iff Filter.HasBasis.mem_lift_iffₓ

/-- If `(p : ι → Prop, s : ι → Set α)` is a basis of a filter `f`, `g` is a monotone function
`Set α → Filter γ`, and for each `i`, `(pg : β i → Prop, sg : β i → Set α)` is a basis
of the filter `g (s i)`, then `(λ (i : ι) (x : β i), p i ∧ pg i x, λ (i : ι) (x : β i), sg i x)`
is a basis of the filter `f.lift g`.

This basis is parametrized by `i : ι` and `x : β i`, so in order to formulate this fact using
`has_basis` one has to use `Σ i, β i` as the index type. See also `Filter.HasBasis.mem_lift_iff`
for the corresponding `mem_iff` statement formulated without using a sigma type. -/
theorem HasBasis.lift {ι} {p : ι → Prop} {s : ι → Set α} {f : Filter α} (hf : f.HasBasis p s)
    {β : ι → Type*} {pg : ∀ i, β i → Prop} {sg : ∀ i, β i → Set γ} {g : Set α → Filter γ}
    (hg : ∀ i, (g (s i)).HasBasis (pg i) (sg i)) (gm : Monotone g) :
    (f.lift g).HasBasis (fun i : Σi, β i => p i.1 ∧ pg i.1 i.2) fun i : Σi, β i => sg i.1 i.2 := by
  refine' ⟨fun t => (hf.mem_lift_iff hg gm).trans _⟩
  -- ⊢ (∃ i, p i ∧ ∃ x, pg i x ∧ sg i x ⊆ t) ↔ ∃ i, (p i.fst ∧ pg i.fst i.snd) ∧ sg …
  simp [Sigma.exists, and_assoc, exists_and_left]
  -- 🎉 no goals
#align filter.has_basis.lift Filter.HasBasis.lift

theorem mem_lift_sets (hg : Monotone g) {s : Set β} : s ∈ f.lift g ↔ ∃ t ∈ f, s ∈ g t :=
  (f.basis_sets.mem_lift_iff (fun s => (g s).basis_sets) hg).trans <| by
    simp only [id, exists_mem_subset_iff]
    -- 🎉 no goals
#align filter.mem_lift_sets Filter.mem_lift_sets

theorem sInter_lift_sets (hg : Monotone g) :
    ⋂₀ { s | s ∈ f.lift g } = ⋂ s ∈ f, ⋂₀ { t | t ∈ g s } := by
  simp only [sInter_eq_biInter, mem_setOf_eq, Filter.mem_sets, mem_lift_sets hg, iInter_exists,
    iInter_and, @iInter_comm _ (Set β)]
#align filter.sInter_lift_sets Filter.sInter_lift_sets

theorem mem_lift {s : Set β} {t : Set α} (ht : t ∈ f) (hs : s ∈ g t) : s ∈ f.lift g :=
  le_principal_iff.mp <|
    show f.lift g ≤ 𝓟 s from iInf_le_of_le t <| iInf_le_of_le ht <| le_principal_iff.mpr hs
#align filter.mem_lift Filter.mem_lift

theorem lift_le {f : Filter α} {g : Set α → Filter β} {h : Filter β} {s : Set α} (hs : s ∈ f)
    (hg : g s ≤ h) : f.lift g ≤ h :=
  iInf₂_le_of_le s hs hg
#align filter.lift_le Filter.lift_le

theorem le_lift {f : Filter α} {g : Set α → Filter β} {h : Filter β} :
    h ≤ f.lift g ↔ ∀ s ∈ f, h ≤ g s :=
  le_iInf₂_iff
#align filter.le_lift Filter.le_lift

theorem lift_mono (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) : f₁.lift g₁ ≤ f₂.lift g₂ :=
  iInf_mono fun s => iInf_mono' fun hs => ⟨hf hs, hg s⟩
#align filter.lift_mono Filter.lift_mono

theorem lift_mono' (hg : ∀ s ∈ f, g₁ s ≤ g₂ s) : f.lift g₁ ≤ f.lift g₂ := iInf₂_mono hg
#align filter.lift_mono' Filter.lift_mono'

theorem tendsto_lift {m : γ → β} {l : Filter γ} :
    Tendsto m l (f.lift g) ↔ ∀ s ∈ f, Tendsto m l (g s) := by
  simp only [Filter.lift, tendsto_iInf]
  -- 🎉 no goals
#align filter.tendsto_lift Filter.tendsto_lift

theorem map_lift_eq {m : β → γ} (hg : Monotone g) : map m (f.lift g) = f.lift (map m ∘ g) :=
  have : Monotone (map m ∘ g) := map_mono.comp hg
  Filter.ext fun s => by
    simp only [mem_lift_sets hg, mem_lift_sets this, exists_prop, mem_map, Function.comp_apply]
    -- 🎉 no goals
#align filter.map_lift_eq Filter.map_lift_eq

theorem comap_lift_eq {m : γ → β} : comap m (f.lift g) = f.lift (comap m ∘ g) := by
  simp only [Filter.lift, comap_iInf]; rfl
  -- ⊢ ⨅ (i : Set α) (_ : i ∈ f), comap m (g i) = ⨅ (s : Set α) (_ : s ∈ f), (comap …
                                       -- 🎉 no goals
#align filter.comap_lift_eq Filter.comap_lift_eq

theorem comap_lift_eq2 {m : β → α} {g : Set β → Filter γ} (hg : Monotone g) :
    (comap m f).lift g = f.lift (g ∘ preimage m) :=
  le_antisymm (le_iInf₂ fun s hs => iInf₂_le (m ⁻¹' s) ⟨s, hs, Subset.rfl⟩)
    (le_iInf₂ fun _s ⟨s', hs', h_sub⟩ => iInf₂_le_of_le s' hs' <| hg h_sub)
#align filter.comap_lift_eq2 Filter.comap_lift_eq2

theorem lift_map_le {g : Set β → Filter γ} {m : α → β} : (map m f).lift g ≤ f.lift (g ∘ image m) :=
  le_lift.2 fun _s hs => lift_le (image_mem_map hs) le_rfl
#align filter.lift_map_le Filter.lift_map_le

theorem map_lift_eq2 {g : Set β → Filter γ} {m : α → β} (hg : Monotone g) :
    (map m f).lift g = f.lift (g ∘ image m) :=
  lift_map_le.antisymm <| le_lift.2 fun _s hs => lift_le hs <| hg <| image_preimage_subset _ _
#align filter.map_lift_eq2 Filter.map_lift_eq2

theorem lift_comm {g : Filter β} {h : Set α → Set β → Filter γ} :
    (f.lift fun s => g.lift (h s)) = g.lift fun t => f.lift fun s => h s t :=
  le_antisymm
    (le_iInf fun i => le_iInf fun hi => le_iInf fun j => le_iInf fun hj =>
      iInf_le_of_le j <| iInf_le_of_le hj <| iInf_le_of_le i <| iInf_le _ hi)
    (le_iInf fun i => le_iInf fun hi => le_iInf fun j => le_iInf fun hj =>
      iInf_le_of_le j <| iInf_le_of_le hj <| iInf_le_of_le i <| iInf_le _ hi)
#align filter.lift_comm Filter.lift_comm

theorem lift_assoc {h : Set β → Filter γ} (hg : Monotone g) :
    (f.lift g).lift h = f.lift fun s => (g s).lift h :=
  le_antisymm
    (le_iInf₂ fun _s hs => le_iInf₂ fun t ht =>
      iInf_le_of_le t <| iInf_le _ <| (mem_lift_sets hg).mpr ⟨_, hs, ht⟩)
    (le_iInf₂ fun t ht =>
      let ⟨s, hs, h'⟩ := (mem_lift_sets hg).mp ht
      iInf_le_of_le s <| iInf_le_of_le hs <| iInf_le_of_le t <| iInf_le _ h')
#align filter.lift_assoc Filter.lift_assoc

theorem lift_lift_same_le_lift {g : Set α → Set α → Filter β} :
    (f.lift fun s => f.lift (g s)) ≤ f.lift fun s => g s s :=
  le_lift.2 fun _s hs => lift_le hs <| lift_le hs le_rfl
#align filter.lift_lift_same_le_lift Filter.lift_lift_same_le_lift

theorem lift_lift_same_eq_lift {g : Set α → Set α → Filter β} (hg₁ : ∀ s, Monotone fun t => g s t)
    (hg₂ : ∀ t, Monotone fun s => g s t) : (f.lift fun s => f.lift (g s)) = f.lift fun s => g s s :=
  lift_lift_same_le_lift.antisymm <|
    le_lift.2 fun s hs => le_lift.2 fun t ht => lift_le (inter_mem hs ht) <|
      calc
        g (s ∩ t) (s ∩ t) ≤ g s (s ∩ t) := hg₂ (s ∩ t) (inter_subset_left _ _)
        _ ≤ g s t := hg₁ s (inter_subset_right _ _)
#align filter.lift_lift_same_eq_lift Filter.lift_lift_same_eq_lift

theorem lift_principal {s : Set α} (hg : Monotone g) : (𝓟 s).lift g = g s :=
  (lift_le (mem_principal_self _) le_rfl).antisymm (le_lift.2 fun _t ht => hg ht)
#align filter.lift_principal Filter.lift_principal

theorem monotone_lift [Preorder γ] {f : γ → Filter α} {g : γ → Set α → Filter β} (hf : Monotone f)
    (hg : Monotone g) : Monotone fun c => (f c).lift (g c) := fun _ _ h => lift_mono (hf h) (hg h)
#align filter.monotone_lift Filter.monotone_lift

theorem lift_neBot_iff (hm : Monotone g) : (NeBot (f.lift g)) ↔ ∀ s ∈ f, NeBot (g s) := by
  simp only [neBot_iff, Ne.def, ← empty_mem_iff_bot, mem_lift_sets hm, not_exists, not_and]
  -- 🎉 no goals
#align filter.lift_ne_bot_iff Filter.lift_neBot_iff

@[simp]
theorem lift_const {f : Filter α} {g : Filter β} : (f.lift fun _ => g) = g :=
  iInf_subtype'.trans iInf_const
#align filter.lift_const Filter.lift_const

@[simp]
theorem lift_inf {f : Filter α} {g h : Set α → Filter β} :
    (f.lift fun x => g x ⊓ h x) = f.lift g ⊓ f.lift h := by simp only [Filter.lift, iInf_inf_eq]
                                                            -- 🎉 no goals
#align filter.lift_inf Filter.lift_inf

@[simp]
theorem lift_principal2 {f : Filter α} : f.lift 𝓟 = f :=
  le_antisymm (fun s hs => mem_lift hs (mem_principal_self s))
    (le_iInf fun s => le_iInf fun hs => by simp only [hs, le_principal_iff])
                                           -- 🎉 no goals
#align filter.lift_principal2 Filter.lift_principal2

theorem lift_iInf_le {f : ι → Filter α} {g : Set α → Filter β} :
    (iInf f).lift g ≤ ⨅ i, (f i).lift g :=
  le_iInf fun _ => lift_mono (iInf_le _ _) le_rfl
#align filter.lift_infi_le Filter.lift_iInf_le

theorem lift_iInf [Nonempty ι] {f : ι → Filter α} {g : Set α → Filter β}
    (hg : ∀ s t, g (s ∩ t) = g s ⊓ g t) : (iInf f).lift g = ⨅ i, (f i).lift g := by
  refine' lift_iInf_le.antisymm fun s => _
  -- ⊢ s ∈ Filter.lift (iInf f) g → s ∈ ⨅ (i : ι), Filter.lift (f i) g
  have H : ∀ t ∈ iInf f, ⨅ i, (f i).lift g ≤ g t := by
    intro t ht
    refine' iInf_sets_induct ht _ fun hs ht => _
    · inhabit ι
      exact iInf₂_le_of_le default univ (iInf_le _ univ_mem)
    · rw [hg]
      exact le_inf (iInf₂_le_of_le _ _ <| iInf_le _ hs) ht
  simp only [mem_lift_sets (Monotone.of_map_inf hg), exists_imp, and_imp]
  -- ⊢ ∀ (x : Set α), x ∈ iInf f → s ∈ g x → s ∈ ⨅ (i : ι), Filter.lift (f i) g
  exact fun t ht hs => H t ht hs
  -- 🎉 no goals
#align filter.lift_infi Filter.lift_iInf

theorem lift_iInf_of_directed [Nonempty ι] {f : ι → Filter α} {g : Set α → Filter β}
    (hf : Directed (· ≥ ·) f) (hg : Monotone g) : (iInf f).lift g = ⨅ i, (f i).lift g :=
  lift_iInf_le.antisymm fun s => by
    simp only [mem_lift_sets hg, exists_imp, and_imp, mem_iInf_of_directed hf]
    -- ⊢ ∀ (x : Set α) (x_1 : ι), x ∈ f x_1 → s ∈ g x → s ∈ ⨅ (i : ι), Filter.lift (f …
    exact fun t i ht hs => mem_iInf_of_mem i <| mem_lift ht hs
    -- 🎉 no goals
#align filter.lift_infi_of_directed Filter.lift_iInf_of_directed

theorem lift_iInf_of_map_univ {f : ι → Filter α} {g : Set α → Filter β}
    (hg : ∀ s t, g (s ∩ t) = g s ⊓ g t) (hg' : g univ = ⊤) :
    (iInf f).lift g = ⨅ i, (f i).lift g := by
  cases isEmpty_or_nonempty ι
  -- ⊢ Filter.lift (iInf f) g = ⨅ (i : ι), Filter.lift (f i) g
  · simp [iInf_of_empty, hg']
    -- 🎉 no goals
  · exact lift_iInf hg
    -- 🎉 no goals
#align filter.lift_infi_of_map_univ Filter.lift_iInf_of_map_univ

end lift

section Lift'

/-- Specialize `lift` to functions `Set α → Set β`. This can be viewed as a generalization of `map`.
This is essentially a push-forward along a function mapping each set to a set. -/
protected def lift' (f : Filter α) (h : Set α → Set β) :=
  f.lift (𝓟 ∘ h)
#align filter.lift' Filter.lift'

variable {f f₁ f₂ : Filter α} {h h₁ h₂ : Set α → Set β}

@[simp]
theorem lift'_top (h : Set α → Set β) : (⊤ : Filter α).lift' h = 𝓟 (h univ) :=
  lift_top _
#align filter.lift'_top Filter.lift'_top

theorem mem_lift' {t : Set α} (ht : t ∈ f) : h t ∈ f.lift' h :=
  le_principal_iff.mp <| show f.lift' h ≤ 𝓟 (h t) from iInf_le_of_le t <| iInf_le_of_le ht <| le_rfl
#align filter.mem_lift' Filter.mem_lift'

theorem tendsto_lift' {m : γ → β} {l : Filter γ} :
    Tendsto m l (f.lift' h) ↔ ∀ s ∈ f, ∀ᶠ a in l, m a ∈ h s := by
  simp only [Filter.lift', tendsto_lift, tendsto_principal, comp]
  -- 🎉 no goals
#align filter.tendsto_lift' Filter.tendsto_lift'

theorem HasBasis.lift' {ι} {p : ι → Prop} {s} (hf : f.HasBasis p s) (hh : Monotone h) :
    (f.lift' h).HasBasis p (h ∘ s) :=
  ⟨fun t => (hf.mem_lift_iff (fun i => hasBasis_principal (h (s i)))
    (monotone_principal.comp hh)).trans <| by simp only [exists_const, true_and, comp]⟩
                                              -- 🎉 no goals
#align filter.has_basis.lift' Filter.HasBasis.lift'

theorem mem_lift'_sets (hh : Monotone h) {s : Set β} : s ∈ f.lift' h ↔ ∃ t ∈ f, h t ⊆ s :=
  mem_lift_sets <| monotone_principal.comp hh
#align filter.mem_lift'_sets Filter.mem_lift'_sets

theorem eventually_lift'_iff (hh : Monotone h) {p : β → Prop} :
    (∀ᶠ y in f.lift' h, p y) ↔ ∃ t ∈ f, ∀ y ∈ h t, p y :=
  mem_lift'_sets hh
#align filter.eventually_lift'_iff Filter.eventually_lift'_iff

theorem sInter_lift'_sets (hh : Monotone h) : ⋂₀ { s | s ∈ f.lift' h } = ⋂ s ∈ f, h s :=
  (sInter_lift_sets (monotone_principal.comp hh)).trans <| iInter₂_congr fun _ _ => csInf_Ici
#align filter.sInter_lift'_sets Filter.sInter_lift'_sets

theorem lift'_le {f : Filter α} {g : Set α → Set β} {h : Filter β} {s : Set α} (hs : s ∈ f)
    (hg : 𝓟 (g s) ≤ h) : f.lift' g ≤ h :=
  lift_le hs hg
#align filter.lift'_le Filter.lift'_le

theorem lift'_mono (hf : f₁ ≤ f₂) (hh : h₁ ≤ h₂) : f₁.lift' h₁ ≤ f₂.lift' h₂ :=
  lift_mono hf fun s => principal_mono.mpr <| hh s
#align filter.lift'_mono Filter.lift'_mono

theorem lift'_mono' (hh : ∀ s ∈ f, h₁ s ⊆ h₂ s) : f.lift' h₁ ≤ f.lift' h₂ :=
  iInf₂_mono fun s hs => principal_mono.mpr <| hh s hs
#align filter.lift'_mono' Filter.lift'_mono'

theorem lift'_cong (hh : ∀ s ∈ f, h₁ s = h₂ s) : f.lift' h₁ = f.lift' h₂ :=
  le_antisymm (lift'_mono' fun s hs => le_of_eq <| hh s hs)
    (lift'_mono' fun s hs => le_of_eq <| (hh s hs).symm)
#align filter.lift'_cong Filter.lift'_cong

theorem map_lift'_eq {m : β → γ} (hh : Monotone h) : map m (f.lift' h) = f.lift' (image m ∘ h) :=
  calc
    map m (f.lift' h) = f.lift (map m ∘ 𝓟 ∘ h) := map_lift_eq <| monotone_principal.comp hh
    _ = f.lift' (image m ∘ h) := by simp only [comp, Filter.lift', map_principal]
                                    -- 🎉 no goals
#align filter.map_lift'_eq Filter.map_lift'_eq

theorem lift'_map_le {g : Set β → Set γ} {m : α → β} : (map m f).lift' g ≤ f.lift' (g ∘ image m) :=
  lift_map_le
#align filter.lift'_map_le Filter.lift'_map_le

theorem map_lift'_eq2 {g : Set β → Set γ} {m : α → β} (hg : Monotone g) :
    (map m f).lift' g = f.lift' (g ∘ image m) :=
  map_lift_eq2 <| monotone_principal.comp hg
#align filter.map_lift'_eq2 Filter.map_lift'_eq2

theorem comap_lift'_eq {m : γ → β} : comap m (f.lift' h) = f.lift' (preimage m ∘ h) := by
  simp only [Filter.lift', comap_lift_eq, (· ∘ ·), comap_principal]
  -- 🎉 no goals
#align filter.comap_lift'_eq Filter.comap_lift'_eq

theorem comap_lift'_eq2 {m : β → α} {g : Set β → Set γ} (hg : Monotone g) :
    (comap m f).lift' g = f.lift' (g ∘ preimage m) :=
  comap_lift_eq2 <| monotone_principal.comp hg
#align filter.comap_lift'_eq2 Filter.comap_lift'_eq2

theorem lift'_principal {s : Set α} (hh : Monotone h) : (𝓟 s).lift' h = 𝓟 (h s) :=
  lift_principal <| monotone_principal.comp hh
#align filter.lift'_principal Filter.lift'_principal

theorem lift'_pure {a : α} (hh : Monotone h) : (pure a : Filter α).lift' h = 𝓟 (h {a}) := by
  rw [← principal_singleton, lift'_principal hh]
  -- 🎉 no goals
#align filter.lift'_pure Filter.lift'_pure

theorem lift'_bot (hh : Monotone h) : (⊥ : Filter α).lift' h = 𝓟 (h ∅) := by
  rw [← principal_empty, lift'_principal hh]
  -- 🎉 no goals
#align filter.lift'_bot Filter.lift'_bot

theorem le_lift' {f : Filter α} {h : Set α → Set β} {g : Filter β} :
    g ≤ f.lift' h ↔ ∀ s ∈ f, h s ∈ g :=
  le_lift.trans <| forall₂_congr fun _ _ => le_principal_iff
#align filter.le_lift' Filter.le_lift'

theorem principal_le_lift' {t : Set β} : 𝓟 t ≤ f.lift' h ↔ ∀ s ∈ f, t ⊆ h s :=
  le_lift'
#align filter.principal_le_lift' Filter.principal_le_lift'

theorem monotone_lift' [Preorder γ] {f : γ → Filter α} {g : γ → Set α → Set β} (hf : Monotone f)
    (hg : Monotone g) : Monotone fun c => (f c).lift' (g c) := fun _ _ h => lift'_mono (hf h) (hg h)
#align filter.monotone_lift' Filter.monotone_lift'

theorem lift_lift'_assoc {g : Set α → Set β} {h : Set β → Filter γ} (hg : Monotone g)
    (hh : Monotone h) : (f.lift' g).lift h = f.lift fun s => h (g s) :=
  calc
    (f.lift' g).lift h = f.lift fun s => (𝓟 (g s)).lift h := lift_assoc (monotone_principal.comp hg)
    _ = f.lift fun s => h (g s) := by simp only [lift_principal, hh, eq_self_iff_true]
                                      -- 🎉 no goals
#align filter.lift_lift'_assoc Filter.lift_lift'_assoc

theorem lift'_lift'_assoc {g : Set α → Set β} {h : Set β → Set γ} (hg : Monotone g)
    (hh : Monotone h) : (f.lift' g).lift' h = f.lift' fun s => h (g s) :=
  lift_lift'_assoc hg (monotone_principal.comp hh)
#align filter.lift'_lift'_assoc Filter.lift'_lift'_assoc

theorem lift'_lift_assoc {g : Set α → Filter β} {h : Set β → Set γ} (hg : Monotone g) :
    (f.lift g).lift' h = f.lift fun s => (g s).lift' h :=
  lift_assoc hg
#align filter.lift'_lift_assoc Filter.lift'_lift_assoc

theorem lift_lift'_same_le_lift' {g : Set α → Set α → Set β} :
    (f.lift fun s => f.lift' (g s)) ≤ f.lift' fun s => g s s :=
  lift_lift_same_le_lift
#align filter.lift_lift'_same_le_lift' Filter.lift_lift'_same_le_lift'

theorem lift_lift'_same_eq_lift' {g : Set α → Set α → Set β} (hg₁ : ∀ s, Monotone fun t => g s t)
    (hg₂ : ∀ t, Monotone fun s => g s t) :
    (f.lift fun s => f.lift' (g s)) = f.lift' fun s => g s s :=
  lift_lift_same_eq_lift (fun s => monotone_principal.comp (hg₁ s)) fun t =>
    monotone_principal.comp (hg₂ t)
#align filter.lift_lift'_same_eq_lift' Filter.lift_lift'_same_eq_lift'

theorem lift'_inf_principal_eq {h : Set α → Set β} {s : Set β} :
    f.lift' h ⊓ 𝓟 s = f.lift' fun t => h t ∩ s := by
  simp only [Filter.lift', Filter.lift, (· ∘ ·), ← inf_principal, iInf_subtype', ← iInf_inf]
  -- 🎉 no goals
#align filter.lift'_inf_principal_eq Filter.lift'_inf_principal_eq

theorem lift'_neBot_iff (hh : Monotone h) : NeBot (f.lift' h) ↔ ∀ s ∈ f, (h s).Nonempty :=
  calc
    NeBot (f.lift' h) ↔ ∀ s ∈ f, NeBot (𝓟 (h s)) := lift_neBot_iff (monotone_principal.comp hh)
    _ ↔ ∀ s ∈ f, (h s).Nonempty := by simp only [principal_neBot_iff]
                                      -- 🎉 no goals
#align filter.lift'_ne_bot_iff Filter.lift'_neBot_iff

@[simp]
theorem lift'_id {f : Filter α} : f.lift' id = f :=
  lift_principal2
#align filter.lift'_id Filter.lift'_id

theorem lift'_iInf [Nonempty ι] {f : ι → Filter α} {g : Set α → Set β}
    (hg : ∀ s t, g (s ∩ t) = g s ∩ g t) : (iInf f).lift' g = ⨅ i, (f i).lift' g :=
  lift_iInf fun s t => by simp only [inf_principal, comp, hg]
                          -- 🎉 no goals
#align filter.lift'_infi Filter.lift'_iInf

theorem lift'_iInf_of_map_univ {f : ι → Filter α} {g : Set α → Set β}
    (hg : ∀ {s t}, g (s ∩ t) = g s ∩ g t) (hg' : g univ = univ) :
    (iInf f).lift' g = ⨅ i, (f i).lift' g :=
  lift_iInf_of_map_univ (fun s t => by simp only [inf_principal, comp, hg])
                                       -- 🎉 no goals
    (by rw [Function.comp_apply, hg', principal_univ])
        -- 🎉 no goals
#align filter.lift'_infi_of_map_univ Filter.lift'_iInf_of_map_univ

theorem lift'_inf (f g : Filter α) {s : Set α → Set β} (hs : ∀ t₁ t₂, s (t₁ ∩ t₂) = s t₁ ∩ s t₂) :
    (f ⊓ g).lift' s = f.lift' s ⊓ g.lift' s := by
  rw [inf_eq_iInf, inf_eq_iInf, lift'_iInf hs]
  -- ⊢ ⨅ (i : Bool), Filter.lift' (bif i then f else g) s = ⨅ (b : Bool), bif b the …
  refine iInf_congr ?_
  -- ⊢ ∀ (i : Bool), Filter.lift' (bif i then f else g) s = bif i then Filter.lift' …
  rintro (_|_) <;> rfl
  -- ⊢ Filter.lift' (bif false then f else g) s = bif false then Filter.lift' f s e …
                   -- 🎉 no goals
                   -- 🎉 no goals
#align filter.lift'_inf Filter.lift'_inf

theorem lift'_inf_le (f g : Filter α) (s : Set α → Set β) :
    (f ⊓ g).lift' s ≤ f.lift' s ⊓ g.lift' s :=
  le_inf (lift'_mono inf_le_left le_rfl) (lift'_mono inf_le_right le_rfl)
#align filter.lift'_inf_le Filter.lift'_inf_le

theorem comap_eq_lift' {f : Filter β} {m : α → β} : comap m f = f.lift' (preimage m) :=
  Filter.ext fun _ => (mem_lift'_sets monotone_preimage).symm
#align filter.comap_eq_lift' Filter.comap_eq_lift'

end Lift'

section Prod

variable {f : Filter α}

theorem prod_def {f : Filter α} {g : Filter β} :
    f ×ˢ g = f.lift fun s => g.lift' fun t => s ×ˢ t := by
  simpa only [Filter.lift', Filter.lift, (f.basis_sets.prod g.basis_sets).eq_biInf,
    iInf_prod, iInf_and] using iInf_congr fun i => iInf_comm
#align filter.prod_def Filter.prod_def

alias mem_prod_same_iff := mem_prod_self_iff
#align filter.mem_prod_same_iff Filter.mem_prod_same_iff

theorem prod_same_eq : f ×ˢ f = f.lift' fun t : Set α => t ×ˢ t :=
  f.basis_sets.prod_self.eq_biInf
#align filter.prod_same_eq Filter.prod_same_eq

theorem tendsto_prod_self_iff {f : α × α → β} {x : Filter α} {y : Filter β} :
    Filter.Tendsto f (x ×ˢ x) y ↔ ∀ W ∈ y, ∃ U ∈ x, ∀ x x' : α, x ∈ U → x' ∈ U → f (x, x') ∈ W := by
  simp only [tendsto_def, mem_prod_same_iff, prod_sub_preimage_iff, exists_prop, iff_self_iff]
  -- 🎉 no goals
#align filter.tendsto_prod_self_iff Filter.tendsto_prod_self_iff

variable {α₁ : Type*} {α₂ : Type*} {β₁ : Type*} {β₂ : Type*}

theorem prod_lift_lift {f₁ : Filter α₁} {f₂ : Filter α₂} {g₁ : Set α₁ → Filter β₁}
    {g₂ : Set α₂ → Filter β₂} (hg₁ : Monotone g₁) (hg₂ : Monotone g₂) :
    f₁.lift g₁ ×ˢ f₂.lift g₂ = f₁.lift fun s => f₂.lift fun t => g₁ s ×ˢ g₂ t := by
  simp only [prod_def, lift_assoc hg₁]
  -- ⊢ (Filter.lift f₁ fun s => Filter.lift (g₁ s) fun s => Filter.lift' (Filter.li …
  apply congr_arg; funext x
  -- ⊢ (fun s => Filter.lift (g₁ s) fun s => Filter.lift' (Filter.lift f₂ g₂) fun t …
                   -- ⊢ (Filter.lift (g₁ x) fun s => Filter.lift' (Filter.lift f₂ g₂) fun t => s ×ˢ  …
  rw [lift_comm]
  -- ⊢ (Filter.lift (g₁ x) fun s => Filter.lift' (Filter.lift f₂ g₂) fun t => s ×ˢ  …
  apply congr_arg; funext y
  -- ⊢ (fun s => Filter.lift' (Filter.lift f₂ g₂) fun t => s ×ˢ t) = fun t => Filte …
                   -- ⊢ (Filter.lift' (Filter.lift f₂ g₂) fun t => y ×ˢ t) = Filter.lift f₂ fun s => …
  apply lift'_lift_assoc hg₂
  -- 🎉 no goals
#align filter.prod_lift_lift Filter.prod_lift_lift

theorem prod_lift'_lift' {f₁ : Filter α₁} {f₂ : Filter α₂} {g₁ : Set α₁ → Set β₁}
    {g₂ : Set α₂ → Set β₂} (hg₁ : Monotone g₁) (hg₂ : Monotone g₂) :
    f₁.lift' g₁ ×ˢ f₂.lift' g₂ = f₁.lift fun s => f₂.lift' fun t => g₁ s ×ˢ g₂ t :=
  calc
    f₁.lift' g₁ ×ˢ f₂.lift' g₂ = f₁.lift fun s => f₂.lift fun t => 𝓟 (g₁ s) ×ˢ 𝓟 (g₂ t) :=
      prod_lift_lift (monotone_principal.comp hg₁) (monotone_principal.comp hg₂)
    _ = f₁.lift fun s => f₂.lift fun t => 𝓟 (g₁ s ×ˢ g₂ t) := by
      { simp only [prod_principal_principal] }
      -- 🎉 no goals
#align filter.prod_lift'_lift' Filter.prod_lift'_lift'

end Prod

end Filter
