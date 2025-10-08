/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Alex Kontorovich
-/
import Mathlib.Data.Set.Piecewise
import Mathlib.Order.Filter.Tendsto
import Mathlib.Order.Filter.Bases.Finite

/-!
# (Co)product of a family of filters

In this file we define two filters on `Π i, α i` and prove some basic properties of these filters.

* `Filter.pi (f : Π i, Filter (α i))` to be the maximal filter on `Π i, α i` such that
  `∀ i, Filter.Tendsto (Function.eval i) (Filter.pi f) (f i)`. It is defined as
  `Π i, Filter.comap (Function.eval i) (f i)`. This is a generalization of `Filter.prod` to indexed
  products.

* `Filter.coprodᵢ (f : Π i, Filter (α i))`: a generalization of `Filter.coprod`; it is the supremum
  of `comap (eval i) (f i)`.
-/


open Set Function Filter

namespace Filter

variable {ι : Type*} {α : ι → Type*} {f f₁ f₂ : (i : ι) → Filter (α i)} {s : (i : ι) → Set (α i)}
  {p : ∀ i, α i → Prop}

section Pi

theorem tendsto_eval_pi (f : ∀ i, Filter (α i)) (i : ι) : Tendsto (eval i) (pi f) (f i) :=
  tendsto_iInf' i tendsto_comap

theorem tendsto_pi {β : Type*} {m : β → ∀ i, α i} {l : Filter β} :
    Tendsto m l (pi f) ↔ ∀ i, Tendsto (fun x => m x i) l (f i) := by
  simp only [pi, tendsto_iInf, tendsto_comap_iff]; rfl

/-- If a function tends to a product `Filter.pi f` of filters, then its `i`-th component tends to
`f i`. See also `Filter.Tendsto.apply_nhds` for the special case of converging to a point in a
product of topological spaces. -/
alias ⟨Tendsto.apply, _⟩ := tendsto_pi

theorem le_pi {g : Filter (∀ i, α i)} : g ≤ pi f ↔ ∀ i, Tendsto (eval i) g (f i) :=
  tendsto_pi

@[mono]
theorem pi_mono (h : ∀ i, f₁ i ≤ f₂ i) : pi f₁ ≤ pi f₂ :=
  iInf_mono fun i => comap_mono <| h i

theorem mem_pi_of_mem (i : ι) {s : Set (α i)} (hs : s ∈ f i) : eval i ⁻¹' s ∈ pi f :=
  mem_iInf_of_mem i <| preimage_mem_comap hs

theorem pi_mem_pi {I : Set ι} (hI : I.Finite) (h : ∀ i ∈ I, s i ∈ f i) : I.pi s ∈ pi f := by
  rw [pi_def, biInter_eq_iInter]
  refine mem_iInf_of_iInter hI (fun i => ?_) Subset.rfl
  exact preimage_mem_comap (h i i.2)

theorem mem_pi {s : Set (∀ i, α i)} :
    s ∈ pi f ↔ ∃ I : Set ι, I.Finite ∧ ∃ t : ∀ i, Set (α i), (∀ i, t i ∈ f i) ∧ I.pi t ⊆ s := by
  constructor
  · simp only [pi, mem_iInf', mem_comap, pi_def]
    rintro ⟨I, If, V, hVf, -, rfl, -⟩
    choose t htf htV using hVf
    exact ⟨I, If, t, htf, iInter₂_mono fun i _ => htV i⟩
  · rintro ⟨I, If, t, htf, hts⟩
    exact mem_of_superset (pi_mem_pi If fun i _ => htf i) hts

theorem mem_pi' {s : Set (∀ i, α i)} :
    s ∈ pi f ↔ ∃ I : Finset ι, ∃ t : ∀ i, Set (α i), (∀ i, t i ∈ f i) ∧ Set.pi (↑I) t ⊆ s :=
  mem_pi.trans exists_finite_iff_finset

theorem mem_of_pi_mem_pi [∀ i, NeBot (f i)] {I : Set ι} (h : I.pi s ∈ pi f) {i : ι} (hi : i ∈ I) :
    s i ∈ f i := by
  classical
  rcases mem_pi.1 h with ⟨I', -, t, htf, hts⟩
  refine mem_of_superset (htf i) fun x hx => ?_
  have : ∀ i, (t i).Nonempty := fun i => nonempty_of_mem (htf i)
  choose g hg using this
  have : update g i x ∈ I'.pi t := fun j _ => by
    rcases eq_or_ne j i with (rfl | hne) <;> simp [*]
  simpa using hts this i hi

@[simp]
theorem pi_mem_pi_iff [∀ i, NeBot (f i)] {I : Set ι} (hI : I.Finite) :
    I.pi s ∈ pi f ↔ ∀ i ∈ I, s i ∈ f i :=
  ⟨fun h _i hi => mem_of_pi_mem_pi h hi, pi_mem_pi hI⟩

theorem Eventually.eval_pi {i : ι} (hf : ∀ᶠ x : α i in f i, p i x) :
    ∀ᶠ x : ∀ i : ι, α i in pi f, p i (x i) := (tendsto_eval_pi _ _).eventually hf

theorem eventually_pi [Finite ι] (hf : ∀ i, ∀ᶠ x in f i, p i x) :
    ∀ᶠ x : ∀ i, α i in pi f, ∀ i, p i (x i) := eventually_all.2 fun _i => (hf _).eval_pi

theorem hasBasis_pi {ι' : ι → Type*} {s : ∀ i, ι' i → Set (α i)} {p : ∀ i, ι' i → Prop}
    (h : ∀ i, (f i).HasBasis (p i) (s i)) :
    (pi f).HasBasis (fun If : Set ι × ∀ i, ι' i => If.1.Finite ∧ ∀ i ∈ If.1, p i (If.2 i))
      fun If : Set ι × ∀ i, ι' i => If.1.pi fun i => s i <| If.2 i := by
  simpa [Set.pi_def] using HasBasis.iInf' fun i => (h i).comap (eval i : (∀ j, α j) → α i)

theorem hasBasis_pi_same_index {κ : Type*} {p : κ → Prop} {s : Π i : ι, κ → Set (α i)}
    (h : ∀ i : ι, (f i).HasBasis p (s i))
    (h_dir : ∀ I : Set ι, ∀ k : ι → κ, I.Finite → (∀ i ∈ I, p (k i)) →
      ∃ k₀, p k₀ ∧ ∀ i ∈ I, s i k₀ ⊆ s i (k i)) :
    (pi f).HasBasis (fun Ik : Set ι × κ ↦ Ik.1.Finite ∧ p Ik.2)
      (fun Ik ↦ Ik.1.pi (fun i ↦ s i Ik.2)) := by
  refine hasBasis_pi h |>.to_hasBasis ?_ ?_
  · rintro ⟨I, k⟩ ⟨hI, hk⟩
    rcases h_dir I k hI hk with ⟨k₀, hk₀, hk₀'⟩
    exact ⟨⟨I, k₀⟩, ⟨hI, hk₀⟩, Set.pi_mono hk₀'⟩
  · rintro ⟨I, k⟩ ⟨hI, hk⟩
    exact ⟨⟨I, fun _ ↦ k⟩, ⟨hI, fun _ _ ↦ hk⟩, subset_rfl⟩

theorem HasBasis.pi_self {α : Type*} {κ : Type*} {f : Filter α} {p : κ → Prop} {s : κ → Set α}
    (h : f.HasBasis p s) :
    (pi fun _ ↦ f).HasBasis (fun Ik : Set ι × κ ↦ Ik.1.Finite ∧ p Ik.2)
      (fun Ik ↦ Ik.1.pi (fun _ ↦ s Ik.2)) := by
  refine hasBasis_pi_same_index (fun _ ↦ h) (fun I k hI hk ↦ ?_)
  rcases h.mem_iff.mp (biInter_mem hI |>.mpr fun i hi ↦ h.mem_of_mem (hk i hi))
    with ⟨k₀, hk₀, hk₀'⟩
  exact ⟨k₀, hk₀, fun i hi ↦ hk₀'.trans (biInter_subset_of_mem hi)⟩

theorem le_pi_principal (s : (i : ι) → Set (α i)) :
    𝓟 (univ.pi s) ≤ pi fun i ↦ 𝓟 (s i) :=
  le_pi.2 fun i ↦ tendsto_principal_principal.2 fun _f hf ↦ hf i trivial

/-- The indexed product of finitely many principal filters
is the principal filter corresponding to the cylinder `Set.univ.pi s`.

If the index type is infinite, then `mem_pi_principal` and `hasBasis_pi_principal` may be useful. -/
@[simp]
theorem pi_principal [Finite ι] (s : (i : ι) → Set (α i)) :
    pi (fun i ↦ 𝓟 (s i)) = 𝓟 (univ.pi s) := by
  simp [Filter.pi, Set.pi_def]

/-- The indexed product of a (possibly, infinite) family of principal filters
is generated by the finite `Set.pi` cylinders.

If the index type is finite, then the indexed product of principal filters
is a principal filter, see `pi_principal`. -/
theorem mem_pi_principal {t : Set ((i : ι) → α i)} :
    t ∈ pi (fun i ↦ 𝓟 (s i)) ↔ ∃ I : Set ι, I.Finite ∧ I.pi s ⊆ t :=
  (hasBasis_pi (fun i ↦ hasBasis_principal _)).mem_iff.trans <| by simp

/-- The indexed product of a (possibly, infinite) family of principal filters
is generated by the finite `Set.pi` cylinders.

If the index type is finite, then the indexed product of principal filters
is a principal filter, see `pi_principal`. -/
theorem hasBasis_pi_principal (s : (i : ι) → Set (α i)) :
    HasBasis (pi fun i ↦ 𝓟 (s i)) Set.Finite (Set.pi · s) :=
  ⟨fun _ ↦ mem_pi_principal⟩

/-- The indexed product of finitely many pure filters `pure (f i)` is the pure filter `pure f`.

If the index type is infinite, then `mem_pi_pure` and `hasBasis_pi_pure` below may be useful. -/
@[simp]
theorem pi_pure [Finite ι] (f : (i : ι) → α i) : pi (pure <| f ·) = pure f := by
  simp only [← principal_singleton, pi_principal, univ_pi_singleton]

/-- The indexed product of a (possibly, infinite) family of pure filters `pure (f i)`
is generated by the sets of functions that are equal to `f` on a finite set.

If the index type is finite, then the indexed product of pure filters is a pure filter,
see `pi_pure`. -/
theorem mem_pi_pure {f : (i : ι) → α i} {s : Set ((i : ι) → α i)} :
    s ∈ pi (fun i ↦ pure (f i)) ↔ ∃ I : Set ι, I.Finite ∧ ∀ g, (∀ i ∈ I, g i = f i) → g ∈ s := by
  simp only [← principal_singleton, mem_pi_principal]
  simp [subset_def]

/-- The indexed product of a (possibly, infinite) family of pure filters `pure (f i)`
is generated by the sets of functions that are equal to `f` on a finite set.

If the index type is finite, then the indexed product of pure filters is a pure filter,
see `pi_pure`. -/
theorem hasBasis_pi_pure (f : (i : ι) → α i) :
    HasBasis (pi fun i ↦ pure (f i)) Set.Finite (fun I ↦ {g | ∀ i ∈ I, g i = f i}) :=
  ⟨fun _ ↦ mem_pi_pure⟩

@[simp]
theorem pi_inf_principal_univ_pi_eq_bot :
    pi f ⊓ 𝓟 (Set.pi univ s) = ⊥ ↔ ∃ i, f i ⊓ 𝓟 (s i) = ⊥ := by
  constructor
  · simp only [inf_principal_eq_bot, mem_pi]
    contrapose!
    rintro (hsf : ∀ i, ∃ᶠ x in f i, x ∈ s i) I - t htf hts
    have : ∀ i, (s i ∩ t i).Nonempty := fun i => ((hsf i).and_eventually (htf i)).exists
    choose x hxs hxt using this
    exact hts (fun i _ => hxt i) (mem_univ_pi.2 hxs)
  · simp only [inf_principal_eq_bot]
    rintro ⟨i, hi⟩
    filter_upwards [mem_pi_of_mem i hi] with x using mt fun h => h i trivial

@[simp]
theorem pi_inf_principal_pi_eq_bot [∀ i, NeBot (f i)] {I : Set ι} :
    pi f ⊓ 𝓟 (Set.pi I s) = ⊥ ↔ ∃ i ∈ I, f i ⊓ 𝓟 (s i) = ⊥ := by
  classical
  rw [← univ_pi_piecewise_univ I, pi_inf_principal_univ_pi_eq_bot]
  refine exists_congr fun i => ?_
  by_cases hi : i ∈ I <;> simp [hi, NeBot.ne']

@[simp]
theorem pi_inf_principal_univ_pi_neBot :
    NeBot (pi f ⊓ 𝓟 (Set.pi univ s)) ↔ ∀ i, NeBot (f i ⊓ 𝓟 (s i)) := by simp [neBot_iff]

@[simp]
theorem pi_inf_principal_pi_neBot [∀ i, NeBot (f i)] {I : Set ι} :
    NeBot (pi f ⊓ 𝓟 (I.pi s)) ↔ ∀ i ∈ I, NeBot (f i ⊓ 𝓟 (s i)) := by simp [neBot_iff]

instance PiInfPrincipalPi.neBot [h : ∀ i, NeBot (f i ⊓ 𝓟 (s i))] {I : Set ι} :
    NeBot (pi f ⊓ 𝓟 (I.pi s)) :=
  (pi_inf_principal_univ_pi_neBot.2 ‹_›).mono <|
    inf_le_inf_left _ <| principal_mono.2 fun _ hx i _ => hx i trivial

@[simp]
theorem pi_eq_bot : pi f = ⊥ ↔ ∃ i, f i = ⊥ := by
  simpa using @pi_inf_principal_univ_pi_eq_bot ι α f fun _ => univ

@[simp]
theorem pi_neBot : NeBot (pi f) ↔ ∀ i, NeBot (f i) := by simp [neBot_iff]

instance [∀ i, NeBot (f i)] : NeBot (pi f) :=
  pi_neBot.2 ‹_›

@[simp]
theorem map_eval_pi (f : ∀ i, Filter (α i)) [∀ i, NeBot (f i)] (i : ι) :
    map (eval i) (pi f) = f i := by
  refine le_antisymm (tendsto_eval_pi f i) fun s hs => ?_
  rcases mem_pi.1 (mem_map.1 hs) with ⟨I, hIf, t, htf, hI⟩
  rw [← image_subset_iff] at hI
  refine mem_of_superset (htf i) ((subset_eval_image_pi ?_ _).trans hI)
  exact nonempty_of_mem (pi_mem_pi hIf fun i _ => htf i)

@[simp]
theorem pi_le_pi [∀ i, NeBot (f₁ i)] : pi f₁ ≤ pi f₂ ↔ ∀ i, f₁ i ≤ f₂ i :=
  ⟨fun h i => map_eval_pi f₁ i ▸ (tendsto_eval_pi _ _).mono_left h, pi_mono⟩

@[simp]
theorem pi_inj [∀ i, NeBot (f₁ i)] : pi f₁ = pi f₂ ↔ f₁ = f₂ := by
  refine ⟨fun h => ?_, congr_arg pi⟩
  have hle : f₁ ≤ f₂ := pi_le_pi.1 h.le
  haveI : ∀ i, NeBot (f₂ i) := fun i => neBot_of_le (hle i)
  exact hle.antisymm (pi_le_pi.1 h.ge)

theorem tendsto_piMap_pi {β : ι → Type*} {f : ∀ i, α i → β i} {l : ∀ i, Filter (α i)}
    {l' : ∀ i, Filter (β i)} (h : ∀ i, Tendsto (f i) (l i) (l' i)) :
    Tendsto (Pi.map f) (pi l) (pi l') :=
  tendsto_pi.2 fun i ↦ (h i).comp (tendsto_eval_pi _ _)

theorem pi_comap {β : ι → Type*} {f : ∀ i, α i → β i} {l : ∀ i, Filter (β i)} :
    pi (fun i ↦ comap (f i) (l i)) = comap (Pi.map f) (pi l) := by
  simp [Filter.pi, Filter.comap_comap, Function.comp_def]

end Pi

/-! ### `n`-ary coproducts of filters -/

section CoprodCat

-- for "Coprod"

/-- Coproduct of filters. -/
protected def coprodᵢ (f : ∀ i, Filter (α i)) : Filter (∀ i, α i) :=
  ⨆ i : ι, comap (eval i) (f i)

theorem mem_coprodᵢ_iff {s : Set (∀ i, α i)} :
    s ∈ Filter.coprodᵢ f ↔ ∀ i : ι, ∃ t₁ ∈ f i, eval i ⁻¹' t₁ ⊆ s := by simp [Filter.coprodᵢ]

theorem compl_mem_coprodᵢ {s : Set (∀ i, α i)} :
    sᶜ ∈ Filter.coprodᵢ f ↔ ∀ i, (eval i '' s)ᶜ ∈ f i := by
  simp only [Filter.coprodᵢ, mem_iSup, compl_mem_comap]

theorem coprodᵢ_neBot_iff' :
    NeBot (Filter.coprodᵢ f) ↔ (∀ i, Nonempty (α i)) ∧ ∃ d, NeBot (f d) := by
  simp only [Filter.coprodᵢ, iSup_neBot, ← exists_and_left, ← comap_eval_neBot_iff']

@[simp]
theorem coprodᵢ_neBot_iff [∀ i, Nonempty (α i)] : NeBot (Filter.coprodᵢ f) ↔ ∃ d, NeBot (f d) := by
  simp [coprodᵢ_neBot_iff', *]

theorem coprodᵢ_eq_bot_iff' : Filter.coprodᵢ f = ⊥ ↔ (∃ i, IsEmpty (α i)) ∨ f = ⊥ := by
  simpa only [not_neBot, not_and_or, funext_iff, not_forall, not_exists, not_nonempty_iff]
    using coprodᵢ_neBot_iff'.not

@[simp]
theorem coprodᵢ_eq_bot_iff [∀ i, Nonempty (α i)] : Filter.coprodᵢ f = ⊥ ↔ f = ⊥ := by
  simpa [funext_iff] using coprodᵢ_neBot_iff.not

@[simp] theorem coprodᵢ_bot' : Filter.coprodᵢ (⊥ : ∀ i, Filter (α i)) = ⊥ :=
  coprodᵢ_eq_bot_iff'.2 (Or.inr rfl)

@[simp]
theorem coprodᵢ_bot : Filter.coprodᵢ (fun _ => ⊥ : ∀ i, Filter (α i)) = ⊥ :=
  coprodᵢ_bot'

theorem NeBot.coprodᵢ [∀ i, Nonempty (α i)] {i : ι} (h : NeBot (f i)) : NeBot (Filter.coprodᵢ f) :=
  coprodᵢ_neBot_iff.2 ⟨i, h⟩

@[instance]
theorem coprodᵢ_neBot [∀ i, Nonempty (α i)] [Nonempty ι] (f : ∀ i, Filter (α i))
    [H : ∀ i, NeBot (f i)] : NeBot (Filter.coprodᵢ f) :=
  (H (Classical.arbitrary ι)).coprodᵢ

@[mono]
theorem coprodᵢ_mono (hf : ∀ i, f₁ i ≤ f₂ i) : Filter.coprodᵢ f₁ ≤ Filter.coprodᵢ f₂ :=
  iSup_mono fun i => comap_mono (hf i)

variable {β : ι → Type*} {m : ∀ i, α i → β i}

theorem map_pi_map_coprodᵢ_le :
    map (fun k : ∀ i, α i => fun i => m i (k i)) (Filter.coprodᵢ f) ≤
      Filter.coprodᵢ fun i => map (m i) (f i) := by
  simp only [le_def, mem_map, mem_coprodᵢ_iff]
  intro s h i
  obtain ⟨t, H, hH⟩ := h i
  exact ⟨{ x : α i | m i x ∈ t }, H, fun x hx => hH hx⟩

theorem Tendsto.pi_map_coprodᵢ {g : ∀ i, Filter (β i)} (h : ∀ i, Tendsto (m i) (f i) (g i)) :
    Tendsto (fun k : ∀ i, α i => fun i => m i (k i)) (Filter.coprodᵢ f) (Filter.coprodᵢ g) :=
  map_pi_map_coprodᵢ_le.trans (coprodᵢ_mono h)

end CoprodCat

end Filter
