/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Patrick Massot
-/
import Mathlib.Topology.Neighborhoods

/-!
# Neighborhoods of a set

In this file we define the filter `𝓝ˢ s` or `nhdsSet s` consisting of all neighborhoods of a set
`s`.

## Main Properties

There are a couple different notions equivalent to `s ∈ 𝓝ˢ t`:
* `s ⊆ interior t` using `subset_interior_iff_mem_nhdsSet`
* `∀ x : X, x ∈ t → s ∈ 𝓝 x` using `mem_nhdsSet_iff_forall`
* `∃ U : Set X, IsOpen U ∧ t ⊆ U ∧ U ⊆ s` using `mem_nhdsSet_iff_exists`

Furthermore, we have the following results:
* `monotone_nhdsSet`: `𝓝ˢ` is monotone
* In T₁-spaces, `𝓝ˢ`is strictly monotone and hence injective:
  `strict_mono_nhdsSet`/`injective_nhdsSet`. These results are in
  `Mathlib/Topology/Separation/Basic.lean`.
-/

open Set Filter Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : Filter X}
  {s t s₁ s₂ t₁ t₂ : Set X} {x : X}

theorem nhdsSet_diagonal (X) [TopologicalSpace (X × X)] :
    𝓝ˢ (diagonal X) = ⨆ (x : X), 𝓝 (x, x) := by
  rw [nhdsSet, ← range_diag, ← range_comp]
  rfl

theorem mem_nhdsSet_iff_forall : s ∈ 𝓝ˢ t ↔ ∀ x : X, x ∈ t → s ∈ 𝓝 x := by
  simp_rw [nhdsSet, Filter.mem_sSup, forall_mem_image]

lemma nhdsSet_le : 𝓝ˢ s ≤ f ↔ ∀ x ∈ s, 𝓝 x ≤ f := by simp [nhdsSet]

theorem bUnion_mem_nhdsSet {t : X → Set X} (h : ∀ x ∈ s, t x ∈ 𝓝 x) : (⋃ x ∈ s, t x) ∈ 𝓝ˢ s :=
  mem_nhdsSet_iff_forall.2 fun x hx => mem_of_superset (h x hx) <|
    subset_iUnion₂ (s := fun x _ => t x) x hx

theorem subset_interior_iff_mem_nhdsSet : s ⊆ interior t ↔ t ∈ 𝓝ˢ s := by
  simp_rw [mem_nhdsSet_iff_forall, subset_interior_iff_nhds]

theorem disjoint_principal_nhdsSet : Disjoint (𝓟 s) (𝓝ˢ t) ↔ Disjoint (closure s) t := by
  rw [disjoint_principal_left, ← subset_interior_iff_mem_nhdsSet, interior_compl,
    subset_compl_iff_disjoint_left]

theorem disjoint_nhdsSet_principal : Disjoint (𝓝ˢ s) (𝓟 t) ↔ Disjoint s (closure t) := by
  rw [disjoint_comm, disjoint_principal_nhdsSet, disjoint_comm]

theorem mem_nhdsSet_iff_exists : s ∈ 𝓝ˢ t ↔ ∃ U : Set X, IsOpen U ∧ t ⊆ U ∧ U ⊆ s := by
  rw [← subset_interior_iff_mem_nhdsSet, subset_interior_iff]

/-- A proposition is true on a set neighborhood of `s` iff it is true on a larger open set -/
theorem eventually_nhdsSet_iff_exists {p : X → Prop} :
    (∀ᶠ x in 𝓝ˢ s, p x) ↔ ∃ t, IsOpen t ∧ s ⊆ t ∧ ∀ x, x ∈ t → p x :=
  mem_nhdsSet_iff_exists

/-- A proposition is true on a set neighborhood of `s`
iff it is eventually true near each point in the set. -/
theorem eventually_nhdsSet_iff_forall {p : X → Prop} :
    (∀ᶠ x in 𝓝ˢ s, p x) ↔ ∀ x, x ∈ s → ∀ᶠ y in 𝓝 x, p y :=
  mem_nhdsSet_iff_forall

theorem hasBasis_nhdsSet (s : Set X) : (𝓝ˢ s).HasBasis (fun U => IsOpen U ∧ s ⊆ U) fun U => U :=
  ⟨fun t => by simp [mem_nhdsSet_iff_exists, and_assoc]⟩

@[simp]
lemma lift'_nhdsSet_interior (s : Set X) : (𝓝ˢ s).lift' interior = 𝓝ˢ s :=
  (hasBasis_nhdsSet s).lift'_interior_eq_self fun _ ↦ And.left

lemma Filter.HasBasis.nhdsSet_interior {ι : Sort*} {p : ι → Prop} {s : ι → Set X} {t : Set X}
    (h : (𝓝ˢ t).HasBasis p s) : (𝓝ˢ t).HasBasis p (interior <| s ·) :=
  lift'_nhdsSet_interior t ▸ h.lift'_interior

theorem IsOpen.mem_nhdsSet (hU : IsOpen s) : s ∈ 𝓝ˢ t ↔ t ⊆ s := by
  rw [← subset_interior_iff_mem_nhdsSet, hU.interior_eq]

/-- An open set belongs to its own set neighborhoods filter. -/
theorem IsOpen.mem_nhdsSet_self (ho : IsOpen s) : s ∈ 𝓝ˢ s := ho.mem_nhdsSet.mpr Subset.rfl

theorem principal_le_nhdsSet : 𝓟 s ≤ 𝓝ˢ s := fun _s hs =>
  (subset_interior_iff_mem_nhdsSet.mpr hs).trans interior_subset

theorem subset_of_mem_nhdsSet (h : t ∈ 𝓝ˢ s) : s ⊆ t := principal_le_nhdsSet h

theorem Filter.Eventually.self_of_nhdsSet {p : X → Prop} (h : ∀ᶠ x in 𝓝ˢ s, p x) : ∀ x ∈ s, p x :=
  principal_le_nhdsSet h

nonrec theorem Filter.EventuallyEq.self_of_nhdsSet {Y} {f g : X → Y} (h : f =ᶠ[𝓝ˢ s] g) :
    EqOn f g s :=
  h.self_of_nhdsSet

@[simp]
theorem nhdsSet_eq_principal_iff : 𝓝ˢ s = 𝓟 s ↔ IsOpen s := by
  rw [← principal_le_nhdsSet.ge_iff_eq', le_principal_iff, mem_nhdsSet_iff_forall,
    isOpen_iff_mem_nhds]

alias ⟨_, IsOpen.nhdsSet_eq⟩ := nhdsSet_eq_principal_iff

@[simp]
theorem nhdsSet_interior : 𝓝ˢ (interior s) = 𝓟 (interior s) :=
  isOpen_interior.nhdsSet_eq

@[simp]
theorem nhdsSet_singleton : 𝓝ˢ {x} = 𝓝 x := by simp [nhdsSet]

theorem mem_nhdsSet_interior : s ∈ 𝓝ˢ (interior s) :=
  subset_interior_iff_mem_nhdsSet.mp Subset.rfl

@[simp]
theorem nhdsSet_empty : 𝓝ˢ (∅ : Set X) = ⊥ := by rw [isOpen_empty.nhdsSet_eq, principal_empty]

theorem mem_nhdsSet_empty : s ∈ 𝓝ˢ (∅ : Set X) := by simp

@[simp]
theorem nhdsSet_univ : 𝓝ˢ (univ : Set X) = ⊤ := by rw [isOpen_univ.nhdsSet_eq, principal_univ]

@[gcongr, mono]
theorem nhdsSet_mono (h : s ⊆ t) : 𝓝ˢ s ≤ 𝓝ˢ t :=
  sSup_le_sSup <| image_mono h

theorem monotone_nhdsSet : Monotone (𝓝ˢ : Set X → Filter X) := fun _ _ => nhdsSet_mono

theorem nhds_le_nhdsSet (h : x ∈ s) : 𝓝 x ≤ 𝓝ˢ s :=
  le_sSup <| mem_image_of_mem _ h

@[simp]
theorem nhdsSet_union (s t : Set X) : 𝓝ˢ (s ∪ t) = 𝓝ˢ s ⊔ 𝓝ˢ t := by
  simp only [nhdsSet, image_union, sSup_union]

theorem union_mem_nhdsSet (h₁ : s₁ ∈ 𝓝ˢ t₁) (h₂ : s₂ ∈ 𝓝ˢ t₂) : s₁ ∪ s₂ ∈ 𝓝ˢ (t₁ ∪ t₂) := by
  rw [nhdsSet_union]
  exact union_mem_sup h₁ h₂

@[simp]
theorem nhdsSet_insert (x : X) (s : Set X) : 𝓝ˢ (insert x s) = 𝓝 x ⊔ 𝓝ˢ s := by
  rw [insert_eq, nhdsSet_union, nhdsSet_singleton]

/- This inequality cannot be improved to an equality. For instance,
if `X` has two elements and the coarse topology and `s` and `t` are distinct singletons then
`𝓝ˢ (s ∩ t) = ⊥` while `𝓝ˢ s ⊓ 𝓝ˢ t = ⊤` and those are different. -/
theorem nhdsSet_inter_le (s t : Set X) : 𝓝ˢ (s ∩ t) ≤ 𝓝ˢ s ⊓ 𝓝ˢ t :=
  (monotone_nhdsSet (X := X)).map_inf_le s t

theorem nhdsSet_iInter_le {ι : Sort*} (s : ι → Set X) : 𝓝ˢ (⋂ i, s i) ≤ ⨅ i, 𝓝ˢ (s i) :=
  (monotone_nhdsSet (X := X)).map_iInf_le

theorem nhdsSet_sInter_le (s : Set (Set X)) : 𝓝ˢ (⋂₀ s) ≤ ⨅ x ∈ s, 𝓝ˢ x :=
  (monotone_nhdsSet (X := X)).map_sInf_le

variable (s) in
theorem IsClosed.nhdsSet_le_sup (h : IsClosed t) : 𝓝ˢ s ≤ 𝓝ˢ (s ∩ t) ⊔ 𝓟 (tᶜ) :=
  calc
    𝓝ˢ s = 𝓝ˢ (s ∩ t ∪ s ∩ tᶜ) := by rw [Set.inter_union_compl s t]
    _ = 𝓝ˢ (s ∩ t) ⊔ 𝓝ˢ (s ∩ tᶜ) := by rw [nhdsSet_union]
    _ ≤ 𝓝ˢ (s ∩ t) ⊔ 𝓝ˢ (tᶜ) := sup_le_sup_left (monotone_nhdsSet inter_subset_right) _
    _ = 𝓝ˢ (s ∩ t) ⊔ 𝓟 (tᶜ) := by rw [h.isOpen_compl.nhdsSet_eq]

variable (s) in
theorem IsClosed.nhdsSet_le_sup' (h : IsClosed t) :
    𝓝ˢ s ≤ 𝓝ˢ (t ∩ s) ⊔ 𝓟 (tᶜ) := by rw [Set.inter_comm]; exact h.nhdsSet_le_sup s

theorem Filter.Eventually.eventually_nhdsSet {p : X → Prop} (h : ∀ᶠ y in 𝓝ˢ s, p y) :
    ∀ᶠ y in 𝓝ˢ s, ∀ᶠ x in 𝓝 y, p x :=
  eventually_nhdsSet_iff_forall.mpr fun x x_in ↦
    (eventually_nhdsSet_iff_forall.mp h x x_in).eventually_nhds

theorem Filter.Eventually.union_nhdsSet {p : X → Prop} :
    (∀ᶠ x in 𝓝ˢ (s ∪ t), p x) ↔ (∀ᶠ x in 𝓝ˢ s, p x) ∧ ∀ᶠ x in 𝓝ˢ t, p x := by
  rw [nhdsSet_union, eventually_sup]

theorem Filter.Eventually.union {p : X → Prop} (hs : ∀ᶠ x in 𝓝ˢ s, p x) (ht : ∀ᶠ x in 𝓝ˢ t, p x) :
    ∀ᶠ x in 𝓝ˢ (s ∪ t), p x :=
  Filter.Eventually.union_nhdsSet.mpr ⟨hs, ht⟩

theorem nhdsSet_iUnion {ι : Sort*} (s : ι → Set X) : 𝓝ˢ (⋃ i, s i) = ⨆ i, 𝓝ˢ (s i) := by
  simp only [nhdsSet, image_iUnion, sSup_iUnion (β := Filter X)]

theorem eventually_nhdsSet_iUnion₂ {ι : Sort*} {p : ι → Prop} {s : ι → Set X} {P : X → Prop} :
    (∀ᶠ x in 𝓝ˢ (⋃ (i) (_ : p i), s i), P x) ↔ ∀ i, p i → ∀ᶠ x in 𝓝ˢ (s i), P x := by
  simp only [nhdsSet_iUnion, eventually_iSup]

theorem eventually_nhdsSet_iUnion {ι : Sort*} {s : ι → Set X} {P : X → Prop} :
    (∀ᶠ x in 𝓝ˢ (⋃ i, s i), P x) ↔ ∀ i, ∀ᶠ x in 𝓝ˢ (s i), P x := by
  simp only [nhdsSet_iUnion, eventually_iSup]
