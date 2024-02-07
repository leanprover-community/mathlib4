/-
Copyright (c) 2023 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Separation
/-!
# Separated maps and locally injective maps out of a topological space.

This module introduces a pair of dual notions `IsSeparatedMap` and `IsLocallyInjective`.

A function from a topological space `X` to a type `Y` is a separated map if any two distinct
points in `X` with the same image in `Y` can be separated by open neighborhoods.
A constant function is a separated map if and only if `X` is a `T2Space`.

A function from a topological space `X` is locally injective if every point of `X`
has a neighborhood on which `f` is injective.
A constant function is locally injective if and only if `X` is discrete.

Given `f : X → Y` we can form the pullback $X \times_Y X$; the diagonal map
$\Delta: X \to X \times_Y X$ is always an embedding. It is a closed embedding
iff `f` is a separated map, iff the equal locus of any two continuous maps
coequalized by `f` is closed. It is an open embedding iff `f` is locally injective,
iff any such equal locus is open. Therefore, if `f` is a locally injective separated map,
the equal locus of two continuous maps coequalized by `f` is clopen, so if the two maps
agree on a point, then they agree on the whole connected component.

The analogue of separated maps and locally injective maps in algebraic geometry are
separated morphisms and unramified morphisms, respectively.

## Reference

https://stacks.math.columbia.edu/tag/0CY0
-/

open scoped Topology

variable {X Y A} [TopologicalSpace X] [TopologicalSpace A]

theorem embedding_toPullbackDiag (f : X → Y) : Embedding (toPullbackDiag f) :=
  Embedding.mk' _ (injective_toPullbackDiag f) fun x ↦ by
    rw [toPullbackDiag, nhds_induced, Filter.comap_comap, nhds_prod_eq, Filter.comap_prod]
    erw [Filter.comap_id, inf_idem]

lemma Continuous.mapPullback {X₁ X₂ Y₁ Y₂ Z₁ Z₂}
    [TopologicalSpace X₁] [TopologicalSpace X₂] [TopologicalSpace Z₁] [TopologicalSpace Z₂]
    {f₁ : X₁ → Y₁} {g₁ : Z₁ → Y₁} {f₂ : X₂ → Y₂} {g₂ : Z₂ → Y₂}
    {mapX : X₁ → X₂} (contX : Continuous mapX) {mapY : Y₁ → Y₂}
    {mapZ : Z₁ → Z₂} (contZ : Continuous mapZ)
    {commX : f₂ ∘ mapX = mapY ∘ f₁} {commZ : g₂ ∘ mapZ = mapY ∘ g₁} :
    Continuous (Function.mapPullback mapX mapY mapZ commX commZ) := by
  refine continuous_induced_rng.mpr (continuous_prod_mk.mpr ⟨?_, ?_⟩) <;>
  apply_rules [continuous_fst, continuous_snd, continuous_subtype_val, Continuous.comp]

/-- A function from a topological space `X` to a type `Y` is a separated map if any two distinct
  points in `X` with the same image in `Y` can be separated by open neighborhoods. -/
def IsSeparatedMap (f : X → Y) : Prop := ∀ x₁ x₂, f x₁ = f x₂ →
    x₁ ≠ x₂ → ∃ s₁ s₂, IsOpen s₁ ∧ IsOpen s₂ ∧ x₁ ∈ s₁ ∧ x₂ ∈ s₂ ∧ Disjoint s₁ s₂

lemma t2space_iff_isSeparatedMap (y : Y) : T2Space X ↔ IsSeparatedMap fun _ : X ↦ y :=
  ⟨fun ⟨t2⟩ _ _ _ hne ↦ t2 hne, fun sep ↦ ⟨fun x₁ x₂ hne ↦ sep x₁ x₂ rfl hne⟩⟩

lemma T2Space.isSeparatedMap [T2Space X] (f : X → Y) : IsSeparatedMap f := fun _ _ _ ↦ t2_separation

lemma Function.Injective.isSeparatedMap {f : X → Y} (inj : f.Injective) : IsSeparatedMap f :=
  fun _ _ he hne ↦ (hne (inj he)).elim

lemma isSeparatedMap_iff_disjoint_nhds {f : X → Y} : IsSeparatedMap f ↔
    ∀ x₁ x₂, f x₁ = f x₂ → x₁ ≠ x₂ → Disjoint (𝓝 x₁) (𝓝 x₂) :=
  forall₃_congr fun x x' _ ↦ by simp only [(nhds_basis_opens x).disjoint_iff (nhds_basis_opens x'),
    exists_prop, ← exists_and_left, and_assoc, and_comm, and_left_comm]

lemma isSeparatedMap_iff_nhds {f : X → Y} : IsSeparatedMap f ↔
    ∀ x₁ x₂, f x₁ = f x₂ → x₁ ≠ x₂ → ∃ s₁ ∈ 𝓝 x₁, ∃ s₂ ∈ 𝓝 x₂, Disjoint s₁ s₂ := by
  simp_rw [isSeparatedMap_iff_disjoint_nhds, Filter.disjoint_iff]

open Set Filter in
theorem isSeparatedMap_iff_isClosed_diagonal {f : X → Y} :
    IsSeparatedMap f ↔ IsClosed f.pullbackDiagonal := by
  simp_rw [isSeparatedMap_iff_nhds, ← isOpen_compl_iff, isOpen_iff_mem_nhds,
    Subtype.forall, Prod.forall, nhds_induced, nhds_prod_eq]
  refine forall₄_congr fun x₁ x₂ _ _ ↦ ⟨fun h ↦ ?_, fun ⟨t, ht, t_sub⟩ ↦ ?_⟩
  · simp_rw [← Filter.disjoint_iff, ← compl_diagonal_mem_prod] at h
    exact ⟨_, h, subset_rfl⟩
  · obtain ⟨s₁, h₁, s₂, h₂, s_sub⟩ := mem_prod_iff.mp ht
    exact ⟨s₁, h₁, s₂, h₂, disjoint_left.2 fun x h₁ h₂ ↦ @t_sub ⟨(x, x), rfl⟩ (s_sub ⟨h₁, h₂⟩) rfl⟩

theorem isSeparatedMap_iff_closedEmbedding {f : X → Y} :
    IsSeparatedMap f ↔ ClosedEmbedding (toPullbackDiag f) := by
  rw [isSeparatedMap_iff_isClosed_diagonal, ← range_toPullbackDiag]
  exact ⟨fun h ↦ ⟨embedding_toPullbackDiag f, h⟩, fun h ↦ h.2⟩

theorem isSeparatedMap_iff_isClosedMap {f : X → Y} :
    IsSeparatedMap f ↔ IsClosedMap (toPullbackDiag f) :=
  isSeparatedMap_iff_closedEmbedding.trans
    ⟨ClosedEmbedding.isClosedMap, closedEmbedding_of_continuous_injective_closed
      (embedding_toPullbackDiag f).continuous (injective_toPullbackDiag f)⟩

open Function.Pullback in
theorem IsSeparatedMap.pullback {f : X → Y} (sep : IsSeparatedMap f) (g : A → Y) :
    IsSeparatedMap (@snd X Y A f g) := by
  rw [isSeparatedMap_iff_isClosed_diagonal] at sep ⊢
  rw [← preimage_map_fst_pullbackDiagonal]
  refine sep.preimage (Continuous.mapPullback ?_ ?_) <;>
  apply_rules [continuous_fst, continuous_subtype_val, Continuous.comp]

theorem IsSeparatedMap.comp_left {f : X → Y} (sep : IsSeparatedMap f) {g : Y → A}
    (inj : g.Injective) : IsSeparatedMap (g ∘ f) := fun x₁ x₂ he ↦ sep x₁ x₂ (inj he)

theorem IsSeparatedMap.comp_right {f : X → Y} (sep : IsSeparatedMap f) {g : A → X}
    (cont : Continuous g) (inj : g.Injective) : IsSeparatedMap (f ∘ g) := by
  rw [isSeparatedMap_iff_isClosed_diagonal] at sep ⊢
  rw [← inj.preimage_pullbackDiagonal]
  exact sep.preimage (cont.mapPullback cont)

/-- A function from a topological space `X` is locally injective if every point of `X`
  has a neighborhood on which `f` is injective. -/
def IsLocallyInjective (f : X → Y) : Prop := ∀ x : X, ∃ U, IsOpen U ∧ x ∈ U ∧ U.InjOn f

lemma Function.Injective.IsLocallyInjective {f : X → Y} (inj : f.Injective) :
    IsLocallyInjective f := fun _ ↦ ⟨_, isOpen_univ, trivial, fun _ _ _ _ ↦ @inj _ _⟩

lemma isLocallyInjective_iff_nhds {f : X → Y} :
    IsLocallyInjective f ↔ ∀ x : X, ∃ U ∈ 𝓝 x, U.InjOn f := by
  constructor <;> intro h x
  · obtain ⟨U, ho, hm, hi⟩ := h x; exact ⟨U, ho.mem_nhds hm, hi⟩
  · obtain ⟨U, hn, hi⟩ := h x
    exact ⟨interior U, isOpen_interior, mem_interior_iff_mem_nhds.mpr hn, hi.mono interior_subset⟩

theorem isLocallyInjective_iff_isOpen_diagonal {f : X → Y} :
    IsLocallyInjective f ↔ IsOpen f.pullbackDiagonal := by
  simp_rw [isLocallyInjective_iff_nhds, isOpen_iff_mem_nhds,
    Subtype.forall, Prod.forall, nhds_induced, nhds_prod_eq, Filter.mem_comap]
  refine ⟨?_, fun h x ↦ ?_⟩
  · rintro h x x' hx (rfl : x = x')
    obtain ⟨U, hn, hi⟩ := h x
    exact ⟨_, Filter.prod_mem_prod hn hn, fun {p} hp ↦ hi hp.1 hp.2 p.2⟩
  · obtain ⟨t, ht, t_sub⟩ := h x x rfl rfl
    obtain ⟨t₁, h₁, t₂, h₂, prod_sub⟩ := Filter.mem_prod_iff.mp ht
    exact ⟨t₁ ∩ t₂, Filter.inter_mem h₁ h₂,
      fun x₁ h₁ x₂ h₂ he ↦ @t_sub ⟨(x₁, x₂), he⟩ (prod_sub ⟨h₁.1, h₂.2⟩)⟩

theorem IsLocallyInjective_iff_openEmbedding {f : X → Y} :
    IsLocallyInjective f ↔ OpenEmbedding (toPullbackDiag f) := by
  rw [isLocallyInjective_iff_isOpen_diagonal, ← range_toPullbackDiag]
  exact ⟨fun h ↦ ⟨embedding_toPullbackDiag f, h⟩, fun h ↦ h.2⟩

theorem isLocallyInjective_iff_isOpenMap {f : X → Y} :
    IsLocallyInjective f ↔ IsOpenMap (toPullbackDiag f) :=
  IsLocallyInjective_iff_openEmbedding.trans
    ⟨OpenEmbedding.isOpenMap, openEmbedding_of_continuous_injective_open
      (embedding_toPullbackDiag f).continuous (injective_toPullbackDiag f)⟩

theorem discreteTopology_iff_locallyInjective (y : Y) :
    DiscreteTopology X ↔ IsLocallyInjective fun _ : X ↦ y := by
  rw [discreteTopology_iff_singleton_mem_nhds, isLocallyInjective_iff_nhds]
  refine forall_congr' fun x ↦ ⟨fun h ↦ ⟨{x}, h, Set.injOn_singleton _ _⟩, fun ⟨U, hU, inj⟩ ↦ ?_⟩
  convert hU; ext x'; refine ⟨?_, fun h ↦ inj h (mem_of_mem_nhds hU) rfl⟩
  rintro rfl; exact mem_of_mem_nhds hU

theorem IsLocallyInjective.comp_left {f : X → Y} (hf : IsLocallyInjective f) {g : Y → A}
    (hg : g.Injective) : IsLocallyInjective (g ∘ f) :=
  fun x ↦ let ⟨U, hU, hx, inj⟩ := hf x; ⟨U, hU, hx, hg.comp_injOn inj⟩

theorem IsLocallyInjective.comp_right {f : X → Y} (hf : IsLocallyInjective f) {g : A → X}
    (cont : Continuous g) (hg : g.Injective) : IsLocallyInjective (f ∘ g) := by
  rw [isLocallyInjective_iff_isOpen_diagonal] at hf ⊢
  rw [← hg.preimage_pullbackDiagonal]
  apply hf.preimage (cont.mapPullback cont)

section eqLocus

variable {f : X → Y} (sep : IsSeparatedMap f) (inj : IsLocallyInjective f)
  {g₁ g₂ : A → X} (h₁ : Continuous g₁) (h₂ : Continuous g₂)

theorem IsSeparatedMap.isClosed_eqLocus (he : f ∘ g₁ = f ∘ g₂) : IsClosed {a | g₁ a = g₂ a} :=
  let g : A → f.Pullback f := fun a ↦ ⟨⟨g₁ a, g₂ a⟩, congr_fun he a⟩
  (isSeparatedMap_iff_isClosed_diagonal.mp sep).preimage (by continuity : Continuous g)

theorem IsLocallyInjective.isOpen_eqLocus (he : f ∘ g₁ = f ∘ g₂) : IsOpen {a | g₁ a = g₂ a} :=
  let g : A → f.Pullback f := fun a ↦ ⟨⟨g₁ a, g₂ a⟩, congr_fun he a⟩
  (isLocallyInjective_iff_isOpen_diagonal.mp inj).preimage (by continuity : Continuous g)

end eqLocus

variable {E A : Type*} [TopologicalSpace E] [TopologicalSpace A] {p : E → X}

namespace IsSeparatedMap

variable (sep : IsSeparatedMap p) (inj : IsLocallyInjective p) {s : Set A} (hs : IsPreconnected s)
  {g g₁ g₂ : A → E}

/-- If `p` is a locally injective separated map, and `A` is a connected space,
  then two lifts `g₁, g₂ : A → E` of a map `f : A → X` are equal if they agree at one point. -/
theorem eq_of_comp_eq [PreconnectedSpace A] (h₁ : Continuous g₁) (h₂ : Continuous g₂)
    (he : p ∘ g₁ = p ∘ g₂) (a : A) (ha : g₁ a = g₂ a) : g₁ = g₂ := funext fun a' ↦ by
  apply (IsClopen.eq_univ ⟨sep.isClosed_eqLocus h₁ h₂ he, inj.isOpen_eqLocus h₁ h₂ he⟩ ⟨a, ha⟩).symm
    ▸ Set.mem_univ a'

theorem eqOn_of_comp_eqOn (h₁ : ContinuousOn g₁ s) (h₂ : ContinuousOn g₂ s)
    (he : s.EqOn (p ∘ g₁) (p ∘ g₂)) {a : A} (has : a ∈ s) (ha : g₁ a = g₂ a) : s.EqOn g₁ g₂ := by
  rw [← Set.restrict_eq_restrict_iff] at he ⊢
  rw [continuousOn_iff_continuous_restrict] at h₁ h₂
  rw [isPreconnected_iff_preconnectedSpace] at hs
  exact sep.eq_of_comp_eq inj h₁ h₂ he ⟨a, has⟩ ha

theorem const_of_comp [PreconnectedSpace A] (cont : Continuous g)
    (he : ∀ a a', p (g a) = p (g a')) (a a') : g a = g a' :=
  congr_fun (sep.eq_of_comp_eq inj cont continuous_const (funext fun a ↦ he a a') a' rfl) a

theorem constOn_of_comp (cont : ContinuousOn g s)
    (he : ∀ a ∈ s, ∀ a' ∈ s, p (g a) = p (g a'))
    {a a'} (ha : a ∈ s) (ha' : a' ∈ s) : g a = g a' :=
  sep.eqOn_of_comp_eqOn inj hs cont continuous_const.continuousOn
    (fun a ha ↦ he a ha a' ha') ha' rfl ha

end IsSeparatedMap
