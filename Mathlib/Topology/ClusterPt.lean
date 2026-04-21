/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
module

public import Mathlib.Topology.Neighborhoods

/-!
# Lemmas on cluster and accumulation points

In this file we prove various lemmas on [cluster points](https://en.wikipedia.org/wiki/Limit_point)
(also known as limit points and accumulation points) of a filter and of a sequence.

A filter `F` on `X` has `x` as a cluster point if `ClusterPt x F : 𝓝 x ⊓ F ≠ ⊥`. A map `f : α → X`
clusters at `x` along `F : Filter α` if `MapClusterPt x F f : ClusterPt x (map f F)`.
In particular the notion of cluster point of a sequence `u` is `MapClusterPt x atTop u`.
-/
set_option backward.defeqAttrib.useBackward true

public section

open Set Filter Topology

universe u v w

variable {X : Type u} [TopologicalSpace X] {Y : Type v} {ι : Sort w} {α β : Type*}
  {x : X} {s s₁ s₂ t : Set X}

@[simp]
protected lemma ClusterPt.top : ClusterPt x ⊤ := by simp [ClusterPt]

theorem clusterPt_sup {F G : Filter X} : ClusterPt x (F ⊔ G) ↔ ClusterPt x F ∨ ClusterPt x G := by
  simp only [ClusterPt, inf_sup_left, sup_neBot]

theorem ClusterPt.neBot {F : Filter X} (h : ClusterPt x F) : NeBot (𝓝 x ⊓ F) :=
  h

theorem Filter.HasBasis.clusterPt_iff {ιX ιF} {pX : ιX → Prop} {sX : ιX → Set X} {pF : ιF → Prop}
    {sF : ιF → Set X} {F : Filter X} (hX : (𝓝 x).HasBasis pX sX) (hF : F.HasBasis pF sF) :
    ClusterPt x F ↔ ∀ ⦃i⦄, pX i → ∀ ⦃j⦄, pF j → (sX i ∩ sF j).Nonempty :=
  hX.inf_basis_neBot_iff hF

theorem Filter.HasBasis.clusterPt_iff_frequently {ι} {p : ι → Prop} {s : ι → Set X} {F : Filter X}
    (hx : (𝓝 x).HasBasis p s) : ClusterPt x F ↔ ∀ i, p i → ∃ᶠ x in F, x ∈ s i := by
  simp only [hx.clusterPt_iff F.basis_sets, Filter.frequently_iff, inter_comm (s _),
    Set.Nonempty, id, mem_inter_iff]

theorem clusterPt_iff_frequently {F : Filter X} : ClusterPt x F ↔ ∀ s ∈ 𝓝 x, ∃ᶠ y in F, y ∈ s :=
  (𝓝 x).basis_sets.clusterPt_iff_frequently

theorem ClusterPt.frequently {F : Filter X} {p : X → Prop} (hx : ClusterPt x F)
    (hp : ∀ᶠ y in 𝓝 x, p y) : ∃ᶠ y in F, p y :=
  clusterPt_iff_frequently.mp hx {y | p y} hp

theorem Filter.HasBasis.clusterPt_iff_frequently' {ι} {p : ι → Prop} {s : ι → Set X} {F : Filter X}
    (hx : F.HasBasis p s) : ClusterPt x F ↔ ∀ i, p i → ∃ᶠ x in 𝓝 x, x ∈ s i := by
  simp only [(𝓝 x).basis_sets.clusterPt_iff hx, Filter.frequently_iff]
  exact ⟨fun h a b c d ↦ h d b, fun h a b c d ↦ h c d b⟩

theorem clusterPt_iff_frequently' {F : Filter X} : ClusterPt x F ↔ ∀ s ∈ F, ∃ᶠ y in 𝓝 x, y ∈ s :=
  F.basis_sets.clusterPt_iff_frequently'

theorem ClusterPt.frequently' {F : Filter X} {p : X → Prop} (hx : ClusterPt x F)
    (hp : ∀ᶠ y in F, p y) : ∃ᶠ y in 𝓝 x, p y :=
  clusterPt_iff_frequently'.mp hx {y | p y} hp

theorem clusterPt_iff_nonempty {F : Filter X} :
    ClusterPt x F ↔ ∀ ⦃U : Set X⦄, U ∈ 𝓝 x → ∀ ⦃V⦄, V ∈ F → (U ∩ V).Nonempty :=
  inf_neBot_iff

theorem clusterPt_iff_not_disjoint {F : Filter X} :
    ClusterPt x F ↔ ¬Disjoint (𝓝 x) F := by
  rw [disjoint_iff, ClusterPt, neBot_iff]

protected theorem Filter.HasBasis.clusterPt_iff_forall_mem_closure {ι} {p : ι → Prop}
    {s : ι → Set X} {F : Filter X} (hF : F.HasBasis p s) :
    ClusterPt x F ↔ ∀ i, p i → x ∈ closure (s i) := by
  simp only [(nhds_basis_opens _).clusterPt_iff hF, mem_closure_iff]
  tauto

theorem clusterPt_iff_forall_mem_closure {F : Filter X} :
    ClusterPt x F ↔ ∀ s ∈ F, x ∈ closure s :=
  F.basis_sets.clusterPt_iff_forall_mem_closure

alias ⟨ClusterPt.mem_closure_of_mem, _⟩ := clusterPt_iff_forall_mem_closure

/-- `x` is a cluster point of a set `s` if every neighbourhood of `x` meets `s` on a nonempty
set. See also `mem_closure_iff_clusterPt`. -/
theorem clusterPt_principal_iff :
    ClusterPt x (𝓟 s) ↔ ∀ U ∈ 𝓝 x, (U ∩ s).Nonempty :=
  inf_principal_neBot_iff

theorem clusterPt_principal_iff_frequently :
    ClusterPt x (𝓟 s) ↔ ∃ᶠ y in 𝓝 x, y ∈ s := by
  simp only [clusterPt_principal_iff, frequently_iff, Set.Nonempty, mem_inter_iff]

theorem ClusterPt.of_le_nhds {f : Filter X} (H : f ≤ 𝓝 x) [NeBot f] : ClusterPt x f := by
  rwa [ClusterPt, inf_eq_right.mpr H]

theorem ClusterPt.of_le_nhds' {f : Filter X} (H : f ≤ 𝓝 x) (_hf : NeBot f) :
    ClusterPt x f :=
  ClusterPt.of_le_nhds H

theorem ClusterPt.of_nhds_le {f : Filter X} (H : 𝓝 x ≤ f) : ClusterPt x f := by
  simp only [ClusterPt, inf_eq_left.mpr H, nhds_neBot]

theorem ClusterPt.mono {f g : Filter X} (H : ClusterPt x f) (h : f ≤ g) : ClusterPt x g :=
  NeBot.mono H <| inf_le_inf_left _ h

theorem ClusterPt.of_inf_left {f g : Filter X} (H : ClusterPt x <| f ⊓ g) : ClusterPt x f :=
  H.mono inf_le_left

theorem ClusterPt.of_inf_right {f g : Filter X} (H : ClusterPt x <| f ⊓ g) :
    ClusterPt x g :=
  H.mono inf_le_right

section MapClusterPt

variable {F : Filter α} {u : α → X} {x : X}

theorem mapClusterPt_def : MapClusterPt x F u ↔ ClusterPt x (map u F) := Iff.rfl
alias ⟨MapClusterPt.clusterPt, _⟩ := mapClusterPt_def

theorem Filter.EventuallyEq.mapClusterPt_iff {v : α → X} (h : u =ᶠ[F] v) :
    MapClusterPt x F u ↔ MapClusterPt x F v := by
  simp only [mapClusterPt_def, map_congr h]

alias ⟨MapClusterPt.congrFun, _⟩ := Filter.EventuallyEq.mapClusterPt_iff

theorem MapClusterPt.mono {G : Filter α} (h : MapClusterPt x F u) (hle : F ≤ G) :
    MapClusterPt x G u :=
  h.clusterPt.mono (map_mono hle)

theorem MapClusterPt.tendsto_comp' [TopologicalSpace Y] {f : X → Y} {y : Y}
    (hf : Tendsto f (𝓝 x ⊓ map u F) (𝓝 y)) (hu : MapClusterPt x F u) : MapClusterPt y F (f ∘ u) :=
  (tendsto_inf.2 ⟨hf, tendsto_map.mono_left inf_le_right⟩).neBot (hx := hu)

theorem MapClusterPt.tendsto_comp [TopologicalSpace Y] {f : X → Y} {y : Y}
    (hf : Tendsto f (𝓝 x) (𝓝 y)) (hu : MapClusterPt x F u) : MapClusterPt y F (f ∘ u) :=
  hu.tendsto_comp' (hf.mono_left inf_le_left)

theorem mapClusterPt_id_iff [TopologicalSpace α] {a : α} : MapClusterPt a F id ↔ ClusterPt a F := by
  rw [MapClusterPt, map_id]

alias ⟨_, ClusterPt.mapClusterPt_id⟩ := mapClusterPt_id_iff

theorem MapClusterPt.continuousAt_comp [TopologicalSpace Y] {f : X → Y} (hf : ContinuousAt f x)
    (hu : MapClusterPt x F u) : MapClusterPt (f x) F (f ∘ u) :=
  hu.tendsto_comp hf

theorem ContinuousAt.mapClusterPt [TopologicalSpace α] {a : α} (hf : ContinuousAt u a)
    (hu : ClusterPt a F) : MapClusterPt (u a) F u :=
  hu.mapClusterPt_id.continuousAt_comp hf

theorem Filter.HasBasis.mapClusterPt_iff_frequently {ι : Sort*} {p : ι → Prop} {s : ι → Set X}
    (hx : (𝓝 x).HasBasis p s) : MapClusterPt x F u ↔ ∀ i, p i → ∃ᶠ a in F, u a ∈ s i := by
  simp_rw [MapClusterPt, hx.clusterPt_iff_frequently, frequently_map]

theorem mapClusterPt_iff_frequently : MapClusterPt x F u ↔ ∀ s ∈ 𝓝 x, ∃ᶠ a in F, u a ∈ s :=
  (𝓝 x).basis_sets.mapClusterPt_iff_frequently

theorem MapClusterPt.frequently (h : MapClusterPt x F u) {p : X → Prop} (hp : ∀ᶠ y in 𝓝 x, p y) :
    ∃ᶠ a in F, p (u a) :=
  h.clusterPt.frequently hp

theorem mapClusterPt_comp {φ : α → β} {u : β → X} :
    MapClusterPt x F (u ∘ φ) ↔ MapClusterPt x (map φ F) u := Iff.rfl

theorem Filter.Tendsto.mapClusterPt [NeBot F] (h : Tendsto u F (𝓝 x)) : MapClusterPt x F u :=
  .of_le_nhds h

theorem MapClusterPt.of_comp {φ : β → α} {p : Filter β} (h : Tendsto φ p F)
    (H : MapClusterPt x p (u ∘ φ)) : MapClusterPt x F u :=
  H.clusterPt.mono <| map_mono h

theorem IsClosed.mem_of_mapClusterPt {l : X} {s : Set X} {f : α → X} {b : Filter α}
    (hs : IsClosed s) (hf : MapClusterPt l b f) (h : ∀ᶠ (x : α) in b, f x ∈ s) : l ∈ s :=
  (hf.frequently' h).mem_of_closed hs

/-- A point `a` is a cluster point of the sequence `x` if and only if `a` belongs to the closure
of every tail `x '' {n | i ≤ n}`. -/
theorem mapClusterPt_atTop_iff_forall_mem_closure {ι : Type*} [Preorder ι] [IsDirectedOrder ι]
    [Nonempty ι] {x : ι → X} {a : X} :
    MapClusterPt a atTop x ↔ ∀ i, a ∈ closure (x '' Ici i) := by
  simp [MapClusterPt, (atTop_basis.map x).clusterPt_iff_forall_mem_closure]

end MapClusterPt

theorem accPt_sup {x : X} {F G : Filter X} :
    AccPt x (F ⊔ G) ↔ AccPt x F ∨ AccPt x G := by
  simp only [AccPt, inf_sup_left, sup_neBot]

theorem accPt_iff_clusterPt {x : X} {F : Filter X} : AccPt x F ↔ ClusterPt x (𝓟 {x}ᶜ ⊓ F) := by
  rw [AccPt, nhdsWithin, ClusterPt, inf_assoc]

/-- `x` is an accumulation point of a set `C` iff it is a cluster point of `C ∖ {x}`. -/
theorem accPt_principal_iff_clusterPt {x : X} {C : Set X} :
    AccPt x (𝓟 C) ↔ ClusterPt x (𝓟 (C \ { x })) := by
  rw [accPt_iff_clusterPt, inf_principal, inter_comm, diff_eq]

/-- `x` is an accumulation point of a set `C` iff every neighborhood
of `x` contains a point of `C` other than `x`. -/
theorem accPt_iff_nhds {x : X} {C : Set X} : AccPt x (𝓟 C) ↔ ∀ U ∈ 𝓝 x, ∃ y ∈ U ∩ C, y ≠ x := by
  simp [accPt_principal_iff_clusterPt, clusterPt_principal_iff, Set.Nonempty,
    and_assoc]

/-- `x` is an accumulation point of a set `C` iff
there are points near `x` in `C` and different from `x`. -/
theorem accPt_iff_frequently {x : X} {C : Set X} : AccPt x (𝓟 C) ↔ ∃ᶠ y in 𝓝 x, y ≠ x ∧ y ∈ C := by
  simp [accPt_principal_iff_clusterPt, clusterPt_principal_iff_frequently, and_comm]

/--
Variant of `accPt_iff_frequently`: A point `x` is an accumulation point of a set `C` iff points in
punctured neighborhoods are frequently contained in `C`.
-/
theorem accPt_iff_frequently_nhdsNE {X : Type*} [TopologicalSpace X] {x : X} {C : Set X} :
    AccPt x (𝓟 C) ↔ ∃ᶠ (y : X) in 𝓝[≠] x, y ∈ C := by
  have : (∃ᶠ z in 𝓝[≠] x, z ∈ C) ↔ ∃ᶠ z in 𝓝 x, z ∈ C ∧ z ∈ ({x} : Set X)ᶜ :=
    frequently_inf_principal.trans <| by simp only [and_comm]
  rw [accPt_iff_frequently, this]
  congr! 2
  tauto

theorem accPt_principal_iff_nhdsWithin : AccPt x (𝓟 s) ↔ (𝓝[s \ {x}] x).NeBot := by
  rw [accPt_principal_iff_clusterPt, ClusterPt, nhdsWithin]

/-- If `x` is an accumulation point of `F` and `F ≤ G`, then
`x` is an accumulation point of `G`. -/
theorem AccPt.mono {F G : Filter X} (h : AccPt x F) (hFG : F ≤ G) : AccPt x G :=
  NeBot.mono h (inf_le_inf_left _ hFG)

theorem AccPt.clusterPt {x : X} {F : Filter X} (h : AccPt x F) : ClusterPt x F :=
  (accPt_iff_clusterPt.mp h).mono inf_le_right

theorem clusterPt_principal {x : X} {C : Set X} :
    ClusterPt x (𝓟 C) ↔ x ∈ C ∨ AccPt x (𝓟 C) := by
  constructor
  · intro h
    by_contra! hc
    rw [accPt_principal_iff_clusterPt] at hc
    simp_all only [not_false_eq_true, diff_singleton_eq_self, not_true_eq_false, hc.1]
  · rintro (h | h)
    · exact clusterPt_principal_iff.mpr fun _ mem ↦ ⟨x, ⟨mem_of_mem_nhds mem, h⟩⟩
    · exact h.clusterPt

/-- The set of cluster points of a filter is closed. In particular, the set of limit points
of a sequence is closed. -/
theorem isClosed_setOf_clusterPt {f : Filter X} : IsClosed { x | ClusterPt x f } := by
  simp only [clusterPt_iff_forall_mem_closure, setOf_forall]
  exact isClosed_biInter fun _ _ ↦ isClosed_closure

theorem mem_closure_iff_clusterPt : x ∈ closure s ↔ ClusterPt x (𝓟 s) :=
  mem_closure_iff_frequently.trans clusterPt_principal_iff_frequently.symm

alias ⟨_, ClusterPt.mem_closure⟩ := mem_closure_iff_clusterPt

theorem mem_closure_iff_nhds_ne_bot : x ∈ closure s ↔ 𝓝 x ⊓ 𝓟 s ≠ ⊥ :=
  mem_closure_iff_clusterPt.trans neBot_iff

theorem mem_closure_iff_nhdsWithin_neBot : x ∈ closure s ↔ NeBot (𝓝[s] x) :=
  mem_closure_iff_clusterPt

lemma notMem_closure_iff_nhdsWithin_eq_bot : x ∉ closure s ↔ 𝓝[s] x = ⊥ := by
  rw [mem_closure_iff_nhdsWithin_neBot, not_neBot]

theorem mem_interior_iff_not_clusterPt_compl : x ∈ interior s ↔ ¬ClusterPt x (𝓟 sᶜ) := by
  rw [← mem_closure_iff_clusterPt, closure_compl, mem_compl_iff, not_not]

/-- If `x` is not an isolated point of a topological space, then `{x}ᶜ` is dense in the whole
space. -/
theorem dense_compl_singleton (x : X) [NeBot (𝓝[≠] x)] : Dense ({x}ᶜ : Set X) := by
  intro y
  rcases eq_or_ne y x with (rfl | hne)
  · rwa [mem_closure_iff_nhdsWithin_neBot]
  · exact subset_closure hne

/-- If `x` is not an isolated point of a topological space, then the closure of `{x}ᶜ` is the whole
space. -/
theorem closure_compl_singleton (x : X) [NeBot (𝓝[≠] x)] : closure {x}ᶜ = (univ : Set X) :=
  (dense_compl_singleton x).closure_eq

/-- If `x` is not an isolated point of a topological space, then the interior of `{x}` is empty. -/
@[simp]
theorem interior_singleton (x : X) [NeBot (𝓝[≠] x)] : interior {x} = (∅ : Set X) :=
  interior_eq_empty_iff_dense_compl.2 (dense_compl_singleton x)

theorem not_isOpen_singleton (x : X) [NeBot (𝓝[≠] x)] : ¬IsOpen ({x} : Set X) :=
  dense_compl_singleton_iff_not_open.1 (dense_compl_singleton x)

theorem closure_eq_cluster_pts : closure s = { a | ClusterPt a (𝓟 s) } :=
  Set.ext fun _ => mem_closure_iff_clusterPt

theorem mem_closure_iff_nhds : x ∈ closure s ↔ ∀ t ∈ 𝓝 x, (t ∩ s).Nonempty :=
  mem_closure_iff_clusterPt.trans clusterPt_principal_iff

theorem mem_closure_iff_nhds' : x ∈ closure s ↔ ∀ t ∈ 𝓝 x, ∃ y : s, ↑y ∈ t := by
  simp only [mem_closure_iff_nhds, Set.inter_nonempty_iff_exists_right, SetCoe.exists, exists_prop]

theorem mem_closure_iff_comap_neBot :
    x ∈ closure s ↔ NeBot (comap ((↑) : s → X) (𝓝 x)) := by
  simp_rw [mem_closure_iff_nhds, comap_neBot_iff, Set.inter_nonempty_iff_exists_right,
    SetCoe.exists, exists_prop]

theorem mem_closure_iff_nhds_basis' {p : ι → Prop} {s : ι → Set X} (h : (𝓝 x).HasBasis p s) :
    x ∈ closure t ↔ ∀ i, p i → (s i ∩ t).Nonempty :=
  mem_closure_iff_clusterPt.trans <|
    (h.clusterPt_iff (hasBasis_principal _)).trans <| by simp only [forall_const]

theorem mem_closure_iff_nhds_basis {p : ι → Prop} {s : ι → Set X} (h : (𝓝 x).HasBasis p s) :
    x ∈ closure t ↔ ∀ i, p i → ∃ y ∈ t, y ∈ s i :=
  (mem_closure_iff_nhds_basis' h).trans <| by
    simp only [Set.Nonempty, mem_inter_iff, and_comm]

theorem clusterPt_iff_lift'_closure {F : Filter X} :
    ClusterPt x F ↔ pure x ≤ (F.lift' closure) := by
  simp_rw [clusterPt_iff_forall_mem_closure,
    (hasBasis_pure _).le_basis_iff F.basis_sets.lift'_closure, id, singleton_subset_iff, true_and,
    exists_const]

theorem clusterPt_iff_lift'_closure' {F : Filter X} :
    ClusterPt x F ↔ (F.lift' closure ⊓ pure x).NeBot := by
  rw [clusterPt_iff_lift'_closure, inf_comm]
  constructor
  · intro h
    simp [h, pure_neBot]
  · intro h U hU
    simp_rw [← forall_mem_nonempty_iff_neBot, mem_inf_iff] at h
    simpa using h ({x} ∩ U) ⟨{x}, by simp, U, hU, rfl⟩

@[simp]
theorem clusterPt_lift'_closure_iff {F : Filter X} :
    ClusterPt x (F.lift' closure) ↔ ClusterPt x F := by
  simp [clusterPt_iff_lift'_closure, lift'_lift'_assoc (monotone_closure X) (monotone_closure X)]

theorem isClosed_iff_clusterPt : IsClosed s ↔ ∀ a, ClusterPt a (𝓟 s) → a ∈ s :=
  calc
    IsClosed s ↔ closure s ⊆ s := closure_subset_iff_isClosed.symm
    _ ↔ ∀ a, ClusterPt a (𝓟 s) → a ∈ s := by simp only [subset_def, mem_closure_iff_clusterPt]

theorem isClosed_iff_accPt : IsClosed s ↔ ∀ a, AccPt a (𝓟 s) → a ∈ s := by
  simp [isClosed_iff_clusterPt, clusterPt_principal, or_imp]

theorem isClosed_iff_nhds :
    IsClosed s ↔ ∀ x, (∀ U ∈ 𝓝 x, (U ∩ s).Nonempty) → x ∈ s := by
  simp_rw [isClosed_iff_clusterPt, ClusterPt, inf_principal_neBot_iff]

lemma isClosed_iff_forall_filter :
    IsClosed s ↔ ∀ x, ∀ F : Filter X, F.NeBot → F ≤ 𝓟 s → F ≤ 𝓝 x → x ∈ s := by
  simp_rw [isClosed_iff_clusterPt]
  exact ⟨fun hs x F F_ne FS Fx ↦ hs _ <| NeBot.mono F_ne (le_inf Fx FS),
         fun hs x hx ↦ hs x (𝓝 x ⊓ 𝓟 s) hx inf_le_right inf_le_left⟩

theorem mem_closure_of_mem_closure_union (h : x ∈ closure (s₁ ∪ s₂))
    (h₁ : s₁ᶜ ∈ 𝓝 x) : x ∈ closure s₂ := by
  rw [mem_closure_iff_nhds_ne_bot] at *
  rwa [← sup_principal, inf_sup_left, inf_principal_eq_bot.mpr h₁, bot_sup_eq] at h
