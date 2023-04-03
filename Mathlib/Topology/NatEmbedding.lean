/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Homeomorph

/-!
-/

open Function Filter Set Topology

theorem Sigma.fst_surjective {f : ι → Type _} [h : ∀ i, Nonempty (f i)] :
    Surjective (fst : (Σ i, f i) → ι) := fun i ↦
  let ⟨x⟩ := h i; ⟨⟨i, x⟩, rfl⟩

theorem Infinite.sigma_of_exists {f : ι → Type _} (h : ∃ i, Infinite (f i)) :
    Infinite (Σ i, f i) :=
  let ⟨i, _⟩ := h; .of_injective (Sigma.mk i) sigma_mk_injective

instance [Nonempty ι] {f : ι → Type _} [h : ∀ i, Infinite (f i)] : Infinite (Σ i, f i) :=
  let ⟨i⟩ := ‹Nonempty ι›; .sigma_of_exists ⟨i, h i⟩

instance [Infinite ι] {f : ι → Type _} [∀ i, Nonempty (f i)] : Infinite (Σ i, f i) :=
  .of_surjective Sigma.fst Sigma.fst_surjective

theorem Set.infinite_unionᵢ_of_left {α β : Type _} [Infinite α]
    {s : α → Set β} (hne : ∀ a, (s a).Nonempty) (hd : Pairwise (Disjoint on s)) :
    (⋃ a, s a).Infinite :=
  have := λ a ↦ (hne a).to_subtype
  infinite_coe_iff.mp <| .of_injective (sigmaToUnionᵢ _) (sigmaToUnionᵢ_injective _ hd)

theorem Set.infinite_unionᵢ_of_right {ι : Sort _} {β : Type _} {s : ι → Set β} {i : ι}
    (h : (s i).Infinite) : (⋃ a, s a).Infinite :=
  h.mono <| subset_unionᵢ _ _

variable (X : Type _) [TopologicalSpace X] [T2Space X] [Infinite X]

/-- In an infinite Hausdorff topological space, there exists a sequence of pairwise disjoint
infinite open sets. -/
theorem exists_seq_infinite_isOpen_pairwise_disjoint :
    ∃ U : ℕ → Set X, (∀ n, (U n).Infinite) ∧ (∀ n, IsOpen (U n)) ∧ Pairwise (Disjoint on U) := by
  suffices : ∃ U : ℕ → Set X, (∀ n, (U n).Nonempty) ∧ (∀ n, IsOpen (U n)) ∧ Pairwise (Disjoint on U)
  · rcases this with ⟨U, hne, ho, hd⟩
    refine ⟨fun n ↦ ⋃ m, U (.pair n m), ?_, fun _ ↦ isOpen_unionᵢ fun _ ↦ ho _, ?_⟩
    · refine fun n ↦ infinite_unionᵢ_of_left (fun _ ↦ hne _) (fun m m' hne ↦ hd ?_)
      simpa
    · refine fun n n' hne ↦ disjoint_unionᵢ_left.2 fun m ↦ disjoint_unionᵢ_right.2 fun m' ↦ hd ?_
      simp [hne]
  by_cases h : DiscreteTopology X
  · refine ⟨fun n ↦ {Infinite.natEmbedding X n}, fun _ ↦ singleton_nonempty _,
      fun _ ↦ isOpen_discrete _, fun _ _ h ↦ ?_⟩
    simpa using h
  · simp only [discreteTopology_iff_nhds_ne, not_forall, ← Ne.def, ← neBot_iff] at h
    cases' h with x hx
    suffices : ∃ U : ℕ → Set X, (∀ n, (U n).Nonempty ∧ IsOpen (U n) ∧ (U n)ᶜ ∈ 𝓝 x) ∧
      Pairwise (Disjoint on U)
    · rcases this with ⟨U, hU, hd⟩
      exact ⟨U, fun n ↦ (hU n).1, fun n ↦ (hU n).2.1, hd⟩
    have : IsSymm (Set X) Disjoint := ⟨fun _ _ h ↦ h.symm⟩
    refine exists_seq_of_forall_finset_exists' (fun U : Set X ↦ U.Nonempty ∧ IsOpen U ∧ Uᶜ ∈ 𝓝 x)
      Disjoint fun S hS ↦ ?_
    have : (⋂ U ∈ S, interior (Uᶜ)) \ {x} ∈ 𝓝[≠] x := inter_mem_inf ((binterᵢ_finset_mem _).2
      fun U hU ↦ interior_mem_nhds.2 (hS _ hU).2.2) (mem_principal_self _)
    rcases hx.nonempty_of_mem this with ⟨y, hyU, hyx : y ≠ x⟩
    rcases t2_separation hyx with ⟨V, W, hVo, hWo, hyV, hxW, hVW⟩
    refine ⟨V ∩ ⋂ U ∈ S, interior (Uᶜ), ⟨⟨y, hyV, hyU⟩, ?_, ?_⟩, fun U hU ↦ ?_⟩
    · exact hVo.inter (isOpen_binterᵢ_finset fun _ _ ↦ isOpen_interior)
    · refine mem_of_superset (hWo.mem_nhds hxW) fun z hzW ⟨hzV, _⟩ ↦ ?_
      exact disjoint_left.1 hVW hzV hzW
    · exact disjoint_left.2 fun z hzU ⟨_, hzU'⟩ ↦ interior_subset (mem_interᵢ₂.1 hzU' U hU) hzU

/-- If `X` is an infinite Hausdorff topological space, then there exists a topological embedding
`f : ℕ → X`.

Note: this theorem is true for an infinite KC-space but the proof in this case is different. -/
theorem exists_topology_embedding_nat : ∃ f : ℕ → X, Embedding f := by
  rcases exists_seq_infinite_isOpen_pairwise_disjoint X with ⟨U, hUi, hUo, hd⟩
  choose f hf using fun n ↦ (hUi n).nonempty
  refine ⟨f, Inducing.embedding ⟨Eq.symm (eq_bot_of_singletons_open fun n ↦ ⟨U n, hUo n, ?_⟩)⟩⟩
  refine eq_singleton_iff_unique_mem.2 ⟨hf _, fun m hm ↦ ?_⟩
  exact hd.eq (not_disjoint_iff.2 ⟨f m, hf _, hm⟩)

/-- If `X` is an infinite Hausdorff topological space, then there exists an infinite set `s : Set X`
that has the induced topology is the discrete topology. -/
theorem exists_infinite_discreteTopology : ∃ s : Set X, s.Infinite ∧ DiscreteTopology s := by
  rcases exists_topology_embedding_nat X with ⟨f, hf⟩
  refine ⟨range f, infinite_range_of_injective hf.inj, ?_⟩
  exact (Homeomorph.ofEmbedding f hf).symm.embedding.discreteTopology
