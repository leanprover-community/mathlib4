/-
Copyright (c) 2019 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
module

public import Mathlib.Topology.UniformSpace.UniformEmbedding

/-!
# Indexed product of uniform spaces
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section


noncomputable section

open scoped Uniformity Topology
open Filter UniformSpace Function Set

universe u

variable {ι ι' β : Type*} (α : ι → Type u) [U : ∀ i, UniformSpace (α i)] [UniformSpace β]

instance Pi.uniformSpace : UniformSpace (∀ i, α i) :=
  UniformSpace.ofCoreEq (⨅ i, UniformSpace.comap (eval i) (U i)).toCore
      Pi.topologicalSpace <|
    Eq.symm toTopologicalSpace_iInf

lemma Pi.uniformSpace_eq :
    Pi.uniformSpace α = ⨅ i, UniformSpace.comap (eval i) (U i) := by
  ext : 1; rfl

theorem Pi.uniformity :
    𝓤 (∀ i, α i) = ⨅ i : ι, (Filter.comap fun a => (a.1 i, a.2 i)) (𝓤 (α i)) :=
  iInf_uniformity

variable {α}

instance [Countable ι] [∀ i, IsCountablyGenerated (𝓤 (α i))] :
    IsCountablyGenerated (𝓤 (∀ i, α i)) := by
  rw [Pi.uniformity]
  infer_instance

theorem uniformContinuous_pi {β : Type*} [UniformSpace β] {f : β → ∀ i, α i} :
    UniformContinuous f ↔ ∀ i, UniformContinuous fun x => f x i := by
  simp only [UniformContinuous, Pi.uniformity, tendsto_iInf, tendsto_comap_iff, Function.comp_def]

variable (α)

theorem Pi.uniformContinuous_proj (i : ι) : UniformContinuous fun a : ∀ i : ι, α i => a i :=
  uniformContinuous_pi.1 uniformContinuous_id i

theorem Pi.uniformContinuous_precomp' (φ : ι' → ι) :
    UniformContinuous (fun (f : (∀ i, α i)) (j : ι') ↦ f (φ j)) :=
  uniformContinuous_pi.mpr fun j ↦ uniformContinuous_proj α (φ j)

theorem Pi.uniformContinuous_precomp (φ : ι' → ι) :
    UniformContinuous (· ∘ φ : (ι → β) → (ι' → β)) :=
  Pi.uniformContinuous_precomp' _ φ

theorem Pi.uniformContinuous_postcomp' {β : ι → Type*} [∀ i, UniformSpace (β i)]
    {g : ∀ i, α i → β i} (hg : ∀ i, UniformContinuous (g i)) :
    UniformContinuous (fun (f : (∀ i, α i)) (i : ι) ↦ g i (f i)) :=
  uniformContinuous_pi.mpr fun i ↦ (hg i).comp <| uniformContinuous_proj α i

theorem Pi.uniformContinuous_postcomp {α : Type*} [UniformSpace α] {g : α → β}
    (hg : UniformContinuous g) : UniformContinuous (g ∘ · : (ι → α) → (ι → β)) :=
  Pi.uniformContinuous_postcomp' _ fun _ ↦ hg

lemma Pi.uniformSpace_comap_precomp' (φ : ι' → ι) :
    UniformSpace.comap (fun g i' ↦ g (φ i')) (Pi.uniformSpace (fun i' ↦ α (φ i'))) =
    ⨅ i', UniformSpace.comap (eval (φ i')) (U (φ i')) := by
  simp [Pi.uniformSpace_eq, UniformSpace.comap_iInf, ← UniformSpace.comap_comap, comp_def]

lemma Pi.uniformSpace_comap_precomp (φ : ι' → ι) :
    UniformSpace.comap (· ∘ φ) (Pi.uniformSpace (fun _ ↦ β)) =
    ⨅ i', UniformSpace.comap (eval (φ i')) ‹UniformSpace β› :=
  uniformSpace_comap_precomp' (fun _ ↦ β) φ

lemma Pi.uniformContinuous_restrict (S : Set ι) :
    UniformContinuous (S.restrict : (∀ i : ι, α i) → (∀ i : S, α i)) :=
  Pi.uniformContinuous_precomp' _ ((↑) : S → ι)

lemma Pi.uniformSpace_comap_restrict (S : Set ι) :
    UniformSpace.comap (S.restrict) (Pi.uniformSpace (fun i : S ↦ α i)) =
    ⨅ i ∈ S, UniformSpace.comap (eval i) (U i) := by
  simp +unfoldPartialApp
    [← iInf_subtype'', ← uniformSpace_comap_precomp' _ ((↑) : S → ι), Set.restrict]

lemma cauchy_pi_iff [Nonempty ι] {l : Filter (∀ i, α i)} :
    Cauchy l ↔ ∀ i, Cauchy (map (eval i) l) := by
  simp_rw +instances [Pi.uniformSpace_eq, cauchy_iInf_uniformSpace, cauchy_comap_uniformSpace]

lemma cauchy_pi_iff' {l : Filter (∀ i, α i)} [l.NeBot] :
    Cauchy l ↔ ∀ i, Cauchy (map (eval i) l) := by
  simp_rw +instances [Pi.uniformSpace_eq, cauchy_iInf_uniformSpace', cauchy_comap_uniformSpace]

lemma Cauchy.pi [Nonempty ι] {l : ∀ i, Filter (α i)} (hl : ∀ i, Cauchy (l i)) :
    Cauchy (Filter.pi l) := by
  have := fun i ↦ (hl i).1
  simpa [cauchy_pi_iff]

instance Pi.complete [∀ i, CompleteSpace (α i)] : CompleteSpace (∀ i, α i) where
  complete {f} hf := by
    have := hf.1
    simp_rw [cauchy_pi_iff', cauchy_iff_exists_le_nhds] at hf
    choose x hx using hf
    use x
    rwa [nhds_pi, le_pi]

lemma Pi.uniformSpace_comap_restrict_sUnion (𝔖 : Set (Set ι)) :
    UniformSpace.comap (⋃₀ 𝔖).restrict (Pi.uniformSpace (fun i : (⋃₀ 𝔖) ↦ α i)) =
    ⨅ S ∈ 𝔖, UniformSpace.comap S.restrict (Pi.uniformSpace (fun i : S ↦ α i)) := by
  simp_rw [Pi.uniformSpace_comap_restrict α, iInf_sUnion]

/- An infimum of complete uniformities is complete,
as long as the whole family is bounded by some common T2 topology. -/
protected theorem CompleteSpace.iInf {ι X : Type*} {u : ι → UniformSpace X}
    (hu : ∀ i, @CompleteSpace X (u i))
    (ht : ∃ t, @T2Space X t ∧ ∀ i, (u i).toTopologicalSpace ≤ t) :
    @CompleteSpace X (⨅ i, u i) := by
  -- We can assume `X` is nonempty.
  nontriviality X
  rcases ht with ⟨t, ht, hut⟩
  -- The diagonal map `(X, ⨅ i, u i) → ∀ i, (X, u i)` is a uniform embedding.
  have : @IsUniformInducing X (ι → X) (⨅ i, u i) (Pi.uniformSpace (U := u)) (const ι) := by
    simp_rw [isUniformInducing_iff, iInf_uniformity, Pi.uniformity, Filter.comap_iInf,
      Filter.comap_comap, comp_def, const, Prod.eta, comap_id']
  -- Hence, it suffices to show that its range, the diagonal, is closed in `Π i, (X, u i)`.
  simp_rw [@completeSpace_iff_isComplete_range _ _ (_) (_) _ this, range_const_eq_diagonal,
    setOf_forall]
  -- The separation of `t` ensures that this is the case in `Π i, (X, t)`, hence the result
  -- since the topology associated to each `u i` is finer than `t`.
  have : Pi.topologicalSpace (t₂ := fun i ↦ (u i).toTopologicalSpace) ≤
         Pi.topologicalSpace (t₂ := fun _ ↦ t) :=
    iInf_mono fun i ↦ induced_mono <| hut i
  refine IsClosed.isComplete <| .mono ?_ this
  exact isClosed_iInter fun i ↦ isClosed_iInter fun j ↦
    isClosed_eq (continuous_apply _) (continuous_apply _)
