/-
Copyright (c) 2019 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.Separation

#align_import topology.uniform_space.pi from "leanprover-community/mathlib"@"2705404e701abc6b3127da906f40bae062a169c9"

/-!
# Indexed product of uniform spaces
-/


noncomputable section

open Uniformity Topology

section

open Filter UniformSpace Function

universe u

variable {ι ι' β : Type*} (α : ι → Type u) [U : ∀ i, UniformSpace (α i)] [UniformSpace β]

instance Pi.uniformSpace : UniformSpace (∀ i, α i) :=
  UniformSpace.ofCoreEq (⨅ i, UniformSpace.comap (fun a : ∀ i, α i => a i) (U i)).toCore
      Pi.topologicalSpace <|
    Eq.symm toTopologicalSpace_iInf
#align Pi.uniform_space Pi.uniformSpace

lemma Pi.uniformSpace_eq :
    Pi.uniformSpace α = ⨅ i, UniformSpace.comap (eval i) (U i) := by
  ext : 1; rfl

theorem Pi.uniformity :
    𝓤 (∀ i, α i) = ⨅ i : ι, (Filter.comap fun a => (a.1 i, a.2 i)) (𝓤 (α i)) :=
  iInf_uniformity
#align Pi.uniformity Pi.uniformity

variable {α}

theorem uniformContinuous_pi {β : Type*} [UniformSpace β] {f : β → ∀ i, α i} :
    UniformContinuous f ↔ ∀ i, UniformContinuous fun x => f x i := by
  -- porting note: required `Function.comp` to close
  simp only [UniformContinuous, Pi.uniformity, tendsto_iInf, tendsto_comap_iff, Function.comp]
#align uniform_continuous_pi uniformContinuous_pi

variable (α)

theorem Pi.uniformContinuous_proj (i : ι) : UniformContinuous fun a : ∀ i : ι, α i => a i :=
  uniformContinuous_pi.1 uniformContinuous_id i
#align Pi.uniform_continuous_proj Pi.uniformContinuous_proj

theorem Pi.uniformContinuous_precomp' {ι' : Type*} (φ : ι' → ι) :
    UniformContinuous (fun (f : (∀ i, α i)) (j : ι') ↦ f (φ j)) :=
  uniformContinuous_pi.mpr fun j ↦ uniformContinuous_proj α (φ j)

theorem Pi.uniformContinuous_precomp {ι' β : Type*} [UniformSpace β] (φ : ι' → ι) :
    UniformContinuous (· ∘ φ : (ι → β) → (ι' → β)) :=
  Pi.uniformContinuous_precomp' _ φ

theorem Pi.uniformContinuous_postcomp' {β : ι → Type*} [∀ i, UniformSpace (β i)]
    {g : ∀ i, α i → β i} (hg : ∀ i, UniformContinuous (g i)) :
    UniformContinuous (fun (f : (∀ i, α i)) (i : ι) ↦ g i (f i)) :=
  uniformContinuous_pi.mpr fun i ↦ (hg i).comp <| uniformContinuous_proj α i

theorem Pi.uniformContinuous_postcomp {α β : Type*} [UniformSpace α] [UniformSpace β] {g : α → β}
    (hg : UniformContinuous g) : UniformContinuous (g ∘ · : (ι → α) → (ι → β)) :=
  Pi.uniformContinuous_postcomp' _ fun _ ↦ hg

lemma cauchy_pi_iff [Nonempty ι] {l : Filter (∀ i, α i)} :
    Cauchy l ↔ ∀ i, Cauchy (map (eval i) l) := by
  simp_rw [Pi.uniformSpace_eq, cauchy_iInf_uniformSpace, cauchy_comap_uniformSpace]

lemma cauchy_pi_iff' {l : Filter (∀ i, α i)} [l.NeBot] :
    Cauchy l ↔ ∀ i, Cauchy (map (eval i) l) := by
  simp_rw [Pi.uniformSpace_eq, cauchy_iInf_uniformSpace', cauchy_comap_uniformSpace]

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
#align Pi.complete Pi.complete

instance Pi.separated [∀ i, SeparatedSpace (α i)] : SeparatedSpace (∀ i, α i) :=
  separated_def.2 fun x y H => by
    ext i
    -- porting note: should be `eq_ofSeparated_ofUniformContinuous`?
    apply eq_of_separated_of_uniformContinuous (Pi.uniformContinuous_proj α i)
    apply H
#align Pi.separated Pi.separated

lemma Pi.uniformSpace_comap_precomp' (f : ι' → ι) :
    UniformSpace.comap (fun g i' ↦ g (f i')) (Pi.uniformSpace (fun i' ↦ α (f i'))) =
    ⨅ i', UniformSpace.comap (eval (f i')) (U (f i')) := by
  simp [Pi.uniformSpace_eq, UniformSpace.comap_iInf, ← UniformSpace.comap_comap, comp]

lemma Pi.uniformSpace_comap_restrict (S : Set ι) :
    UniformSpace.comap (S.restrict) (Pi.uniformSpace (fun i : S ↦ α i)) =
    ⨅ i ∈ S, UniformSpace.comap (eval i) (U i) := by
  simp [← iInf_subtype'', ← uniformSpace_comap_precomp' _ ((↑) : S → ι), Set.restrict]

lemma Pi.uniformSpace_comap_precomp (f : ι' → ι) :
    UniformSpace.comap (· ∘ f) (Pi.uniformSpace (fun _ ↦ β)) =
    ⨅ i', UniformSpace.comap (eval (f i')) ‹UniformSpace β› :=
  uniformSpace_comap_precomp' (fun _ ↦ β) f

end
