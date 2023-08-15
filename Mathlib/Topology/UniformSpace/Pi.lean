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

open Filter UniformSpace

universe u

variable {ι : Type*} (α : ι → Type u) [U : ∀ i, UniformSpace (α i)]


instance Pi.uniformSpace : UniformSpace (∀ i, α i) :=
  UniformSpace.ofCoreEq (⨅ i, UniformSpace.comap (fun a : ∀ i, α i => a i) (U i)).toCore
      Pi.topologicalSpace <|
    Eq.symm toTopologicalSpace_iInf
#align Pi.uniform_space Pi.uniformSpace

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

instance Pi.complete [∀ i, CompleteSpace (α i)] : CompleteSpace (∀ i, α i) :=
  ⟨by
    intro f hf
    haveI := hf.1
    have : ∀ i, ∃ x : α i, Filter.map (fun a : ∀ i, α i => a i) f ≤ 𝓝 x := by
      intro i
      have key : Cauchy (map (fun a : ∀ i : ι, α i => a i) f) :=
        hf.map (Pi.uniformContinuous_proj α i)
      exact cauchy_iff_exists_le_nhds.1 key
    choose x hx using this
    use x
    rwa [nhds_pi, le_pi]⟩
#align Pi.complete Pi.complete

instance Pi.separated [∀ i, SeparatedSpace (α i)] : SeparatedSpace (∀ i, α i) :=
  separated_def.2 fun x y H => by
    ext i
    -- porting note: should be `eq_ofSeparated_ofUniformContinuous`?
    apply eq_of_separated_of_uniformContinuous (Pi.uniformContinuous_proj α i)
    apply H
#align Pi.separated Pi.separated

end
