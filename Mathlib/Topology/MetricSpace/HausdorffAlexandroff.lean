/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Topology.Instances.CantorSet
public import Mathlib.Topology.MetricSpace.PiNat

/-!
# Hausdorff–Alexandroff Theorem

In this file, we prove the Hausdorff–Alexandroff theorem, which states that every
nonempty compact metric space is a continuous image of the Cantor set.

## Main theorems

* `exists_nat_bool_continuous_surjective_of_compact`: Hausdorff–Alexandroff Theorem.

## Proof Outline

First, note that the Cantor set is homeomorphic to `ℕ → Bool`, as shown in
`cantorSetHomeomorphNatToBool`. Therefore, in this file, we work only with the space
`ℕ → Bool` and refer to it as the "Cantor space".

The proof consists of three steps. Let `X` be a compact metric space.

1. Every compact metric space is homeomorphic to a closed subset of the Hilbert cube.
   This is already proved in `exists_closed_embedding_to_hilbert_cube`. Using this result,
   we may assume that `X` is a closed subset of the Hilbert cube.
2. We construct a continuous surjection `cantorToHilbert` from the Cantor space to the Hilbert
   cube.
3. Taking the preimage of `X` under this surjection, it remains to prove that any closed
   subset of the Cantor space is the continuous image of the Cantor space.
-/

@[expose] public section

namespace Real

/-- Convert a sequence of binary digits to a real number from `unitInterval`. -/
noncomputable def fromBinary : (ℕ → Bool) → unitInterval :=
  let φ : (ℕ → Bool) ≃ₜ (ℕ → Fin 2) := Homeomorph.piCongrRight
    (fun _ ↦ finTwoEquiv.toHomeomorphOfDiscrete.symm)
  Subtype.coind (ofDigits ∘ φ) (fun _ ↦ ⟨ofDigits_nonneg _, ofDigits_le_one _⟩)

theorem fromBinary_continuous : Continuous fromBinary :=
  Continuous.subtype_mk (continuous_ofDigits.comp' (Homeomorph.continuous _)) _

theorem fromBinary_surjective : fromBinary.Surjective := by
  refine Subtype.coind_surjective _ ((ofDigits_SurjOn (by norm_num)).comp ?_)
  simp only [Set.surjOn_univ, Homeomorph.surjective _]

end Real

open Real

/-- A continuous surjection from the Cantor space to the Hilbert cube. -/
noncomputable def cantorToHilbert (x : ℕ → Bool) : ℕ → unitInterval :=
  Pi.map (fun _ b ↦ fromBinary b) (cantorSpaceHomeomorphNatToCantorSpace x)

theorem cantorToHilbert_continuous : Continuous cantorToHilbert :=
  continuous_pi (fun _ ↦ fromBinary_continuous.comp (by fun_prop))

theorem cantorToHilbert_surjective : cantorToHilbert.Surjective :=
  (Function.Surjective.piMap (fun _ ↦ fromBinary_surjective)).comp
    cantorSpaceHomeomorphNatToCantorSpace.surjective

attribute [local instance] PiNat.metricSpace in
theorem exists_retractionCantorSet {X : Set (ℕ → Bool)} (h_closed : IsClosed X)
    (h_nonempty : X.Nonempty) : ∃ f : (ℕ → Bool) → (ℕ → Bool), Continuous f ∧ Set.range f = X := by
  obtain ⟨f, fs, frange, hf⟩ := PiNat.exists_lipschitz_retraction_of_isClosed h_closed h_nonempty
  exact ⟨f, hf.continuous, frange⟩

/-- **Hausdorff–Alexandroff theorem**: every nonempty compact metric space is a continuous image
of the Cantor set. -/
theorem exists_nat_bool_continuous_surjective_of_compact (X : Type*) [Nonempty X] [MetricSpace X]
    [CompactSpace X] : ∃ f : (ℕ → Bool) → X, Continuous f ∧ Function.Surjective f := by
  -- `X` is homeomorphic to a closed subset `KH` of the Hilbert cube.
  let : TopologicalSpace.SeparableSpace X :=
    TopologicalSpace.SecondCountableTopology.to_separableSpace
  obtain ⟨emb, h_emb⟩ := Metric.PiNatEmbed.exists_embedding_to_hilbert_cube (X := X)
  let KH : Set (ℕ → unitInterval) := Set.range emb
  let g : X ≃ₜ KH := h_emb.toHomeomorph
  -- `KC` is the closed preimage of `KH` under the continuous surjection `cantorToHilbert`.
  let KC : Set (ℕ → Bool) := cantorToHilbert ⁻¹' KH
  have hKC_closed : IsClosed KC :=
    IsClosed.preimage cantorToHilbert_continuous (Topology.IsClosedEmbedding.isClosed_range
    <| Continuous.isClosedEmbedding (Topology.IsEmbedding.continuous h_emb) h_emb.injective)
  -- Take a retraction `f'` from the Cantor space to `KC`.
  obtain ⟨f, hf_continuous, hf_surjective⟩ := exists_retractionCantorSet hKC_closed
    <| Set.Nonempty.preimage (Set.range_nonempty emb) cantorToHilbert_surjective
  let f' : (ℕ → Bool) → KC := Subtype.coind f (by simp [← hf_surjective])
  have hf'_surjective : Function.Surjective f' := Subtype.coind_surjective _ (by grind [Set.SurjOn])
  -- Let `h` be the restriction of `cantorToHilbert` to `KC → KH`.
  let h : KC → KH := KH.restrictPreimage cantorToHilbert
  have hh_continuous : Continuous h := Continuous.restrictPreimage cantorToHilbert_continuous
  have hh_surjective : Function.Surjective h :=
    Set.restrictPreimage_surjective _ cantorToHilbert_surjective
  -- Take the composition `g.symm ∘ h ∘ f'` as the desired continuous surjection from the Cantor
  -- space to `X`.
  exact ⟨g.symm ∘ h ∘ f', by fun_prop, g.symm.surjective.comp <| hh_surjective.comp hf'_surjective⟩
