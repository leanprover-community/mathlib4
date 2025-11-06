/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Topology.Instances.CantorSet
import Mathlib.Topology.UnitInterval

/-!
# Hausdorff–Alexandroff Theorem

In this file, we prove the Hausdorff–Alexandroff theorem, which states that every compact
metric space is a continuous image of the Cantor set.

## Proof Outline

First, note that the Cantor set is homeomorphic to `ℕ → Bool`, as shown in
`Mathlib.Topology.Instances.CantorSet`. Therefore, in this file, we work only with the space
`ℕ → Bool` and refer to it as the "Cantor space".

The proof consists of three steps. Let `X` be a compact metric space.

1. Every compact metric space is homeomorphic to a closed subset of the Hilbert cube.
   This is already proved in `Mathlib.Topology.Compactness.HilbertCubeEmbedding`. Using this result,
   we may assume that `X` is a closed subset of the Hilbert cube.
2. We construct a continuous surjection `cantorToHilbert` from the Cantor space to the Hilbert
   cube.
3. Taking the preimage of `X` under this surjection, it remains to prove that any closed
   subset of the Cantor space is the continuous image of the Cantor space.
-/

namespace Real

/-- Convert a sequence of binary digits to a real number from `unitInterval`. -/
noncomputable def fromBinary : (ℕ → Bool) → unitInterval :=
  let φ : (ℕ → Bool) ≃ₜ (ℕ → Fin 2) := Homeomorph.piCongrRight
    (fun _ ↦ finTwoEquiv.toHomeomorphOfDiscrete.symm)
  Subtype.coind (ofDigits ∘ φ) (fun _ ↦ ⟨ofDigits_nonneg _, ofDigits_le_one _⟩)

theorem fromBinary_continuous : Continuous fromBinary :=
  Continuous.subtype_mk (continuous_ofDigits.comp' (Homeomorph.continuous _)) _

theorem fromBinary_surjective : fromBinary.Surjective := by
  refine Subtype.coind_surjective' _ ((ofDigits_SurjOn (by norm_num)).comp ?_)
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
