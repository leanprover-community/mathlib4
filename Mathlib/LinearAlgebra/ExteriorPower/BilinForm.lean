/-
Copyright (c) 2026 Kirill Kondrashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Kirill Kondrashov
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Bilinear forms on exterior powers

The file is a home for results about the bilinear forms on exterior powers of a module.

## Main definitions / results:

* `LinearMap.BilinForm.exteriorPower`: a bilinear form on a module induces a bilinear form on its
  exterior powers.
* `LinearMap.BilinForm.bijective_exteriorPower`: if a module carries a bijective bilinear form,
  the induced bilinear forms on its exterior powers is also bijective.

-/

noncomputable section

namespace LinearMap.BilinForm

open Function exteriorPower

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  (B : LinearMap.BilinForm R M) (n : ℕ)

/-- A bilinear form on `M` induces a bilinear form on each exterior power. -/
public protected def exteriorPower : LinearMap.BilinForm R (⋀[R]^n M) :=
  (pairingDual R M n).comp (map n B)

@[simp] lemma bilinForm_ιMulti_ιMulti (v w : Fin n → M) :
    B.exteriorPower n (ιMulti R n v) (ιMulti R n w) = (Matrix.of fun i j ↦ B (v j) (w i)).det := by
  simp [LinearMap.BilinForm.exteriorPower]

public lemma bijective_exteriorPower [Module.Free R M] [Module.Finite R M] (hB : Bijective B) :
    Bijective (B.exteriorPower n) := by
  refine (bijective_pairingDual R M n).comp ⟨?_, ?_⟩
  · exact exteriorPower.map_injective (LinearEquiv.ofBijective _ hB).symm (by ext; simp)
  · exact exteriorPower.map_surjective hB.surjective

end LinearMap.BilinForm
