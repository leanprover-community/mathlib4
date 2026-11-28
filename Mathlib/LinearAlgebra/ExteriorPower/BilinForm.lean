/-
Copyright (c) 2026 Kirill Kondrashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Kirill Kondrashov
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.WedgePairing

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Bilinear forms on exterior powers

The file is a home for results about the bilinear forms on exterior powers of a module.

## Main definitions / results:

* `LinearMap.BilinForm.exteriorPower`: a bilinear form on a module induces a bilinear form on its
  exterior powers.
* `LinearMap.BilinForm.bijective_exteriorPower`: if a module carries a bijective bilinear form,
  the induced bilinear forms on its exterior powers is also bijective.
* `LinearMap.BilinForm.discr`: the discriminant of a bilinear form with respect to a volume form.
-/

noncomputable section

namespace LinearMap.BilinForm

open Function exteriorPower

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  (B : LinearMap.BilinForm R M) (n : ℕ)

/-- A bilinear form on `M` induces a bilinear form on each exterior power. -/
public protected def exteriorPower : LinearMap.BilinForm R (⋀[R]^n M) :=
  (pairingDual R M n).comp (map n B)

@[simp] public lemma bilinForm_ιMulti_ιMulti (v w : Fin n → M) :
    B.exteriorPower n (ιMulti R n v) (ιMulti R n w) = (Matrix.of fun i j ↦ B (v j) (w i)).det := by
  simp [LinearMap.BilinForm.exteriorPower]

public lemma bijective_exteriorPower [Module.Free R M] [Module.Finite R M] (hB : Bijective B) :
    Bijective (B.exteriorPower n) := by
  refine (bijective_pairingDual R M n).comp ⟨?_, ?_⟩
  · exact exteriorPower.map_injective (LinearEquiv.ofBijective _ hB).symm (by ext; simp)
  · exact exteriorPower.map_surjective hB.surjective

/-- Bases in duality for `B` induce bases in duality for `B.exteriorPower n`. -/
public lemma exteriorPower_apply_basis_exteriorPower {ι : Type*} [LinearOrder ι] [Finite ι]
    (b c : Module.Basis ι R M) (hc : ∀ i, B (c i) = b.dualBasis i) (s : Set.powersetCard ι n) :
    B.exteriorPower n (c.exteriorPower n s) = (b.exteriorPower n).dualBasis s := by
  simpa [LinearMap.BilinForm.exteriorPower, Function.comp_def, hc] using
    pairingDual_apply_dualBasis_exteriorPower n b s

section Discriminant

open Module

variable (vol : ⋀[R]^(finrank R M) M ≃ₗ[R] R)

/-- The discriminant of a bilinear form with respect to a volume form. -/
public def discr : R := B.exteriorPower (finrank R M) (vol.symm 1) (vol.symm 1)

public lemma discr_def :
    B.discr vol = B.exteriorPower (finrank R M) (vol.symm 1) (vol.symm 1) := by
  rfl

/-- On the top exterior power, the pairing is the discriminant times the product of the volumes. -/
@[simp] public lemma discr_mul_vol_mul_vol (x y : ⋀[R]^(finrank R M) M) :
    B.discr vol * (vol x * vol y) = B.exteriorPower (finrank R M) x y := by
  calc
    _ = B.exteriorPower _ (vol x • vol.symm 1) (vol y • vol.symm 1) := by
      rw [discr_def, LinearMap.map_smul₂, map_smul]
      ring
    _ = _ := by simp [← map_smul]

/-- For bases in duality under `B`, the product of their volumes is inverse to the discriminant. -/
public lemma discr_mul_vol_topVector_mul_vol_topVector [Nontrivial R]
    {ι : Type*} [LinearOrder ι] [Fintype ι]
    (b c : Basis ι R M) (hc : ∀ i, B (c i) = b.dualBasis i) :
    B.discr vol * (vol b.topVector * vol c.topVector) = 1 := by
  have hι : (Finset.univ : Finset ι).card = finrank R M := by simp [finrank_eq_card_basis b]
  rw [mul_comm (vol _), B.discr_mul_vol_mul_vol, ← c.topVector_eq_exteriorPower ⟨_, hι⟩,
    ← b.topVector_eq_exteriorPower ⟨_, hι⟩, B.exteriorPower_apply_basis_exteriorPower _ b c hc,
    Basis.dualBasis_apply_self, ite_eq_left rfl]

end Discriminant

end LinearMap.BilinForm
