/-
Copyright (c) 2026 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

module

public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

/-! # Localization of tensor product

We construct an isomorphism `(S ⊗[R] A)[(1 ⊗ₜ W)⁻¹] ≅ (S ⊗[R] A)[W⁻¹]`.
-/

@[expose] public section

open Algebra TensorProduct

variable {R S A : Type*}
  [CommSemiring R] [CommSemiring S] [CommSemiring A]
  [Algebra R S] [Algebra R A] (W₁ : Submonoid A) (W₂ : Submonoid (S ⊗[R] A))
  (hw : W₁.map includeRight = W₂)

namespace IsLocalization

variable (A₁ SA₁ : Type*)
  [CommSemiring A₁] [CommSemiring SA₁]
  [Algebra A A₁] [IsLocalization W₁ A₁]
  [Algebra R A₁] [IsScalarTower R A A₁]
  [Algebra (S ⊗[R] A) SA₁] [IsLocalization W₂ SA₁]
  [Algebra R SA₁] [Algebra S SA₁] [IsScalarTower R S SA₁] [IsScalarTower S (S ⊗[R] A) SA₁]
  [IsScalarTower R (S ⊗[R] A) SA₁]

/-- `(S ⊗[R] A)[(1 ⊗ₜ W)⁻¹] ≅ (S ⊗[R] A)[W⁻¹]`. -/
noncomputable def tensorEquiv : SA₁ ≃ₐ[S] S ⊗[R] A₁ := .ofAlgHom
  (liftAlgHom (M := W₂)
    (f := Algebra.TensorProduct.map (1 : S →ₐ[S] S) (Algebra.algHom R A A₁)) <| by
      rw [← hw]
      rintro ⟨_, w, hw, rfl⟩
      exact (map_units _ ⟨w, hw⟩).map includeRight)
  (.liftEquiv _ _ _ _ <| liftAlgHom (M := W₁) (f := (Algebra.algHom _ _ _).comp includeRight)
    fun w ↦ map_units (M := W₂) SA₁ ⟨_, hw ▸ ⟨_, w.2, rfl⟩⟩)
  (ext_ring <| algHom_ext W₁ <| by ext; simp [Algebra.algHom])
  (algHom_ext W₂ <| by ext; simp [Algebra.algHom])

@[simp] lemma tensorEquiv_mk'_tmul (s : S) (n : A) (d : A) (hd : d ∈ W₁) :
    tensorEquiv W₁ W₂ hw A₁ SA₁ (mk' (M := W₂) _ (s ⊗ₜ[R] n) ⟨1 ⊗ₜ[R] d, hw ▸ ⟨d, hd, rfl⟩⟩) =
      s ⊗ₜ[R] mk' (M := W₁) _ n ⟨d, hd⟩ := by
  simp [tensorEquiv, lift_mk'_spec, Algebra.algHom]

@[simp] lemma tensorEquiv_symm_tmul_mk' (s : S) (n : A) (d : A) (hd : d ∈ W₁) :
    (tensorEquiv W₁ W₂ hw A₁ SA₁).symm (s ⊗ₜ[R] mk' (M := W₁) _ n ⟨d, hd⟩) =
      mk' (M := W₂) _ (s ⊗ₜ[R] n) ⟨1 ⊗ₜ[R] d, hw ▸ ⟨d, hd, rfl⟩⟩ := by
  rw [← tensorEquiv_mk'_tmul _ _ hw A₁ SA₁, AlgEquiv.symm_apply_apply]

end IsLocalization

namespace Localization

/-- `(S ⊗[R] A)[(1 ⊗ₜ W)⁻¹] ≅ S ⊗[R] A[W⁻¹]`. -/
noncomputable def tensorEquiv : Localization W₂ ≃ₐ[S] S ⊗[R] Localization W₁ :=
  IsLocalization.tensorEquiv W₁ W₂ hw _ _

@[simp] theorem tensorEquiv_mk_tmul (s : S) (n : A) (d : A) (hd : d ∈ W₁) :
    tensorEquiv W₁ W₂ hw (mk (s ⊗ₜ[R] n) ⟨1 ⊗ₜ[R] d, hw ▸ ⟨d, hd, rfl⟩⟩) =
      s ⊗ₜ[R] mk n ⟨d, hd⟩ := by
  simp [mk_eq_mk', tensorEquiv, hd]

@[simp] theorem tensorEquiv_symm_tmul_mk (s : S) (n : A) (d : A) (hd : d ∈ W₁) :
    (tensorEquiv W₁ W₂ hw).symm (s ⊗ₜ[R] mk n ⟨d, hd⟩) =
      (mk (s ⊗ₜ[R] n) ⟨1 ⊗ₜ[R] d, hw ▸ ⟨d, hd, rfl⟩⟩) := by
  rw [← tensorEquiv_mk_tmul W₁ W₂ hw, AlgEquiv.symm_apply_apply]

end Localization
