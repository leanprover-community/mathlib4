/-
Copyright (c) 2026 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic

/-!
# Lifting bilinear forms to quotients
-/
@[expose] public section

namespace LinearMap

section Asymmetric -- "asymmetric" case of a form `M × N → P`

variable {R R₂ S S₂ M N P : Type*} [Ring R] [Ring R₂] [Ring S] [Ring S₂]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [Module R M] [Module S N] [Module R₂ P]
    [Module S₂ P] [SMulCommClass R₂ S₂ P] {ρ : R →+* R₂} {σ : S →+* S₂}

attribute [local instance] SMulCommClass.symm

/-- Lift a bilinear form from `M × N → P` to `(M ⧸ M') × (N ⧸ N') → P`. -/
def liftQ₂ (M' : Submodule R M) (N' : Submodule S N) (f : M →ₛₗ[ρ] N →ₛₗ[σ] P)
    (hM' : M' ≤ f.ker) (hN' : N' ≤ f.flip.ker) :
    M ⧸ M' →ₛₗ[ρ] N ⧸ N' →ₛₗ[σ] P :=
  have : ∀ n ∈ N', n ∈ (M'.liftQ f hM').flip.ker := fun n hn ↦ by
    simp_rw [LinearMap.mem_ker, LinearMap.ext_iff, LinearMap.flip_apply, Submodule.Quotient.forall,
      Submodule.liftQ_apply, ← f.flip_apply, show f.flip n = 0 from hN' hn, LinearMap.zero_apply,
      forall_true_iff]
  (N'.liftQ (M'.liftQ f hM').flip this).flip

@[simp]
lemma liftQ₂_mk {M' : Submodule R M} {N' : Submodule S N} {f : M →ₛₗ[ρ] N →ₛₗ[σ] P}
    (hM' : M' ≤ f.ker) (hN' : N' ≤ f.flip.ker) (m : M) (n : N) :
    f.liftQ₂ M' N' hM' hN' (Submodule.Quotient.mk m) (Submodule.Quotient.mk n) = f m n :=
  rfl

end Asymmetric

section Symmetric -- "symmetric" case of a form `M × M → P`

variable {R S M P : Type*} [AddCommGroup M] [CommRing R] [CommRing S]
    [Module R M] [AddCommGroup P] [Module S P] {I₁ I₂ : R →+* S}

/-- Special case of `LinearMap.liftQ₂` with left and right spaces the same. Reducible so
that simp lemmas about `LinearMap.liftQ₂` apply to it. -/
abbrev IsRefl.liftQ₂ (f : M →ₛₗ[I₁] M →ₛₗ[I₂] P)
    (N : Submodule R M) (hf : f.IsRefl) (hN : N ≤ f.ker) :
    M ⧸ N →ₛₗ[I₁] M ⧸ N →ₛₗ[I₂] P :=
  f.liftQ₂ N N hN (hf.ker_flip ▸ hN)

end Symmetric

end LinearMap
