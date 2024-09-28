/-
Copyright (c) 2024 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Jack Cheverton, Samyak Dhar Tuladhar
-/

import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Order.CompleteLattice
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-! # Joint eigenspaces of a commuting pair of symmetric operators

This file collects various decomposition results for joint eigenspaces of a commuting pair
of symmetric operators on a finite-dimensional inner product space.

# Main Result

* `LinearMap.IsSymmetric.directSum_isInternal_of_commute` establishes that
   if `{A B : E →ₗ[𝕜] E}`, then `IsSymmetric A`, `IsSymmetric B` and `A ∘ₗ B = B ∘ₗ A` imply that
   `E` decomposes as an internal direct sum of the pairwise orthogonal spaces
   `eigenspace B μ ⊓ eigenspace A ν`

## TODO

Develop a `Diagonalization` structure for linear maps and / or matrices which consists of a basis,
and a proof obligation that the basis vectors are eigenvectors.

## Tags

self-adjoint operator, simultaneous eigenspaces, joint eigenspaces

-/

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

open Module.End

namespace LinearMap

namespace IsSymmetric

section Pair

variable {α : 𝕜} {A B : E →ₗ[𝕜] E}

/--If a pair of operators commute, then the eigenspaces of one are invariant under the other.-/
theorem eigenspace_invariant_of_commute
    (hAB : A ∘ₗ B = B ∘ₗ A) (α : 𝕜) : ∀ v ∈ (eigenspace A α), (B v ∈ eigenspace A α) := by
  intro v hv
  rw [eigenspace, mem_ker, sub_apply, Module.algebraMap_end_apply, ← comp_apply A B v, hAB,
    comp_apply B A v, ← map_smul, ← map_sub, hv, map_zero] at *

/--The simultaneous eigenspaces of a pair of commuting symmetric operators form an
`OrthogonalFamily`.-/
theorem orthogonalFamily_eigenspace_inf_eigenspace (hA : A.IsSymmetric) (hB : B.IsSymmetric) :
    OrthogonalFamily 𝕜 (fun (i : 𝕜 × 𝕜) => (eigenspace A i.2 ⊓ eigenspace B i.1 : Submodule 𝕜 E))
    (fun i => (eigenspace A i.2 ⊓ eigenspace B i.1).subtypeₗᵢ) :=
     OrthogonalFamily.of_pairwise fun i j hij v ⟨hv1 , hv2⟩ ↦ by
    obtain (h₁ | h₂) : i.1 ≠ j.1 ∨ i.2 ≠ j.2 := by rwa [Ne.eq_def, Prod.ext_iff, not_and_or] at hij
    all_goals intro w ⟨hw1, hw2⟩
    · exact hB.orthogonalFamily_eigenspaces.pairwise h₁ hv2 w hw2
    · exact hA.orthogonalFamily_eigenspaces.pairwise h₂ hv1 w hw1

open Submodule in

/-- The intersection of eigenspaces of commuting selfadjoint operators is equal to the eigenspace of
one operator restricted to the eigenspace of the other, which is an invariant subspace because the
operators commute. -/
theorem eigenspace_inf_eigenspace
    (hAB : A ∘ₗ B = B ∘ₗ A) (γ : 𝕜) :
    eigenspace A α ⊓ eigenspace B γ = map (Submodule.subtype (eigenspace A α))
      (eigenspace (B.restrict (eigenspace_invariant_of_commute hAB α)) γ) :=
  (eigenspace A α).inf_genEigenspace _ _ (k := 1)

variable [FiniteDimensional 𝕜 E]

/-- If A and B are commuting symmetric operators on a finite dimensional inner product space
then the eigenspaces of the restriction of B to any eigenspace of A exhaust that eigenspace.-/
theorem iSup_eigenspace_inf_eigenspace (hB : B.IsSymmetric)
    (hAB : A ∘ₗ B = B ∘ₗ A):
    (⨆ γ, eigenspace A α ⊓ eigenspace B γ) = eigenspace A α := by
  conv_rhs => rw [← (eigenspace A α).map_subtype_top]
  simp only [eigenspace_inf_eigenspace hAB, ← Submodule.map_iSup]
  congr 1
  rw [← Submodule.orthogonal_eq_bot_iff]
  exact orthogonalComplement_iSup_eigenspaces_eq_bot <|
    hB.restrict_invariant <| eigenspace_invariant_of_commute hAB α

/-- If A and B are commuting symmetric operators acting on a finite dimensional inner product space,
then the simultaneous eigenspaces of A and B exhaust the space. -/
theorem iSup_iSup_eigenspace_inf_eigenspace_eq_top (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (hAB : A ∘ₗ B = B ∘ₗ A) :
    (⨆ α, ⨆ γ, eigenspace A α ⊓ eigenspace B γ) = ⊤ := by
  simpa [iSup_eigenspace_inf_eigenspace hB hAB] using
    Submodule.orthogonal_eq_bot_iff.mp <| hA.orthogonalComplement_iSup_eigenspaces_eq_bot

/-- Given a commuting pair of symmetric linear operators on a finite dimensional inner product
space, the space decomposes as an internal direct sum of simultaneous eigenspaces of these
operators. -/
theorem directSum_isInteral_of_commute (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (hAB : A ∘ₗ B = B ∘ₗ A) :
    DirectSum.IsInternal (fun (i : 𝕜 × 𝕜) ↦ (eigenspace A i.2 ⊓ eigenspace B i.1)):= by
  apply (orthogonalFamily_eigenspace_inf_eigenspace hA hB).isInternal_iff.mpr
  rw [Submodule.orthogonal_eq_bot_iff, iSup_prod, iSup_comm]
  exact iSup_iSup_eigenspace_inf_eigenspace_eq_top hA hB hAB

end Pair

section Oliver

/-
I claim it is usually better to work within the lattice of submodules and so I think rather
than proving
a headline result in the language of DirectSum.IsInternal
I'd prove the equivalent pair of conditions according to
DirectSum.isInternal_submodule_iff_independent_and_iSup_eq_top
[Feel free to disagree with me here; I mention this primarily because I use this language below]
-/


variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {S T : E →ₗ[𝕜] E}

/-
It's interesting that the following isn't Module.End.InnerProductSpace. It seems he is opening three
distinct namespaces.
-/
open Module End InnerProductSpace

/-Maybe I should prove a `LinearMap.IsSymmetric.pow` lemma as suggested by Jireh.
What would that be? The name suggests it clearly. We'd want a theorem saying that if `T`
is a symmetric operator then every nonnegative power `T^n` is also symmetric.

First, we can prove that if two symmetric operators commute then their product is a symmetric
operator. That should certainly be a lemma.
-/

example (hS : S.IsSymmetric) (hT : T.IsSymmetric) (hST : Commute S T) : (S * T).IsSymmetric := by
  refine fun x y ↦ ?_
  simp only [mul_apply]
  --maybe first do this with calc block and then see what can be done.
  --rw [IsSymmetric]
  --this is a mess, actually. One notices at this point that there is a lemma about
  --selfadjoint things that will do the job very easily.
  --so the efficient way to provide the theorem below is indeed to convert over to
  --selfadjointness and then prove it that way.

example (hT : T.IsSymmetric) {n : ℕ} : (T ^ n).IsSymmetric := by
  rw [LinearMap.isSymmetric_iff_isSelfAdjoint] at *
  exact hT.pow n

--term mode version

example (hT : T.IsSymmetric) {n : ℕ} : (T ^ n).IsSymmetric :=
  (isSymmetric_iff_isSelfAdjoint _).mpr <| (isSymmetric_iff_isSelfAdjoint _).mp hT |>.pow _

/-It seems to be a good idea to try to do this by the method of induction employed by Jireh below.
To see what is going on, note that the base case should be `LinearMap.IsSymmetric T^0`. We seem to
need `pow_zero T`, which is a proof that `T^0=1`. I would like to include this fact in a
proof that 1 is symmetric. We have `LinearMap.isSymmetric_id`.

Ok, back up. We are trying to show that `T^0` is symmetric, and then assuming that `T^k` is
symmetric, use this to show `T ^ (k + 1)` is symmetric. This should be easy since
`T ^ (k + 1) = T * T^k = T^k * T` and so working with the inner products, one can reverse this.

So `P : (n : ℕ) → m ≤ n → Prop` is what in this case? It should be `P n hn` is a proof that
`(T ^ n).IsSymmetric`. The base should be that `(T ^ 0).IsSymmetric`. Can we make this clean?

Maybe we can use a `refine` and provide a proof like the following one.
-/
 --have H : (T ^ 0).IsSymmetric := pow_zero T ▸ LinearMap.isSymmetric_id
/-
It's interesting in H above that the goal is used to enable the `▸` to work.
There is some kind of unification going on.

What does "function expected" error mean in the following? I guess it means there has to be a
function
type to apply to the left hand side. The proof of the equality won't work. (I would have
expected that `pow_zero` would have been the function...but that isn't applied to `1`, but
to `T`.)
-/
-- have L : (T ^ 0) = id := one_eq_id (R := 𝕜) (M := E) ▸ (pow_zero T)
/-
For some reason, in what follows the `▸` isn't working. It should be a proof of the
base case.

Ok it works now. This time the function worked because we could use the `one_eq_id` equality
to `▸` `id.isSymmetric` into `1.isSymmetric`.
-/

--  refine Nat.le_induction (pow_zero T ▸ one_eq_id (R := 𝕜) (M := E) ▸ LinearMap.isSymmetric_id)
--    (fun k hk ih ↦ ?_) n (Nat.zero_le _)
--  rw [@iterate_succ]
/-
Now all that is left is the inductive step. To this end, we first need to be able to split
`T ^ (k + 1) = T * T ^ k` somehow, and then invoke the products of symmetric ops are symmetric.
-/


example (hT : T.IsSymmetric) {n : ℕ} {μ : 𝕜} (hn : 1 ≤ n) :
    genEigenspace T μ n = genEigenspace T μ 1 := by
  refine Nat.le_induction rfl (fun k hk ih ↦ ?_) n hn
  refine ih ▸ le_antisymm (fun x hx ↦ ?_) ((genEigenspace T μ).mono k.le_succ)
  obtain (rfl | hx_ne) := eq_or_ne x 0
  · exact zero_mem _
  · have hμ : HasEigenvalue T μ := hasEigenvalue_of_hasGenEigenvalue (k := k + 1) <|
      (genEigenspace T μ (k + 1)).ne_bot_iff.mpr ⟨x, hx, hx_ne⟩
    have hT' := LinearMap.isSymmetric_iff_isSelfAdjoint T |>.mp hT
    have hTμ : ((T - μ • 1) ^ k).IsSymmetric  := by
      rw [LinearMap.isSymmetric_iff_isSelfAdjoint]
      refine .pow (hT'.sub (.smul ?_ ?_)) k
      · exact hT.conj_eigenvalue_eq_self hμ
      · exact (LinearMap.isSymmetric_iff_isSelfAdjoint 1).mp LinearMap.isSymmetric_id
    rw [mem_genEigenspace, ← norm_eq_zero, ← sq_eq_zero_iff, norm_sq_eq_inner (𝕜 := 𝕜)]
    rw [hTμ, ← LinearMap.comp_apply, ← LinearMap.mul_eq_comp, ← pow_add]
    simp [mem_genEigenspace .. |>.mp <| (genEigenspace T μ).mono (show k + 1 ≤ k + k by gcongr) hx]


/-The following is the suggested starting result of Oliver.
Let's try to write a more or less nice proof of this.
It seems to me that the point here is that some sup and inf versions of things are available
for generalized eigenspaces already.
Particularly:
`DirectSum.isInternal_submodule_iff_independent_and_iSup_eq_top`
-/

lemma iSup_iInf_maxGenEigenspace_eq_top_of_commute {ι K V : Type*}
    [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : ι → End K V)
    (h : Pairwise fun i j ↦ Commute (f i) (f j))
    (h' : ∀ i, ⨆ μ, (f i).maxGenEigenspace μ = ⊤) :
    ⨆ χ : ι → K, ⨅ i, (f i).maxGenEigenspace (χ i) = ⊤ := by
sorry

end Oliver

end IsSymmetric

end LinearMap
