/-
Copyright (c) 2024 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Jack Cheverton, Samyak Dhar Tuladhar
-/

import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Order.CompleteLattice
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

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

Here is the `IsSelfAdjoint` version of the .pow lemma:

@[aesop safe apply]
theorem pow {x : R} (hx : IsSelfAdjoint x) (n : ℕ) : IsSelfAdjoint (x ^ n) := by
  simp only [isSelfAdjoint_iff, star_pow, hx.star_eq]

This might be reproducible in our setting. Alas it is not. It uses `star A = A`.
We will need some calculation simplifications for this.
-/

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
   {S T : E →ₗ[𝕜] E}

lemma mul_of_comm (hS : S.IsSymmetric) (hT : T.IsSymmetric) (hST : Commute S T) :
    (S * T).IsSymmetric := by
  refine fun x y ↦ ?_
  nth_rw 1 [hST]
  simp only [mul_apply]
  rw [← hS, hT]

lemma pow (hT : T.IsSymmetric) (n : ℕ) : (T ^ n).IsSymmetric := by
  refine Nat.le_induction (pow_zero T ▸ one_eq_id (R := 𝕜) (M := E) ▸ isSymmetric_id)
    (fun k _ ih ↦ ?_) n (Nat.zero_le _)
  rw [iterate_succ, ← mul_eq_comp]
  exact mul_of_comm ih hT <| _root_.id <| Commute.symm <| Commute.pow_right rfl _

variable [FiniteDimensional 𝕜 E]


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
So probably want to use `DirectSum.IsInternal.submodule_iSup_eq_top`.

Note that Oliver has a Lie Theoretic version ready that is more general than for commuting things.
It may be good to just hitch our result to that one, which will require proving
some independence. I'm not sure what that will do for the understandability of the code,
but if the goal is to be able to build up the library, then stacking things on top of general
results is probably most efficient. Talk to Jireh about the relative benefit of such dependencies.


-/

/-
:= by
  have _ := Fintype.ofFinite n
*why the _ here? We don't need a named instance?*
  revert T
*This gives us access to the T.*
  change ∀ T, _
*This change statement doesn't apparently do anything at all in the version below...*
  refine Fintype.induction_subsingleton_or_nontrivial n (fun m _ hhm T hT _ ↦ ?_)
    (fun m hm hmm H T hT hC ↦ ?_)
*This is a much more targeted approach than using the intro.*
  · obtain (hm | hm) := isEmpty_or_nonempty m
*Before I did by_cases case : Nonempty m...the above is better, because the obtain is like a have*
*followed by a rcases...*
    · simp
*apparently, this is a terminal simp! This is good to know, although I might forget later!*
    · have := uniqueOfSubsingleton (Classical.choice hm)
*What does this unique thing do?*
      simpa only [ciInf_unique, ← (Equiv.funUnique m 𝕜).symm.iSup_comp]
        using hT default |>.orthogonalComplement_iSup_eigenspaces_eq_bot
*Let's try to finally understand `simpa`, here. Here is the docs version:
simpa [rules, ⋯] using e will simplify the goal and the type of e using rules,
then try to close the goal using e.

Simplifying the type of e makes it more likely to match the goal (which has also been simplified).
This construction also tends to be more robust under changes to the simp lemma set.

simpa [rules, ⋯] will simplify the goal and the type of a hypothesis this if present in the context
then try to close the goal using the assumption tactic.

So `simpa` tries to simplify e and the goal simultaneously and then use (the simplified) `e` to
close the goal. Without specifying `e`, simpa uses the `this` hypothesis for this purpose.

So now we need to dissect

`simpa only [ciInf_unique, ← (Equiv.funUnique m 𝕜).symm.iSup_comp]`
`using hT default |>.orthogonalComplement_iSup_eigenspaces_eq_bot`

The `ciInf` is a proof that `⨅ i, s i = s default`.
The `Equiv.funUnique m K` is a proof that `(α → β) ≃ β`, i.e. the unique element of `α`
allows us to identify the arrow type with `β` via an equivalence (bijection). The `.symm`
I guess turns around the map sending `β` into this arrow type. Finally, `iSup_comp` gives
`{g : ι' → α} (e : ι ≃ ι') : ⨆ x, g (e x) = ⨆ y, g y`, so one can just sup over the elements of
`β` in this situation and doing so over the arrow type isn't necessary. I remember using this
in the original.

Ok I was being very silly. This just required applying x to default. Grr.

*
  · have i := Classical.arbitrary m
    classical
    specialize H {x // x ≠ i} (Fintype.card_subtype_lt (x := i) (by simp))
      (Subtype.restrict (· ≠ i) T) (hT ·) (hC · ·)
    simp only [Submodule.orthogonal_eq_bot_iff] at *
    rw [← (Equiv.funSplitAt i 𝕜).symm.iSup_comp, iSup_prod, iSup_comm]
    convert H with γ
    rw [← iSup_eigenspace_restrict (T i) (hT i) (iInf_eigenspace_invariant_of_commute hC i γ)]
    congr! with μ
    rw [← Module.End.genEigenspace_one, ← Submodule.inf_genEigenspace _ _ _ (k := 1), inf_comm,
      iInf_split_single _ i, iInf_subtype]
    congr! with x hx
    · simp
    · simp [dif_neg hx]

Now what is
`specialize H {x // x ≠ i} (Fintype.card_subtype_lt (x := i) (by simp))`
 `(Subtype.restrict (· ≠ i) f) (hf ·) (hC · ·)`
doing?

The `specialize` tactic should replace H with a version with a bunch of universals
instantiated.

So this is very different than the theorem before. There is no longer
an `IsSymmetric` assumption...

Worked to try to adapt Jireh's proof more or less directly. Was a useful exercise. Now, let's try
to internalize the workings of `convert` for the line `convert H with γ`

exact e and refine e require e to be defeq to the goal


-/

lemma iSup_iInf_maxGenEigenspace_eq_top_of_commute {ι K V : Type*}
    [Finite ι] [Field K] [DecidableEq K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : ι → End K V) (h : Pairwise fun i j ↦ Commute (f i) (f j))
    (h' : ∀ i, ⨆ μ, (f i).maxGenEigenspace μ = ⊤) :
    ⨆ χ : ι → K, ⨅ i, (f i).maxGenEigenspace (χ i) = ⊤ := by
  have _ := Fintype.ofFinite ι
  revert f
  refine Fintype.induction_subsingleton_or_nontrivial ι (fun m _ hhm f hf x ↦ ?_)
    (fun m hm hmm H f hf hC ↦ ?_)
  · obtain (hm | hm) := isEmpty_or_nonempty m
    · simp
    · have := uniqueOfSubsingleton (Classical.choice hm)
      simpa [ciInf_unique, ← (Equiv.funUnique m K).symm.iSup_comp] using x default
  · have i := Classical.arbitrary m
    classical
    specialize H {x // x ≠ i} (Fintype.card_subtype_lt (x := i) (by simp))
     (Subtype.restrict (· ≠ i) f) (fun _ _ _ ↦ hf <| by simpa [Subtype.coe_ne_coe]) (hC ·)
    rw [← H]
    have P1 := iInf_split_single (fun μ ↦ (fun j ↦ Module.End.maxGenEigenspace (f j) μ) i)
    simp only [ne_eq] at P1
    --rw [P1 i m]
    --Don't know what those old theorems did, but I can't access `iInf_split_single` without
    --this rewrite...












/-
What are we currently trying to do?
What was
`rw [← iSup_eigenspace_restrict (T i) (hT i) (iInf_eigenspace_invariant_of_commute hC i γ)]`?

-/



    --rw [← iSup_eigenspace_restrict (T i) (hT i) (iInf_eigenspace_invariant_of_commute hC i γ)]
    --congr! with μ
    --rw [← genEigenspace_one, ← Submodule.inf_genEigenspace _ _ _ (k := 1), inf_comm,
    --  iInf_split_single _ i, iInf_subtype]
    --congr! with x hx
    --· simp
    --· simp [dif_neg hx]
/-
This might be doable using the fintype induction on `ι`. Let's set this up and see.
So for the first bullet, `n` has either no or one element.

What does `∀ (i : n), ⨆ μ, (f i).maxGenEigenspace μ = ⊤` mean in each case?
If `n` has no elements, then what is `f i`? If `n` is the empty type, then it has
no terms of type `n`, so this is vacuously true, because it never gets off the ground.
If `n` has one element, then this says that `⨆ μ, (f i).maxGenEigenspace μ = ⊤` where `i`
is this single term of type `n`. Is there a way to do this without a case split on the
`Subsingleton` instance? Let's look around `Subsingleton` to see...
-/



end Oliver

end IsSymmetric

end LinearMap
