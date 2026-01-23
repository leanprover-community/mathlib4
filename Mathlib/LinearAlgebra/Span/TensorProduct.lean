/-
Copyright (c) 2026 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Algebra.Epi
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.Flat.Basic

/-!
# The interaction of linear span and tensor product for mixed scalars.
-/

@[expose] public section

open Function TensorProduct

namespace Submodule

variable {R : Type*} (A : Type*) {M : Type*}

section CommSemiring

variable [CommSemiring R] [CommSemiring A] [Algebra R A]
  [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]
  (p : Submodule R M)

/-- If `A` is an `R`-algebra and `p` is an `R`-submodule of an `A`-module `M`, this is the natural
surjection `A ⊗[R] p → span A p`.

See also `Submodule.tensorEquivSpan`. -/
def tensorToSpan : A ⊗[R] p →ₗ[A] span A (p : Set M) :=
  AlgebraTensorModule.lift
    { toFun a := a • p.inclusionSpan A
      map_add' a b := add_smul a b _
      map_smul' a b := smul_assoc a b _ }

@[simp] lemma tensorToSpan_apply_tmul (a : A) (x : p) :
    p.tensorToSpan A (a ⊗ₜ x) = a • (x : M) :=
  rfl

lemma surjective_tensorToSpan : Surjective (p.tensorToSpan A) := by
  intro v
  obtain ⟨f, hf⟩ := (Finsupp.mem_span_iff_linearCombination _ _ _).mp v.property
  use f.sum fun x a ↦ a ⊗ₜ x
  rw [map_finsuppSum, Subtype.ext_iff, ← Submodule.subtype_apply, map_finsuppSum]
  simpa using hf

variable [Algebra.IsEpi R A] [Module.Flat R A]

open Module.Flat LinearMap in
lemma injective_tensorToSpan : Injective (p.tensorToSpan A) := by
  let f : A ⊗[R] (span A (p : Set M)) →ₗ[A] span A (p : Set M) :=
    AlgebraTensorModule.lift <| (restrictScalarsₗ R A _ _ A) ∘ₗ lsmul A (span A (p : Set M))
  let g : A ⊗[R] p →ₗ[R] A ⊗[R] span A (p : Set M) := (p.inclusionSpan A).lTensor A
  have hf : Injective f := Algebra.injective_lift_lsmul R A _
  have hg : Injective g := lTensor_preserves_injective_linearMap _ (p.injective_inclusionSpan A)
  have : p.tensorToSpan A = f.restrictScalars R ∘ₗ g := by ext; simp [tensorToSpan, f, g]
  rw [← LinearMap.coe_restrictScalars R, this, coe_comp]
  exact hf.comp hg

/-- If `A` is a flat epi `R`-algebra and `p` is an `R`-submodule of an `A`-module `M` then the
natural surjection from `A ⊗[R] p` to `span A p` is an equivalence. -/
noncomputable def tensorEquivSpan : A ⊗[R] p ≃ₗ[A] span A (p : Set M) :=
  .ofBijective (p.tensorToSpan A) ⟨p.injective_tensorToSpan A, p.surjective_tensorToSpan A⟩

@[simp] lemma tensorEquivSpan_apply_tmul (a : A) (x : p) :
    p.tensorEquivSpan A (a ⊗ₜ x) = a • (x : M) :=
  rfl

variable (R) in
/-- If `A` is a flat epi `R`-algebra and `s` is a subset of an `A`-module `M` then the natural
surjection from `A ⊗[R] span R s` to `span A s` is an equivalence. -/
noncomputable def tensorSpanEquivSpan (s : Set M) : A ⊗[R] span R s ≃ₗ[A] span A s :=
  ((span R s).tensorEquivSpan A).trans <| .ofEq _ _ <| span_span_of_tower R A s

@[simp] lemma coe_tensorSpanEquivSpan_apply_tmul {s : Set M} (a : A) (x : span R s) :
    tensorSpanEquivSpan R A s (a ⊗ₜ x) = a • (x : M) :=
  rfl

end CommSemiring

section CommRing

open Module

variable [CommRing R] [CommRing A] [Nontrivial A]
  [Algebra R A] [Algebra.IsEpi R A] [Module.Flat R A]
  [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
  (p : Submodule R M) [Free R p] [Module.Finite R p]

@[simp] lemma finrank_span_eq_finrank :
    finrank A (span A (p : Set M)) = finrank R p := by
  rcases subsingleton_or_nontrivial R; · simp [Algebra.subsingleton R A]
  let ι := Free.ChooseBasisIndex R p
  let b₁ : Basis ι R p := Free.chooseBasis R p
  let b₂ : Basis ι A (span A (p : Set M)) := (b₁.baseChange A).map <| p.tensorEquivSpan A
  rw [finrank_eq_card_basis b₁, finrank_eq_card_basis b₂]

variable (R) in
lemma finrank_span_eq_finrank_span [IsPrincipalIdealRing R] [IsDomain R] [IsTorsionFree R M]
    (s : Set M) [Module.Finite R (span R s)] :
    finrank A (span A s) = finrank R (span R s) := by
  rw [← span_span_of_tower R, finrank_span_eq_finrank]

end CommRing

end Submodule
