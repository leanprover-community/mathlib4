/-
Copyright (c) 2025 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles, Zhixuan Dai, Zhenyan Fu, Yiming Fu, Jingting Wang
-/
import Mathlib.LinearAlgebra.TensorAlgebra.Basic

/-!
# Symmetric Algebras

Given a commutative semiring `R`, and an `R`-module `M`, we construct the symmetric algebra of `M`.
This is the free commutative `R`-algebra generated (`R`-linearly) by the module `M`.

## Notation

1. `SymmetricAlgebra R M` is a concrete construction of the symmetric algebra defined as a
   quotient of the tensor algebra. It is endowed with an R-algebra structure and a commutative
   ring structure.
2. `SymmetricAlgebra.ι R` is the canonical R-linear map `M →ₗ[R] SymmetricAlgebra R M`.
3. Given a morphism `ι : M →ₗ[R] A`, `IsSymmetricAlgebra ι` is a proposition saying that the algebra
   homomorphism from `SymmetricAlgebra R M` to `A` lifted from `ι` is bijective.
4. Given a linear map `f : M →ₗ[R] A'` to an commutative R-algebra `A'`, and a morphism
   `ι : M →ₗ[R] A` with `p : IsSymmetricAlgebra ι`, `IsSymmetricAlgebra.lift p f`
   is the lift of `f` to an `R`-algebra morphism `A →ₐ[R] A'`.

## Note

See `SymAlg R` instead if you are looking for the symmetrized algebra, which gives a commutative
multiplication on `R` by $a \circ b = \frac{1}{2}(ab + ba)$.
-/

universe u

variable (R M : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- Relation on the tensor algebra which will yield the symmetric algebra when
quotiented out by. -/
inductive TensorAlgebra.SymRel : TensorAlgebra R M → TensorAlgebra R M → Prop where
  | mul_comm (x y : M) : SymRel (ι R x * ι R y) (ι R y * ι R x)

open TensorAlgebra

/-- Concrete construction of the symmetric algebra of `M` by quotienting out
the tensor algebra by the commutativity relation. -/
abbrev SymmetricAlgebra := RingQuot (SymRel R M)

namespace SymmetricAlgebra

/-- Algebra homomorphism from the tensor algebra over `M` to the symmetric algebra over `M`. -/
abbrev algHom : TensorAlgebra R M →ₐ[R] SymmetricAlgebra R M := RingQuot.mkAlgHom R (SymRel R M)

lemma algHom_surjective : Function.Surjective (algHom R M) :=
  RingQuot.mkAlgHom_surjective _ _

/-- Canonical inclusion of `M` into the symmetric algebra `SymmetricAlgebra R M`. -/
def ι : M →ₗ[R] SymmetricAlgebra R M := algHom R M ∘ₗ TensorAlgebra.ι R

@[elab_as_elim]
theorem induction {motive : SymmetricAlgebra R M → Prop}
    (algebraMap : ∀ r, motive (algebraMap R (SymmetricAlgebra R M) r)) (ι : ∀ x, motive (ι R M x))
    (mul : ∀ a b, motive a → motive b → motive (a * b))
    (add : ∀ a b, motive a → motive b → motive (a + b))
    (a : SymmetricAlgebra R M) : motive a := by
  rcases algHom_surjective _ _ a with ⟨a, rfl⟩
  induction a using TensorAlgebra.induction with
  | algebraMap r => rw [AlgHom.map_algebraMap]; exact algebraMap r
  | ι x => exact ι x
  | mul x y hx hy => rw [map_mul]; exact mul _ _ hx hy
  | add x y hx hy => rw [map_add]; exact add _ _ hx hy

open TensorAlgebra in
instance : CommSemiring (SymmetricAlgebra R M) where
  mul_comm a b := by
    have ι_commute (x y : M) : Commute (ι R M x) (ι R M y) := by
      simp [commute_iff_eq, ι, ← map_mul, RingQuot.mkAlgHom_rel _ (SymRel.mul_comm x y)]
    change Commute a b
    induction b using SymmetricAlgebra.induction with
    | algebraMap r => exact Algebra.commute_algebraMap_right _ _
    | ι x => induction a using SymmetricAlgebra.induction with
      | algebraMap r => exact Algebra.commute_algebraMap_left _ _
      | ι y => exact ι_commute _ _
      | mul a b ha hb => exact ha.mul_left hb
      | add a b ha hb => exact ha.add_left hb
    | mul b c hb hc => exact hb.mul_right hc
    | add b c hb hc => exact hb.add_right hc

variable {R M} {A : Type*} [CommSemiring A] [Algebra R A]

/-- For any linear map `f : M →ₗ[R] A`, `SymmetricAlgebra.lift f` lifts the linear map to an
R-algebra homomorphism from `SymmetricAlgebra R M` to `A`. -/
def lift : (M →ₗ[R] A) ≃ (SymmetricAlgebra R M →ₐ[R] A) := by
  let equiv : (TensorAlgebra R M →ₐ[R] A) ≃
    {f : TensorAlgebra R M →ₐ[R] A // ∀ {x y}, (TensorAlgebra.SymRel R M) x y → f x = f y} := by
    refine (Equiv.subtypeUnivEquiv fun h _ _ h' ↦ ?_).symm
    induction h' with | mul_comm x y => rw [map_mul, map_mul, mul_comm]
  exact (TensorAlgebra.lift R).trans <| equiv.trans <| RingQuot.liftAlgHom R

variable (f : M →ₗ[R] A)

@[simp]
lemma lift_ι_apply (a : M) : lift f (ι R M a) = f a := by
  simp [lift, ι, algHom]

@[simp]
lemma lift_comp_ι : lift f ∘ₗ ι R M = f := LinearMap.ext <| lift_ι_apply f

theorem algHom_ext {F G : SymmetricAlgebra R M →ₐ[R] A}
    (h : F ∘ₗ ι R M = (G ∘ₗ ι R M : M →ₗ[R] A)) : F = G := by
  ext x
  exact congr($h x)

@[simp]
lemma lift_ι : lift (ι R M) = .id R (SymmetricAlgebra R M) := by
  apply algHom_ext
  rw [lift_comp_ι]
  rfl

end SymmetricAlgebra

variable {A : Type*} [CommSemiring A] [Algebra R A] (f : M →ₗ[R] A)
variable {R} {M}

/-- Given a morphism `ι : M →ₗ[R] A`, `IsSymmetricAlgebra ι` is a proposition saying that the
algebra homomorphism from `SymmetricAlgebra R M` to `A` is bijective. -/
def IsSymmetricAlgebra (f : M →ₗ[R] A) : Prop :=
  Function.Bijective (SymmetricAlgebra.lift f)

theorem SymmetricAlgebra.isSymmetricAlgebra_ι : IsSymmetricAlgebra (ι R M) := by
  rw [IsSymmetricAlgebra, lift_ι]
  exact Function.Involutive.bijective (congrFun rfl)

namespace IsSymmetricAlgebra

variable {f : M →ₗ[R] A} (h : IsSymmetricAlgebra f)

section equiv

/-- For `ι : M →ₗ[R] A`, construst the algebra isomorphism `SymmetricAlgebra R M ≃ₐ[R] A`
from `IsSymmetricAlgebra ι`. -/
noncomputable def equiv : SymmetricAlgebra R M ≃ₐ[R] A :=
  .ofBijective (SymmetricAlgebra.lift f) h

@[simp]
lemma equiv_apply (a : SymmetricAlgebra R M) : h.equiv a = SymmetricAlgebra.lift f a := rfl

@[simp]
lemma equiv_toAlgHom : h.equiv = SymmetricAlgebra.lift f := rfl

@[simp]
lemma equiv_symm_apply (a : M) : h.equiv.symm (f a) = SymmetricAlgebra.ι R M a :=
  h.equiv.injective (by simp)

@[simp]
lemma equiv_symm_comp : h.equiv.symm ∘ₗ f = SymmetricAlgebra.ι R M :=
  LinearMap.ext fun x ↦ equiv_symm_apply h x

end equiv

section UniversalProperty

variable {A' : Type*} [CommSemiring A'] [Algebra R A'] (g : M →ₗ[R] A')

/-- Given a morphism `φ : M →ₗ[R] A'`, lift this to a morphism of type `A →ₐ[R] A'` (where `A`
satisfies the universal property of the symmetric algebra of `M`) -/
noncomputable def lift : A →ₐ[R] A' := (SymmetricAlgebra.lift g).comp h.equiv.symm

@[simp]
lemma lift_eq (a : M) : h.lift g (f a) = g a := by simp [lift]

@[simp]
lemma lift_comp_linearMap : h.lift g ∘ₗ f = g := LinearMap.ext <| lift_eq h g

lemma algHom_ext (h : IsSymmetricAlgebra f) {F G : A →ₐ[R] A'}
    (hFG : F ∘ₗ f = (G ∘ₗ f : M →ₗ[R] A')) : F = G := by
  suffices F.comp h.equiv.toAlgHom = G.comp h.equiv.toAlgHom by
    rw [DFunLike.ext'_iff] at this ⊢
    exact h.equiv.surjective.injective_comp_right this
  refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun x ↦ ?_)
  simpa using congr($hFG x)

variable {g} in
lemma lift_unique {F : A →ₐ[R] A'} (hF : F ∘ₗ f = g) : F = h.lift g :=
  h.algHom_ext (by simpa)

end UniversalProperty

end IsSymmetricAlgebra
