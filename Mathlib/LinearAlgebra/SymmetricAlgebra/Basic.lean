/-
Copyright (c) 2025 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles, Zhixuan Dai, Zhenyan Fu, Yiming Fu, Jingting Wang
-/
import Mathlib.LinearAlgebra.TensorAlgebra.Basic

/-!
# Symmetric Algebras

Given a commutative semiring `R`, and an `R`-module `L`, we construct the symmetric algebra of `L`.
This is the free commutative `R`-algebra generated (`R`-linearly) by the module `L`.

## Notation

1. `SymmetricAlgebra R L` is a concrete construction of the symmetric algebra defined as a
   quotient of the tensor algebra. It is endowed with an R-algebra structure and a commutative
   ring structure.
2. `SymmetricAlgebra.ι R` is the canonical R-linear map `L → TensorAlgebra R L`.
3. Given a morphism `ι : L →ₗ[R] A`, `IsSymmetricAlgebra ι` is a proposition saying that the algebra
   homomorphism from `SymmetricAlgebra R L` to `A` is bijective.
4. Given a linear map `f : L →ₗ[R] A'` to an commutative R-algebra `A'`, and a morphism
   `ι : L →ₗ[R] A` with `p : IsSymmetricAlgebra ι`, `IsSymmetricAlgebra.lift p f`
   is the lift of `f` to an `R`-algebra morphism `A →ₐ[R] A'`.

-/

open RingQuot

universe u

variable (R L : Type*) [CommSemiring R] [AddCommMonoid L] [Module R L]

open TensorAlgebra in
/-- Relation on the tensor algebra which will yield the symmetric algebra when
quotiented out by. -/
inductive SymRel : TensorAlgebra R L → TensorAlgebra R L → Prop where
  | mul_comm (x y : L) : SymRel (ι R x * ι R y) (ι R y * ι R x)

/-- Concrete construction of the symmetric algebra of L by quotienting out
the tensor algebra by the commutativity relation. -/
abbrev SymmetricAlgebra := RingQuot (SymRel R L)

namespace SymmetricAlgebra

/-- Algebra homomorphism from the tensor algebra over L to the symmetric algebra over L. -/
abbrev algHom : TensorAlgebra R L →ₐ[R] SymmetricAlgebra R L := RingQuot.mkAlgHom R (SymRel R L)

lemma algHom_surjective : Function.Surjective (algHom R L) :=
  RingQuot.mkAlgHom_surjective _ _

/-- Canonical inclusion of `L` into the symmetric algebra `𝔖 R L`. -/
def ι : L →ₗ[R] SymmetricAlgebra R L := (algHom R L).toLinearMap.comp (TensorAlgebra.ι R (M := L))

@[elab_as_elim]
theorem induction {motive : SymmetricAlgebra R L → Prop}
    (algebraMap : ∀ r, motive (algebraMap R (SymmetricAlgebra R L) r)) (ι : ∀ x, motive (ι R L x))
    (mul : ∀ a b, motive a → motive b → motive (a * b))
    (add : ∀ a b, motive a → motive b → motive (a + b))
    (a : SymmetricAlgebra R L) : motive a := by
  rcases algHom_surjective _ _ a with ⟨a, rfl⟩
  induction a using TensorAlgebra.induction with
  | algebraMap r => rw [AlgHom.map_algebraMap]; exact algebraMap r
  | ι x => exact ι x
  | mul x y hx hy => rw [map_mul]; exact mul _ _ hx hy
  | add x y hx hy => rw [map_add]; exact add _ _ hx hy

open TensorAlgebra in
instance : CommSemiring (SymmetricAlgebra R L) where
  mul_comm a b := by
    have ι_commute (x y : L) : Commute (ι R L x) (ι R L y) := by
      simp [commute_iff_eq, ι, ← map_mul, mkAlgHom_rel _ (SymRel.mul_comm x y)]
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

variable {R L} {A : Type*} [CommSemiring A] [Algebra R A] (f : L →ₗ[R] A)

/-- For any linear map `f : L →ₗ[R] A`, `SymmetricAlgebra.lift f` lifts the linear map to an
R-algebra homomorphism from `SymmetricAlgebra R L` to `A`. -/
def lift : SymmetricAlgebra R L →ₐ[R] A :=
  RingQuot.liftAlgHom R (s := SymRel R L) ⟨TensorAlgebra.lift R f, fun _ _ r ↦ by
    induction r with | mul_comm x y => simp [mul_comm]⟩

@[simp]
lemma lift_ι_apply (a : L) : lift f (ι R L a) = f a := by
  simp [lift, ι, algHom]

@[simp]
lemma lift_comp_ι : lift f ∘ₗ ι R L = f := LinearMap.ext <| lift_ι_apply f

theorem algHom_ext {F G : SymmetricAlgebra R L →ₐ[R] A}
    (h : F ∘ₗ ι R L = (G ∘ₗ ι R L : L →ₗ[R] A)) : F = G := by
  ext x
  exact congr($h x)

@[simp]
lemma lift_ι : (lift (ι R L)) = AlgHom.id R (SymmetricAlgebra R L) := by
  apply algHom_ext
  rw [lift_comp_ι]
  rfl

end SymmetricAlgebra

variable {A : Type*} [CommSemiring A] [Algebra R A] (f : L →ₗ[R] A)
variable {R} {L}

/-- Given a morphism `ι : L →ₗ[R] A`, `IsSymmetricAlgebra ι` is a proposition saying that the
algebra homomorphism from `SymmetricAlgebra R L` to `A` is bijective. -/
def IsSymmetricAlgebra (f : L →ₗ[R] A) : Prop :=
  Function.Bijective (SymmetricAlgebra.lift f)

theorem SymmetricAlgebra.isSymmetricAlgebra_ι : IsSymmetricAlgebra (ι R L) := by
  rw [IsSymmetricAlgebra, lift_ι]
  exact Function.Involutive.bijective (congrFun rfl)

namespace IsSymmetricAlgebra

variable {f : L →ₗ[R] A} (h : IsSymmetricAlgebra f)

section equiv

/-- For `ι : L →ₗ[R] A`, construst the algebra isomorphism `(SymmetricAlgebra R L) ≃ₐ[R] A`
from `IsSymmetricAlgebra ι`. -/
noncomputable def equiv : SymmetricAlgebra R L ≃ₐ[R] A :=
  .ofBijective (SymmetricAlgebra.lift f) h

@[simp]
lemma equiv_apply (a : SymmetricAlgebra R L) : h.equiv a = SymmetricAlgebra.lift f a := rfl

@[simp]
lemma equiv_toAlgHom : h.equiv = SymmetricAlgebra.lift f := rfl

@[simp]
lemma equiv_symm_apply (a : L) : h.equiv.symm (f a) = SymmetricAlgebra.ι R L a :=
  h.equiv.injective (by simp)

@[simp]
lemma equiv_symm_comp : h.equiv.symm ∘ₗ f = SymmetricAlgebra.ι R L :=
  LinearMap.ext fun x ↦ equiv_symm_apply h x

end equiv

section UniversalProperty

variable {A' : Type*} [CommSemiring A'] [Algebra R A'] (g : L →ₗ[R] A')

/-- Given a morphism `φ : L →ₗ[R] A'`, lift this to a morphism of type `A →ₐ[R] A'` (where `A`
satisfies the universal property of the symmetric algebra of `L`) -/
noncomputable def lift : A →ₐ[R] A' := (SymmetricAlgebra.lift g).comp h.equiv.symm

@[simp]
lemma lift_eq (a : L) : h.lift g (f a) = g a := by simp [lift]

@[simp]
lemma lift_comp_linearMap : h.lift g ∘ₗ f = g := LinearMap.ext <| lift_eq h g

lemma algHom_ext (h : IsSymmetricAlgebra f) {F G : A →ₐ[R] A'}
    (hFG : F ∘ₗ f = (G ∘ₗ f : L →ₗ[R] A')) : F = G := by
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
