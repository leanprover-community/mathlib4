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

## Theorems

1. `SymmetricAlgebra.isSymmetricAlgebra R L` states that the concrete construction of the symmetric
   algebra satisfies the univeral property codified in `IsSymmetricAlgebra`.

-/

open RingQuot

universe u

variable (R L : Type*) [CommSemiring R] [AddCommMonoid L] [Module R L]

open TensorAlgebra in
/-- Relation on the tensor algebra which will yield the symmetric algebra when
quotiented out by. -/
inductive SymRel : (TensorAlgebra R L) → (TensorAlgebra R L) → Prop where
  | mul_comm (x y : L) : SymRel (ι R x * ι R y) (ι R y * ι R x)

/-- Concrete construction of the symmetric algebra of L by quotienting out
the tensor algebra by the commutativity relation. -/
abbrev SymmetricAlgebra := RingQuot (SymRel R L)

namespace SymmetricAlgebra

open TensorAlgebra in
instance : CommSemiring (SymmetricAlgebra R L) where
  mul_comm a b := match a, b with
    | ⟨a⟩, ⟨b⟩ => by
      apply Quot.ind _ a; apply Quot.ind _ b; intro a b;
      rw [mul_quot, mul_quot]
      suffices h : ∀ (x : TensorAlgebra R L),
      (⟨Quot.mk (RingQuot.Rel (SymRel R L)) (x * a)⟩ : (RingQuot (SymRel R L))) =
       ⟨Quot.mk (RingQuot.Rel (SymRel R L)) (a * x)⟩ by
        exact (h b)
      let P : TensorAlgebra R L → TensorAlgebra R L → Prop :=
       fun x y ↦ (⟨Quot.mk (RingQuot.Rel (SymRel R L)) (x * y)⟩ : (RingQuot (SymRel R L))) =
        ⟨Quot.mk (RingQuot.Rel (SymRel R L)) (y * x)⟩
      have P_smul (r : R) (x : TensorAlgebra R L) : P x (algebraMap R (TensorAlgebra R L) r) := by
        unfold P; rw [Algebra.commutes]
      have P_mul (x y z : TensorAlgebra R L) (h1 : P z x) (h2 : P z y) : P z (x * y) := by
        unfold P at h1 h2 ⊢
        rw [← mul_quot, ← mul_quot, ← mul_quot, ← mul_quot,
            ← mul_assoc, mul_quot, h1, ← mul_quot, mul_assoc, mul_quot, h2, ← mul_quot, mul_assoc]
      have P_add (x y z : TensorAlgebra R L) (h1 : P z x) (h2 : P z y) : P z (x + y) := by
        unfold P at h1 h2 ⊢
        rw [mul_add, add_mul, ← add_quot, ← add_quot, h1, h2]
      have P_symm {x y : TensorAlgebra R L} (h : P x y) : P y x := h.symm
      have P_base (x y : L) : P (ι R x) (ι R y) := by
        unfold P
        rw [Quot.sound (Rel.of (SymRel.mul_comm x y))]
      apply TensorAlgebra.induction (C := fun y ↦ ∀ (x : TensorAlgebra R L), P x y) _ _ _ _ a
      · intro r; exact P_smul r
      · intro x; apply TensorAlgebra.induction
        · intro r; exact P_symm (P_smul r (ι R x))
        · intro y; exact P_base y x
        · intro a1 a2 h1 h2; exact P_symm (P_mul a1 a2 (ι R x) (P_symm h1) (P_symm h2))
        · intro a1 a2 h1 h2; exact P_symm (P_add a1 a2 (ι R x) (P_symm h1) (P_symm h2))
      · intro a1 a2 h1 h2 x; exact P_mul a1 a2 x (h1 x) (h2 x)
      · intro a1 a2 h1 h2 x; exact P_add a1 a2 x (h1 x) (h2 x)

/-- Algebra homomorphism from the tensor algebra over L to the symmetric algebra over L. -/
abbrev algHom : TensorAlgebra R L →ₐ[R] SymmetricAlgebra R L := RingQuot.mkAlgHom R (SymRel R L)

/-- Canonical inclusion of `L` into the symmetric algebra `𝔖 R L`. -/
def ι : L →ₗ[R] SymmetricAlgebra R L := (algHom R L).toLinearMap.comp (TensorAlgebra.ι R (M := L))

variable {R L} {A : Type*} [CommSemiring A] [Algebra R A] (f : L →ₗ[R] A)

/-- For any linear map `f : L →ₗ[R] A`, `SymmetricAlgebra.lift f` lifts the linear map to an
R-algebra homomorphism from `SymmetricAlgebra R L` to `A`. -/
def lift : (SymmetricAlgebra R L) →ₐ[R] A :=
  RingQuot.liftAlgHom R (s := SymRel R L) ⟨TensorAlgebra.lift R f, fun _ _ r ↦ by
    induction r with | mul_comm x y => simp [mul_comm]⟩

@[simp]
lemma lift_ι_apply (a : L) : (lift f) ((ι R L) a) = f a := by
  simp [lift, ι, algHom]

@[simp]
lemma lift_comp_ι : (lift f) ∘ₗ (ι R L) = f := LinearMap.ext fun x ↦ lift_ι_apply f x

theorem algHom_ext {F G : (SymmetricAlgebra R L) →ₐ[R] A}
    (h : F ∘ₗ (ι R L) = (G ∘ₗ (ι R L) : L →ₗ[R] A)) : F = G := by
  ext x
  exact congr($h x)

@[simp]
lemma lift_iota : (lift (ι R L)) = AlgHom.id R (SymmetricAlgebra R L) := by
  apply algHom_ext
  rw [lift_comp]
  rfl

end SymmetricAlgebra

variable {A : Type*} [CommSemiring A] [Algebra R A] (f : L →ₗ[R] A)
variable {R} {L}

/-- Given a morphism `ι : L →ₗ[R] A`, `IsSymmetricAlgebra ι` is a proposition saying that the
algebra homomorphism from `SymmetricAlgebra R L` to `A` is bijective. -/
def IsSymmetricAlgebra (f : L →ₗ[R] A) : Prop :=
  Function.Bijective (SymmetricAlgebra.lift f)

theorem SymmetricAlgebra.isSymmetricAlgebra : IsSymmetricAlgebra (ι R L) := by
  rw [IsSymmetricAlgebra, lift_iota]
  exact Function.Involutive.bijective (congrFun rfl)

namespace IsSymmetricAlgebra

variable {f : L →ₗ[R] A} (h : IsSymmetricAlgebra f)

section equiv

/-- For `ι : L →ₗ[R] A`, construst the algebra isomorphism `(SymmetricAlgebra R L) ≃ₐ[R] A`
from `IsSymmetricAlgebra ι`. -/
noncomputable def equiv : (SymmetricAlgebra R L) ≃ₐ[R] A :=
  AlgEquiv.ofBijective (SymmetricAlgebra.lift f) h

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
lemma lift_eq (a : L) : (h.lift g) (f a) = g a := by simp [lift]

@[simp]
lemma lift_comp_linearMap : (h.lift g) ∘ₗ f = g := LinearMap.ext fun x ↦ lift_eq h g x

lemma algHom_ext (h : IsSymmetricAlgebra f) {F G : A →ₐ[R] A'}
    (hFG : (F ∘ₗ f) = (G ∘ₗ f : L →ₗ[R] A')) : F = G := by
  suffices F.comp h.equiv.toAlgHom = G.comp h.equiv.toAlgHom by
    rw [DFunLike.ext'_iff] at this ⊢
    exact h.equiv.surjective.injective_comp_right this
  refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun x ↦ ?_)
  simpa using congr($hFG x)

variable {g} in
lemma lift_unique {F : A →ₐ[R] A'} (hF : F ∘ₗ f = g) : F = (h.lift g) :=
  h.algHom_ext (by simpa)

end UniversalProperty

end IsSymmetricAlgebra
