/-
Copyright (c) 2025 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles, Zhixuan Dai, Zhenyan Fu, Yiming Fu, Jingting Wang, Eric Wieser
-/
import Mathlib.LinearAlgebra.TensorAlgebra.Basic

/-!
# Symmetric Algebras

Given a commutative semiring `R`, and an `R`-module `M`, we construct the symmetric algebra of `M`.
This is the free commutative `R`-algebra generated (`R`-linearly) by the module `M`.

## Notation

* `SymmetricAlgebra R M`: a concrete construction of the symmetric algebra defined as a
  quotient of the tensor algebra. It is endowed with an R-algebra structure and a commutative
  ring structure.
* `SymmetricAlgebra.ι R`: the canonical R-linear map `M →ₗ[R] SymmetricAlgebra R M`.

## Note

See `SymAlg R` instead if you are looking for the symmetrized algebra, which gives a commutative
multiplication on `R` by $a \circ b = \frac{1}{2}(ab + ba)$.
-/

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
  | algebraMap r => rw [AlgHom.commutes]; exact algebraMap r
  | ι x => exact ι x
  | mul x y hx hy => rw [map_mul]; exact mul _ _ hx hy
  | add x y hx hy => rw [map_add]; exact add _ _ hx hy

open TensorAlgebra in
instance : CommSemiring (SymmetricAlgebra R M) where
  mul_comm a b := by
    show Commute a b
    induction b using SymmetricAlgebra.induction with
    | algebraMap r => exact Algebra.commute_algebraMap_right _ _
    | ι x => induction a using SymmetricAlgebra.induction with
      | algebraMap r => exact Algebra.commute_algebraMap_left _ _
      | ι y => simp [commute_iff_eq, ι, ← map_mul, RingQuot.mkAlgHom_rel _ (SymRel.mul_comm x y)]
      | mul a b ha hb => exact ha.mul_left hb
      | add a b ha hb => exact ha.add_left hb
    | mul b c hb hc => exact hb.mul_right hc
    | add b c hb hc => exact hb.add_right hc

instance (R M) [CommRing R] [AddCommMonoid M] [Module R M] : CommRing (SymmetricAlgebra R M) where
  __ := inferInstanceAs (CommSemiring (SymmetricAlgebra R M))
  __ := inferInstanceAs (Ring (RingQuot (SymRel R M)))

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

@[ext]
theorem algHom_ext {F G : SymmetricAlgebra R M →ₐ[R] A}
    (h : F ∘ₗ ι R M = (G ∘ₗ ι R M : M →ₗ[R] A)) : F = G := by
  ext x
  exact congr($h x)

@[simp]
lemma lift_ι : lift (ι R M) = .id R (SymmetricAlgebra R M) := by
  apply algHom_ext
  rw [lift_comp_ι]
  ext
  simp

/-- The left-inverse of `algebraMap`. -/
def algebraMapInv : SymmetricAlgebra R M →ₐ[R] R :=
  lift (0 : M →ₗ[R] R)

variable (M)

theorem algebraMap_leftInverse :
    Function.LeftInverse algebraMapInv (algebraMap R <| SymmetricAlgebra R M) := fun x => by
  simp [algebraMapInv]

@[simp]
theorem algebraMap_inj (x y : R) :
    algebraMap R (SymmetricAlgebra R M) x = algebraMap R (SymmetricAlgebra R M) y ↔ x = y :=
  (algebraMap_leftInverse M).injective.eq_iff

@[simp]
theorem algebraMap_eq_zero_iff (x : R) : algebraMap R (SymmetricAlgebra R M) x = 0 ↔ x = 0 :=
  map_eq_zero_iff (algebraMap _ _) (algebraMap_leftInverse _).injective

@[simp]
theorem algebraMap_eq_one_iff (x : R) : algebraMap R (SymmetricAlgebra R M) x = 1 ↔ x = 1 :=
  map_eq_one_iff (algebraMap _ _) (algebraMap_leftInverse _).injective

/-- A `SymmetricAlgebra` over a nontrivial semiring is nontrivial. -/
instance [Nontrivial R] : Nontrivial (SymmetricAlgebra R M) :=
  (algebraMap_leftInverse M).injective.nontrivial

end SymmetricAlgebra
