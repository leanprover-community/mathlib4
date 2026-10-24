/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.RingTheory.HopfAlgebra.Convolution
public import Mathlib.RingTheory.HopfAlgebra.Primitive

/-!
# Constructing Hopf algebras from algebra generators

To upgrade a bialgebra to a Hopf algebra, an antipode candidate that is an anti-algebra hom
only needs to satisfy the antipode identities on an algebra-generating set.

## Main declarations

* `HopfAlgebra.ofGenerators`: construct a Hopf algebra from antipode data on an
  algebra-generating set.
* `HopfAlgebra.ofPrimitives`: construct a Hopf algebra from a primitive-element generating set.
* `HopfAlgebra.eq_antipodeAlgHomOp_of_primitives`: an anti-algebra hom that negates a
  primitive generating set is necessarily the antipode.

## References

* [D. Grinberg, V. Reiner, *Hopf algebras in combinatorics*][GrinbergReiner2020]
-/

public section

open Algebra Bialgebra Coalgebra LinearMap MulOpposite WithConv

variable {R A : Type*} [CommSemiring R]

namespace LinearMap

section ExtensionPrinciple

/-! ### Extension principle from algebra generators -/

variable [Semiring A] [Bialgebra R A] {g : A →ₗ[R] A} {s : Set A}

/-- If a unital antimultiplicative map `g` is a left convolution inverse of the identity
pointwise on an algebra-generating set, then `toConv g * toConv id = 1`. -/
theorem convMul_id_eq_one_of_adjoin_eq_top
    (g_one : g 1 = 1) (g_mul : ∀ x y, g (x * y) = g y * g x)
    (adjoin_eq_top : adjoin R s = ⊤)
    (g_convMul_id : ∀ p ∈ s,
      (toConv g * toConv (.id : A →ₗ[R] A)) p = (1 : WithConv (A →ₗ[R] A)) p) :
    toConv g * toConv id = 1 := by
  ext x; refine adjoin_le
    (S := (eqLocus (toConv g * toConv (.id : A →ₗ[R] A)).ofConv (ofConv 1)).toSubalgebra ?_
      fun a b ha hb ↦ ?_)
    g_convMul_id (adjoin_eq_top.ge mem_top)
  · simp [g_one, TensorProduct.one_def]
  let 𝓡a := ℛ R a; let 𝓡b := ℛ R b
  simp only [mem_eqLocus, 𝓡a.convMul_apply, 𝓡b.convMul_apply, convOne_apply, id_apply] at ha hb ⊢
  calc (toConv g * toConv (.id : A →ₗ[R] A)) (a * b)
      _ = ∑ p ∈ 𝓡a.index, ∑ q ∈ 𝓡b.index,
            g (𝓡b.left q) * (g (𝓡a.left p) * 𝓡a.right p) * 𝓡b.right q := by
        simp [← 𝓡a.eq, ← 𝓡b.eq, Finset.sum_mul_sum, g_mul, mul_assoc]
      _ = ∑ q ∈ 𝓡b.index, g (𝓡b.left q) * algebraMap R A (counit a) * 𝓡b.right q := by
        rw [Finset.sum_comm]; simp_rw [← Finset.sum_mul, ← Finset.mul_sum, ha]
      _ = algebraMap R A (counit (a * b)) := by
        simp_rw [← commutes, mul_assoc, ← Finset.mul_sum, hb, ← map_mul, ← Bialgebra.counit_mul]

/-- If a unital antimultiplicative map `g` is a right convolution inverse of the identity
pointwise on an algebra-generating set, then `toConv id * toConv g = 1`. -/
theorem id_convMul_eq_one_of_adjoin_eq_top
    (g_one : g 1 = 1) (g_mul : ∀ x y, g (x * y) = g y * g x)
    (adjoin_eq_top : adjoin R s = ⊤)
    (id_convMul_g : ∀ p ∈ s,
      (toConv (.id : A →ₗ[R] A) * toConv g) p = (1 : WithConv (A →ₗ[R] A)) p) :
    toConv id * toConv g = 1 := by
  ext x; refine adjoin_le
    (S := (eqLocus (toConv (.id : A →ₗ[R] A) * toConv g).ofConv (ofConv 1)).toSubalgebra ?_
      fun a b ha hb ↦ ?_)
    id_convMul_g (adjoin_eq_top.ge mem_top)
  · simp [g_one, TensorProduct.one_def]
  let 𝓡a := ℛ R a; let 𝓡b := ℛ R b
  simp only [mem_eqLocus, 𝓡a.convMul_apply, 𝓡b.convMul_apply, convOne_apply, id_apply] at ha hb ⊢
  calc (toConv (.id : A →ₗ[R] A) * toConv g) (a * b)
      _ = ∑ p ∈ 𝓡a.index, ∑ q ∈ 𝓡b.index,
            𝓡a.left p * (𝓡b.left q * g (𝓡b.right q)) * g (𝓡a.right p) := by
        simp [← 𝓡a.eq, ← 𝓡b.eq, Finset.sum_mul_sum, g_mul, mul_assoc]
      _ = ∑ p ∈ 𝓡a.index, 𝓡a.left p * algebraMap R A (counit b) * g (𝓡a.right p) := by
        simp_rw [← Finset.sum_mul, ← Finset.mul_sum, hb]
      _ = algebraMap R A (counit (a * b)) := by
        simp_rw [← commutes, mul_assoc, ← Finset.mul_sum, ha, ← map_mul, mul_comm (counit b),
          ← Bialgebra.counit_mul]

end ExtensionPrinciple

end LinearMap

namespace HopfAlgebra

section Construction
variable [Semiring A] [Bialgebra R A] {s : Set A}

/-- Build a Hopf algebra structure on a bialgebra `A` from an algebra homomorphism into
`Aᵐᵒᵖ` that is a two-sided convolution inverse of the identity at every element of an
algebra-generating set. -/
noncomputable abbrev ofGenerators (S : A →ₐ[R] Aᵐᵒᵖ) (adjoin_eq_top : adjoin R s = ⊤)
    (S_convMul_id : ∀ p ∈ s,
      (toConv ((opLinearEquiv R).symm.toLinearMap ∘ₗ S.toLinearMap) *
        toConv (.id : A →ₗ[R] A)) p = (1 : WithConv (A →ₗ[R] A)) p)
    (id_convMul_S : ∀ p ∈ s,
      (toConv (.id : A →ₗ[R] A) *
        toConv ((opLinearEquiv R).symm.toLinearMap ∘ₗ S.toLinearMap)) p =
        (1 : WithConv (A →ₗ[R] A)) p) :
    HopfAlgebra R A :=
  ofConvInverse ((opLinearEquiv R).symm.toLinearMap ∘ₗ S.toLinearMap)
    (convMul_id_eq_one_of_adjoin_eq_top (by simp) (fun _ _ ↦ by simp) adjoin_eq_top
      S_convMul_id)
    (id_convMul_eq_one_of_adjoin_eq_top (by simp) (fun _ _ ↦ by simp) adjoin_eq_top
      id_convMul_S)

end Construction

section Primitives
variable [Ring A] {s : Set A}

/-- Upgrade a bialgebra generated by primitive elements to a Hopf algebra by specifying the
antipode-on-generators formula `S p = op (-p)`. -/
noncomputable abbrev ofPrimitives [Bialgebra R A] (S : A →ₐ[R] Aᵐᵒᵖ)
    (adjoin_eq_top : adjoin R s = ⊤) (prim : ∀ p ∈ s, IsPrimitiveElem R p)
    (S_apply : ∀ p ∈ s, S p = op (-p)) : HopfAlgebra R A := by
  refine ofGenerators S adjoin_eq_top ?_ ?_ <;> intro p hp <;>
    simp [convMul_apply, (prim p hp).comul_eq_tmul_add_tmul, (prim p hp).counit_eq_zero,
      S_apply p hp]

/-- An anti-algebra hom on a Hopf algebra that negates a primitive algebra-generating set is
the antipode. See the remark following Proposition 1.4.17 in [GrinbergReiner2020]. -/
theorem eq_antipodeAlgHomOp_of_primitives [HopfAlgebra R A] (S : A →ₐ[R] Aᵐᵒᵖ)
    (adjoin_eq_top : adjoin R s = ⊤) (prim : ∀ p ∈ s, IsPrimitiveElem R p)
    (S_apply : ∀ p ∈ s, S p = op (-p)) : S = antipodeAlgHomOp R A :=
  AlgHom.ext_of_adjoin_eq_top adjoin_eq_top fun p hp ↦ by
    simp [S_apply p hp, (prim p hp).antipode_eq_neg]

end Primitives

end HopfAlgebra
