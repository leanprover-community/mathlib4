/-
Copyright (c) 2024 Ali Ramsey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ali Ramsey
-/
module

public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.Coalgebra.Convolution

/-!
# Hopf algebras

In this file we define `HopfAlgebra`, and provide instances for:

* Commutative semirings: `CommSemiring.toHopfAlgebra`

## Main definitions

* `HopfAlgebra R A` : the Hopf algebra structure on an `R`-bialgebra `A`.
* `HopfAlgebra.antipode` : the `R`-linear map `A →ₗ[R] A`.
* `HopfAlgebra.IsRTensorAntipodeAt`, `HopfAlgebra.IsLTensorAntipodeAt` :
  the antipode axioms evaluated at a single element, for a candidate antipode `S : A →ₐ[R] Aᵐᵒᵖ`.

## Main results

* `HopfAlgebra.antipode_one` : the antipode of the unit is the unit.
* `HopfAlgebra.antipode_mul` : the antipode is an antihomomorphism: `S(ab) = S(b)S(a)`.
* `HopfAlgebra.mul_rTensor_comul_eq_of_adjoin_eq_top`,
  `HopfAlgebra.mul_lTensor_comul_eq_of_adjoin_eq_top` : a candidate antipode `S : A →ₐ[R] Aᵐᵒᵖ`
  satisfies the antipode axioms on all of `A` if it does so on an algebra-generating subset.

## TODO

* Uniqueness of Hopf algebra structure on a bialgebra (i.e. if the algebra and coalgebra structures
  agree then the antipodes must also agree).

* If `A` is commutative then `antipode` is an algebra homomorphism.

* If `A` is commutative then `antipode` is necessarily a bijection and its square is
  the identity.

(Note that all three facts have been proved for Hopf bimonoids in an arbitrary braided category,
so we could deduce the facts here from an equivalence `HopfAlgCat R ≌ Hopf (ModuleCat R)`.)

## References

* <https://en.wikipedia.org/wiki/Hopf_algebra>

* [C. Kassel, *Quantum Groups* (§III.3)][Kassel1995]


-/

public section

open Bialgebra

universe u v w

/-- Isolates the antipode of a Hopf algebra, to allow API to be constructed before proving the
Hopf algebra axioms. See `HopfAlgebra` for documentation. -/
class HopfAlgebraStruct (R : Type u) (A : Type v) [CommSemiring R] [Semiring A]
    extends Bialgebra R A where
  /-- The antipode of the Hopf algebra. -/
  antipode (R) : A →ₗ[R] A

/-- A Hopf algebra over a commutative (semi)ring `R` is a bialgebra over `R` equipped with an
`R`-linear endomorphism `antipode` satisfying the antipode axioms. -/
class HopfAlgebra (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] extends
    HopfAlgebraStruct R A where
  /-- One of the antipode axioms for a Hopf algebra. -/
  mul_antipode_rTensor_comul :
    LinearMap.mul' R A ∘ₗ antipode.rTensor A ∘ₗ comul = (Algebra.linearMap R A) ∘ₗ counit
  /-- One of the antipode axioms for a Hopf algebra. -/
  mul_antipode_lTensor_comul :
    LinearMap.mul' R A ∘ₗ antipode.lTensor A ∘ₗ comul = (Algebra.linearMap R A) ∘ₗ counit

namespace HopfAlgebra

export HopfAlgebraStruct (antipode)

variable {R : Type u} {A : Type v} [CommSemiring R] [Semiring A] [HopfAlgebra R A] {a : A}

@[simp]
theorem mul_antipode_rTensor_comul_apply (a : A) :
    LinearMap.mul' R A ((antipode R).rTensor A (Coalgebra.comul a)) =
    algebraMap R A (Coalgebra.counit a) :=
  LinearMap.congr_fun mul_antipode_rTensor_comul a

@[simp]
theorem mul_antipode_lTensor_comul_apply (a : A) :
    LinearMap.mul' R A ((antipode R).lTensor A (Coalgebra.comul a)) =
    algebraMap R A (Coalgebra.counit a) :=
  LinearMap.congr_fun mul_antipode_lTensor_comul a

@[simp]
theorem antipode_one :
    HopfAlgebra.antipode R (1 : A) = 1 := by
  simpa [Algebra.TensorProduct.one_def] using mul_antipode_rTensor_comul_apply (R := R) (1 : A)

open Coalgebra

lemma sum_antipode_mul_eq_algebraMap_counit (repr : Repr R a) :
    ∑ i ∈ repr.index, antipode R (repr.left i) * repr.right i =
      algebraMap R A (counit a) := by
  simpa [← repr.eq, map_sum] using congr($(mul_antipode_rTensor_comul (R := R)) a)

lemma sum_mul_antipode_eq_algebraMap_counit (repr : Repr R a) :
    ∑ i ∈ repr.index, repr.left i * antipode R (repr.right i) =
      algebraMap R A (counit a) := by
  simpa [← repr.eq, map_sum] using congr($(mul_antipode_lTensor_comul (R := R)) a)

lemma sum_antipode_mul_eq_smul (repr : Repr R a) :
    ∑ i ∈ repr.index, antipode R (repr.left i) * repr.right i =
      counit (R := R) a • 1 := by
  rw [sum_antipode_mul_eq_algebraMap_counit, Algebra.smul_def, mul_one]

lemma sum_mul_antipode_eq_smul (repr : Repr R a) :
    ∑ i ∈ repr.index, repr.left i * antipode R (repr.right i) =
      counit (R := R) a • 1 := by
  rw [sum_mul_antipode_eq_algebraMap_counit, Algebra.smul_def, mul_one]

@[simp] lemma counit_antipode (a : A) : counit (R := R) (antipode R a) = counit a := by
  calc
        counit (antipode R a)
    _ = counit (∑ i ∈ (ℛ R a).index, (ℛ R a).left i * antipode R ((ℛ R a).right i)) := by
      simp_rw [map_sum, counit_mul, ← smul_eq_mul, ← map_smul, ← map_sum, sum_counit_smul]
    _ = counit a := by simpa using congr(counit (R := R) $(sum_mul_antipode_eq_smul (ℛ R a)))

@[simp] lemma counit_comp_antipode : counit ∘ₗ antipode R = counit (A := A) := by
  ext; exact counit_antipode _

/-! ### The antipode is an antihomomorphism

We prove that `antipode (a * b) = antipode b * antipode a`. The proof uses the "left inverse
equals right inverse" trick in the convolution algebra `(A ⊗ A) →ₗ[R] A`.
-/

open scoped TensorProduct
open WithConv

/-- The antipode reverses multiplication: `S(ab) = S(b)S(a)`. -/
theorem antipode_mul (a b : A) :
    antipode R (a * b) = antipode R b * antipode R a := by
  -- We show that the linear maps `S ∘ μ` and `μ ∘ (S ⊗ S) ∘ comm` are equal,
  -- by proving they are both convolution inverses of `μ`.
  suffices h : antipode R ∘ₗ LinearMap.mul' R A =
      LinearMap.mul' R A ∘ₗ TensorProduct.map (antipode R) (antipode R) ∘ₗ
        TensorProduct.comm R A A by
    exact congr(($h) (a ⊗ₜ b))
  -- Use `left_inv_eq_right_inv` in the convolution algebra `WithConv ((A ⊗ A) →ₗ[R] A)`.
  refine toConv_injective
    (left_inv_eq_right_inv
      (b := toConv (antipode R ∘ₗ LinearMap.mul' R A))
      (a := toConv (LinearMap.mul' R A))
      (c := toConv (LinearMap.mul' R A ∘ₗ TensorProduct.map (antipode R) (antipode R) ∘ₗ
        TensorProduct.comm R A A))
      ?_ ?_)
  · -- Left inverse: `(S ∘ μ) * μ = 1`.
    refine WithConv.ext (TensorProduct.ext' fun x y => ?_)
    -- Unfold convolution product: `(f * g)(x ⊗ y) = μ(f ⊗ g)(Δ(x ⊗ y))`.
    simp only [LinearMap.convMul_apply, LinearMap.convOne_apply]
    -- The coalgebra on `A ⊗ A: Δ(x ⊗ y) = σ (Δx ⊗ Δy)` where `σ = tensorTensorTensorComm`.
    rw [TensorProduct.comul_tmul]
    -- Use Sweedler representations for `x` and `y`.
    let ℛx := ℛ R x; let ℛy := ℛ R y
    conv_lhs => rw [← ℛx.eq, ← ℛy.eq]
    simp only [TensorProduct.sum_tmul, TensorProduct.tmul_sum, map_sum,
      TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul, TensorProduct.map_tmul,
      LinearMap.mul'_apply, LinearMap.comp_apply]
    rw [Finset.sum_comm]
    -- The counit on `A ⊗ A`: `ε(x ⊗ y) = ε(y) • ε(x) = ε(x)ε(y)` since `R` is commutative.
    simp only [TensorProduct.counit_tmul, Algebra.algebraMap_eq_smul_one]
    -- Use the bialgebra comultiplication axiom: `Δ(xy) = Δ(x)Δ(y)`.
    have key := mul_antipode_rTensor_comul_apply (R := R) (x * y)
    rw [Bialgebra.comul_mul, ← ℛx.eq, ← ℛy.eq] at key
    simp only [Finset.sum_mul, Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul,
      map_sum, LinearMap.rTensor_tmul, LinearMap.mul'_apply, Bialgebra.counit_mul] at key
    rw [Finset.sum_comm] at key
    simpa [Algebra.algebraMap_eq_smul_one, mul_comm (counit x) (counit y)] using key
  · -- Right inverse: `μ * (μ ∘ (S ⊗ S) ∘ comm) = 1`.
    refine WithConv.ext (TensorProduct.ext' fun x y => ?_)
    simp only [LinearMap.convMul_apply, LinearMap.convOne_apply]
    rw [TensorProduct.comul_tmul]
    let ℛx := ℛ R x; let ℛy := ℛ R y
    conv_lhs => rw [← ℛx.eq, ← ℛy.eq]
    simp only [TensorProduct.sum_tmul, TensorProduct.tmul_sum, map_sum,
      TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul, TensorProduct.map_tmul,
      LinearMap.mul'_apply, LinearMap.comp_apply]
    rw [Finset.sum_comm]
    simp only [TensorProduct.counit_tmul, Algebra.algebraMap_eq_smul_one]
    -- Rearrange the sum using antipode axioms.
    calc ∑ i ∈ ℛx.index, ∑ j ∈ ℛy.index,
        (ℛx.left i * ℛy.left j) * (antipode R (ℛy.right j) * antipode R (ℛx.right i))
      _ = ∑ i ∈ ℛx.index, ∑ j ∈ ℛy.index,
          ℛx.left i * (ℛy.left j * antipode R (ℛy.right j) * antipode R (ℛx.right i)) := by
        simp [mul_assoc]
      _ = ∑ i ∈ ℛx.index, ℛx.left i *
          ((∑ j ∈ ℛy.index, ℛy.left j * antipode R (ℛy.right j)) * antipode R (ℛx.right i)) := by
        simp [Finset.sum_mul, Finset.mul_sum]
      _ = ∑ i ∈ ℛx.index, ℛx.left i *
          (counit y • 1 * antipode R (ℛx.right i)) := by
        rw [sum_mul_antipode_eq_smul ℛy]
      _ = ∑ i ∈ ℛx.index, ℛx.left i *
          (algebraMap R A (counit y) * antipode R (ℛx.right i)) := by
        simp [Algebra.smul_def]
      _ = ∑ i ∈ ℛx.index, algebraMap R A (counit y) * (ℛx.left i * antipode R (ℛx.right i)) := by
        congr 1; ext i; rw [← mul_assoc, ← mul_assoc, Algebra.commutes]
      _ = algebraMap R A (counit y) * ∑ i ∈ ℛx.index, ℛx.left i * antipode R (ℛx.right i) := by
        rw [← Finset.mul_sum]
      _ = algebraMap R A (counit y) * (counit (R := R) x • (1 : A)) := by
        rw [sum_mul_antipode_eq_smul ℛx]
      _ = (counit (R := R) x * counit y) • (1 : A) := by
        simp only [Algebra.smul_def, mul_one, ← map_mul, mul_comm (counit x)]
      _ = (counit (R := R) y • counit x) • (1 : A) := by
        simp only [smul_eq_mul, mul_comm (counit y)]

/-! ### Construction by axiom verification on algebra generators

Given an `R`-bialgebra `A` and a candidate antipode `S : A →ₐ[R] Aᵐᵒᵖ`, the elements of `A`
where each antipode axiom holds form a subalgebra. So a `HopfAlgebra R A` instance can be
constructed by verifying the axioms on a set whose algebra-adjoint is `⊤` — typically a small
generating set, e.g. the image of the universal map in a free construction. The corollaries
`mul_rTensor_comul_eq_of_adjoin_eq_top` and `mul_lTensor_comul_eq_of_adjoin_eq_top` package
this for use with `HopfAlgebra.ofAlgHom`.
-/

section Construction

variable {R A : Type*} [CommSemiring R] [Semiring A] [Bialgebra R A]

open MulOpposite

/-- The rTensor antipode axiom evaluated at the single element `a ∈ A`, for the candidate
antipode `S : A →ₐ[R] Aᵐᵒᵖ`. The Hopf algebra field `mul_antipode_rTensor_comul` is the
linear-map equation `∀ x, (IsRTensorAntipodeAt R S x).eq` where `S` is the antipode viewed
as an algebra map into `Aᵐᵒᵖ`. -/
@[mk_iff]
structure IsRTensorAntipodeAt (R : Type*) [CommSemiring R] {A : Type*}
    [Semiring A] [Bialgebra R A] (S : A →ₐ[R] Aᵐᵒᵖ) (a : A) : Prop where
  /-- The pointwise Sweedler-form rTensor antipode equation at `a`. -/
  eq : LinearMap.mul' R A
      (((opLinearEquiv R).symm.toLinearMap ∘ₗ S.toLinearMap).rTensor A (comul a)) =
    algebraMap R A (counit a)

/-- The lTensor antipode axiom evaluated at the single element `a ∈ A`. -/
@[mk_iff]
structure IsLTensorAntipodeAt (R : Type*) [CommSemiring R] {A : Type*}
    [Semiring A] [Bialgebra R A] (S : A →ₐ[R] Aᵐᵒᵖ) (a : A) : Prop where
  /-- The pointwise Sweedler-form lTensor antipode equation at `a`. -/
  eq : LinearMap.mul' R A
      (((opLinearEquiv R).symm.toLinearMap ∘ₗ S.toLinearMap).lTensor A (comul a)) =
    algebraMap R A (counit a)

variable {S : A →ₐ[R] Aᵐᵒᵖ}

namespace IsRTensorAntipodeAt

protected lemma add {a b : A}
    (ha : IsRTensorAntipodeAt R S a) (hb : IsRTensorAntipodeAt R S b) :
    IsRTensorAntipodeAt R S (a + b) := ⟨by
  simp only [map_add]; rw [ha.eq, hb.eq, ← map_add]⟩

protected lemma algebraMap (r : R) :
    IsRTensorAntipodeAt R S (algebraMap R A r) := ⟨by
  rw [Bialgebra.comul_algebraMap, Bialgebra.counit_algebraMap,
      Algebra.TensorProduct.algebraMap_apply, LinearMap.rTensor_tmul]
  simp⟩

/-- If `S` satisfies the rTensor antipode axiom at `a` and at `b`, it does so at `a * b`.
This is the load-bearing closure lemma: the Sweedler computation expanding `comul (a*b)`,
applying the antihomomorphism property `S(xy) = S(y) * S(x)`, and collapsing the inner and
outer sums via the inductive hypotheses. -/
protected lemma mul {a b : A}
    (ha : IsRTensorAntipodeAt R S a) (hb : IsRTensorAntipodeAt R S b) :
    IsRTensorAntipodeAt R S (a * b) := ⟨by
  set S₀ : A →ₗ[R] A := (opLinearEquiv R).symm.toLinearMap ∘ₗ S.toLinearMap with hS₀
  have hS₀_antihom : ∀ x y : A, S₀ (x * y) = S₀ y * S₀ x := fun x y => by simp [hS₀, map_mul]
  let ℛa := ℛ R a
  let ℛb := ℛ R b
  calc LinearMap.mul' R A (S₀.rTensor A (comul (a * b)))
      _ = LinearMap.mul' R A (S₀.rTensor A (comul a * comul b)) := by rw [Bialgebra.comul_mul]
      _ = ∑ p ∈ ℛa.index, ∑ q ∈ ℛb.index,
            S₀ (ℛa.left p * ℛb.left q) * (ℛa.right p * ℛb.right q) := by
        rw [← ℛa.eq, ← ℛb.eq, Finset.sum_mul_sum]
        simp [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.rTensor]
      _ = ∑ p ∈ ℛa.index, ∑ q ∈ ℛb.index,
            S₀ (ℛb.left q) * (S₀ (ℛa.left p) * ℛa.right p) * ℛb.right q := by
        simp_rw [hS₀_antihom, mul_assoc]
      _ = ∑ q ∈ ℛb.index, S₀ (ℛb.left q) *
            (∑ p ∈ ℛa.index, S₀ (ℛa.left p) * ℛa.right p) * ℛb.right q := by
        rw [Finset.sum_comm]; simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
      _ = ∑ q ∈ ℛb.index,
            algebraMap R A (counit a) * S₀ (ℛb.left q) * ℛb.right q := by
        refine Finset.sum_congr rfl fun q _ => ?_
        have hℛa : ∑ p ∈ ℛa.index, S₀ (ℛa.left p) * ℛa.right p = algebraMap R A (counit a) := by
          have := ha.eq; rw [← ℛa.eq] at this
          simpa [LinearMap.rTensor, LinearMap.mul'_apply] using this
        rw [hℛa, show S₀ (ℛb.left q) * algebraMap R A (counit a)
            = algebraMap R A (counit a) * S₀ (ℛb.left q) from (Algebra.commutes _ _).symm]
      _ = algebraMap R A (counit a) *
            ∑ q ∈ ℛb.index, S₀ (ℛb.left q) * ℛb.right q := by
        rw [Finset.mul_sum]; simp_rw [mul_assoc]
      _ = algebraMap R A (counit a) * algebraMap R A (counit b) := by
        congr 1
        have := hb.eq; rw [← ℛb.eq] at this
        simpa [LinearMap.rTensor, LinearMap.mul'_apply] using this
      _ = algebraMap R A (counit (a * b)) := by rw [Bialgebra.counit_mul, map_mul]⟩

end IsRTensorAntipodeAt

namespace IsLTensorAntipodeAt

protected lemma add {a b : A}
    (ha : IsLTensorAntipodeAt R S a) (hb : IsLTensorAntipodeAt R S b) :
    IsLTensorAntipodeAt R S (a + b) := ⟨by
  simp only [map_add]; rw [ha.eq, hb.eq, ← map_add]⟩

protected lemma algebraMap (r : R) :
    IsLTensorAntipodeAt R S (algebraMap R A r) := ⟨by
  rw [Bialgebra.comul_algebraMap, Bialgebra.counit_algebraMap,
      Algebra.TensorProduct.algebraMap_apply, LinearMap.lTensor_tmul]
  simp⟩

/-- If `S` satisfies the lTensor antipode axiom at `a` and at `b`, it does so at `a * b`.
Mirror image of `IsRTensorAntipodeAt.mul`. -/
protected lemma mul {a b : A}
    (ha : IsLTensorAntipodeAt R S a) (hb : IsLTensorAntipodeAt R S b) :
    IsLTensorAntipodeAt R S (a * b) := ⟨by
  set S₀ : A →ₗ[R] A := (opLinearEquiv R).symm.toLinearMap ∘ₗ S.toLinearMap with hS₀
  have hS₀_antihom : ∀ x y : A, S₀ (x * y) = S₀ y * S₀ x := fun x y => by simp [hS₀, map_mul]
  let ℛa := ℛ R a
  let ℛb := ℛ R b
  calc LinearMap.mul' R A (S₀.lTensor A (comul (a * b)))
      _ = LinearMap.mul' R A (S₀.lTensor A (comul a * comul b)) := by rw [Bialgebra.comul_mul]
      _ = ∑ p ∈ ℛa.index, ∑ q ∈ ℛb.index,
            (ℛa.left p * ℛb.left q) * S₀ (ℛa.right p * ℛb.right q) := by
        rw [← ℛa.eq, ← ℛb.eq, Finset.sum_mul_sum]
        simp [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.lTensor]
      _ = ∑ p ∈ ℛa.index, ∑ q ∈ ℛb.index,
            ℛa.left p * (ℛb.left q * S₀ (ℛb.right q)) * S₀ (ℛa.right p) := by
        simp_rw [hS₀_antihom, mul_assoc]
      _ = ∑ p ∈ ℛa.index,
            ℛa.left p * (∑ q ∈ ℛb.index, ℛb.left q * S₀ (ℛb.right q)) * S₀ (ℛa.right p) := by
        simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
      _ = ∑ p ∈ ℛa.index,
            algebraMap R A (counit b) * ℛa.left p * S₀ (ℛa.right p) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        have hℛb : ∑ q ∈ ℛb.index, ℛb.left q * S₀ (ℛb.right q) = algebraMap R A (counit b) := by
          have := hb.eq; rw [← ℛb.eq] at this
          simpa [LinearMap.lTensor, LinearMap.mul'_apply] using this
        rw [hℛb, show ℛa.left p * algebraMap R A (counit b)
            = algebraMap R A (counit b) * ℛa.left p from (Algebra.commutes _ _).symm]
      _ = algebraMap R A (counit b) *
            ∑ p ∈ ℛa.index, ℛa.left p * S₀ (ℛa.right p) := by
        rw [Finset.mul_sum]; simp_rw [mul_assoc]
      _ = algebraMap R A (counit b) * algebraMap R A (counit a) := by
        congr 1
        have := ha.eq; rw [← ℛa.eq] at this
        simpa [LinearMap.lTensor, LinearMap.mul'_apply] using this
      _ = algebraMap R A (counit (a * b)) := by
        rw [Bialgebra.counit_mul, mul_comm (counit a) (counit b), map_mul]⟩

end IsLTensorAntipodeAt

/-- A candidate antipode `S : A →ₐ[R] Aᵐᵒᵖ` satisfies the rTensor antipode axiom on all of `A`
if it satisfies it on a set whose algebra-adjoint is everything. -/
theorem mul_rTensor_comul_eq_of_adjoin_eq_top
    (S : A →ₐ[R] Aᵐᵒᵖ) {s : Set A}
    (hs : Algebra.adjoin R s = ⊤)
    (h : ∀ x ∈ s, IsRTensorAntipodeAt R S x) :
    LinearMap.mul' R A ∘ₗ ((opLinearEquiv R).symm.toLinearMap ∘ₗ S.toLinearMap).rTensor A
        ∘ₗ comul =
      Algebra.linearMap R A ∘ₗ counit := by
  let locus : Subalgebra R A :=
    { carrier := { a | IsRTensorAntipodeAt R S a }
      mul_mem' := .mul
      add_mem' := .add
      algebraMap_mem' := .algebraMap }
  ext x
  exact (Algebra.adjoin_le (S := locus) h (hs ▸ Algebra.mem_top : x ∈ Algebra.adjoin R s)).eq

/-- A candidate antipode `S : A →ₐ[R] Aᵐᵒᵖ` satisfies the lTensor antipode axiom on all of `A`
if it satisfies it on a set whose algebra-adjoint is everything. -/
theorem mul_lTensor_comul_eq_of_adjoin_eq_top
    (S : A →ₐ[R] Aᵐᵒᵖ) {s : Set A}
    (hs : Algebra.adjoin R s = ⊤)
    (h : ∀ x ∈ s, IsLTensorAntipodeAt R S x) :
    LinearMap.mul' R A ∘ₗ ((opLinearEquiv R).symm.toLinearMap ∘ₗ S.toLinearMap).lTensor A
        ∘ₗ comul =
      Algebra.linearMap R A ∘ₗ counit := by
  let locus : Subalgebra R A :=
    { carrier := { a | IsLTensorAntipodeAt R S a }
      mul_mem' := .mul
      add_mem' := .add
      algebraMap_mem' := .algebraMap }
  ext x
  exact (Algebra.adjoin_le (S := locus) h (hs ▸ Algebra.mem_top : x ∈ Algebra.adjoin R s)).eq

end Construction

end HopfAlgebra

namespace CommSemiring

variable (R : Type u) [CommSemiring R]

open HopfAlgebra

/-- Every commutative (semi)ring is a Hopf algebra over itself -/
instance toHopfAlgebra : HopfAlgebra R R where
  antipode := .id
  mul_antipode_rTensor_comul := by ext; simp
  mul_antipode_lTensor_comul := by ext; simp

@[simp]
theorem antipode_eq_id : antipode R (A := R) = .id := rfl

end CommSemiring
