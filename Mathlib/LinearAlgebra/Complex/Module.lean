/-
Copyright (c) 2020 Alexander Bentkamp, Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Sébastien Gouëzel, Eric Wieser
-/
module

public import Mathlib.Algebra.Algebra.RestrictScalars
public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Real.Star
public import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Algebra.Order.Monoid.Submonoid

/-!
# Complex number as a vector space over `ℝ`

This file contains the following instances:
* Any `•`-structure (`SMul`, `MulAction`, `DistribMulAction`, `Module`, `Algebra`) on
  `ℝ` imbues a corresponding structure on `ℂ`. This includes the statement that `ℂ` is an `ℝ`
  algebra.
* any complex vector space is a real vector space;
* any finite-dimensional complex vector space is a finite-dimensional real vector space;
* the space of `ℝ`-linear maps from a real vector space to a complex vector space is a complex
  vector space.

It also defines bundled versions of four standard maps (respectively, the real part, the imaginary
part, the embedding of `ℝ` in `ℂ`, and the complex conjugate):

* `Complex.reLm` (`ℝ`-linear map);
* `Complex.imLm` (`ℝ`-linear map);
* `Complex.ofRealAm` (`ℝ`-algebra (homo)morphism);
* `Complex.conjAe` (`ℝ`-algebra equivalence).

It also provides a universal property of the complex numbers `Complex.lift`, which constructs a
`ℂ →ₐ[ℝ] A` into any `ℝ`-algebra `A` given a square root of `-1`.

In addition, this file provides a decomposition into `realPart` and `imaginaryPart` for any
element of a `StarModule` over `ℂ`.

## Notation

* `ℜ` and `ℑ` for the `realPart` and `imaginaryPart`, respectively, in the locale
  `ComplexStarModule`.
-/

@[expose] public section

assert_not_exists NNReal
namespace Complex

open ComplexConjugate

open scoped SMul

variable {R : Type*} {S : Type*}

attribute [local ext] Complex.ext


/- The priority of the following instances has been manually lowered, as when they don't apply
they lead Lean to a very costly path, and most often they don't apply (most actions on `ℂ` don't
come from actions on `ℝ`). See https://github.com/leanprover-community/mathlib4/pull/11980 -/

-- priority manually adjusted in https://github.com/leanprover-community/mathlib4/pull/11980
instance (priority := 90) [SMul R ℝ] [SMul S ℝ] [SMulCommClass R S ℝ] : SMulCommClass R S ℂ where
  smul_comm r s x := by ext <;> simp [smul_re, smul_im, smul_comm]

-- priority manually adjusted in https://github.com/leanprover-community/mathlib4/pull/11980
instance (priority := 90) [SMul R S] [SMul R ℝ] [SMul S ℝ] [IsScalarTower R S ℝ] :
    IsScalarTower R S ℂ where
  smul_assoc r s x := by ext <;> simp [smul_re, smul_im, smul_assoc]

-- priority manually adjusted in https://github.com/leanprover-community/mathlib4/pull/11980
instance (priority := 90) [SMul R ℝ] [SMul Rᵐᵒᵖ ℝ] [IsCentralScalar R ℝ] :
    IsCentralScalar R ℂ where
  op_smul_eq_smul r x := by ext <;> simp [smul_re, smul_im, op_smul_eq_smul]

-- priority manually adjusted in https://github.com/leanprover-community/mathlib4/pull/11980
instance (priority := 90) mulAction [Monoid R] [MulAction R ℝ] : MulAction R ℂ where
  one_smul x := by ext <;> simp [smul_re, smul_im, one_smul]
  mul_smul r s x := by ext <;> simp [smul_re, smul_im, mul_smul]

-- priority manually adjusted in https://github.com/leanprover-community/mathlib4/pull/11980
instance (priority := 90) distribSMul [DistribSMul R ℝ] : DistribSMul R ℂ where
  smul_add r x y := by ext <;> simp [smul_re, smul_im, smul_add]
  smul_zero r := by ext <;> simp [smul_re, smul_im, smul_zero]

-- priority manually adjusted in https://github.com/leanprover-community/mathlib4/pull/11980
instance (priority := 90) [Semiring R] [DistribMulAction R ℝ] : DistribMulAction R ℂ :=
  { Complex.distribSMul, Complex.mulAction with }

-- priority manually adjusted in https://github.com/leanprover-community/mathlib4/pull/11980
instance (priority := 100) instModule [Semiring R] [Module R ℝ] : Module R ℂ where
  add_smul r s x := by ext <;> simp [smul_re, smul_im, add_smul]
  zero_smul r := by ext <;> simp [smul_re, smul_im, zero_smul]

-- priority manually adjusted in https://github.com/leanprover-community/mathlib4/pull/11980
instance (priority := 95) instAlgebraOfReal [CommSemiring R] [Algebra R ℝ] : Algebra R ℂ where
  algebraMap := Complex.ofRealHom.comp (algebraMap R ℝ)
  smul_def' := fun r x => by ext <;> simp [smul_re, smul_im, Algebra.smul_def]
  commutes' := fun r ⟨xr, xi⟩ => by ext <;> simp [Algebra.commutes]

instance : StarModule ℝ ℂ :=
  ⟨fun r x => by simp only [star_def, star_trivial, real_smul, map_mul, conj_ofReal]⟩

@[simp]
theorem coe_algebraMap : (algebraMap ℝ ℂ : ℝ → ℂ) = ((↑) : ℝ → ℂ) :=
  rfl

example : (Semiring.toNatAlgebra : Algebra ℕ ℂ) = Complex.instAlgebraOfReal := by
  with_reducible_and_instances rfl

example : (Ring.toIntAlgebra ℂ : Algebra ℤ ℂ) = Complex.instAlgebraOfReal := by
  with_reducible_and_instances rfl

example : Module.restrictScalars ℝ ℂ ℂ = Complex.instModule := by
  with_reducible_and_instances rfl

section

variable {A : Type*} [Semiring A] [Algebra ℝ A]

/-- We need this lemma since `Complex.coe_algebraMap` diverts the simp-normal form away from
`AlgHom.commutes`. -/
@[simp]
theorem _root_.AlgHom.map_coe_real_complex (f : ℂ →ₐ[ℝ] A) (x : ℝ) : f x = algebraMap ℝ A x :=
  f.commutes x

/-- Two `ℝ`-algebra homomorphisms from `ℂ` are equal if they agree on `Complex.I`. -/
@[ext]
theorem algHom_ext ⦃f g : ℂ →ₐ[ℝ] A⦄ (h : f I = g I) : f = g := by
  ext ⟨x, y⟩
  simp only [mk_eq_add_mul_I, map_add, AlgHom.map_coe_real_complex, map_mul, h]

end

open Module Submodule

/-- `ℂ` has a basis over `ℝ` given by `1` and `I`. -/
noncomputable def basisOneI : Basis (Fin 2) ℝ ℂ :=
  .ofEquivFun
    { toFun := fun z => ![z.re, z.im]
      invFun := fun c => c 0 + c 1 • I
      left_inv := fun z => by simp
      right_inv := fun c => by
        ext i
        fin_cases i <;> simp
      map_add' := fun z z' => by simp
      map_smul' := fun c z => by simp }

@[simp]
theorem coe_basisOneI_repr (z : ℂ) : ⇑(basisOneI.repr z) = ![z.re, z.im] :=
  rfl

@[simp]
theorem coe_basisOneI : ⇑basisOneI = ![1, I] :=
  funext fun i =>
    Basis.apply_eq_iff.mpr <|
      Finsupp.ext fun j => by
        fin_cases i <;> fin_cases j <;> simp

end Complex

/-- Register as an instance (with low priority) the fact that a complex vector space is also a real
vector space. -/
instance (priority := 900) Module.complexToReal (E : Type*) [AddCommGroup E] [Module ℂ E] :
    Module ℝ E :=
  .restrictScalars ℝ ℂ E

/-- Register as an instance (with low priority) the fact that a complex algebra is also a real
algebra. -/
instance (priority := 900) Algebra.complexToReal {A : Type*} [Semiring A] [Algebra ℂ A] :
    Algebra ℝ A :=
  .restrictScalars ℝ ℂ A

-- try to make sure we're not introducing diamonds but we will need
-- `reducible_and_instances` which currently fails https://github.com/leanprover-community/mathlib4/issues/10906
example : Prod.algebra ℝ ℂ ℂ = (Prod.algebra ℂ ℂ ℂ).complexToReal := rfl

-- try to make sure we're not introducing diamonds but we will need
-- `reducible_and_instances` which currently fails https://github.com/leanprover-community/mathlib4/issues/10906
example {ι : Type*} [Fintype ι] :
    Pi.algebra (R := ℝ) ι (fun _ ↦ ℂ) = (Pi.algebra (R := ℂ) ι (fun _ ↦ ℂ)).complexToReal :=
  rfl

example {A : Type*} [Ring A] [inst : Algebra ℂ A] :
    (inst.complexToReal).toModule = (inst.toModule).complexToReal := by
  with_reducible_and_instances rfl

@[simp, norm_cast]
theorem Complex.coe_smul {E : Type*} [AddCommGroup E] [Module ℂ E] (x : ℝ) (y : E) :
    (x : ℂ) • y = x • y :=
  rfl

/-- The scalar action of `ℝ` on a `ℂ`-module `E` induced by `Module.complexToReal` commutes with
another scalar action of `M` on `E` whenever the action of `ℂ` commutes with the action of `M`. -/
instance (priority := 900) SMulCommClass.complexToReal {M E : Type*} [AddCommGroup E] [Module ℂ E]
    [SMul M E] [SMulCommClass ℂ M E] : SMulCommClass ℝ M E where
  smul_comm r _ _ := smul_comm (r : ℂ) _ _

/-- The scalar action of `ℝ` on a `ℂ`-module `E` induced by `Module.complexToReal` associates with
another scalar action of `M` on `E` whenever the action of `ℂ` associates with the action of `M`. -/
instance IsScalarTower.complexToReal {M E : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup E]
    [Module ℂ E] [SMul M E] [IsScalarTower ℂ M E] : IsScalarTower ℝ M E where
  smul_assoc r _ _ := smul_assoc (r : ℂ) _ _

-- check that the following instance is implied by the one above.
example (E : Type*) [AddCommGroup E] [Module ℂ E] : IsScalarTower ℝ ℂ E := inferInstance

instance (priority := 900) StarModule.complexToReal {E : Type*} [AddCommGroup E] [Star E]
    [Module ℂ E] [StarModule ℂ E] : StarModule ℝ E :=
  ⟨fun r a => by rw [← smul_one_smul ℂ r a, star_smul, star_smul, star_one, smul_one_smul]⟩

namespace Complex

open ComplexConjugate

/-- Linear map version of the real part function, from `ℂ` to `ℝ`. -/
def reLm : ℂ →ₗ[ℝ] ℝ where
  toFun x := x.re
  map_add' := add_re
  map_smul' := by simp

@[simp]
theorem reLm_coe : ⇑reLm = re :=
  rfl

/-- Linear map version of the imaginary part function, from `ℂ` to `ℝ`. -/
def imLm : ℂ →ₗ[ℝ] ℝ where
  toFun x := x.im
  map_add' := add_im
  map_smul' := by simp

@[simp]
theorem imLm_coe : ⇑imLm = im :=
  rfl

/-- `ℝ`-algebra morphism version of the canonical embedding of `ℝ` in `ℂ`. -/
def ofRealAm : ℝ →ₐ[ℝ] ℂ :=
  Algebra.ofId ℝ ℂ

@[simp]
theorem ofRealAm_coe : ⇑ofRealAm = ((↑) : ℝ → ℂ) :=
  rfl

/-- `ℝ`-algebra isomorphism version of the complex conjugation function from `ℂ` to `ℂ` -/
def conjAe : ℂ ≃ₐ[ℝ] ℂ :=
  { conj with
    invFun := conj
    left_inv := star_star
    right_inv := star_star
    commutes' := conj_ofReal }

@[simp]
theorem conjAe_coe : ⇑conjAe = conj :=
  rfl

/-- The matrix representation of `conjAe`. -/
@[simp]
theorem toMatrix_conjAe :
    conjAe.toLinearEquiv.toLinearMap.toMatrix basisOneI basisOneI = !![1, 0; 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [LinearMap.toMatrix_apply]

/-- The identity and the complex conjugation are the only two `ℝ`-algebra homomorphisms of `ℂ`. -/
theorem real_algHom_eq_id_or_conj (f : ℂ →ₐ[ℝ] ℂ) : f = AlgHom.id ℝ ℂ ∨ f = conjAe := by
  refine
      (eq_or_eq_neg_of_sq_eq_sq (f I) I <| by rw [← map_pow, I_sq, map_neg, map_one]).imp ?_ ?_ <;>
    refine fun h => algHom_ext ?_
  exacts [h, conj_I.symm ▸ h]

/-- The natural `LinearEquiv` from `ℂ` to `ℝ × ℝ`. -/
@[simps! +simpRhs apply symm_apply_re symm_apply_im]
def equivRealProdLm : ℂ ≃ₗ[ℝ] ℝ × ℝ :=
  { equivRealProdAddHom with
    map_smul' := fun r c => by simp }

theorem equivRealProdLm_symm_apply (p : ℝ × ℝ) :
    Complex.equivRealProdLm.symm p = p.1 + p.2 * Complex.I := Complex.equivRealProd_symm_apply p

section lift

variable {A : Type*} [Ring A] [Algebra ℝ A]

open Algebra

/-- There is an `AlgHom` from `ℂ` to any `ℝ`-algebra with an element that squares to `-1`.

See `Complex.lift` for this as an equiv. -/
def liftAux (I' : A) (hf : I' * I' = -1) : ℂ →ₐ[ℝ] A :=
  AlgHom.ofLinearMap
    ((Algebra.linearMap ℝ A).comp reLm + (LinearMap.toSpanSingleton _ _ I').comp imLm)
    (show algebraMap ℝ A 1 + (0 : ℝ) • I' = 1 by rw [map_one, zero_smul, add_zero]) ?_
where finally
  rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩
  rw [mk_mul_mk]
  change
    algebraMap ℝ A (x₁ * x₂ - y₁ * y₂) + (x₁ * y₂ + y₁ * x₂) • I' =
      (algebraMap ℝ A x₁ + y₁ • I') * (algebraMap ℝ A x₂ + y₂ • I')
  rw [add_mul, mul_add, mul_add, add_comm _ (y₁ • I' * y₂ • I'), add_add_add_comm]
  congr 1
  -- equate "real" and "imaginary" parts
  · rw [smul_mul_smul_comm, hf, smul_neg, ← algebraMap_eq_smul_one, ← sub_eq_add_neg,
      ← map_mul, ← map_sub]
  · rw [smul_def, smul_def, smul_def, ← right_comm _ x₂,
      ← mul_assoc, ← add_mul, ← map_mul, ← map_mul, ← map_add]

@[simp]
theorem liftAux_apply (I' : A) (hI') (z : ℂ) : liftAux I' hI' z = algebraMap ℝ A z.re + z.im • I' :=
  rfl

theorem liftAux_apply_I (I' : A) (hI') : liftAux I' hI' I = I' := by simp

@[simp]
theorem adjoin_I : ℝ[I] = ⊤ := by
  refine top_unique fun x hx => ?_; clear hx
  rw [← x.re_add_im, ← smul_eq_mul, ← Complex.coe_algebraMap]
  exact add_mem (algebraMap_mem _ _) (Subalgebra.smul_mem _ (subset_adjoin <| by simp) _)

@[simp]
theorem range_liftAux (I' : A) (hI') : (liftAux I' hI').range = ℝ[I'] := by
  simp_rw [← Algebra.map_top, ← adjoin_I, AlgHom.map_adjoin, Set.image_singleton, liftAux_apply_I]

/-- A universal property of the complex numbers, providing a unique `ℂ →ₐ[ℝ] A` for every element
of `A` which squares to `-1`.

This can be used to embed the complex numbers in the `Quaternion`s.

This isomorphism is named to match the very similar `Zsqrtd.lift`. -/
@[simps +simpRhs]
def lift : { I' : A // I' * I' = -1 } ≃ (ℂ →ₐ[ℝ] A) where
  toFun I' := liftAux I' I'.prop
  invFun F := ⟨F I, by rw [← map_mul, I_mul_I, map_neg, map_one]⟩
  left_inv I' := Subtype.ext <| liftAux_apply_I (I' : A) I'.prop
  right_inv _ := algHom_ext <| liftAux_apply_I _ _

-- When applied to `Complex.I` itself, `lift` is the identity.
@[simp]
theorem liftAux_I : liftAux I I_mul_I = AlgHom.id ℝ ℂ :=
  algHom_ext <| liftAux_apply_I _ _

-- When applied to `-Complex.I`, `lift` is conjugation, `conj`.
@[simp]
theorem liftAux_neg_I : liftAux (-I) ((neg_mul_neg _ _).trans I_mul_I) = conjAe :=
  algHom_ext <| (liftAux_apply_I _ _).trans conj_I.symm

end lift

end Complex

section RealImaginaryPart

open Complex

variable {A : Type*}

section AddCommGroup

variable [AddCommGroup A] [Module ℂ A] [StarAddMonoid A] [StarModule ℂ A]

/-- Create a `selfAdjoint` element from a `skewAdjoint` element by multiplying by the scalar
`-Complex.I`. -/
@[simps]
def skewAdjoint.negISMul : skewAdjoint A →ₗ[ℝ] selfAdjoint A where
  toFun a :=
    ⟨-I • ↑a, by
      simp only [neg_smul, neg_mem_iff, selfAdjoint.mem_iff, star_smul, star_def, conj_I,
        star_val_eq, smul_neg, neg_neg]⟩
  map_add' a b := by
    ext
    simp only [AddSubgroup.coe_add, smul_add, AddMemClass.mk_add_mk]
  map_smul' a b := by
    ext
    simp only [neg_smul, skewAdjoint.val_smul, RingHom.id_apply,
      selfAdjoint.val_smul, smul_neg, neg_inj]
    rw [smul_comm]

theorem skewAdjoint.I_smul_neg_I (a : skewAdjoint A) : I • (skewAdjoint.negISMul a : A) = a := by
  simp only [smul_smul, skewAdjoint.negISMul_apply_coe, neg_smul, smul_neg, I_mul_I, one_smul,
    neg_neg]

/-- The real part `ℜ a` of an element `a` of a star module over `ℂ`, as a linear map. This is just
`selfAdjointPart ℝ`, but we provide it as a separate definition in order to link it with lemmas
concerning the `imaginaryPart`, which doesn't exist in star modules over other rings. -/
noncomputable def realPart : A →ₗ[ℝ] selfAdjoint A :=
  selfAdjointPart ℝ

/-- The imaginary part `ℑ a` of an element `a` of a star module over `ℂ`, as a linear map into the
self adjoint elements. In a general star module, we have a decomposition into the `selfAdjoint`
and `skewAdjoint` parts, but in a star module over `ℂ` we have
`realPart_add_I_smul_imaginaryPart`, which allows us to decompose into a linear combination of
`selfAdjoint`s. -/
noncomputable def imaginaryPart : A →ₗ[ℝ] selfAdjoint A :=
  skewAdjoint.negISMul.comp (skewAdjointPart ℝ)

@[inherit_doc]
scoped[ComplexStarModule] notation "ℜ" => realPart
@[inherit_doc]
scoped[ComplexStarModule] notation "ℑ" => imaginaryPart

open ComplexStarModule

theorem realPart_apply_coe (a : A) : (ℜ a : A) = (2 : ℝ)⁻¹ • (a + star a) := by
  unfold realPart
  simp only [selfAdjointPart_apply_coe, invOf_eq_inv]

theorem imaginaryPart_apply_coe (a : A) : (ℑ a : A) = -I • (2 : ℝ)⁻¹ • (a - star a) := by
  unfold imaginaryPart
  simp only [LinearMap.coe_comp, Function.comp_apply, skewAdjoint.negISMul_apply_coe,
    skewAdjointPart_apply_coe, invOf_eq_inv, neg_smul]

/-- The standard decomposition of `ℜ a + Complex.I • ℑ a = a` of an element of a star module over
`ℂ` into a linear combination of self adjoint elements. -/
theorem realPart_add_I_smul_imaginaryPart (a : A) : (ℜ a : A) + I • (ℑ a : A) = a := by
  simpa only [smul_smul, realPart_apply_coe, imaginaryPart_apply_coe, neg_smul, I_mul_I, one_smul,
    neg_sub, add_add_sub_cancel, smul_sub, smul_add, neg_sub_neg, invOf_eq_inv] using
    invOf_two_smul_add_invOf_two_smul ℝ a

@[simp]
theorem realPart_I_smul (a : A) : ℜ (I • a) = -ℑ a := by
  ext
  simp [realPart_apply_coe, imaginaryPart_apply_coe, smul_comm I, sub_eq_add_neg, add_comm]

@[simp]
theorem imaginaryPart_I_smul (a : A) : ℑ (I • a) = ℜ a := by
  ext
  simp [realPart_apply_coe, imaginaryPart_apply_coe, smul_comm I (2⁻¹ : ℝ), smul_smul I]

theorem realPart_smul (z : ℂ) (a : A) : ℜ (z • a) = z.re • ℜ a - z.im • ℑ a := by
  have := by congrm (ℜ ($((re_add_im z).symm) • a))
  simpa [-re_add_im, add_smul, ← smul_smul, sub_eq_add_neg]

theorem imaginaryPart_smul (z : ℂ) (a : A) : ℑ (z • a) = z.re • ℑ a + z.im • ℜ a := by
  have := by congrm (ℑ ($((re_add_im z).symm) • a))
  simpa [-re_add_im, add_smul, ← smul_smul]

lemma skewAdjointPart_eq_I_smul_imaginaryPart (x : A) :
    (skewAdjointPart ℝ x : A) = I • (imaginaryPart x : A) := by
  simp [imaginaryPart_apply_coe, smul_smul]

lemma imaginaryPart_eq_neg_I_smul_skewAdjointPart (x : A) :
    (imaginaryPart x : A) = -I • (skewAdjointPart ℝ x : A) :=
  rfl

lemma IsSelfAdjoint.coe_realPart {x : A} (hx : IsSelfAdjoint x) :
    (ℜ x : A) = x :=
  hx.coe_selfAdjointPart_apply ℝ

nonrec lemma IsSelfAdjoint.imaginaryPart {x : A} (hx : IsSelfAdjoint x) :
    ℑ x = 0 := by
  rw [imaginaryPart, LinearMap.comp_apply, hx.skewAdjointPart_apply _, map_zero]

lemma realPart_comp_subtype_selfAdjoint :
    realPart.comp (selfAdjoint.submodule ℝ A).subtype = LinearMap.id :=
  selfAdjointPart_comp_subtype_selfAdjoint ℝ

lemma imaginaryPart_comp_subtype_selfAdjoint :
    imaginaryPart.comp (selfAdjoint.submodule ℝ A).subtype = 0 := by
  rw [imaginaryPart, LinearMap.comp_assoc, skewAdjointPart_comp_subtype_selfAdjoint,
    LinearMap.comp_zero]

@[simp]
lemma selfAdjoint.realPart_coe {x : selfAdjoint A} : ℜ (x : A) = x :=
  Subtype.ext x.property.coe_realPart

@[simp]
lemma selfAdjoint.imaginaryPart_coe {x : selfAdjoint A} : ℑ (x : A) = 0 :=
  x.property.imaginaryPart

lemma imaginaryPart_realPart {x : A} : ℑ (ℜ x : A) = 0 :=
  (ℜ x).property.imaginaryPart

lemma imaginaryPart_imaginaryPart {x : A} : ℑ (ℑ x : A) = 0 :=
  (ℑ x).property.imaginaryPart

lemma realPart_idem {x : A} : ℜ (ℜ x : A) = ℜ x :=
  Subtype.ext <| (ℜ x).property.coe_realPart

lemma realPart_imaginaryPart {x : A} : ℜ (ℑ x : A) = ℑ x :=
  Subtype.ext <| (ℑ x).property.coe_realPart

lemma realPart_surjective : Function.Surjective (realPart (A := A)) :=
  fun x ↦ ⟨(x : A), Subtype.ext x.property.coe_realPart⟩

lemma imaginaryPart_surjective : Function.Surjective (imaginaryPart (A := A)) :=
  fun x ↦
    ⟨I • (x : A), Subtype.ext <| by simp only [imaginaryPart_I_smul, x.property.coe_realPart]⟩

lemma ComplexStarModule.ext {x y : A} (h₁ : ℜ x = ℜ y) (h₂ : ℑ x = ℑ y) : x = y := by
  rw [← realPart_add_I_smul_imaginaryPart x, ← realPart_add_I_smul_imaginaryPart y, h₁, h₂]

lemma ComplexStarModule.ext_iff {x y : A} : x = y ↔ ℜ x = ℜ y ∧ ℑ x = ℑ y where
  mp := by grind
  mpr h := ext h.1 h.2

@[simp]
theorem ker_imaginaryPart : imaginaryPart.ker = selfAdjoint.submodule ℝ A := by
  ext x
  simp [selfAdjoint.submodule, selfAdjoint.mem_iff, imaginaryPart, Subtype.ext_iff]
  grind

@[simp]
lemma imaginaryPart_eq_zero_iff {x : A} : ℑ x = 0 ↔ IsSelfAdjoint x := by
  simpa [-ker_imaginaryPart] using! SetLike.ext_iff.mp ker_imaginaryPart x

open Submodule

lemma span_selfAdjoint : span ℂ (selfAdjoint A : Set A) = ⊤ := by
  refine eq_top_iff'.mpr fun x ↦ ?_
  rw [← realPart_add_I_smul_imaginaryPart x]
  exact add_mem (subset_span (ℜ x).property) <|
    SMulMemClass.smul_mem _ <| subset_span (ℑ x).property

end AddCommGroup

open scoped ComplexStarModule

/-- The natural `ℝ`-linear equivalence between `selfAdjoint ℂ` and `ℝ`. -/
@[simps apply symm_apply]
def Complex.selfAdjointEquiv : selfAdjoint ℂ ≃ₗ[ℝ] ℝ where
  toFun := fun z ↦ (z : ℂ).re
  invFun := fun x ↦ ⟨x, conj_ofReal x⟩
  left_inv := fun z ↦ Subtype.ext <| conj_eq_iff_re.mp z.property.star_eq
  map_add' := by simp
  map_smul' := by simp

lemma Complex.coe_selfAdjointEquiv (z : selfAdjoint ℂ) :
    (selfAdjointEquiv z : ℂ) = z := by
  simpa [selfAdjointEquiv_symm_apply]
    using (congr_arg Subtype.val <| Complex.selfAdjointEquiv.left_inv z)

@[simp]
lemma realPart_ofReal (r : ℝ) : (ℜ (r : ℂ) : ℂ) = r := by
  rw [realPart_apply_coe, star_def, conj_ofReal, ← two_smul ℝ (r : ℂ)]
  simp

@[simp]
lemma imaginaryPart_ofReal (r : ℝ) : ℑ (r : ℂ) = 0 := by
  ext1; simp [imaginaryPart_apply_coe, conj_ofReal]

set_option linter.style.whitespace false in -- manual alignment is not recognised
lemma Complex.coe_realPart (z : ℂ) : (ℜ z : ℂ) = z.re := calc
  (ℜ z : ℂ) = (↑(ℜ (↑z.re + ↑z.im * I))) := by congrm (ℜ $((re_add_im z).symm))
  _         = z.re                       := by
    rw [map_add, AddSubmonoid.coe_add, mul_comm, ← smul_eq_mul, realPart_I_smul]
    simp

section NonUnitalNonAssocRing

variable [NonUnitalNonAssocRing A] [StarRing A] [Module ℂ A] [IsScalarTower ℂ A A]
  [SMulCommClass ℂ A A] [StarModule ℂ A]

lemma star_mul_self_add_self_mul_star (a : A) :
    star a * a + a * star a = 2 • (ℜ a * ℜ a + ℑ a * ℑ a) :=
  have a_eq := (realPart_add_I_smul_imaginaryPart a).symm
  calc
    star a * a + a * star a = _ :=
      congr((star $(a_eq)) * $(a_eq) + $(a_eq) * (star $(a_eq)))
    _ = 2 • (ℜ a * ℜ a + ℑ a * ℑ a) := by
      simp [mul_add, add_mul, smul_smul, mul_smul_comm,
        smul_mul_assoc]
      abel

lemma star_mul_self_sub_self_mul_star (a : A) :
    star a * a - a * star a = 2 • I • (ℜ a * ℑ a - ℑ a * ℜ a) :=
  have a_eq := (realPart_add_I_smul_imaginaryPart a).symm
  calc
    star a * a - a * star a = _ :=
      congr((star $(a_eq)) * $(a_eq) - $(a_eq) * (star $(a_eq)))
    _ = 2 • I • (ℜ a * ℑ a - ℑ a * ℜ a) := by
      simp [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, smul_smul]
      module

/-- An element in a non-unital star `ℂ`-algebra is normal if and only if its real and imaginary
parts commute. -/
lemma isStarNormal_iff_commute_realPart_imaginaryPart {x : A} :
    IsStarNormal x ↔ Commute (ℜ x : A) (ℑ x : A) := by
  rw [isStarNormal_iff, commute_iff_eq, ← sub_eq_zero, star_mul_self_sub_self_mul_star,
    two_smul ℕ, ← two_smul ℂ, smul_eq_zero_iff_right two_ne_zero, smul_eq_zero_iff_right I_ne_zero,
    sub_eq_zero, commute_iff_eq]

lemma Commute.realPart_imaginaryPart (x : A) [IsStarNormal x] :
    Commute (ℜ x : A) (ℑ x : A) :=
  isStarNormal_iff_commute_realPart_imaginaryPart.mp inferInstance

lemma star_mul_self_eq_realPart_sq_add_imaginaryPart_sq (x : A) [hx : IsStarNormal x] :
    star x * x = ℜ x * ℜ x + ℑ x * ℑ x := calc
  star x * x = ℜ x * ℜ x + ℑ x * ℑ x + Complex.I • (ℜ x * ℑ x - ℑ x * ℜ x) := by
    conv_lhs => rw [← realPart_add_I_smul_imaginaryPart x]
    simp [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, smul_sub]
    grind
  _ = _ := by simp [Commute.realPart_imaginaryPart x |>.eq]

end NonUnitalNonAssocRing

section StarOrderedRing

variable [NonUnitalRing A] [StarRing A] [PartialOrder A]
    [StarOrderedRing A] [Module ℂ A] [StarModule ℂ A]

lemma nonneg_iff_realPart_imaginaryPart {a : A} :
    0 ≤ a ↔ 0 ≤ ℜ a ∧ ℑ a = 0 := by
  refine ⟨fun h ↦ ⟨?_, h.isSelfAdjoint.imaginaryPart⟩, fun h ↦ ?_⟩
  · simpa +singlePass [← h.isSelfAdjoint.coe_realPart] using! h
  · rw [← realPart_add_I_smul_imaginaryPart a, h.2]
    simpa using! h.1

lemma nonpos_iff_realPart_imaginaryPart {a : A} :
    a ≤ 0 ↔ ℜ a ≤ 0 ∧ ℑ a = 0 := by
  simpa using nonneg_iff_realPart_imaginaryPart (a := -a)

lemma realPart_nonneg_of_nonneg {a : A} (ha : 0 ≤ a) : 0 ≤ ℜ a :=
  nonneg_iff_realPart_imaginaryPart.mp ha |>.1

lemma realPart_nonpos_of_nonpos {a : A} (ha : a ≤ 0) : ℜ a ≤ 0 :=
  nonpos_iff_realPart_imaginaryPart.mp ha |>.1

lemma le_iff_realPart_imaginaryPart {a b : A} :
    a ≤ b ↔ ℜ a ≤ ℜ b ∧ ℑ a = ℑ b := by
  simpa [sub_eq_zero, eq_comm (a := ℑ a)] using nonneg_iff_realPart_imaginaryPart (a := b - a)

lemma imaginaryPart_eq_of_le {a b : A} (hab : a ≤ b) :
    ℑ a = ℑ b :=
  le_iff_realPart_imaginaryPart.mp hab |>.2

lemma realPart_mono {a b : A} (hab : a ≤ b) :
    ℜ a ≤ ℜ b :=
  le_iff_realPart_imaginaryPart.mp hab |>.1

end StarOrderedRing

@[simp]
lemma realPart_one [Ring A] [StarRing A] [Module ℂ A] [StarModule ℂ A] :
    ℜ (1 : A) = 1 := by
  ext; simp [realPart_apply_coe, ← two_smul ℝ]

lemma mem_unitary_iff_isStarNormal_and_realPart_sq_add_imaginaryPart_sq_eq_one [Ring A]
    [StarRing A] [Module ℂ A] [SMulCommClass ℂ A A] [IsScalarTower ℂ A A] [StarModule ℂ A] {x : A} :
    x ∈ unitary A ↔ IsStarNormal x ∧ ℜ x ^ 2 + ℑ x ^ 2 = (1 : A) := by
  rw [Unitary.mem_iff]
  refine ⟨fun ⟨h, h'⟩ ↦ ?_, fun ⟨hx, h⟩ ↦ ?_⟩
  · have : IsStarNormal x := ⟨h.trans h'.symm⟩
    exact ⟨this, by simp [sq, ← star_mul_self_eq_realPart_sq_add_imaginaryPart_sq x, h]⟩
  · simp [← hx.star_comm_self.eq, star_mul_self_eq_realPart_sq_add_imaginaryPart_sq, ← sq, h]

end RealImaginaryPart
