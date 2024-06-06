/-
Copyright (c) 2020 Alexander Bentkamp, Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Sébastien Gouëzel, Eric Wieser
-/
import Mathlib.Algebra.CharP.Invertible
import Mathlib.Algebra.Order.Module.OrderedSMul
import Mathlib.Data.Complex.Cardinality
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.FiniteDimensional

#align_import data.complex.module from "leanprover-community/mathlib"@"c7bce2818663f456335892ddbdd1809f111a5b72"

/-!
# Complex number as a vector space over `ℝ`

This file contains the following instances:
* Any `•`-structure (`SMul`, `MulAction`, `DistribMulAction`, `Module`, `Algebra`) on
  `ℝ` imbues a corresponding structure on `ℂ`. This includes the statement that `ℂ` is an `ℝ`
  algebra.
* any complex vector space is a real vector space;
* any finite dimensional complex vector space is a finite dimensional real vector space;
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


namespace Complex

open ComplexConjugate

open scoped SMul

variable {R : Type*} {S : Type*}

attribute [local ext] Complex.ext

-- Test that the `SMul ℚ ℂ` instance is correct.
example : (Complex.SMul.instSMulRealComplex : SMul ℚ ℂ) = (Algebra.toSMul : SMul ℚ ℂ) := rfl

/- The priority of the following instances has been manually lowered, as when they don't apply
they lead Lean to a very costly path, and most often they don't apply (most actions on `ℂ` don't
come from actions on `ℝ`). See #11980-/

-- priority manually adjusted in #11980
instance (priority := 90) [SMul R ℝ] [SMul S ℝ] [SMulCommClass R S ℝ] : SMulCommClass R S ℂ where
  smul_comm r s x := by ext <;> simp [smul_re, smul_im, smul_comm]

-- priority manually adjusted in #11980
instance (priority := 90) [SMul R S] [SMul R ℝ] [SMul S ℝ] [IsScalarTower R S ℝ] :
    IsScalarTower R S ℂ where
  smul_assoc r s x := by ext <;> simp [smul_re, smul_im, smul_assoc]

-- priority manually adjusted in #11980
instance (priority := 90) [SMul R ℝ] [SMul Rᵐᵒᵖ ℝ] [IsCentralScalar R ℝ] :
    IsCentralScalar R ℂ where
  op_smul_eq_smul r x := by ext <;> simp [smul_re, smul_im, op_smul_eq_smul]

-- priority manually adjusted in #11980
instance (priority := 90) mulAction [Monoid R] [MulAction R ℝ] : MulAction R ℂ where
  one_smul x := by ext <;> simp [smul_re, smul_im, one_smul]
  mul_smul r s x := by ext <;> simp [smul_re, smul_im, mul_smul]

-- priority manually adjusted in #11980
instance (priority := 90) distribSMul [DistribSMul R ℝ] : DistribSMul R ℂ where
  smul_add r x y := by ext <;> simp [smul_re, smul_im, smul_add]
  smul_zero r := by ext <;> simp [smul_re, smul_im, smul_zero]

-- priority manually adjusted in #11980
instance (priority := 90) [Semiring R] [DistribMulAction R ℝ] : DistribMulAction R ℂ :=
  { Complex.distribSMul, Complex.mulAction with }

-- priority manually adjusted in #11980
instance (priority := 100) instModule [Semiring R] [Module R ℝ] : Module R ℂ where
  add_smul r s x := by ext <;> simp [smul_re, smul_im, add_smul]
  zero_smul r := by ext <;> simp [smul_re, smul_im, zero_smul]

-- priority manually adjusted in #11980
instance (priority := 95) instAlgebraOfReal [CommSemiring R] [Algebra R ℝ] : Algebra R ℂ :=
  { Complex.ofReal.comp (algebraMap R ℝ) with
    smul := (· • ·)
    smul_def' := fun r x => by ext <;> simp [smul_re, smul_im, Algebra.smul_def]
    commutes' := fun r ⟨xr, xi⟩ => by ext <;> simp [smul_re, smul_im, Algebra.commutes] }

instance : StarModule ℝ ℂ :=
  ⟨fun r x => by simp only [star_def, star_trivial, real_smul, map_mul, conj_ofReal]⟩

@[simp]
theorem coe_algebraMap : (algebraMap ℝ ℂ : ℝ → ℂ) = ((↑) : ℝ → ℂ) :=
  rfl
#align complex.coe_algebra_map Complex.coe_algebraMap

section

variable {A : Type*} [Semiring A] [Algebra ℝ A]

/-- We need this lemma since `Complex.coe_algebraMap` diverts the simp-normal form away from
`AlgHom.commutes`. -/
@[simp]
theorem _root_.AlgHom.map_coe_real_complex (f : ℂ →ₐ[ℝ] A) (x : ℝ) : f x = algebraMap ℝ A x :=
  f.commutes x
#align alg_hom.map_coe_real_complex AlgHom.map_coe_real_complex

/-- Two `ℝ`-algebra homomorphisms from `ℂ` are equal if they agree on `Complex.I`. -/
@[ext]
theorem algHom_ext ⦃f g : ℂ →ₐ[ℝ] A⦄ (h : f I = g I) : f = g := by
  ext ⟨x, y⟩
  simp only [mk_eq_add_mul_I, AlgHom.map_add, AlgHom.map_coe_real_complex, AlgHom.map_mul, h]
#align complex.alg_hom_ext Complex.algHom_ext

end

open Submodule FiniteDimensional

/-- `ℂ` has a basis over `ℝ` given by `1` and `I`. -/
noncomputable def basisOneI : Basis (Fin 2) ℝ ℂ :=
  Basis.ofEquivFun
    { toFun := fun z => ![z.re, z.im]
      invFun := fun c => c 0 + c 1 • I
      left_inv := fun z => by simp
      right_inv := fun c => by
        ext i
        fin_cases i <;> simp
      map_add' := fun z z' => by simp
      map_smul' := fun c z => by simp }
set_option linter.uppercaseLean3 false in
#align complex.basis_one_I Complex.basisOneI

@[simp]
theorem coe_basisOneI_repr (z : ℂ) : ⇑(basisOneI.repr z) = ![z.re, z.im] :=
  rfl
set_option linter.uppercaseLean3 false in
#align complex.coe_basis_one_I_repr Complex.coe_basisOneI_repr

@[simp]
theorem coe_basisOneI : ⇑basisOneI = ![1, I] :=
  funext fun i =>
    Basis.apply_eq_iff.mpr <|
      Finsupp.ext fun j => by
        fin_cases i <;> fin_cases j <;>
          -- Porting note: removed `only`, consider squeezing again
          simp [coe_basisOneI_repr, Finsupp.single_eq_of_ne, Matrix.cons_val_zero,
            Matrix.cons_val_one, Matrix.head_cons, Fin.one_eq_zero_iff, Ne, not_false_iff, I_re,
            Nat.succ_succ_ne_one, one_im, I_im, one_re, Finsupp.single_eq_same, Fin.zero_eq_one_iff]
set_option linter.uppercaseLean3 false in
#align complex.coe_basis_one_I Complex.coe_basisOneI

instance : FiniteDimensional ℝ ℂ :=
  of_fintype_basis basisOneI

@[simp]
theorem finrank_real_complex : FiniteDimensional.finrank ℝ ℂ = 2 := by
  rw [finrank_eq_card_basis basisOneI, Fintype.card_fin]
#align complex.finrank_real_complex Complex.finrank_real_complex

@[simp]
theorem rank_real_complex : Module.rank ℝ ℂ = 2 := by simp [← finrank_eq_rank, finrank_real_complex]
#align complex.rank_real_complex Complex.rank_real_complex

theorem rank_real_complex'.{u} : Cardinal.lift.{u} (Module.rank ℝ ℂ) = 2 := by
  rw [← finrank_eq_rank, finrank_real_complex, Cardinal.lift_natCast, Nat.cast_ofNat]
#align complex.rank_real_complex' Complex.rank_real_complex'

/-- `Fact` version of the dimension of `ℂ` over `ℝ`, locally useful in the definition of the
circle. -/
theorem finrank_real_complex_fact : Fact (finrank ℝ ℂ = 2) :=
  ⟨finrank_real_complex⟩
#align complex.finrank_real_complex_fact Complex.finrank_real_complex_fact

end Complex

/- Register as an instance (with low priority) the fact that a complex vector space is also a real
vector space. -/
instance (priority := 900) Module.complexToReal (E : Type*) [AddCommGroup E] [Module ℂ E] :
    Module ℝ E :=
  RestrictScalars.module ℝ ℂ E
#align module.complex_to_real Module.complexToReal

/- Register as an instance (with low priority) the fact that a complex algebra is also a real
algebra. -/
instance (priority := 900) Algebra.complexToReal {A : Type*} [Semiring A] [Algebra ℂ A] :
    Algebra ℝ A :=
  RestrictScalars.algebra ℝ ℂ A

-- try to make sure we're not introducing diamonds but we will need
-- `reducible_and_instances` which currently fails #10906
example : Prod.algebra ℝ ℂ ℂ = (Prod.algebra ℂ ℂ ℂ).complexToReal := rfl

-- try to make sure we're not introducing diamonds but we will need
-- `reducible_and_instances` which currently fails #10906
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
#align complex.coe_smul Complex.coe_smul

/-- The scalar action of `ℝ` on a `ℂ`-module `E` induced by `Module.complexToReal` commutes with
another scalar action of `M` on `E` whenever the action of `ℂ` commutes with the action of `M`. -/
instance (priority := 900) SMulCommClass.complexToReal {M E : Type*} [AddCommGroup E] [Module ℂ E]
    [SMul M E] [SMulCommClass ℂ M E] : SMulCommClass ℝ M E where
  smul_comm r _ _ := (smul_comm (r : ℂ) _ _ : _)
#align smul_comm_class.complex_to_real SMulCommClass.complexToReal

/-- The scalar action of `ℝ` on a `ℂ`-module `E` induced by `Module.complexToReal` associates with
another scalar action of `M` on `E` whenever the action of `ℂ` associates with the action of `M`. -/
instance IsScalarTower.complexToReal {M E : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup E]
    [Module ℂ E] [SMul M E] [IsScalarTower ℂ M E] : IsScalarTower ℝ M E where
  smul_assoc r _ _ := (smul_assoc (r : ℂ) _ _ : _)
#align module.real_complex_tower IsScalarTower.complexToReal

-- check that the following instance is implied by the one above.
example (E : Type*) [AddCommGroup E] [Module ℂ E] : IsScalarTower ℝ ℂ E := inferInstance

instance (priority := 100) FiniteDimensional.complexToReal (E : Type*) [AddCommGroup E]
    [Module ℂ E] [FiniteDimensional ℂ E] : FiniteDimensional ℝ E :=
  FiniteDimensional.trans ℝ ℂ E
#align finite_dimensional.complex_to_real FiniteDimensional.complexToReal

theorem rank_real_of_complex (E : Type*) [AddCommGroup E] [Module ℂ E] :
    Module.rank ℝ E = 2 * Module.rank ℂ E :=
  Cardinal.lift_inj.1 <| by
    rw [← lift_rank_mul_lift_rank ℝ ℂ E, Complex.rank_real_complex']
    simp only [Cardinal.lift_id']
#align rank_real_of_complex rank_real_of_complex

theorem finrank_real_of_complex (E : Type*) [AddCommGroup E] [Module ℂ E] :
    FiniteDimensional.finrank ℝ E = 2 * FiniteDimensional.finrank ℂ E := by
  rw [← FiniteDimensional.finrank_mul_finrank ℝ ℂ E, Complex.finrank_real_complex]
#align finrank_real_of_complex finrank_real_of_complex

instance (priority := 900) StarModule.complexToReal {E : Type*} [AddCommGroup E] [Star E]
    [Module ℂ E] [StarModule ℂ E] : StarModule ℝ E :=
  ⟨fun r a => by rw [← smul_one_smul ℂ r a, star_smul, star_smul, star_one, smul_one_smul]⟩
#align star_module.complex_to_real StarModule.complexToReal

namespace Complex

open ComplexConjugate

/-- Linear map version of the real part function, from `ℂ` to `ℝ`. -/
def reLm : ℂ →ₗ[ℝ] ℝ where
  toFun x := x.re
  map_add' := add_re
  map_smul' := by simp
#align complex.re_lm Complex.reLm

@[simp]
theorem reLm_coe : ⇑reLm = re :=
  rfl
#align complex.re_lm_coe Complex.reLm_coe

/-- Linear map version of the imaginary part function, from `ℂ` to `ℝ`. -/
def imLm : ℂ →ₗ[ℝ] ℝ where
  toFun x := x.im
  map_add' := add_im
  map_smul' := by simp
#align complex.im_lm Complex.imLm

@[simp]
theorem imLm_coe : ⇑imLm = im :=
  rfl
#align complex.im_lm_coe Complex.imLm_coe

/-- `ℝ`-algebra morphism version of the canonical embedding of `ℝ` in `ℂ`. -/
def ofRealAm : ℝ →ₐ[ℝ] ℂ :=
  Algebra.ofId ℝ ℂ
#align complex.of_real_am Complex.ofRealAm

@[simp]
theorem ofRealAm_coe : ⇑ofRealAm = ((↑) : ℝ → ℂ) :=
  rfl
#align complex.of_real_am_coe Complex.ofRealAm_coe

/-- `ℝ`-algebra isomorphism version of the complex conjugation function from `ℂ` to `ℂ` -/
def conjAe : ℂ ≃ₐ[ℝ] ℂ :=
  { conj with
    invFun := conj
    left_inv := star_star
    right_inv := star_star
    commutes' := conj_ofReal }
#align complex.conj_ae Complex.conjAe

@[simp]
theorem conjAe_coe : ⇑conjAe = conj :=
  rfl
#align complex.conj_ae_coe Complex.conjAe_coe

/-- The matrix representation of `conjAe`. -/
@[simp]
theorem toMatrix_conjAe :
    LinearMap.toMatrix basisOneI basisOneI conjAe.toLinearMap = !![1, 0; 0, -1] := by
  ext i j
  -- Porting note: replaced non-terminal `simp [LinearMap.toMatrix_apply]`
  fin_cases i <;> fin_cases j <;> simp [LinearMap.toMatrix_apply]
#align complex.to_matrix_conj_ae Complex.toMatrix_conjAe

/-- The identity and the complex conjugation are the only two `ℝ`-algebra homomorphisms of `ℂ`. -/
theorem real_algHom_eq_id_or_conj (f : ℂ →ₐ[ℝ] ℂ) : f = AlgHom.id ℝ ℂ ∨ f = conjAe := by
  refine
      (eq_or_eq_neg_of_sq_eq_sq (f I) I <| by rw [← map_pow, I_sq, map_neg, map_one]).imp ?_ ?_ <;>
    refine fun h => algHom_ext ?_
  exacts [h, conj_I.symm ▸ h]
#align complex.real_alg_hom_eq_id_or_conj Complex.real_algHom_eq_id_or_conj

/-- The natural `AddEquiv` from `ℂ` to `ℝ × ℝ`. -/
@[simps! (config := { simpRhs := true }) apply symm_apply_re symm_apply_im]
def equivRealProdAddHom : ℂ ≃+ ℝ × ℝ :=
  { equivRealProd with map_add' := by simp }
#align complex.equiv_real_prod_add_hom Complex.equivRealProdAddHom

theorem equivRealProdAddHom_symm_apply (p : ℝ × ℝ) :
    Complex.equivRealProdAddHom.symm p = p.1 + p.2 * Complex.I := Complex.equivRealProd_symm_apply p

/-- The natural `LinearEquiv` from `ℂ` to `ℝ × ℝ`. -/
@[simps! (config := { simpRhs := true }) apply symm_apply_re symm_apply_im]
def equivRealProdLm : ℂ ≃ₗ[ℝ] ℝ × ℝ :=
  { equivRealProdAddHom with
    -- Porting note: `simp` has issues with `Prod.smul_def`
    map_smul' := fun r c => by simp [equivRealProdAddHom, Prod.smul_def, smul_eq_mul] }
#align complex.equiv_real_prod_lm Complex.equivRealProdLm

theorem equivRealProdLm_symm_apply (p : ℝ × ℝ) :
    Complex.equivRealProdLm.symm p = p.1 + p.2 * Complex.I := Complex.equivRealProd_symm_apply p
section lift

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- There is an alg_hom from `ℂ` to any `ℝ`-algebra with an element that squares to `-1`.

See `Complex.lift` for this as an equiv. -/
def liftAux (I' : A) (hf : I' * I' = -1) : ℂ →ₐ[ℝ] A :=
  AlgHom.ofLinearMap
    ((Algebra.linearMap ℝ A).comp reLm + (LinearMap.toSpanSingleton _ _ I').comp imLm)
    (show algebraMap ℝ A 1 + (0 : ℝ) • I' = 1 by rw [RingHom.map_one, zero_smul, add_zero])
    fun ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ =>
    show
      algebraMap ℝ A (x₁ * x₂ - y₁ * y₂) + (x₁ * y₂ + y₁ * x₂) • I' =
        (algebraMap ℝ A x₁ + y₁ • I') * (algebraMap ℝ A x₂ + y₂ • I') by
      rw [add_mul, mul_add, mul_add, add_comm _ (y₁ • I' * y₂ • I'), add_add_add_comm]
      congr 1
      -- equate "real" and "imaginary" parts
      · let inst : SMulCommClass ℝ A A := by infer_instance  -- Porting note: added
        rw [smul_mul_smul, hf, smul_neg, ← Algebra.algebraMap_eq_smul_one, ← sub_eq_add_neg, ←
          RingHom.map_mul, ← RingHom.map_sub]
      · rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, ← Algebra.right_comm _ x₂, ←
          mul_assoc, ← add_mul, ← RingHom.map_mul, ← RingHom.map_mul, ← RingHom.map_add]
#align complex.lift_aux Complex.liftAux

@[simp]
theorem liftAux_apply (I' : A) (hI') (z : ℂ) : liftAux I' hI' z = algebraMap ℝ A z.re + z.im • I' :=
  rfl
#align complex.lift_aux_apply Complex.liftAux_apply

theorem liftAux_apply_I (I' : A) (hI') : liftAux I' hI' I = I' := by simp
set_option linter.uppercaseLean3 false in
#align complex.lift_aux_apply_I Complex.liftAux_apply_I

/-- A universal property of the complex numbers, providing a unique `ℂ →ₐ[ℝ] A` for every element
of `A` which squares to `-1`.

This can be used to embed the complex numbers in the `Quaternion`s.

This isomorphism is named to match the very similar `Zsqrtd.lift`. -/
@[simps (config := { simpRhs := true })]
def lift : { I' : A // I' * I' = -1 } ≃ (ℂ →ₐ[ℝ] A) where
  toFun I' := liftAux I' I'.prop
  invFun F := ⟨F I, by rw [← F.map_mul, I_mul_I, AlgHom.map_neg, AlgHom.map_one]⟩
  left_inv I' := Subtype.ext <| liftAux_apply_I (I' : A) I'.prop
  right_inv F := algHom_ext <| liftAux_apply_I _ _
#align complex.lift Complex.lift

-- When applied to `Complex.I` itself, `lift` is the identity.
@[simp]
theorem liftAux_I : liftAux I I_mul_I = AlgHom.id ℝ ℂ :=
  algHom_ext <| liftAux_apply_I _ _
set_option linter.uppercaseLean3 false in
#align complex.lift_aux_I Complex.liftAux_I

-- When applied to `-Complex.I`, `lift` is conjugation, `conj`.
@[simp]
theorem liftAux_neg_I : liftAux (-I) ((neg_mul_neg _ _).trans I_mul_I) = conjAe :=
  algHom_ext <| (liftAux_apply_I _ _).trans conj_I.symm
set_option linter.uppercaseLean3 false in
#align complex.lift_aux_neg_I Complex.liftAux_neg_I

end lift

end Complex

section RealImaginaryPart

open Complex

variable {A : Type*} [AddCommGroup A] [Module ℂ A] [StarAddMonoid A] [StarModule ℂ A]

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
    simp only [neg_smul, skewAdjoint.val_smul, AddSubgroup.coe_mk, RingHom.id_apply,
      selfAdjoint.val_smul, smul_neg, neg_inj]
    rw [smul_comm]
set_option linter.uppercaseLean3 false in
#align skew_adjoint.neg_I_smul skewAdjoint.negISMul

theorem skewAdjoint.I_smul_neg_I (a : skewAdjoint A) : I • (skewAdjoint.negISMul a : A) = a := by
  simp only [smul_smul, skewAdjoint.negISMul_apply_coe, neg_smul, smul_neg, I_mul_I, one_smul,
    neg_neg]
set_option linter.uppercaseLean3 false in
#align skew_adjoint.I_smul_neg_I skewAdjoint.I_smul_neg_I

/-- The real part `ℜ a` of an element `a` of a star module over `ℂ`, as a linear map. This is just
`selfAdjointPart ℝ`, but we provide it as a separate definition in order to link it with lemmas
concerning the `imaginaryPart`, which doesn't exist in star modules over other rings. -/
noncomputable def realPart : A →ₗ[ℝ] selfAdjoint A :=
  selfAdjointPart ℝ
#align real_part realPart

/-- The imaginary part `ℑ a` of an element `a` of a star module over `ℂ`, as a linear map into the
self adjoint elements. In a general star module, we have a decomposition into the `selfAdjoint`
and `skewAdjoint` parts, but in a star module over `ℂ` we have
`realPart_add_I_smul_imaginaryPart`, which allows us to decompose into a linear combination of
`selfAdjoint`s. -/
noncomputable def imaginaryPart : A →ₗ[ℝ] selfAdjoint A :=
  skewAdjoint.negISMul.comp (skewAdjointPart ℝ)
#align imaginary_part imaginaryPart

@[inherit_doc]
scoped[ComplexStarModule] notation "ℜ" => realPart
@[inherit_doc]
scoped[ComplexStarModule] notation "ℑ" => imaginaryPart

open ComplexStarModule

theorem realPart_apply_coe (a : A) : (ℜ a : A) = (2 : ℝ)⁻¹ • (a + star a) := by
  unfold realPart
  simp only [selfAdjointPart_apply_coe, invOf_eq_inv]
#align real_part_apply_coe realPart_apply_coe

theorem imaginaryPart_apply_coe (a : A) : (ℑ a : A) = -I • (2 : ℝ)⁻¹ • (a - star a) := by
  unfold imaginaryPart
  simp only [LinearMap.coe_comp, Function.comp_apply, skewAdjoint.negISMul_apply_coe,
    skewAdjointPart_apply_coe, invOf_eq_inv, neg_smul]
#align imaginary_part_apply_coe imaginaryPart_apply_coe

/-- The standard decomposition of `ℜ a + Complex.I • ℑ a = a` of an element of a star module over
`ℂ` into a linear combination of self adjoint elements. -/
theorem realPart_add_I_smul_imaginaryPart (a : A) : (ℜ a : A) + I • (ℑ a : A) = a := by
  simpa only [smul_smul, realPart_apply_coe, imaginaryPart_apply_coe, neg_smul, I_mul_I, one_smul,
    neg_sub, add_add_sub_cancel, smul_sub, smul_add, neg_sub_neg, invOf_eq_inv] using
    invOf_two_smul_add_invOf_two_smul ℝ a
set_option linter.uppercaseLean3 false in
#align real_part_add_I_smul_imaginary_part realPart_add_I_smul_imaginaryPart

@[simp]
theorem realPart_I_smul (a : A) : ℜ (I • a) = -ℑ a := by
  ext
  -- Porting note: was
  -- simp [smul_comm I, smul_sub, sub_eq_add_neg, add_comm]
  rw [realPart_apply_coe, NegMemClass.coe_neg, imaginaryPart_apply_coe, neg_smul, neg_neg,
    smul_comm I, star_smul, star_def, conj_I, smul_sub, neg_smul, sub_eq_add_neg]
set_option linter.uppercaseLean3 false in
#align real_part_I_smul realPart_I_smul

@[simp]
theorem imaginaryPart_I_smul (a : A) : ℑ (I • a) = ℜ a := by
  ext
  -- Porting note: was
  -- simp [smul_comm I, smul_smul I]
  rw [realPart_apply_coe, imaginaryPart_apply_coe, smul_comm]
  simp [← smul_assoc]
set_option linter.uppercaseLean3 false in
#align imaginary_part_I_smul imaginaryPart_I_smul

theorem realPart_smul (z : ℂ) (a : A) : ℜ (z • a) = z.re • ℜ a - z.im • ℑ a := by
  have := by congrm (ℜ ($((re_add_im z).symm) • a))
  simpa [-re_add_im, add_smul, ← smul_smul, sub_eq_add_neg]
#align real_part_smul realPart_smul

theorem imaginaryPart_smul (z : ℂ) (a : A) : ℑ (z • a) = z.re • ℑ a + z.im • ℜ a := by
  have := by congrm (ℑ ($((re_add_im z).symm) • a))
  simpa [-re_add_im, add_smul, ← smul_smul]
#align imaginary_part_smul imaginaryPart_smul

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
lemma imaginaryPart_realPart {x : A} : ℑ (ℜ x : A) = 0 :=
  (ℜ x).property.imaginaryPart

@[simp]
lemma imaginaryPart_imaginaryPart {x : A} : ℑ (ℑ x : A) = 0 :=
  (ℑ x).property.imaginaryPart

@[simp]
lemma realPart_idem {x : A} : ℜ (ℜ x : A) = ℜ x :=
  Subtype.ext <| (ℜ x).property.coe_realPart

@[simp]
lemma realPart_imaginaryPart {x : A} : ℜ (ℑ x : A) = ℑ x :=
  Subtype.ext <| (ℑ x).property.coe_realPart

lemma realPart_surjective : Function.Surjective (realPart (A := A)) :=
  fun x ↦ ⟨(x : A), Subtype.ext x.property.coe_realPart⟩

lemma imaginaryPart_surjective : Function.Surjective (imaginaryPart (A := A)) :=
  fun x ↦
    ⟨I • (x : A), Subtype.ext <| by simp only [imaginaryPart_I_smul, x.property.coe_realPart]⟩

open Submodule

lemma span_selfAdjoint : span ℂ (selfAdjoint A : Set A) = ⊤ := by
  refine eq_top_iff'.mpr fun x ↦ ?_
  rw [← realPart_add_I_smul_imaginaryPart x]
  exact add_mem (subset_span (ℜ x).property) <|
    SMulMemClass.smul_mem _ <| subset_span (ℑ x).property

/-- The natural `ℝ`-linear equivalence between `selfAdjoint ℂ` and `ℝ`. -/
@[simps apply symm_apply]
def Complex.selfAdjointEquiv : selfAdjoint ℂ ≃ₗ[ℝ] ℝ where
  toFun := fun z ↦ (z : ℂ).re
  invFun := fun x ↦ ⟨x, conj_ofReal x⟩
  left_inv := fun z ↦ Subtype.ext <| conj_eq_iff_re.mp z.property.star_eq
  right_inv := fun x ↦ rfl
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

lemma Complex.coe_realPart (z : ℂ) : (ℜ z : ℂ) = z.re := calc
  (ℜ z : ℂ) = _    := by congrm (ℜ $((re_add_im z).symm))
  _          = z.re := by
    rw [map_add, AddSubmonoid.coe_add, mul_comm, ← smul_eq_mul, realPart_I_smul]
    simp [conj_ofReal, ← two_mul]

lemma star_mul_self_add_self_mul_star {A : Type*} [NonUnitalRing A] [StarRing A]
    [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [StarModule ℂ A] (a : A) :
    star a * a + a * star a = 2 • (ℜ a * ℜ a + ℑ a * ℑ a) :=
  have a_eq := (realPart_add_I_smul_imaginaryPart a).symm
  calc
    star a * a + a * star a = _ :=
      congr((star $(a_eq)) * $(a_eq) + $(a_eq) * (star $(a_eq)))
    _ = 2 • (ℜ a * ℜ a + ℑ a * ℑ a) := by
      simp [mul_add, add_mul, smul_smul, two_smul, mul_smul_comm,
        smul_mul_assoc]
      abel

end RealImaginaryPart

section Rational

open Cardinal Module

@[simp]
lemma Real.rank_rat_real : Module.rank ℚ ℝ = continuum := by
  refine (Free.rank_eq_mk_of_infinite_lt ℚ ℝ ?_).trans mk_real
  simpa [mk_real] using aleph0_lt_continuum

@[simp]
lemma Complex.rank_rat_complex : Module.rank ℚ ℂ = continuum := by
  refine (Free.rank_eq_mk_of_infinite_lt ℚ ℂ ?_).trans mk_complex
  simpa using aleph0_lt_continuum

/-- `ℂ` and `ℝ` are isomorphic as vector spaces over `ℚ`, or equivalently,
as additive groups. -/
theorem Complex.nonempty_linearEquiv_real : Nonempty (ℂ ≃ₗ[ℚ] ℝ) :=
  LinearEquiv.nonempty_equiv_iff_rank_eq.mpr <| by simp

end Rational
