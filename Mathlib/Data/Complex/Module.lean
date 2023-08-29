/-
Copyright (c) 2020 Alexander Bentkamp, Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Sébastien Gouëzel, Eric Wieser
-/
import Mathlib.Algebra.Order.SMul
import Mathlib.Data.Complex.Cardinality
import Mathlib.Data.Fin.VecNotation
import Mathlib.FieldTheory.Tower
import Mathlib.Algebra.CharP.Invertible

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

variable {R : Type*} {S : Type*}

instance [SMul R ℝ] [SMul S ℝ] [SMulCommClass R S ℝ] : SMulCommClass R S ℂ where
  smul_comm r s x := by ext <;> simp [smul_re, smul_im, smul_comm]
                        -- ⊢ (r • s • x).re = (s • r • x).re
                                -- 🎉 no goals
                                -- 🎉 no goals

instance [SMul R S] [SMul R ℝ] [SMul S ℝ] [IsScalarTower R S ℝ] : IsScalarTower R S ℂ where
  smul_assoc r s x := by ext <;> simp [smul_re, smul_im, smul_assoc]
                         -- ⊢ ((r • s) • x).re = (r • s • x).re
                                 -- 🎉 no goals
                                 -- 🎉 no goals

instance [SMul R ℝ] [SMul Rᵐᵒᵖ ℝ] [IsCentralScalar R ℝ] : IsCentralScalar R ℂ where
  op_smul_eq_smul r x := by ext <;> simp [smul_re, smul_im, op_smul_eq_smul]
                            -- ⊢ (MulOpposite.op r • x).re = (r • x).re
                                    -- 🎉 no goals
                                    -- 🎉 no goals

instance mulAction [Monoid R] [MulAction R ℝ] : MulAction R ℂ where
  one_smul x := by ext <;> simp [smul_re, smul_im, one_smul]
                   -- ⊢ (1 • x).re = x.re
                           -- 🎉 no goals
                           -- 🎉 no goals
  mul_smul r s x := by ext <;> simp [smul_re, smul_im, mul_smul]
                       -- ⊢ ((r * s) • x).re = (r • s • x).re
                               -- 🎉 no goals
                               -- 🎉 no goals

instance distribSMul [DistribSMul R ℝ] : DistribSMul R ℂ where
  smul_add r x y := by ext <;> simp [smul_re, smul_im, smul_add]
                       -- ⊢ (r • (x + y)).re = (r • x + r • y).re
                    -- ⊢ (r • 0).re = 0.re
                            -- 🎉 no goals
                            -- 🎉 no goals
                               -- 🎉 no goals
                               -- 🎉 no goals
  smul_zero r := by ext <;> simp [smul_re, smul_im, smul_zero]

instance [Semiring R] [DistribMulAction R ℝ] : DistribMulAction R ℂ :=
  { Complex.distribSMul, Complex.mulAction with }

instance [Semiring R] [Module R ℝ] : Module R ℂ where
  add_smul r s x := by ext <;> simp [smul_re, smul_im, add_smul]
                       -- ⊢ ((r + s) • x).re = (r • x + s • x).re
                               -- 🎉 no goals
                               -- 🎉 no goals
  zero_smul r := by ext <;> simp [smul_re, smul_im, zero_smul]
                    -- ⊢ (0 • r).re = 0.re
                            -- 🎉 no goals
                            -- 🎉 no goals

instance [CommSemiring R] [Algebra R ℝ] : Algebra R ℂ :=
  { Complex.ofReal.comp (algebraMap R ℝ) with
    smul := (· • ·)
    smul_def' := fun r x => by ext <;> simp [smul_re, smul_im, Algebra.smul_def]
                               -- ⊢ (r • x).re = (↑{ toMonoidHom := ↑src✝, map_zero' := (_ : OneHom.toFun (↑↑src …
                                      -- ⊢ (↑{ toMonoidHom := ↑src✝, map_zero' := (_ : OneHom.toFun (↑↑src✝) 0 = 0), ma …
                                              -- 🎉 no goals
                                              -- 🎉 no goals
                                       -- 🎉 no goals
                                       -- 🎉 no goals
    commutes' := fun r ⟨xr, xi⟩ => by ext <;> simp [smul_re, smul_im, Algebra.commutes] }

instance : StarModule ℝ ℂ :=
  ⟨fun r x => by simp only [star_def, star_trivial, real_smul, map_mul, conj_ofReal]⟩
                 -- 🎉 no goals

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
  -- ⊢ ↑f { re := x, im := y } = ↑g { re := x, im := y }
  simp only [mk_eq_add_mul_I, AlgHom.map_add, AlgHom.map_coe_real_complex, AlgHom.map_mul, h]
  -- 🎉 no goals
#align complex.alg_hom_ext Complex.algHom_ext

end

open Submodule FiniteDimensional

/-- `ℂ` has a basis over `ℝ` given by `1` and `I`. -/
noncomputable def basisOneI : Basis (Fin 2) ℝ ℂ :=
  Basis.ofEquivFun
    { toFun := fun z => ![z.re, z.im]
      invFun := fun c => c 0 + c 1 • I
      left_inv := fun z => by simp
                              -- 🎉 no goals
      right_inv := fun c => by
        ext i
        -- ⊢ AddHom.toFun { toAddHom := { toFun := fun z => ![z.re, z.im], map_add' := (_ …
                                 -- 🎉 no goals
        fin_cases i <;> simp
                                 -- 🎉 no goals
        -- ⊢ AddHom.toFun { toAddHom := { toFun := fun z => ![z.re, z.im], map_add' := (_ …
                        -- 🎉 no goals
                        -- 🎉 no goals
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
        -- ⊢ ↑(↑basisOneI.repr (Matrix.vecCons 1 ![I] { val := 0, isLt := (_ : 0 < 2) })) …
                        -- ⊢ ↑(↑basisOneI.repr (Matrix.vecCons 1 ![I] { val := 0, isLt := (_ : 0 < 2) })) …
                        -- ⊢ ↑(↑basisOneI.repr (Matrix.vecCons 1 ![I] { val := 1, isLt := (_ : (fun a =>  …
          -- Porting note: removed `only`, consider squeezing again
          simp [coe_basisOneI_repr, Finsupp.single_eq_of_ne, Matrix.cons_val_zero,
            Matrix.cons_val_one, Matrix.head_cons, Fin.one_eq_zero_iff, Ne.def, not_false_iff, I_re,
            Nat.succ_succ_ne_one, one_im, I_im, one_re, Finsupp.single_eq_same, Fin.zero_eq_one_iff]
set_option linter.uppercaseLean3 false in
#align complex.coe_basis_one_I Complex.coe_basisOneI

instance : FiniteDimensional ℝ ℂ :=
  of_fintype_basis basisOneI

@[simp]
theorem finrank_real_complex : FiniteDimensional.finrank ℝ ℂ = 2 := by
  rw [finrank_eq_card_basis basisOneI, Fintype.card_fin]
  -- 🎉 no goals
#align complex.finrank_real_complex Complex.finrank_real_complex

@[simp]
theorem rank_real_complex : Module.rank ℝ ℂ = 2 := by simp [← finrank_eq_rank, finrank_real_complex]
                                                      -- 🎉 no goals
#align complex.rank_real_complex Complex.rank_real_complex

theorem rank_real_complex'.{u} : Cardinal.lift.{u} (Module.rank ℝ ℂ) = 2 := by
  rw [← finrank_eq_rank, finrank_real_complex, Cardinal.lift_natCast, Nat.cast_ofNat]
  -- 🎉 no goals
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

instance Module.real_complex_tower (E : Type*) [AddCommGroup E] [Module ℂ E] :
    IsScalarTower ℝ ℂ E :=
  RestrictScalars.isScalarTower ℝ ℂ E
#align module.real_complex_tower Module.real_complex_tower

@[simp, norm_cast]
theorem Complex.coe_smul {E : Type*} [AddCommGroup E] [Module ℂ E] (x : ℝ) (y : E) :
    (x : ℂ) • y = x • y :=
  rfl
#align complex.coe_smul Complex.coe_smul

/-- The scalar action of `ℝ` on a `ℂ`-module `E` induced by `Module.complexToReal` commutes with
another scalar action of `M` on `E` whenever the action of `ℂ` commutes with the action of `M`. -/
instance (priority := 900) SMulCommClass.complexToReal {M E : Type*} [AddCommGroup E] [Module ℂ E]
    [SMul M E] [SMulCommClass ℂ M E] : SMulCommClass ℝ M E
    where smul_comm r _ _ := (smul_comm (r : ℂ) _ _ : _)
#align smul_comm_class.complex_to_real SMulCommClass.complexToReal

instance (priority := 100) FiniteDimensional.complexToReal (E : Type*) [AddCommGroup E]
    [Module ℂ E] [FiniteDimensional ℂ E] : FiniteDimensional ℝ E :=
  FiniteDimensional.trans ℝ ℂ E
#align finite_dimensional.complex_to_real FiniteDimensional.complexToReal

theorem rank_real_of_complex (E : Type*) [AddCommGroup E] [Module ℂ E] :
    Module.rank ℝ E = 2 * Module.rank ℂ E :=
  Cardinal.lift_inj.1 <| by
    rw [← lift_rank_mul_lift_rank ℝ ℂ E, Complex.rank_real_complex']
    -- ⊢ 2 * Cardinal.lift.{0, u_1} (Module.rank ℂ E) = Cardinal.lift.{0, u_1} (2 * M …
    simp only [Cardinal.lift_id']
    -- 🎉 no goals
#align rank_real_of_complex rank_real_of_complex

theorem finrank_real_of_complex (E : Type*) [AddCommGroup E] [Module ℂ E] :
    FiniteDimensional.finrank ℝ E = 2 * FiniteDimensional.finrank ℂ E := by
  rw [← FiniteDimensional.finrank_mul_finrank ℝ ℂ E, Complex.finrank_real_complex]
  -- 🎉 no goals
#align finrank_real_of_complex finrank_real_of_complex

instance (priority := 900) StarModule.complexToReal {E : Type*} [AddCommGroup E] [Star E]
    [Module ℂ E] [StarModule ℂ E] : StarModule ℝ E :=
  ⟨fun r a => by rw [← smul_one_smul ℂ r a, star_smul, star_smul, star_one, smul_one_smul]⟩
                 -- 🎉 no goals
#align star_module.complex_to_real StarModule.complexToReal

namespace Complex

open ComplexConjugate

/-- Linear map version of the real part function, from `ℂ` to `ℝ`. -/
def reLm : ℂ →ₗ[ℝ] ℝ where
  toFun x := x.re
  map_add' := add_re
  map_smul' := by simp
                  -- 🎉 no goals
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
                  -- 🎉 no goals
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
  -- ⊢ ↑(LinearMap.toMatrix basisOneI basisOneI) (AlgEquiv.toLinearMap conjAe) i j  …
  -- Porting note: replaced non-terminal `simp [LinearMap.toMatrix_apply]`
  fin_cases i <;> fin_cases j <;> simp [LinearMap.toMatrix_apply]
  -- ⊢ ↑(LinearMap.toMatrix basisOneI basisOneI) (AlgEquiv.toLinearMap conjAe) { va …
                  -- ⊢ ↑(LinearMap.toMatrix basisOneI basisOneI) (AlgEquiv.toLinearMap conjAe) { va …
                  -- ⊢ ↑(LinearMap.toMatrix basisOneI basisOneI) (AlgEquiv.toLinearMap conjAe) { va …
                                  -- 🎉 no goals
                                  -- 🎉 no goals
                                  -- 🎉 no goals
                                  -- 🎉 no goals
#align complex.to_matrix_conj_ae Complex.toMatrix_conjAe

/-- The identity and the complex conjugation are the only two `ℝ`-algebra homomorphisms of `ℂ`. -/
theorem real_algHom_eq_id_or_conj (f : ℂ →ₐ[ℝ] ℂ) : f = AlgHom.id ℝ ℂ ∨ f = conjAe := by
  refine'
      (eq_or_eq_neg_of_sq_eq_sq (f I) I <| by rw [← map_pow, I_sq, map_neg, map_one]).imp _ _ <;>
    refine' fun h => algHom_ext _
    -- ⊢ ↑f I = ↑(AlgHom.id ℝ ℂ) I
    -- ⊢ ↑f I = ↑↑conjAe I
  exacts [h, conj_I.symm ▸ h]
  -- 🎉 no goals
#align complex.real_alg_hom_eq_id_or_conj Complex.real_algHom_eq_id_or_conj

/-- The natural `AddEquiv` from `ℂ` to `ℝ × ℝ`. -/
@[simps! (config := { simpRhs := true }) apply symm_apply_re symm_apply_im]
def equivRealProdAddHom : ℂ ≃+ ℝ × ℝ :=
  { equivRealProd with map_add' := by simp }
                                      -- 🎉 no goals
#align complex.equiv_real_prod_add_hom Complex.equivRealProdAddHom

/-- The natural `LinearEquiv` from `ℂ` to `ℝ × ℝ`. -/
@[simps! (config := { simpRhs := true }) apply symm_apply_re symm_apply_im]
def equivRealProdLm : ℂ ≃ₗ[ℝ] ℝ × ℝ :=
  { equivRealProdAddHom with
    -- Porting note: `simp` has issues with `Prod.smul_def`
    map_smul' := fun r c => by simp [equivRealProdAddHom, (Prod.smul_def), smul_eq_mul] }
                               -- 🎉 no goals
#align complex.equiv_real_prod_lm Complex.equivRealProdLm

section lift

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- There is an alg_hom from `ℂ` to any `ℝ`-algebra with an element that squares to `-1`.

See `Complex.lift` for this as an equiv. -/
def liftAux (I' : A) (hf : I' * I' = -1) : ℂ →ₐ[ℝ] A :=
  AlgHom.ofLinearMap
    ((Algebra.linearMap ℝ A).comp reLm + (LinearMap.toSpanSingleton _ _ I').comp imLm)
    (show algebraMap ℝ A 1 + (0 : ℝ) • I' = 1 by rw [RingHom.map_one, zero_smul, add_zero])
                                                 -- 🎉 no goals
    fun ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ =>
    show
      algebraMap ℝ A (x₁ * x₂ - y₁ * y₂) + (x₁ * y₂ + y₁ * x₂) • I' =
        (algebraMap ℝ A x₁ + y₁ • I') * (algebraMap ℝ A x₂ + y₂ • I') by
      rw [add_mul, mul_add, mul_add, add_comm _ (y₁ • I' * y₂ • I'), add_add_add_comm]
      -- ⊢ ↑(algebraMap ℝ A) (x₁ * x₂ - y₁ * y₂) + (x₁ * y₂ + y₁ * x₂) • I' = ↑(algebra …
      congr 1
      -- ⊢ ↑(algebraMap ℝ A) (x₁ * x₂ - y₁ * y₂) = ↑(algebraMap ℝ A) x₁ * ↑(algebraMap  …
      -- equate "real" and "imaginary" parts
      · let inst : SMulCommClass ℝ A A := by infer_instance  -- porting note: added
        -- ⊢ ↑(algebraMap ℝ A) (x₁ * x₂ - y₁ * y₂) = ↑(algebraMap ℝ A) x₁ * ↑(algebraMap  …
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
                                                                     -- 🎉 no goals
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
                       -- 🎉 no goals
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
    -- ⊢ ↑((fun a => { val := -I • ↑a, property := (_ : -I • ↑a ∈ selfAdjoint A) }) ( …
    simp only [AddSubgroup.coe_add, smul_add, AddMemClass.mk_add_mk]
    -- 🎉 no goals
  map_smul' a b := by
    ext
    -- ⊢ ↑(AddHom.toFun { toFun := fun a => { val := -I • ↑a, property := (_ : -I • ↑ …
    simp only [neg_smul, skewAdjoint.val_smul, AddSubgroup.coe_mk, RingHom.id_apply,
      selfAdjoint.val_smul, smul_neg, neg_inj]
    rw [smul_comm]
    -- 🎉 no goals
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

scoped[ComplexStarModule] notation "ℜ" => realPart
scoped[ComplexStarModule] notation "ℑ" => imaginaryPart

open ComplexStarModule

@[simp]
theorem realPart_apply_coe (a : A) : (ℜ a : A) = (2 : ℝ)⁻¹ • (a + star a) := by
  unfold realPart
  -- ⊢ ↑(↑(selfAdjointPart ℝ) a) = 2⁻¹ • (a + star a)
  simp only [selfAdjointPart_apply_coe, invOf_eq_inv]
  -- 🎉 no goals
#align real_part_apply_coe realPart_apply_coe

@[simp]
theorem imaginaryPart_apply_coe (a : A) : (ℑ a : A) = -I • (2 : ℝ)⁻¹ • (a - star a) := by
  unfold imaginaryPart
  -- ⊢ ↑(↑(LinearMap.comp skewAdjoint.negISMul (skewAdjointPart ℝ)) a) = -I • 2⁻¹ • …
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
  -- ⊢ ↑(↑ℜ (I • a)) = ↑(-↑ℑ a)
  -- Porting note: was
  -- simp [smul_comm I, smul_sub, sub_eq_add_neg, add_comm]
  rw [realPart_apply_coe, AddSubgroupClass.coe_neg, imaginaryPart_apply_coe, neg_smul, neg_neg,
    smul_comm I, star_smul, star_def, conj_I, smul_sub, neg_smul, sub_eq_add_neg]
set_option linter.uppercaseLean3 false in
#align real_part_I_smul realPart_I_smul

@[simp]
theorem imaginaryPart_I_smul (a : A) : ℑ (I • a) = ℜ a := by
  ext
  -- ⊢ ↑(↑ℑ (I • a)) = ↑(↑ℜ a)
  -- Porting note: was
  -- simp [smul_comm I, smul_smul I]
  rw [realPart_apply_coe, imaginaryPart_apply_coe, smul_comm]
  -- ⊢ 2⁻¹ • -I • (I • a - star (I • a)) = 2⁻¹ • (a + star a)
  simp [←smul_assoc]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align imaginary_part_I_smul imaginaryPart_I_smul

theorem realPart_smul (z : ℂ) (a : A) : ℜ (z • a) = z.re • ℜ a - z.im • ℑ a := by
  -- Porting note: was `nth_rw 1 [← re_add_im z]`
  conv_lhs =>
    rw [← re_add_im z]
  simp [-re_add_im, add_smul, ← smul_smul, sub_eq_add_neg]
  -- 🎉 no goals
#align real_part_smul realPart_smul

theorem imaginaryPart_smul (z : ℂ) (a : A) : ℑ (z • a) = z.re • ℑ a + z.im • ℜ a := by
  -- Porting note: was `nth_rw 1 [← re_add_im z]`
  conv_lhs =>
    rw [← re_add_im z]
  simp [-re_add_im, add_smul, ← smul_smul]
  -- 🎉 no goals
#align imaginary_part_smul imaginaryPart_smul

end RealImaginaryPart

section Rational

open Cardinal Module

@[simp]
lemma Real.rank_rat_real : Module.rank ℚ ℝ = continuum := by
  refine (Free.rank_eq_mk_of_infinite_lt ℚ ℝ ?_).trans mk_real
  -- ⊢ lift.{0, 0} #ℚ < lift.{0, 0} #ℝ
  simpa [mk_real] using aleph0_lt_continuum
  -- 🎉 no goals

@[simp]
lemma Complex.rank_rat_complex : Module.rank ℚ ℂ = continuum := by
  refine (Free.rank_eq_mk_of_infinite_lt ℚ ℂ ?_).trans mk_complex
  -- ⊢ Cardinal.lift.{0, 0} #ℚ < Cardinal.lift.{0, 0} #ℂ
  simpa using aleph0_lt_continuum
  -- 🎉 no goals

/-- `ℂ` and `ℝ` are isomorphic as vector spaces over `ℚ`, or equivalently,
as additive groups. -/
theorem Complex.nonempty_linearEquiv_real : Nonempty (ℂ ≃ₗ[ℚ] ℝ) :=
  LinearEquiv.nonempty_equiv_iff_rank_eq.mpr <| by simp
                                                   -- 🎉 no goals

end Rational
