import DividedPowers.DpAlgebra.Init
import DividedPowers.DpAlgebra.Graded
import DividedPowers.ForMathlib.RingTheory.SubmoduleMem
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.TensorProduct
import Mathlib.LinearAlgebra.Multilinear.Basic

/-! Polynomial laws on modules

Reference : N. Roby, Lois polynômes et lois formelles en théorie des modules… 

-/

section

variable {A B R : Type _} [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B]

lemma AlgEquiv.toFun_eq_coe (e : A ≃ₐ[R] B) : e.toFun = e := rfl

end

section Finset

theorem Finset.congr_equiv {α β A : Type _} [AddCommMonoid A] 
  {f : α → A} {s : Finset α} 
  (e : α ≃ β) : s.sum f = (s.map e).sum (f ∘ e.symm)  := by
  simp only [Function.comp_apply, Finset.sum_map, Equiv.coe_toEmbedding, Equiv.symm_apply_apply]

-- Useful ?
theorem Finset.congr_equiv' {α β A : Type _} [AddCommMonoid A] 
  {f : β → A} {s : Finset α} 
  (e : α ≃ β) : s.sum (f ∘ e) = (s.map e).sum f := by
  simp only [Finset.congr_equiv e]
  apply Finset.sum_congr rfl
  simp only [Function.comp_apply, Equiv.apply_symm_apply, implies_true]

end Finset


section Misc

theorem Finsupp.ofSupportFinite_support {ι α : Type _} [Zero α] 
    (f : ι → α) (hf : f.support.Finite) : 
  (Finsupp.ofSupportFinite f hf).support = hf.toFinset := by 
  ext
  simp only [Finsupp.ofSupportFinite_coe, Finsupp.mem_support_iff, 
    Set.Finite.mem_toFinset, Function.mem_support]
#align finsupp.of_support_finite_support Finsupp.ofSupportFinite_support

end Misc

open Algebra Function LinearMap

open scoped TensorProduct

section Algebra

variable (A : Type _) [CommSemiring A] (R : Type _) [CommSemiring R] [Algebra A R]

namespace Algebra.TensorProduct

-- The natural `R`-algebra map from `R ⊗[A] A` to `R`.
def rid' : R ⊗[A] A →ₐ[R] R := { Algebra.TensorProduct.rid A R with
  map_one' := by simp only [AlgEquiv.toFun_eq_coe, map_one]
  map_zero' := by simp only [AlgEquiv.toFun_eq_coe, map_zero]
  commutes' := fun r => by
    simp only [algebraMap_apply, AlgEquiv.toFun_eq_coe, rid_tmul, one_smul] }
#align algebra.tensor_product.rid' Algebra.TensorProduct.rid'

@[simp]
theorem rid'_tmul (a : A) (r : R) : (rid' A R) (r ⊗ₜ[A] a) = a • r :=
  rfl
#align algebra.tensor_product.rid'_tmul Algebra.TensorProduct.rid'_tmul

end Algebra.TensorProduct

variable (M : Type _) [AddCommMonoid M] [Module A M]

-- Q (not important): I am not sure if `linear_form` is used in mathlib.
namespace LinearForm

open Algebra.TensorProduct LinearMap

def baseChange (f : M →ₗ[A] A) : R ⊗[A] M →ₗ[R] R :=
  (rid' A R).toLinearMap.comp (LinearMap.baseChange R f)
#align linear_form.base_change LinearForm.baseChange

theorem baseChange_apply_tmul (f : M →ₗ[A] A) (r : R) (m : M) :
  baseChange A R M f (r ⊗ₜ[A] m) = r * ((f m) • (1 : R)) := by
  simp only [baseChange, coe_comp, Function.comp_apply, baseChange_tmul, AlgHom.toLinearMap_apply, rid'_tmul,
    Algebra.mul_smul_comm, _root_.mul_one]
#align linear_form.base_change_apply_tmul LinearForm.baseChange_apply_tmul

variable (R' : Type _) [CommSemiring R'] [Algebra A R'] (φ : R →ₐ[A] R')

theorem baseChange_compat_apply (f : M →ₗ[A] A) (m : R ⊗[A] M) :
  φ (baseChange A R M f m) = 
    (baseChange A R' M f) ((rTensor M φ.toLinearMap) m) := by
  induction' m using TensorProduct.induction_on with r m x y hx hy
  · simp only [map_zero]
  · simp only [baseChange, coe_comp, Function.comp_apply, baseChange_tmul, AlgHom.toLinearMap_apply, rid'_tmul,
    map_smul, rTensor_tmul]
  · simp only [map_add, hx, hy]
#align linear_form.base_change_compat_apply LinearForm.baseChange_compat_apply

end LinearForm

end Algebra

namespace MvPolynomial

variable {R : Type _} [CommSemiring R] {ι : Type _}

-- I think it makes more sense to have this in the `mv_polynomial` namespace
--def linear_map.mv_polynomial.coeff (k : ι →₀ ℕ) : mv_polynomial ι A →ₗ[A] A :=
def coeffLinearMap (k : ι →₀ ℕ) : MvPolynomial ι R →ₗ[R] R
    where
  -- or `coeff_linear_map`
  toFun := coeff k
  map_add' := coeff_add k
  map_smul' := coeff_smul k
#align mv_polynomial.coeff_hom MvPolynomial.coeffLinearMap

theorem coeffLinearMap_apply (k : ι →₀ ℕ) (f : MvPolynomial ι R) :
    coeffLinearMap k f = MvPolynomial.coeff k f :=
  rfl
#align mv_polynomial.coeff_hom_apply MvPolynomial.coeffLinearMap_apply

end MvPolynomial

section MvPolynomialModule

/- This is boring stuff devoted to prove 
  the standard linear equivalence between M[σ] and R[σ] ⊗ M 
  for any semiring R, any R-module M and any type σ.
  Probably, this should be generalized to an arbitrary monoid, 
  not only polynomials (corresponding to σ →₀ ℕ). 
  M[σ] has to be defined hss (σ →₀ M) 
  because mathlib doesn't know about “the monoid module”. -/
open scoped TensorProduct

variable (σ : Type _) [DecidableEq σ] 
  (R : Type _) [CommSemiring R] 
  (N : Type _) [AddCommMonoid N] [Module R N]

open Finsupp

/- I wonder whether there's a simpler proof using
the fact that MvPolynomial σ R is a free R-module, 
with basis given by monomials 
One issue is that `Algebra.TensorProduct.Basis` makes
base change on the left, and has different assumptions… -/

-- TODO: rename

noncomputable def zoo : 
  ((σ →₀ ℕ) →₀ N) →ₗ[R] MvPolynomial σ R ⊗[R] N := 
    (Finsupp.lsum R).toFun
      (fun k ↦ {
        toFun := fun n ↦ MvPolynomial.monomial k 1 ⊗ₜ[R] n
        map_add' := fun n n' ↦ by
          simp only [TensorProduct.tmul_add]
        map_smul' := fun r n ↦ by
          simp only [TensorProduct.tmul_smul, RingHom.id_apply] })
#align zoo zoo

noncomputable def zooInv : 
  MvPolynomial σ R ⊗[R] N →ₗ[R] (σ →₀ ℕ) →₀ N := by
  apply TensorProduct.lift
  exact {
    toFun := fun p ↦ 
      { toFun := fun n ↦ Finsupp.ofSupportFinite
          (fun k ↦ MvPolynomial.coeff k p • n) 
          (by 
            suffices : _ ⊆ (p.support : Set (σ →₀ ℕ))
            apply Set.Finite.subset _ this
            simp only [Finset.finite_toSet]
            intro k
            simp only [mem_support, ne_eq, Finset.mem_coe, MvPolynomial.mem_support_iff, not_imp_not]
            intro h; rw [h, zero_smul])
        map_add' := fun n n' ↦ by
          ext k
          simp only [smul_add, coe_add, Pi.add_apply]
          rfl
        map_smul' := fun r n ↦ by
          ext k
          simp only [ofSupportFinite_coe, RingHom.id_apply, Finsupp.coe_smul, Pi.smul_apply, smul_smul]
          rw [mul_comm] }
    map_add' := fun p q ↦ by
      ext n k
      simp only [MvPolynomial.coeff_add, LinearMap.coe_mk, AddHom.coe_mk, ofSupportFinite_coe, LinearMap.add_apply,
        coe_add, Pi.add_apply, add_smul]
    map_smul' := fun r p ↦ by 
      ext n k
      simp only [MvPolynomial.coeff_smul, smul_eq_mul, LinearMap.coe_mk, AddHom.coe_mk, ofSupportFinite_coe,
        RingHom.id_apply, LinearMap.smul_apply, Finsupp.coe_smul, Pi.smul_apply, smul_smul] }
#align zoo_inv zooInv

theorem zooInv_zoo_apply (f) : 
  zooInv σ R N (zoo σ R N f) = f := by
  ext k
  -- rw [← zooInv_coe_apply σ R N, zooInv'_comp_zoo]
  simp only [zooInv, zoo]
  simp only [AddHom.toFun_eq_coe, coe_toAddHom, LinearEquiv.coe_coe,
    coe_lsum, LinearMap.coe_mk, AddHom.coe_mk,
    LinearMap.map_finsupp_sum, TensorProduct.lift.tmul, 
    MvPolynomial.coeff_monomial, Finsupp.sum_apply,
    ofSupportFinite_coe]
  simp only [ite_smul, one_smul, zero_smul, sum_ite_eq', mem_support_iff, ne_eq, sum_ite_self_eq_aux]
#align zoo_inv_zoo_apply zooInv_zoo_apply


theorem zoo_zooInv_apply (p) : 
  (zoo σ R N) (zooInv σ R N p) = p := by
  simp only [← LinearMap.comp_apply]
  conv_rhs => rw [← LinearMap.id_apply (R := R) p]
  revert p
  rw [← LinearMap.ext_iff]
  apply TensorProduct.ext'
  intro p n
  simp only [coe_comp, Function.comp_apply, id_coe, id_eq]
  simp only [zooInv, TensorProduct.lift.tmul, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [zoo, AddHom.toFun_eq_coe, coe_toAddHom, LinearEquiv.coe_coe, coe_lsum, LinearMap.coe_mk, AddHom.coe_mk]
  -- rw [Finsupp.sum]
  conv_rhs => rw [p.as_sum]
  rw [TensorProduct.sum_tmul]
  rw [Finsupp.sum_of_support_subset]
  apply Finset.sum_congr rfl
  . intro k _
    simp only [ofSupportFinite_coe, ← TensorProduct.CompatibleSMul.smul_tmul]
    rw [← map_smul]
    simp only [smul_eq_mul, mul_one]
  . intro k
    simp only [mem_support_iff, ofSupportFinite_coe, ne_eq, MvPolynomial.mem_support_iff, not_imp_not]
    intro h
    simp only [h, zero_smul]
  . intro _ _
    simp only [TensorProduct.tmul_zero]

noncomputable def zooEquiv : 
  ((σ →₀ ℕ) →₀ N) ≃ₗ[R] MvPolynomial σ R ⊗[R] N :=
  { zoo σ R N with
    invFun := zooInv σ R N
    left_inv := zooInv_zoo_apply σ R N
    right_inv := zoo_zooInv_apply σ R N }
#align linear_map_equiv zooEquiv

theorem zooEquiv_apply_single (k : σ →₀ ℕ) (n : N) :
  zooEquiv σ R N (single k n) = 
    (MvPolynomial.monomial k) 1 ⊗ₜ[R] n := by
  rw [zooEquiv, ← LinearEquiv.toFun_eq_coe, AddHom.toFun_eq_coe, coe_toAddHom, LinearMap.coe_mk, coe_toAddHom]
  rw [zoo, AddHom.toFun_eq_coe, coe_toAddHom, LinearEquiv.coe_coe,
    Finsupp.lsum_single, LinearMap.coe_mk, AddHom.coe_mk]
#align zoo_apply_single zooEquiv_apply_single

theorem zooEquiv_symm_apply_tmul (p : MvPolynomial σ R) (n : N) : 
  (zooEquiv σ R N).symm (p ⊗ₜ[R] n) = 
    fun k ↦ MvPolynomial.coeff k p • n := by
  ext k
  rfl

theorem zooEquiv_symm_apply (pn) : 
  (zooEquiv σ R N).symm pn k =
    (TensorProduct.lid R N) 
      ((rTensor N (MvPolynomial.coeffLinearMap k)) pn) := by
  induction pn using TensorProduct.induction_on with
  | C0 => simp only [map_zero, coe_zero, Pi.zero_apply]
  | C1 p n => 
      simp only [rTensor_tmul, TensorProduct.lid_tmul]
      simp only [zooEquiv_symm_apply_tmul]
      rfl
  | Cp p q h h' => 
      simp only [map_add, coe_add, Pi.add_apply]
      simp only [h, h']

end MvPolynomialModule

open scoped TensorProduct

section PolynomialMap

--universes u v₁ v₂ v₃ v₄ w w'
/- variables {A : Type u} {M : Type v₁} {N : Type v₂} [comm_semiring A] [add_comm_monoid M] 
  [module A M] [add_comm_monoid N] [module A N] -/
-- variables {A M N : Type*} [comm_semiring A] [add_comm_monoid M] [module A M] [add_comm_monoid N] [module A N]
/-- A polynomial map M → N between A-modules is a functorial family
of maps R ⊗[A] M → R ⊗[A] N, for all A-algebras R -/
@[ext]
structure PolynomialMap (A : Type _) [CommSemiring A] 
    (M : Type _) [AddCommMonoid M] [Module A M]
    (N : Type _) [AddCommMonoid N] [Module A N] where
  toFun (R : Type _) [CommSemiring R] [Algebra A R] : R ⊗[A] M → R ⊗[A] N
  isCompat {R : Type _} [CommSemiring R] [Algebra A R] 
    {R' : Type _} [CommSemiring R'] [Algebra A R'] (φ : R →ₐ[A] R') :
    φ.toLinearMap.rTensor N ∘ toFun R = 
      toFun R' ∘ φ.toLinearMap.rTensor M
#align polynomial_map PolynomialMap

namespace PolynomialMap

section Apply

variable {A M N : Type _} [CommSemiring A] 
  [AddCommMonoid M] [Module A M] [AddCommMonoid N] [Module A N]

/- lemma is_compat_apply (f : polynomial_map A M N) (R : Type w) [comm_semiring R] [algebra A R] 
  (R' : Type w) [comm_semiring R'] [algebra A R'] (φ : R →ₐ[A] R') (x : R ⊗[A] M) : 
  (φ.to_linear_map.rtensor N) ((f.to_fun R) x) = ((f.to_fun R') (φ.to_linear_map.rtensor M x)) :=
by simpa only using congr_fun (f.is_compat φ) x-/
theorem isCompat_apply (f : PolynomialMap A M N) 
    {R : Type _} [CommSemiring R] [Algebra A R]
    {R' : Type _} [CommSemiring R'] [Algebra A R'] 
    (φ : R →ₐ[A] R') (x : R ⊗[A] M) :
    (φ.toLinearMap.rTensor N) ((f.toFun R) x) = (f.toFun R') (φ.toLinearMap.rTensor M x) := by
  simpa only using congr_fun (f.isCompat φ) x
#align polynomial_map.is_compat_apply PolynomialMap.isCompat_apply

end Apply

section Module

variable {A M N : Type _} [CommSemiring A] [AddCommMonoid M] [Module A M] [AddCommMonoid N]
  [Module A N]

def add (f g : PolynomialMap A M N) : PolynomialMap A M N
    where
  toFun R _ _ := f.toFun R + g.toFun R
  isCompat φ := by
    ext
    simp only [Function.comp_apply, Pi.add_apply, map_add, isCompat_apply]
    
#align polynomial_map.add PolynomialMap.add

instance : Zero (PolynomialMap A M N) :=
  ⟨{  toFun := fun _ => 0
      isCompat := fun _ => rfl }⟩

@[simp]
theorem zero_def (R : Type _) [CommSemiring R] [Algebra A R] :
    (0 : PolynomialMap A M N).toFun R = 0 :=
  rfl
#align polynomial_map.zero_def PolynomialMap.zero_def

instance : Inhabited (PolynomialMap A M N) :=
  ⟨Zero.zero⟩

instance : Add (PolynomialMap A M N) :=
  ⟨add⟩

@[simp]
theorem add_def (f g : PolynomialMap A M N) 
    (R : Type _) [CommSemiring R] [Algebra A R] :
  (f + g).toFun R = f.toFun R + g.toFun R := rfl
#align polynomial_map.add_def PolynomialMap.add_def

@[simp]
theorem add_def_apply (f g : PolynomialMap A M N) 
    (R : Type _) [CommSemiring R] [Algebra A R] (m : R ⊗[A] M) : 
  (f + g).toFun R m = f.toFun R m + g.toFun R m := rfl
#align polynomial_map.add_def_apply PolynomialMap.add_def_apply

instance addCommMonoid : AddCommMonoid (PolynomialMap A M N)
    where
  add := Add.add
  add_assoc f g h := by ext ; simp only [add_def, add_assoc]
  zero := Zero.zero
  zero_add f := by ext ; simp only [add_def, zero_add, zero_def]
  add_zero f := by ext ; simp only [add_def, add_zero, zero_def]
  nsmul n f :=
    { toFun := fun R _ _ => n • (f.toFun R)
      isCompat := fun φ => by
        ext m
        simp only [isCompat_apply, map_nsmul, Function.comp_apply, Pi.smul_apply] }
  nsmul_zero f := by ext ; simp only [zero_smul, Pi.smul_apply]; rfl
  nsmul_succ n f := by
    ext 
    simp only [Pi.smul_apply, add_def_apply, add_comm _ 1]
    simp only [add_smul, one_smul]
  add_comm f g := by ext ; simp only [add_def, add_comm]
#align polynomial_map.add_comm_monoid PolynomialMap.addCommMonoid

def smul (a : A) (f : PolynomialMap A M N) : PolynomialMap A M N
    where
  toFun R _ _ := a • f.toFun R
  isCompat φ := by
    ext m
    simp only [Function.comp_apply, Pi.smul_apply, map_smulₛₗ, RingHom.id_apply, isCompat_apply]
#align polynomial_map.smul PolynomialMap.smul

instance hasSmul : SMul A (PolynomialMap A M N) :=
  ⟨smul⟩
#align polynomial_map.has_smul PolynomialMap.hasSmul

theorem smul_def (f : PolynomialMap A M N) (a : A) (R : Type _) [CommSemiring R] [Algebra A R] :
    (a • f).toFun R = a • f.toFun R :=
  rfl
#align polynomial_map.smul_def PolynomialMap.smul_def

instance : MulAction A (PolynomialMap A M N)
    where
  one_smul f := by ext ; simp only [smul_def, one_smul]
  mul_smul a b f := by ext ; simp only [smul_def, mul_smul]

instance : DistribMulAction A (PolynomialMap A M N)
    where
  smul_zero a := rfl
  smul_add a f g := by ext ; simp only [smul_def, add_def, smul_add]

instance module : Module A (PolynomialMap A M N)
    where
  add_smul a b f := by ext ; simp only [smul_def, add_def, add_smul]
  zero_smul f := by ext ; simp only [smul_def, zero_smul] ; rfl
#align polynomial_map.module PolynomialMap.module

end Module

section Comp

variable {A M N : Type _} [CommSemiring A] [AddCommMonoid M] [Module A M] [AddCommMonoid N]
  [Module A N]

variable {P : Type _} [AddCommMonoid P] [Module A P]

def comp (g : PolynomialMap A N P) (f : PolynomialMap A M N) : PolynomialMap A M P
    where
  toFun R _ _ := (g.toFun R).comp (f.toFun R)
  isCompat φ := by ext ; simp only [Function.comp_apply, isCompat_apply]
#align polynomial_map.comp PolynomialMap.comp

theorem comp_toFun (f : PolynomialMap A M N) (g : PolynomialMap A N P)
    (R : Type _) [CommSemiring R] [Algebra A R] : 
  (g.comp f).toFun R = (g.toFun R).comp (f.toFun R) := rfl
#align polynomial_map.comp_to_fun PolynomialMap.comp_toFun

theorem comp_apply (f : PolynomialMap A M N) (g : PolynomialMap A N P)
  (R : Type _) [CommSemiring R] [Algebra A R] (m : R ⊗[A] M) : 
  (g.comp f).toFun R m = (g.toFun R) (f.toFun R m) := rfl
#align polynomial_map.comp_apply PolynomialMap.comp_apply

variable {Q : Type _} [AddCommMonoid Q] [Module A Q]

theorem comp_assoc (f : PolynomialMap A M N) (g : PolynomialMap A N P)
    (h : PolynomialMap A P Q) :
    h.comp (g.comp f) = (h.comp g).comp f := by 
  ext; simp only [comp_toFun] ; rfl
#align polynomial_map.comp_assoc PolynomialMap.comp_assoc

end Comp

section ConstantMap

variable {A M N : Type _} [CommSemiring A] [AddCommMonoid M] [AddCommMonoid N] [Module A M]
  [Module A N]

open scoped TensorProduct

def ofConstant (n : N) : PolynomialMap A M N
    where
  toFun R _ _ _:= TensorProduct.tmul A 1 n
  isCompat φ := by
    ext
    simp only [Function.comp_apply, rTensor_tmul, AlgHom.toLinearMap_apply, map_one]

#align polynomial_map.of_constant PolynomialMap.ofConstant

end ConstantMap

section Linear

open scoped TensorProduct

variable {A : Type _} [CommSemiring A] {M N : Type _} [AddCommMonoid M] [AddCommMonoid N]
  [Module A M] [Module A N]

def ofLinearMap (v : M →ₗ[A] N) : PolynomialMap A M N
    where
  toFun R _ _ := v.baseChange R
  isCompat φ := by
    ext
    simp only [← LinearMap.comp_apply, baseChange_eq_ltensor, Function.comp_apply, rTensor_comp_lTensor, lTensor_comp_rTensor]
#align polynomial_map.of_linear_map PolynomialMap.ofLinearMap

theorem ofLinearMap_toFun (u : M →ₗ[A] N) 
    (R : Type _) [CommSemiring R] [Algebra A R] :
  (ofLinearMap u).toFun R = baseChange R u := rfl
#align polynomial_map.of_linear_map_to_fun PolynomialMap.ofLinearMap_toFun

def ofLinearMapHom : (M →ₗ[A] N) →ₗ[A] PolynomialMap A M N
    where
  toFun := ofLinearMap
  map_add' u v := by
    ext R _ _ m
    simp only [PolynomialMap.add_def, ofLinearMap_toFun, Pi.add_apply, baseChange_add,
      add_apply]
  map_smul' a v := by ext R _ _ m; simp only [smul_def, ofLinearMap_toFun, baseChange_smul]; rfl
#align polynomial_map.of_linear_map_hom PolynomialMap.ofLinearMapHom

theorem ofLinearMapHom_apply (v : M →ₗ[A] N) : ofLinearMapHom v = ofLinearMap v :=
  rfl
#align polynomial_map.of_linear_map_hom_apply PolynomialMap.ofLinearMapHom_apply

end Linear

/- 
section multilinear

-- I need to understand how to do base change of multilinear maps  in Lean

variables (A N : Type*) [comm_semiring A]
variables {ι : Type*} [fintype ι] (M : ι → Type*) [∀ i, add_comm_monoid (M i)] [∀ i, module A (M i)]
variables  [add_comm_monoid N]  [module A N]

def of_multilinear_map (u : multilinear_map A M N) : polynomial_map A (Π i, M i) N := {
 to_fun := λ  R _ _, 
 begin 
--  by exactI u.base_change R, 

 end,
 is_compat := sorry } 

def of_multilinear_map_to_fun (u : multilinear_map A M N) (R : Type*) [comm_semiring R] [algebra A R] : false := sorry 


def of_multilinear_map : (multilinear_map A M N) 
  →ₗ[A] (polynomial_map A (Π i, M i) N) := {
to_fun := of_multilinear_map_to_fun, 
map_add' := sorry,
map_smul' := sorry }


end multilinear 
-/
section LocallyFinite

variable {A M N : Type _} [CommSemiring A] 
  [AddCommMonoid M] [AddCommMonoid N] [Module A M] [Module A N]

def Locfinsupp {ι : Type _} (f : ι → PolynomialMap A M N) :=
  ∀ (R : Type _) [CommSemiring R] [Algebra A R] (m : R ⊗[A] M),
    (Function.support fun i => (f i).toFun R m).Finite
#align polynomial_map.locfinsupp PolynomialMap.Locfinsupp

variable (A M N)

def withLocfinsupp (ι : Type _) : 
  Submodule A (ι → PolynomialMap A M N) where
  carrier := Locfinsupp
  add_mem' := by 
    intro a b ha hb R _ _ m
    exact Set.Finite.subset (Set.finite_union.mpr ⟨ha R m, hb R m⟩) (Function.support_add _ _)
  zero_mem' := by 
    simp only
    intro R _ _ _
    simp only [Pi.zero_apply, zero_def, support_zero, Set.finite_empty]
  smul_mem' a f hf R _ _ m := by
    skip
    exact Set.Finite.subset (hf R m) (Function.support_smul_subset_right a _)
#align polynomial_map.with_locfinsupp PolynomialMap.withLocfinsupp

namespace Locfinsupp

variable {A M N}

noncomputable def sum {ι : Type _} (f : ι → PolynomialMap A M N) 
    (hf : Locfinsupp f) :
  PolynomialMap A M N where
  toFun R _ _ m := (Finsupp.ofSupportFinite _ (hf R m)).sum fun _ m => m
  isCompat {R _ _ R' _ _} φ := by
    ext m
    simp only [Function.comp_apply, LinearMap.map_finsupp_sum]
    rw [Finsupp.sum]
    suffices _ ⊆ (hf R m).toFinset
      by
      rw [Finsupp.sum_of_support_subset _ this]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Finsupp.ofSupportFinite_coe, _root_.map_sum, isCompat_apply]
      · intro i _; rfl
    · intro i
      simp only [Finsupp.ofSupportFinite_coe, not_imp_not, Finsupp.mem_support_iff,
        Set.Finite.mem_toFinset, Function.mem_support, ← isCompat_apply]
      intro hi
      rw [hi, map_zero]
#align polynomial_map.locfinsupp.sum PolynomialMap.Locfinsupp.sum

theorem sum_eq {ι : Type _} (f : ι → PolynomialMap A M N) 
    (hf : Locfinsupp f) 
    (R : Type _) [CommSemiring R] [Algebra A R] (m : R ⊗[A] M) :
  (Locfinsupp.sum f hf).toFun R m = 
    (Finsupp.ofSupportFinite _ (hf R m)).sum fun _ m => m := rfl
#align polynomial_map.locfinsupp.sum_eq PolynomialMap.Locfinsupp.sum_eq

end Locfinsupp

--TODO: I don't think this is in the right namespace, but I don't know how to rename it.
noncomputable def LinearMap.Locfinsupp.sum {ι : Type _} [DecidableEq ι] :
    withLocfinsupp A M N ι →ₗ[A] PolynomialMap A M N
    where
  toFun fhf := PolynomialMap.Locfinsupp.sum fhf.val fhf.prop
  map_add' := fun ⟨f, hf⟩ ⟨g, hg⟩ => by
    ext R _ _ m
    skip
    simp only [AddMemClass.mk_add_mk, PolynomialMap.Locfinsupp.sum_eq, Pi.add_apply, add_def_apply]
    rw [@Finsupp.sum_of_support_subset _ _ _ _ _ _ ((hf R m).toFinset ∪ (hg R m).toFinset),
      Finsupp.sum_of_support_subset _ (Finset.subset_union_left _ _),
      Finsupp.sum_of_support_subset _ (Finset.subset_union_right _ _), ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    all_goals try intro i hi; rfl
    · intro x
      simp only [Finsupp.ofSupportFinite_support, Set.Finite.mem_toFinset, Function.mem_support,
        Ne.def, Finset.mem_union]
      rw [← not_and_or, not_imp_not]
      intro h
      rw [h.1, h.2, add_zero]
  map_smul' a fhf := by
    ext R _ _ m
    skip
    simp only [smul_def, PolynomialMap.Locfinsupp.sum_eq, Submodule.coe_smul_of_tower,
      Pi.smul_apply, RingHom.id_apply]
    rw [Finsupp.sum_of_support_subset]
    · rw [Finsupp.smul_sum, Finsupp.sum]
      exact Finset.sum_congr rfl fun i _ => rfl
    · intro i
      simp only [Finsupp.ofSupportFinite_coe, SetLike.val_smul, Pi.smul_apply, smul_def, Finsupp.mem_support_iff, ne_eq, not_imp_not, PolynomialMap.smul_def]
      intro hi 
      rw [hi, smul_zero]
    · intro i _ ; rfl
#align polynomial_map.linear_map.locfinsupp.sum PolynomialMap.LinearMap.Locfinsupp.sum

end LocallyFinite

section Coefficients

variable {A M N : Type _} [CommSemiring A] 
  [AddCommMonoid M] [AddCommMonoid N] [Module A M] [Module A N]

variable {ι : Type _} [DecidableEq ι] [Fintype ι]

variable (A N)
noncomputable def generize (m : ι → M) :
  PolynomialMap A M N →ₗ[A] MvPolynomial ι A ⊗[A] N where
  toFun := fun f ↦ f.toFun (MvPolynomial ι A)
    (Finset.univ.sum fun i => MvPolynomial.X i ⊗ₜ[A] m i)
  map_add' := fun p q ↦ by
    simp only [add_def_apply]
  map_smul' := fun r p ↦ by 
    simp only [RingHom.id_apply, PolynomialMap.smul_def, Pi.smul_apply]
  
variable {A N}

theorem generize_comp_equiv (f : PolynomialMap A M N) 
  {ι : Type} {κ : Type _} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (m : κ → M) :
  generize A N m f = (rTensor N 
    (MvPolynomial.aeval (fun i ↦ MvPolynomial.X (e i))).toLinearMap)
      (generize A N (fun x ↦ m (e x)) f)
   := by
  let hf := f.isCompat_apply 
    (MvPolynomial.aeval (fun i ↦ MvPolynomial.X (e i)) : 
        MvPolynomial ι A →ₐ[A] MvPolynomial κ A) 
    (Finset.univ.sum (fun i ↦ MvPolynomial.X i ⊗ₜ[A] (m (e i))))
  simp only [LinearMap.map_sum, rTensor_tmul, AlgHom.toLinearMap_apply,
    MvPolynomial.aeval_X] at hf 
  simp only [generize, coe_mk, AddHom.coe_mk]
  simp only [Function.comp_apply, hf]
  apply congr_arg
  simp only [Finset.congr_equiv e, Finset.map_univ_equiv]
  apply Finset.sum_congr rfl
  intro k _ ; simp only [Function.comp_apply, Equiv.apply_symm_apply]

theorem generize_comp_equiv' (f : PolynomialMap A M N) 
    {ι : Type} {κ : Type _} [Fintype ι] [Fintype κ] 
    [DecidableEq ι][DecidableEq κ] (e : ι ≃ κ) (m : κ → M) :
  (generize A N (fun x ↦ m (e x)) f) = 
    (rTensor N 
      (MvPolynomial.aeval (fun i ↦ MvPolynomial.X (e.symm i))).toLinearMap) 
    (generize A N m f) := by 
  let hf' := f.isCompat_apply 
    (MvPolynomial.aeval (fun i ↦ MvPolynomial.X (e.symm i)) : 
        MvPolynomial κ A →ₐ[A] MvPolynomial ι A) 
    (Finset.univ.sum (fun i ↦ MvPolynomial.X i ⊗ₜ[A] (m i)))
  simp only [LinearMap.map_sum, rTensor_tmul, AlgHom.toLinearMap_apply, MvPolynomial.aeval_X] at hf' 
  simp only [generize, coe_mk, AddHom.coe_mk]
  rw [hf']
  apply congr_arg
  simp only [Finset.congr_equiv e, Finset.map_univ_equiv]
  apply Finset.sum_congr rfl
  intro k _ 
  simp only [Function.comp_apply, Equiv.apply_symm_apply]

theorem generize_comp_embed (f : PolynomialMap A M N) 
  {ι : Type} {κ : Type _} [Fintype ι] [Fintype κ] [DecidableEq ι][DecidableEq κ] (e : ι ↪ κ) (m : κ → M) :
  (rTensor N 
    (MvPolynomial.aeval (fun i ↦ MvPolynomial.X (e i))).toLinearMap)
      (generize A N (fun i ↦ m (e i)) f) = 
   rTensor N (MvPolynomial.aeval (R := A)
    (fun k ↦ if k ∈ Finset.univ.map e then MvPolynomial.X k else (0 : MvPolynomial κ A))).toLinearMap
      (generize A N m f) := by 
  let hf := f.isCompat_apply 
    (MvPolynomial.aeval (fun i ↦ MvPolynomial.X (e i)) : 
        MvPolynomial ι A →ₐ[A] MvPolynomial κ A) 
    (Finset.univ.sum (fun i ↦ MvPolynomial.X i ⊗ₜ[A] (m (e i))))
  simp only [LinearMap.map_sum, rTensor_tmul, AlgHom.toLinearMap_apply,
    MvPolynomial.aeval_X] at hf 
  simp only [generize, coe_mk, AddHom.coe_mk]
  simp only [Function.comp_apply, hf]
  
  let hf' := f.isCompat_apply (MvPolynomial.aeval (R := A)
    (fun k ↦ if k ∈ Finset.univ.map e then MvPolynomial.X k else (0 : MvPolynomial κ A)))
  simp only [LinearMap.map_sum, rTensor_tmul, AlgHom.toLinearMap_apply,
    MvPolynomial.aeval_X] at hf'
  rw [hf', _root_.map_sum]
  simp only [Set.mem_range, rTensor_tmul, AlgHom.toLinearMap_apply, MvPolynomial.aeval_X]
  apply congr_arg
  rw [← Finset.sum_map (Finset.univ : Finset ι) e
    (fun k ↦ (MvPolynomial.X k : MvPolynomial κ A) ⊗ₜ[A] m k)]
  simp_rw [TensorProduct.ite_tmul]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ ↦ rfl)
  . ext k
    simp only [Finset.mem_map, Finset.mem_univ, true_and, forall_true_left, Finset.univ_filter_exists, Finset.mem_image]
  
/-- The coefficients of a `polynomial_map` -/
noncomputable def coeff (m : ι → M) :
  PolynomialMap A M N →ₗ[A] (ι →₀ ℕ) →₀ N := by
    exact (zooEquiv ι A N).symm.comp (generize A N m)
#align polynomial_map.coeff PolynomialMap.coeff

theorem generize_eq (m : ι → M) (f : PolynomialMap A M N)  : 
  generize A N m f = (coeff m f).sum 
    (fun k n => (MvPolynomial.monomial k 1) ⊗ₜ n)  := by
  simp only [coeff]
  dsimp
  generalize h : (zooEquiv ι A N).symm (generize A N m f) = p
  rw [LinearEquiv.symm_apply_eq] at h
  rw [h]
  rfl

theorem coeff_eq (m : ι → M) (k : ι →₀ ℕ) (f : PolynomialMap A M N) :
  coeff m f k =
    (TensorProduct.lid A N)
      ((LinearMap.rTensor N (MvPolynomial.coeffLinearMap k))
        (f.toFun (MvPolynomial ι A) (Finset.univ.sum 
          fun i : ι => MvPolynomial.X i ⊗ₜ[A] m i))) := by 
  simp only [coeff, coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  simp only [generize, coe_mk, AddHom.coe_mk]
  rw [zooEquiv_symm_apply]
#align polynomial_map.coeff_eq PolynomialMap.coeff_eq

  
theorem coeff_comp_equiv {ι : Type} [DecidableEq ι] [Fintype ι] 
  {κ : Type _} [DecidableEq κ] [Fintype κ]
  (e : ι ≃ κ) (m : κ → M) (k : ι →₀ ℕ) (f : PolynomialMap A M N) :
  coeff m f (k.equivMapDomain e) = coeff (m.comp e) f (k) := by
  simp only [coeff]
  
  simp only [coe_comp, LinearEquiv.coe_coe, Function.comp_apply]  
  -- simp only [generize, coe_mk, AddHom.coe_mk]
  simp only [zooEquiv_symm_apply]    
  -- simp only [← LinearEquiv.coe_toLinearMap, ← LinearMap.comp_apply]
  -- rw [← LinearMap.comp_assoc]
  have : m ∘ e = fun x ↦ m (e x) := rfl -- by ext x; rfl
  rw [this]

  /- simp only [AlgHom.coe_toLinearMap]
  generalize hu : (TensorProduct.lid A N).comp (rTensor N (MvPolynomial.coeffLinearMap (Finsupp.equivMapDomain e k))) = u
  -/
  let hf := f.isCompat_apply
    (MvPolynomial.aeval (fun i ↦ MvPolynomial.X (e i)) : 
        MvPolynomial ι A →ₐ[A] MvPolynomial κ A) 
    (Finset.univ.sum (fun i ↦ MvPolynomial.X i ⊗ₜ[A] (m (e i))))
  simp only [LinearMap.map_sum, rTensor_tmul, AlgHom.toLinearMap_apply,
    MvPolynomial.aeval_X] at hf 
  simp only [generize, coe_mk, AddHom.coe_mk]
  simp only [Function.comp_apply, hf]
  apply congr_arg
  simp only [Finset.congr_equiv e, Finset.map_univ_equiv]
  
  -- apply Finset.sum_congr rfl
  -- intro k _ ; simp only [Function.comp_apply, Equiv.apply_symm_apply]

  -- Universe issue !
  -- rw [generize_comp_equiv f e m]

  
  simp [Finsupp.equivMapDomain_apply]
  dsimp

  sorry

theorem image_eq_coeff_sum 
    (m : ι → M) 
    (f : PolynomialMap A M N) 
    (R : Type _) [CommSemiring R] [Algebra A R] (r : ι → R) :
  f.toFun R (Finset.univ.sum fun i => r i ⊗ₜ[A] m i) =
    (coeff m f).sum 
      (fun k n => (Finset.univ.prod fun i => r i ^ k i) ⊗ₜ[A] n) := by
  have that := congr_fun (f.isCompat (MvPolynomial.aeval r)) 
    (Finset.univ.sum fun i => MvPolynomial.X i ⊗ₜ[A] m i)
  simp only [Function.comp_apply, LinearMap.map_sum, LinearMap.rTensor_tmul,
    AlgHom.toLinearMap_apply, MvPolynomial.aeval_X] at that 
  rw [← that]
  let h := generize_eq m f
  simp only [generize, coe_mk, AddHom.coe_mk] at h 
  rw [h]
  simp only [Finsupp.sum, _root_.map_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply]
  apply congr_arg₂ _ _ rfl
  simp [MvPolynomial.aeval_monomial]
#align polynomial_map.image_eq_coeff_sum PolynomialMap.image_eq_coeff_sum

/-- Variant of `image_eq_coeff_sum` over a Finset -/
theorem image_eq_coeff_finset_sum {ι : Type _} [DecidableEq ι]
    (m : ι → M) 
    (f : PolynomialMap A M N) 
    (R : Type _) [CommSemiring R] [Algebra A R] 
    (r : ι → R) (s : Finset ι):
  f.toFun R (s.sum fun i => r i ⊗ₜ[A] m i) =
    (coeff (fun i : s => m i) f).sum 
      (fun k n => (s.prod fun i => r i ^ ((Function.extend (fun x => x.val) k (const ι 0)) i)) ⊗ₜ[A] n) := by
  let m' : s → M := fun i => m i
  let r' : s → R := fun i => r i
  convert image_eq_coeff_sum m' f R r'
  · simp only [Finset.univ_eq_attach, Finsupp.coe_mk]
    rw [← Finset.sum_attach]
  · simp only [Finset.univ_eq_attach, Finsupp.coe_mk]
    rw [← Finset.prod_attach]
    apply Finset.prod_congr rfl
    intro x _
    simp only [Pi.const_zero, exists_apply_eq_apply, not_true]
    apply congr_arg₂ _ rfl
    rw [Subtype.coe_injective.extend_apply]  


-- Useful ?
/-- Variant of `image_eq_coeff_sum'` with a `Finsupp`-/
theorem image_eq_coeff_sum' {ι : Type _} [DecidableEq ι] (m : ι → M) 
    (f : PolynomialMap A M N) 
    (R : Type _) [CommSemiring R] [Algebra A R] (r : ι →₀ R) :
    f.toFun R (r.sum fun i a => a ⊗ₜ[A] m i) =
      (coeff (fun i : r.support => m i) f).sum 
        (fun k n => 
          (r.support.prod 
            (fun i => r i ^ ((Function.extend (fun x => x.val) k (const ι 0)) i) )
           ⊗ₜ[A] n)) := by
  rw [Finsupp.sum]
  rw [image_eq_coeff_finset_sum]
#align polynomial_map.image_eq_coeff_sum' PolynomialMap.image_eq_coeff_sum'

variable {R : Type _} [CommSemiring R] [Algebra A R]

theorem span_tensorProduct_eq_top_of_span_eq_top 
    (σ : Type _) (e : σ → M)
    (hm : Submodule.span A (Set.range e) = ⊤) :
    (Submodule.span R (Set.range fun s => (1 : R) ⊗ₜ[A] e s) : Submodule R (R ⊗[A] M)) = ⊤ :=
  by
  rw [_root_.eq_top_iff]
  intro m h
  induction' m using TensorProduct.induction_on with r m x y hx hy
  exact zero_mem _
  · let f : M →ₗ[A] R ⊗[A] M :=
      { toFun := fun m => (1 : R) ⊗ₜ[A] m
        map_add' := fun x y => by simp only [TensorProduct.tmul_add]
        map_smul' := fun a x => by simp only [TensorProduct.tmul_smul, RingHom.id_apply] }
    suffices : r ⊗ₜ[A] m = r • (1 : R) ⊗ₜ[A] m
    rw [this]
    refine' Submodule.smul_mem _ r _
    apply Submodule.span_le_restrictScalars A
    convert Submodule.apply_mem_span_image_of_mem_span 
      (s := Set.range e) f _ 
    . conv_rhs => rw [← Set.image_univ, Set.image_image, Set.image_univ]
    . rw [hm]; exact Submodule.mem_top
    rw [TensorProduct.smul_tmul']; simp only [Algebra.id.smul_eq_mul, mul_one]
  exact Submodule.add_mem _ (hx Submodule.mem_top) (hy Submodule.mem_top)
#align polynomial_map.span_tensor_product_eq_top_of_span_eq_top PolynomialMap.span_tensorProduct_eq_top_of_span_eq_top

theorem coeff_injective [DecidableEq ι] (m : ι → M) 
    (hm : Submodule.span A (Set.range m) = ⊤)
    (f g : PolynomialMap A M N) (h : coeff m f = coeff m g) : 
  f = g := by
  ext R _ _ p
  suffices hp : p ∈ Submodule.span R (Set.range fun s => 1 ⊗ₜ[A] m s)
  simp only [Submodule.mem_span_iff_exists_sum _ p, TensorProduct.smul_tmul'] at hp
  obtain ⟨r, rfl⟩ := hp
  rw [Finsupp.sum_of_support_subset _ (Finset.subset_univ _)]
  rw [image_eq_coeff_sum m f]
  simp only [image_eq_coeff_sum, h]
  . intro i _
    simp only [smul_eq_mul, mul_one, TensorProduct.zero_tmul]
  . rw [PolynomialMap.span_tensorProduct_eq_top_of_span_eq_top (R := R) ι m hm]
    exact Submodule.mem_top
#align polynomial_map.coeff_injective PolynomialMap.coeff_injective

noncomputable def Finsupp.polynomialMap (b : Basis ι A M) (h : (ι →₀ ℕ) →₀ N) : PolynomialMap A M N
    where
  toFun R _ _ x :=
    h.sum fun k n =>
      (Finset.univ.prod fun i => (LinearForm.baseChange A R _ (b.coord i)) x ^ k i) ⊗ₜ[A] n
  isCompat φ := by
    ext m
    dsimp
    simp only [Finsupp.sum]
    rw [_root_.map_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply]
    apply congr_arg₂ _ _ rfl
    rw [map_prod φ]
    apply Finset.prod_congr rfl
    intro i _
    rw [map_pow]
    apply congr_arg₂ _ _ rfl
    rw [LinearForm.baseChange_compat_apply]
#align polynomial_map.finsupp.polynomial_map PolynomialMap.Finsupp.polynomialMap

theorem Finsupp.polynomialMap_toFun_apply (b : Basis ι A M) 
    (h : (ι →₀ ℕ) →₀ N) (m : R ⊗[A] M) :
  (Finsupp.polynomialMap b h).toFun R m =
    h.sum fun k n =>
      (Finset.univ.prod 
        (fun i => (LinearForm.baseChange A R _ (b.coord i)) m ^ k i)) ⊗ₜ[A] n :=
  rfl
#align polynomial_map.finsupp.polynomial_map_to_fun_apply PolynomialMap.Finsupp.polynomialMap_toFun_apply

example (f g : ι → ℕ) (i : ι) : (f + g) i = f i + g i :=
  Pi.add_apply f g i

theorem coeff_of_finsupp_polynomialMap [DecidableEq ι]
    (b : Basis ι A M) (h : (ι →₀ ℕ) →₀ N) :
  coeff (FunLike.coe b) (Finsupp.polynomialMap b h) = h := by
  simp only [coeff, coe_mk, AddHom.coe_mk]
  simp only [coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  rw [LinearEquiv.symm_apply_eq]
  dsimp [Finsupp.polynomialMap, generize]
  apply congr_arg
  ext k
  apply congr_arg₂ _ _ rfl
  rw [MvPolynomial.monomial_eq]
  simp
  apply congr_arg
  ext i
  congr
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
  simp [LinearForm.baseChange]
  intro j _ hij
  simp only [LinearForm.baseChange_apply_tmul]
  rw [Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
  rw [if_neg hij]
  simp only [zero_smul, MulZeroClass.mul_zero]
#align polynomial_map.coeff_of_finsupp_polynomial_map PolynomialMap.coeff_of_finsupp_polynomialMap

theorem finsupp_polynomialMap_of_coeff [DecidableEq ι] 
    (b : Basis ι A M) (f : PolynomialMap A M N) :
  Finsupp.polynomialMap b (coeff (FunLike.coe b) f) = f := by
  apply coeff_injective (FunLike.coe b)
  · rw [_root_.eq_top_iff]; intro m _
    apply Submodule.span_mono _ (Basis.mem_span_repr_support b m)
    apply Set.image_subset_range
  rw [coeff_of_finsupp_polynomialMap]
#align polynomial_map.finsup_polynomial_map_of_coeff PolynomialMap.finsupp_polynomialMap_of_coeff

example [DecidableEq ι] (b : Basis ι A M) (i j : ι) : 
  (b.coord i) (b j) = ite (j = i) 1 0 := by
  rw [Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]

noncomputable def coeffPolynomialMapEquiv [DecidableEq ι]
    (b : Basis ι A M) :
  ((ι →₀ ℕ) →₀ N) ≃ₗ[A] PolynomialMap A M N where
  toFun h := Finsupp.polynomialMap b h
  map_add' h k := by
--    classical
    ext R _ _ m
    simp only [Finsupp.polynomialMap_toFun_apply, add_def, Pi.add_apply]
    rw [Finsupp.sum_of_support_subset h (h.support.subset_union_left k.support)]
    rw [Finsupp.sum_of_support_subset k (h.support.subset_union_right k.support)]
    rw [Finsupp.sum_of_support_subset (h + k) Finsupp.support_add]
    simp_rw [Finsupp.coe_add, Pi.add_apply, TensorProduct.tmul_add]
    rw [Finset.sum_add_distrib]
    all_goals intro i hi; rw [TensorProduct.tmul_zero]
  map_smul' a h := by
    ext R _ _ m
    -- rw [ext_iff]; ext R _ _ m; skip
    simp only [RingHom.id_apply, smul_def, Pi.smul_apply]
    simp [Finsupp.polynomialMap_toFun_apply]
    rw [Finsupp.sum_of_support_subset (a • h) Finsupp.support_smul]
    simp only [Finsupp.sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp [Finsupp.coe_smul, Pi.smul_apply, TensorProduct.tmul_smul]
    intro k _; rw [TensorProduct.tmul_zero]
  invFun f := coeff (FunLike.coe b) f
  left_inv h := by dsimp; rw [coeff_of_finsupp_polynomialMap]
  right_inv f := by dsimp; rw [finsupp_polynomialMap_of_coeff b]
#align polynomial_map.coeff_polynomial_map_equiv PolynomialMap.coeffPolynomialMapEquiv

end Coefficients

section Graded

universe u v w

variable {A M N : Type _} [CommRing A] 
  [AddCommMonoid M] [AddCommMonoid N] [Module A M] [Module A N]

def IsHomogeneousOfDegree {A : Type u} {M N : Type _} [CommRing A]
    [AddCommMonoid M] [AddCommMonoid N] [Module A M] [Module A N] 
    (p : ℕ) (f : PolynomialMap A M N) : Prop :=
  ∀ (R : Type u) [CommRing R] [Algebra A R] (r : R) (m : R ⊗[A] M), 
    f.toFun R (r • m) = r ^ p • f.toFun R m
#align polynomial_map.is_homogeneous_of_degree PolynomialMap.IsHomogeneousOfDegree

theorem TensorProduct.is_finsupp_sum_tmul {A R : Type _} 
    [CommSemiring A] [CommSemiring R] [Algebra A R] [Module A M] 
    (m : R ⊗[A] M) : 
  ∃ r : M →₀ R, m = r.sum fun x a => a ⊗ₜ[A] x :=
  by
  induction' m using TensorProduct.induction_on with r m x y hx hy
  · use 0; simp only [Finsupp.sum_zero_index]
  · use Finsupp.single m r; simp only [Finsupp.sum_single_index, TensorProduct.zero_tmul]
  · obtain ⟨rx, rfl⟩ := hx
    obtain ⟨ry, rfl⟩ := hy
    use rx + ry
    rw [Finsupp.sum_add_index']
    · intro a; simp only [TensorProduct.zero_tmul]
    · intro m r₁ r₂; rw [TensorProduct.add_tmul]
#align tensor_product.is_finsupp_sum_tmul PolynomialMap.TensorProduct.is_finsupp_sum_tmul

theorem TensorProduct.is_finsupp_sum_tmul' {A R : Type _} 
    [CommSemiring A] [CommSemiring R] [Algebra A R] [Module A M] 
    (t : R ⊗[A] M) : 
  ∃ (n : ℕ) (m : ℕ → M) (r : ℕ → R), t = (Finset.range n).sum fun x => (r x) ⊗ₜ[A] (m x) :=
  by
  induction' t using TensorProduct.induction_on with r m x y hx hy
  · use 0; use const ℕ 0; use const ℕ 0
    simp only [Finset.range_zero, Finset.sum_empty]
    
  · use 1; use const ℕ m; use const ℕ r;
    simp only [Finset.range_one, Finset.sum_singleton, const_apply]

  · obtain ⟨n1, m1, r1, h1⟩ := hx
    obtain ⟨n2, m2, r2, h2⟩ := hy
    use n1 + n2
    use fun x => if x < n1 then m1 x else m2 (x - n1)
    use fun x => if x < n1 then r1 x else r2 (x - n1)
    rw [Finset.sum_range_add]
    apply congr_arg₂ 
    . conv_lhs => rw [h1]
      apply Finset.sum_congr rfl
      intro x hx
      simp only [Finset.mem_range] at hx 
      simp only [if_pos hx]
    . conv_lhs => rw [h2]
      apply Finset.sum_congr rfl
      intro x _
      dsimp
      suffices : ¬ (n1 + x  < n1)
      simp only [if_neg this]
      simp only [add_tsub_cancel_left]
      simp only [not_lt, Nat.le_add_right]
  
def ULift.up_embedding {α : Type _} : α ↪ ULift α where
  toFun := ULift.up
  inj' := ULift.up_injective

theorem ULift.finset_sum (α : Type _) (s : Finset α) (f : α → ℕ) :
  s.sum f = Finset.sum (s.map ULift.up_embedding)
    (fun (x : ULift α) ↦ f x.down) := by 
  rw [Finset.sum_bij' (fun a _ ↦ ULift.up a) _ _ (fun a _ ↦ a.down)]
  . intro a ha
    simp only [Finset.mem_map] at ha 
    obtain ⟨b, hb, rfl⟩ := ha
    exact hb 
  . intro a _ ; rfl
  . intro a _ ; rfl
  . intro a ha
    simp only [Finset.mem_map]
    exact ⟨a, ha, rfl⟩
  . intro a _ ; rfl

theorem ULift.fintype_sum (α : Type _) [Fintype α] (f : α → ℕ) :
  Finset.univ.sum f = Finset.univ.sum (fun (x : ULift α) ↦ f x.down) :=
  by
  rw [ULift.finset_sum]
  apply Finset.sum_congr
  rfl
  intro x _ ; rfl

noncomputable example {ι κ : Type _} [Fintype ι] [Fintype κ] [DecidableEq ι][DecidableEq κ] (e : ι ≃ κ) 
    (k : κ →₀ ℕ) : ι →₀ ℕ := by
  apply Finsupp.comapDomain e k
  apply Set.injOn_of_injective e.injective


    
noncomputable example (f : PolynomialMap A M N) 
  {ι : Type} {κ : Type _} [Fintype ι] [Fintype κ] [DecidableEq ι][DecidableEq κ] (e : ι ≃ κ) 
    (m : κ → M) (k : κ →₀ ℕ)  :
  coeff m f k = coeff (m ∘ e) f (Finsupp.equivCongrLeft e.symm k) := by
  simp only [Finsupp.equivCongrLeft_apply]

  -- simp only [generize, coe_mk, AddHom.coe_mk, zooEquiv_symm_apply, Function.comp_apply, EmbeddingLike.apply_eq_iff_eq]
  let φ : MvPolynomial ι A →ₐ[A] MvPolynomial κ A := 
    MvPolynomial.aeval (fun i ↦ MvPolynomial.X (e i))
  let ψ : MvPolynomial κ A →ₐ[A] MvPolynomial ι A := 
    MvPolynomial.aeval (fun k ↦ MvPolynomial.X (e.symm k))
  let hφ := f.isCompat φ
  let hψ := f.isCompat ψ
  suffices : generize A N (m ∘ e) f = 
    (rTensor N (AlgHom.toLinearMap ψ)) (generize A N m f)
  rw [this]
  sorry





theorem isHomogeneousOfDegree_iff
    (p : ℕ) (f : PolynomialMap A M N) :
  f.IsHomogeneousOfDegree p ↔
    ∀ {ι : Type _} [DecidableEq ι] [Fintype ι] 
      (m : ι → M) (k : ι →₀ ℕ) (h : coeff m f k ≠ 0), 
      (Finset.univ.sum k) = p :=
  by
  classical
  constructor
  · -- difficult direction
    sorry
    /- 
    intro hf
    intro ι _ _ m k h
    suffices hι : Nonempty ι
    obtain ⟨i₀: ι⟩ := hι

    simp only [IsHomogeneousOfDegree] at hf
    specialize hf (MvPolynomial ι A) (MvPolynomial.X i₀) 
      (Finset.sum Finset.univ fun i => MvPolynomial.X i ⊗ₜ[A] m i)
    simp [← Finset.sum_smul] at hf
    have : MvPolynomial.X (R := A) i₀ • (Finset.univ.sum fun (i : ι) => (MvPolynomial.X i : MvPolynomial ι A) ⊗ₜ[A] m i) = 
      Finset.univ.sum (fun i => (MvPolynomial.X i₀ * MvPolynomial.X i : MvPolynomial ι A) ⊗ₜ[A] m i)
    . rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rfl
    let hf' := LinearEquiv.congr_arg (e := (zooEquiv ι A N).symm) hf

    rw [this, image_eq_coeff_sum, image_eq_coeff_sum] at hf
    rw [Finsupp.smul_sum] at hf
    simp only [Finsupp.sum] at hf

    simp_rw [Finset.prod_mul_distrib] at hf

    let hzz := fun k => coeff_eq m k f



    simp only [coeff._eq_1, coe_mk, AddHom.coe_mk, ne_eq] at h 
--    simp only [zooInv._eq_1, coe_mk, AddHom.coe_mk] at h 
    

    sorry
    sorry 
    . sorry -/
  · intro hf R _ _ c m
    -- classical
    obtain ⟨n, m, r, rfl⟩ := TensorProduct.is_finsupp_sum_tmul' m
    simp only [Finset.sum_range]
    rw [Finset.smul_sum]
    simp_rw [TensorProduct.smul_tmul', Pi.smul_def]
    simp only [image_eq_coeff_sum]
    rw [Finsupp.smul_sum]
    apply Finsupp.sum_congr
    intro k hk
    simp only [smul_eq_mul]
    simp_rw [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    -- simp only [Subtype.exists, Finset.mem_range, exists_prop, exists_eq_right, not_lt]
    simp_rw [← smul_eq_mul, ← TensorProduct.smul_tmul']
    let hf' :=  @hf (ULift (Fin n)) _ _ 
    let m' : ULift (Fin n) → M := fun x ↦ m ↑x.down
    let k' : ULift (Fin n) →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun x ↦ k ↑x.down)
    specialize hf m' k'
    
    have : Finset.univ.sum k = Finset.univ.sum k'
    . simp only [Finsupp.equivFunOnFinite_symm_apply_toFun]
      rw [ULift.fintype_sum]
    rw [← this] at hf

    have : coeff (fun (x : Fin n) ↦ m ↑x) f k = coeff m' f k'
    . simp only
      sorry
    rw [← this] at hf

    by_cases hkp : Finset.univ.sum k = p
    . rw [hkp] 
    . rw [not_imp_comm] at hf
      rw [hf hkp]
      simp only [TensorProduct.tmul_zero, smul_zero]
      
    
    


    

#align polynomial_map.is_homogeneous_of_degree_iff PolynomialMap.isHomogeneousOfDegree_iff

end Graded

end PolynomialMap

end PolynomialMap

