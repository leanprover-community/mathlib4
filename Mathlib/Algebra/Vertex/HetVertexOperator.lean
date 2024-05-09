/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.RingTheory.HahnSeries.Binomial

/-!
# Vertex operators
In this file we introduce heterogeneous vertex operators using Hahn series.
## Definitions
* HetVertexOperator : An `R`-linear map from an `R`-module `V` to `HahnSeries Γ W`.
* Composition of heterogeneous vertex operators - values are Hahn series on lex order product.
## Main results
* `HahnSeries Γ R`-module structure on `HetVertexOperator Γ R V W`.  This means we can consider
  products of the form `(X-Y)^n A(X)B(Y)` for all integers `n`, where `(X-Y)^n` is expanded as
  `X^n(1-Y/X)^n` in `R((X))((Y))`
## To do:
* Incorporate OrderedCancelVAdd
* more API to make ext comparisons easier.
* formal variable API?
## References
* R. Borcherds
* G. Mason `Vertex rings and Pierce bundles` ArXiv 1707.00328
* A. Matsuo, K. Nagatomo `On axioms for a vertex algebra and locality of quantum fields`
  arXiv:hep-th/9706118
* H. Li's paper on local systems?
-/

noncomputable section

/-- A heterogeneous `Γ`-vertex operator over a commutator ring `R` is an `R`-linear map from an
`R`-module `V` to `Γ`-Hahn series with coefficients in an `R`-module `W`.-/
abbrev HetVertexOperator (Γ : Type*) [PartialOrder Γ] (R : Type*) [CommRing R]
    (V : Type*) (W : Type*) [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W] :=
  V →ₗ[R] (HahnModule Γ R W)

namespace HetVertexOperator

section Coeff

variable {Γ : Type*} [PartialOrder Γ] {R : Type*} {V W : Type*} [CommRing R]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

open HahnModule

@[ext]
theorem ext (A B : HetVertexOperator Γ R V W) (h : ∀(v : V), A v = B v) :
    A = B := LinearMap.ext h

/-- The coefficient of a heterogeneous vertex operator, viewed as a formal power series with
coefficients in linear maps. -/
@[simps]
def coeff (A : HetVertexOperator Γ R V W) (n : Γ) : V →ₗ[R] W where
  toFun := fun (x : V) => ((of R).symm (A x)).coeff n
  map_add' := by
      intro x y
      simp only [map_add, HahnSeries.add_coeff', Pi.add_apply, forall_const]
      exact rfl
  map_smul' := by
      intro r x
      simp only [map_smul, HahnSeries.smul_coeff, RingHom.id_apply, forall_const]
      exact rfl

theorem coeff.isPWOsupport (A : HetVertexOperator Γ R V W) (v : V) :
    ((of R).symm (A v)).coeff.support.IsPWO :=
  ((of R).symm (A v)).isPWO_support'

@[ext]
theorem coeff_inj : Function.Injective (coeff : HetVertexOperator Γ R V W → Γ → (V →ₗ[R] W)) := by
  intro _ _ h
  ext v n
  exact congrFun (congrArg DFunLike.coe (congrFun h n)) v

/-- Given a coefficient function valued in linear maps satisfying a partially well-ordered support
condition, we produce a heterogeneous vertex operator. -/
@[simps]
def of_coeff (f : Γ → V →ₗ[R] W)
    (hf : ∀(x : V), (Function.support (fun g => f g x)).IsPWO) : HetVertexOperator Γ R V W where
  toFun := fun x => {
    coeff := fun g => f g x
    isPWO_support' := hf x
  }
  map_add' := by
    intros
    simp only [map_add]
    exact rfl
  map_smul' := by
    intros
    simp only [map_smul, RingHom.id_apply]
    exact rfl

@[simp]
theorem add_coeff_apply (A B : HetVertexOperator Γ R V W) (n : Γ) :
    (A + B).coeff n = A.coeff n + B.coeff n := by
  ext v
  simp only [coeff_apply, LinearMap.add_apply, of_symm_add, HahnSeries.add_coeff', Pi.add_apply]

@[simp]
theorem add_coeff (A B : HetVertexOperator Γ R V W) : (A + B).coeff = A.coeff + B.coeff := by
  ext1 n
  exact add_coeff_apply A B n

@[simp]
theorem smul_coeff_apply (A : HetVertexOperator Γ R V W) (r : R) (n : Γ) :
    (r • A).coeff n = r • (A.coeff) n := by
  ext v
  simp only [coeff_apply, LinearMap.smul_apply, of_symm_smul, HahnSeries.smul_coeff]

@[simp]
theorem smul_coeff (A : HetVertexOperator Γ R V W) (r : R) : (r • A).coeff = r • (A.coeff) := by
  ext1 n
  exact smul_coeff_apply A r n

@[simp]
theorem nsmul_coeff (A : HetVertexOperator Γ R V W) {n : ℕ} : (n • A).coeff = n • (A.coeff) := by
  induction n with
  | zero => ext; simp
  | succ n ih => ext; simp [add_nsmul, add_coeff, ih]

end Coeff

section Module

variable {Γ Γ' : Type*} [OrderedCancelAddCommMonoid Γ] [PartialOrder Γ']
  [OrderedCancelAddAction Γ Γ'] {R : Type*} [CommRing R] {V W : Type*} [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W]

/-- The scalar multiplication of Hahn series on heterogeneous vertex operators. -/
def HahnSMul (x : HahnSeries Γ R) (A : HetVertexOperator Γ' R V W) :
    HetVertexOperator Γ' R V W where
  toFun v := x • (A v)
  map_add' u v := by simp only [map_add, smul_add]
  map_smul' r v := by
    simp only [map_smul, RingHom.id_apply]
    exact (HahnModule.smul_comm r x (A v)).symm

instance instHahnModule : Module (HahnSeries Γ R) (HetVertexOperator Γ' R V W) where
  smul x A := HahnSMul x A
  one_smul _ := by
    ext _ _
    simp only [one_smul]
  mul_smul _ _ _ := by
    ext _ _
    simp only [LinearMap.smul_apply, mul_smul]
  smul_zero _ := by
    ext _ _
    simp only [smul_zero, LinearMap.zero_apply, HahnModule.of_symm_zero, HahnSeries.zero_coeff]
  smul_add _ _ _ := by
    ext _ _
    simp only [smul_add, LinearMap.add_apply, LinearMap.smul_apply, HahnModule.of_symm_add,
      HahnSeries.add_coeff', Pi.add_apply]
  add_smul _ _ _ := by
    ext _ _
    simp only [coeff_apply, LinearMap.smul_apply, LinearMap.add_apply, HahnSeries.add_coeff']
    rw [HahnModule.add_smul Module.add_smul]
  zero_smul _ := by
    ext _ _
    simp only [zero_smul, LinearMap.zero_apply, HahnModule.of_symm_zero, HahnSeries.zero_coeff]

end  Module

section Products

variable {Γ Γ' : Type*} [OrderedCancelAddCommMonoid Γ] [OrderedCancelAddCommMonoid Γ'] {R : Type*}
  [CommRing R] {V W : Type*} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

open HahnModule

/-- The composite of two heterogeneous vertex operators acting on a vector, as an iterated Hahn
  series.-/
@[simps]
def CompHahnSeries {U : Type*} [AddCommGroup U] [Module R U] (A : HetVertexOperator Γ R V W)
    (B : HetVertexOperator Γ' R U V) (u : U) : HahnSeries Γ' (HahnSeries Γ W) where
  coeff g' := A (coeff B g' u)
  isPWO_support' := by
    refine Set.IsPWO.mono (((of R).symm (B u)).isPWO_support') ?_
    simp_all only [coeff_apply, Function.support_subset_iff, ne_eq, Function.mem_support]
    intro g' hg' hAB
    apply hg'
    simp_rw [hAB]
    simp_all only [map_zero, HahnSeries.zero_coeff, not_true_eq_false]

@[simp]
theorem CompHahnSeries.add {U : Type*} [AddCommGroup U] [Module R U] (A : HetVertexOperator Γ R V W)
    (B : HetVertexOperator Γ' R U V) (u v : U) :
    CompHahnSeries A B (u + v) = CompHahnSeries A B u + CompHahnSeries A B v := by
  ext
  simp only [CompHahnSeries_coeff, map_add, coeff_apply, HahnSeries.add_coeff', Pi.add_apply]
  rw [← @HahnSeries.add_coeff]

@[simp]
theorem CompHahnSeries.sMul {U : Type*} [AddCommGroup U] [Module R U]
    (A : HetVertexOperator Γ R V W) (B : HetVertexOperator Γ' R U V) (r : R) (u : U) :
    CompHahnSeries A B (r • u) = r • CompHahnSeries A B u := by
  ext
  simp only [CompHahnSeries_coeff, map_smul, coeff_apply, HahnSeries.smul_coeff]
  exact rfl

/-- The composite of two heterogeneous vertex operators, as a heterogeneous vertex operator. -/
@[simps]
def hetComp {U : Type*} [AddCommGroup U] [Module R U] (A : HetVertexOperator Γ R V W)
    (B : HetVertexOperator Γ' R U V) : HetVertexOperator (Γ' ×ₗ Γ) R U W where
  toFun u := HahnModule.of R (HahnSeries.ofIterate (CompHahnSeries A B u))
  map_add' := by
    intro u v
    ext g
    simp only [HahnSeries.ofIterate, CompHahnSeries.add, Equiv.symm_apply_apply,
      HahnModule.of_symm_add, HahnSeries.add_coeff', Pi.add_apply]
  map_smul' := by
    intro r x
    ext g
    simp only [HahnSeries.ofIterate, CompHahnSeries.sMul, Equiv.symm_apply_apply, RingHom.id_apply,
      HahnSeries.smul_coeff, CompHahnSeries_coeff, coeff_apply]
    exact rfl

-- TODO: comp_assoc

/-- The restriction of a heterogeneous vertex operator on a lex product to an element of the left
factor. -/
def ResLeft (A : HetVertexOperator (Γ' ×ₗ Γ) R V W) (g' : Γ'):  HetVertexOperator Γ R V W :=
  HetVertexOperator.of_coeff (fun g => coeff A (toLex (g', g)))
    (fun v => Set.PartiallyWellOrderedOn.fiberProdLex (A v).isPWO_support' _)

theorem coeff_ResLeft (A : HetVertexOperator (Γ' ×ₗ Γ) R V W) (g' : Γ') (g : Γ) :
    coeff (ResLeft A g') g = coeff A (toLex (g', g)) :=
  rfl

/-- The left residue as a linear map. -/
@[simps]
def ResLeft.linearMap (g' : Γ'):
    HetVertexOperator (Γ' ×ₗ Γ) R V W →ₗ[R] HetVertexOperator Γ R V W where
  toFun A := ResLeft A g'
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coeff_left_lex_supp.isPWO (A : HetVertexOperator (Γ ×ₗ Γ') R V W) (g' : Γ') (v : V) :
    (Function.support (fun (g : Γ) => (coeff A (toLex (g, g'))) v)).IsPWO := by
  refine Set.IsPWO.mono (Set.PartiallyWellOrderedOn.imageProdLex (A v).isPWO_support') ?_
  simp_all only [coeff_apply, Function.support_subset_iff, ne_eq, Set.mem_image,
    Function.mem_support]
  exact fun x a ↦ Exists.intro (toLex (x, g')) { left := a, right := rfl }

/-- The restriction of a heterogeneous vertex operator on a lex product to an element of the right
factor. -/
def ResRight (A : HetVertexOperator (Γ ×ₗ Γ') R V W) (g' : Γ') : HetVertexOperator Γ R V W :=
  HetVertexOperator.of_coeff (fun g => coeff A (g, g')) (fun v => coeff_left_lex_supp.isPWO A g' v)

theorem coeff_ResRight (A : HetVertexOperator (Γ ×ₗ Γ') R V W) (g' : Γ') (g : Γ) :
    coeff (ResRight A g') g = coeff A (toLex (g, g')) := rfl

/-- The right residue as a linear map. -/
@[simps]
def ResRight.linearMap (g' : Γ') :
    HetVertexOperator (Γ ×ₗ Γ') R V W →ₗ[R] HetVertexOperator Γ R V W where
  toFun A := ResRight A g'
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Products

section Binomial

variable {Γ : Type*} [OrderedCancelAddCommMonoid Γ] {R : Type*} {V W : Type*} [CommRing R]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

theorem lex_basis_lt : (toLex (0,1) : ℤ ×ₗ ℤ) < (toLex (1,0) : ℤ ×ₗ ℤ) := by decide
--#find_home! lex_basis_lt --[Mathlib.Data.Prod.Lex]

theorem toLex_vAdd_of_sub (k l m n : ℤ) :
    toLex ((m : ℤ) , (n : ℤ)) +ᵥ toLex (k - m, l - n) = toLex (k, l) := by
  rw [vadd_eq_add, ← @toLex_add, Prod.mk_add_mk, Int.add_comm, Int.sub_add_cancel, Int.add_comm,
    Int.sub_add_cancel]

/-- `-Y + X` as a unit of `R((X))((Y))` -/
def subLeft (R : Type*) [CommRing R] : (HahnSeries (ℤ ×ₗ ℤ) R)ˣ :=
  HahnSeries.UnitBinomial (AddGroup.isAddUnit (toLex (0,1))) lex_basis_lt (isUnit_neg_one (α := R))
    (1 : R)

theorem subLeft_eq : (subLeft R).val = HahnSeries.single (toLex (1,0)) 1 +
    HahnSeries.single (toLex (0,1)) (-1 : R) := by
  rw [subLeft, HahnSeries.UnitBinomial_val, add_comm, IsUnit.unit_spec]

@[simp]
theorem subLeft_leadingCoeff [Nontrivial R] : (subLeft R).val.leadingCoeff = (-1 : R) := by
  rw [subLeft_eq, add_comm, HahnSeries.leadingCoeff_single_add_single lex_basis_lt (by simp)]

theorem subLeft_order [Nontrivial R] : (subLeft R).val.order = toLex (0,1) := by
  rw [subLeft_eq, add_comm, HahnSeries.order_single_add_single lex_basis_lt (by simp)]

theorem subLeft_smul_coeff (A : HetVertexOperator (ℤ ×ₗ ℤ) R V W) (k l : ℤ) :
    ((subLeft R).val • A).coeff (toLex (k, l)) =
      A.coeff (toLex (k - 1, l)) - A.coeff (toLex (k, l - 1)) := by
  rw [subLeft_eq, add_smul, add_coeff_apply]
  ext v
  simp only [LinearMap.add_apply, coeff_apply, LinearMap.smul_apply, LinearMap.sub_apply]
  nth_rw 1 [← toLex_vAdd_of_sub k l 1 0]
  rw [sub_zero, HahnModule.single_smul_coeff_add, one_smul, ← toLex_vAdd_of_sub k l 0 1,
    sub_zero, HahnModule.single_smul_coeff_add, neg_one_smul, ← sub_eq_add_neg]

--describe coefficients of powers
--describe coefficients of `subLeft R • A` for `A : HetVO`.

/-- `X - Y` as a unit of `R((Y))((X))` -/
def subRight (R : Type*) [CommRing R] : (HahnSeries (ℤ ×ₗ ℤ) R)ˣ :=
    HahnSeries.UnitBinomial (AddGroup.isAddUnit (toLex (0,1))) lex_basis_lt (isUnit_one (M := R))
    (-1 : R)

theorem subRight_eq : (subRight R).val = HahnSeries.single (toLex (1,0)) (-1 : R) +
    HahnSeries.single (toLex (0,1)) (1 : R) := by
  rw [subRight, HahnSeries.UnitBinomial_val, add_comm, IsUnit.unit_spec]

theorem subRight_leadingCoeff [Nontrivial R] : (subRight R).val.leadingCoeff = (1 : R) := by
  rw [subRight_eq, add_comm, HahnSeries.leadingCoeff_single_add_single lex_basis_lt one_ne_zero]

theorem subRight_order [Nontrivial R] : (subRight R).val.order = toLex (0,1) := by
  rw [subRight_eq, add_comm, HahnSeries.order_single_add_single lex_basis_lt one_ne_zero]

--describe coefficients of powers

/-!
theorem subLeft_smul_eq_subRight_smul (A B : HetVertexOperator (ℤ ×ₗ ℤ) R V W)
    (h : ∀ (k l : ℤ), A.coeff (toLex (k, l)) = B.coeff (toLex (l, k))) (k l : ℤ) :
    ((subLeft R).val • A).coeff (toLex (k, l)) = ((subRight R).val • B).coeff (toLex (l, k)) := by
  sorry
-/

end Binomial

end HetVertexOperator
