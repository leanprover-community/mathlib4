/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.HahnSeries.Multiplication

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
* Residues of heterogeneous vertex operators, when `Γ = Γ' ×ₗ ℤ` or `Γ = ℤ ×ₗ Γ'`.
* more API to make ext comparisons easier.
* formal variable API?
## References
* G. Mason `Vertex rings and Pierce bundles` ArXiv 1707.00328
* A. Matsuo, K. Nagatomo `On axioms for a vertex algebra and locality of quantum fields`
  arXiv:hep-th/9706118
* H. Li's paper on local systems?
-/

noncomputable section

variable {Γ : Type*} [OrderedCancelAddCommMonoid Γ] {R : Type*} {V W : Type*} [CommRing R]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- A heterogeneous `Γ`-vertex operator over a commutator ring `R` is an `R`-linear map from an
`R`-module `V` to `Γ`-Hahn series with coefficients in an `R`-module `W`.-/
abbrev HetVertexOperator (Γ : Type*) [OrderedCancelAddCommMonoid Γ] (R : Type*) [CommRing R]
    (V : Type*) (W : Type*) [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W] :=
  V →ₗ[R] (HahnModule Γ R W)

namespace VertexAlg

@[ext]
theorem HetVertexOperator.ext (A B : HetVertexOperator Γ R V W) (h : ∀(v : V), A v = B v) :
    A = B := LinearMap.ext h

/-- The scalar multiplication of Hahn series on heterogeneous vertex operators. -/
def HahnSMul (x : HahnSeries Γ R) (A : HetVertexOperator Γ R V W) :
    HetVertexOperator Γ R V W where
  toFun v := x • (A v)
  map_add' u v := by simp only [map_add, smul_add]
  map_smul' r v := by
    simp only [map_smul, RingHom.id_apply]
    exact (smul_comm r x (A v)).symm

instance instHahnModule : Module (HahnSeries Γ R) (HetVertexOperator Γ R V W) where
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
    simp only [LinearMap.smul_apply, LinearMap.add_apply, HahnModule.of_symm_add,
      HahnSeries.add_coeff', Pi.add_apply]
    rw [HahnModule.add_smul Module.add_smul]
    simp only [HahnModule.of_symm_add, HahnSeries.add_coeff', Pi.add_apply]
  zero_smul _ := by
    ext _ _
    simp only [zero_smul, LinearMap.zero_apply, HahnModule.of_symm_zero, HahnSeries.zero_coeff]

/-- The coefficient of a heterogeneous vertex operator, viewed as a formal power series with
coefficients in linear maps. -/
@[simps]
def coeff (A : HetVertexOperator Γ R V W) (n : Γ) : V →ₗ[R] W where
  toFun := fun (x : V) => (A x).coeff n
  map_add' := by
      intro x y
      simp only [map_add, HahnSeries.add_coeff', Pi.add_apply, forall_const]
      exact rfl
  map_smul' := by
      intro r x
      simp only [map_smul, HahnSeries.smul_coeff, RingHom.id_apply, forall_const]
      exact rfl

theorem coeff.isPWOsupport (A : HetVertexOperator Γ R V W) (v : V) : (A v).coeff.support.IsPWO :=
  (A v).isPWO_support'

@[ext]
theorem coeff_inj : Function.Injective (coeff : HetVertexOperator Γ R V W → Γ → (V →ₗ[R] W)) := by
  intro _ _ h
  ext v n
  exact congrFun (congrArg DFunLike.coe (congrFun h n)) v

/-- Given a coefficient function valued in linear maps satisfying a partially well-ordered support
condition, we produce a heterogeneous vertex operator. -/
@[simps]
def HetVertexOperator.of_coeff (f : Γ → V →ₗ[R] W)
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

/-- The composite of two heterogeneous vertex operators acting on a vector, as an iterated Hahn
  series.-/
@[simps]
def CompHahnSeries {Γ' : Type*} [OrderedCancelAddCommMonoid Γ'] {U : Type*} [AddCommGroup U]
    [Module R U] (A : HetVertexOperator Γ R V W) (B : HetVertexOperator Γ' R U V) (u : U) :
    HahnSeries Γ' (HahnSeries Γ W) where
  coeff g' := A (coeff B g' u)
  isPWO_support' := by
    refine Set.IsPWO.mono ((B u).isPWO_support') ?_
    simp_all only [coeff_apply, Function.support_subset_iff, ne_eq, Function.mem_support]
    intro g' hg' hAB
    apply hg'
    simp_rw [hAB]
    simp_all only [map_zero, HahnSeries.zero_coeff, not_true_eq_false]

@[simp]
theorem CompHahnSeries.add {Γ' : Type*} [OrderedCancelAddCommMonoid Γ'] {U : Type*} [AddCommGroup U]
    [Module R U] (A : HetVertexOperator Γ R V W) (B : HetVertexOperator Γ' R U V) (u v : U) :
    CompHahnSeries A B (u + v) = CompHahnSeries A B u + CompHahnSeries A B v := by
  ext
  simp only [CompHahnSeries_coeff, map_add, coeff_apply, HahnSeries.add_coeff', Pi.add_apply]
  rw [← @HahnSeries.add_coeff]

@[simp]
theorem CompHahnSeries.sMul {Γ' : Type*} [OrderedCancelAddCommMonoid Γ'] {U : Type*}
    [AddCommGroup U] [Module R U] (A : HetVertexOperator Γ R V W) (B : HetVertexOperator Γ' R U V)
    (r : R) (u : U) : CompHahnSeries A B (r • u) = r • CompHahnSeries A B u := by
  ext
  simp only [CompHahnSeries_coeff, map_smul, coeff_apply, HahnSeries.smul_coeff]
  exact rfl

/-- The composite of two heterogeneous vertex operators, as a heterogeneous vertex operator. -/
@[simps]
def HetComp {Γ' : Type*} [OrderedCancelAddCommMonoid Γ'] {U : Type*} [AddCommGroup U] [Module R U]
    (A : HetVertexOperator Γ R V W) (B : HetVertexOperator Γ' R U V) :
    HetVertexOperator (Γ' ×ₗ Γ) R U W where
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

/-- The residue of a heterogeneous vertex operator on a lex product with `ℤ` on the left. -/
def ResLeft (A : HetVertexOperator (ℤ ×ₗ Γ) R V W) :  HetVertexOperator Γ R V W :=
  HetVertexOperator.of_coeff (fun g => coeff A (toLex (-1, g)))
    (fun v => Set.PartiallyWellOrderedOn.fiberProdLex (A v).isPWO_support' _)

theorem coeff_ResLeft (A : HetVertexOperator (ℤ ×ₗ Γ) R V W) (g : Γ) :
    coeff (ResLeft A) g = coeff A (toLex (-1, g)) := rfl

/-- The left residue as a linear map. -/
@[simps]
def ResLeft.linearMap : HetVertexOperator (ℤ ×ₗ Γ) R V W →ₗ[R] HetVertexOperator Γ R V W where
  toFun := ResLeft
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coeff_left_lex_supp.isPWO (A : HetVertexOperator (Γ ×ₗ ℤ) R V W) (v : V) :
    (Function.support (fun (g : Γ) => (coeff A (toLex (g, -1))) v)).IsPWO := by
  refine Set.IsPWO.mono (Set.PartiallyWellOrderedOn.imageProdLex (A v).isPWO_support') ?_
  simp_all only [coeff_apply, Function.support_subset_iff, ne_eq, Set.mem_image,
    Function.mem_support]
  exact fun x a ↦ Exists.intro (toLex (x, -1)) { left := a, right := rfl }

/-- The residue of a heterogeneous vertex operator on a lex product with `ℤ` on the right. -/
def ResRight (A : HetVertexOperator (Γ ×ₗ ℤ) R V W) : HetVertexOperator Γ R V W :=
  HetVertexOperator.of_coeff (fun g => coeff A (g, -1)) (fun v => coeff_left_lex_supp.isPWO A v)

theorem coeff_ResRight (A : HetVertexOperator (Γ ×ₗ ℤ) R V W) (g : Γ) :
    coeff (ResRight A) g = coeff A (toLex (g, -1)) := rfl

/-- The right residue as a linear map. -/
@[simps]
def ResRight.linearMap : HetVertexOperator (Γ ×ₗ ℤ) R V W →ₗ[R] HetVertexOperator Γ R V W where
  toFun := ResRight
  map_add' _ _ := rfl
  map_smul' _ _ := rfl


end VertexAlg
