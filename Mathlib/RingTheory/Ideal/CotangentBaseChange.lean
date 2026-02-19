/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Ideal.Cotangent

/-!
# Base change of cotangent spaces

Given an `R`-algebra `S`, an ideal `I` of `S` and a flat `R`-algebra `T`, we show that
the base change `T ⊗[R] I/I²` of the cotangent space of `I` is naturally isomorphic to the
cotangent space of the extended ideal `I · (T ⊗[R] S)`.

## Main definitions

* `TensorProduct.AlgebraTensorModule.tensorQuotientEquiv`: The tensor product of a module with
  a quotient module is the quotient of the tensor product, as a linear equivalence compatible
  with an auxiliary scalar action.
* `Algebra.TensorProduct.tensorQuotientEquiv`: The tensor product of an algebra with
  the quotient by an ideal is the quotient of the tensor product, as an algebra equivalence.
* `Ideal.Cotangent.lift`: Lift a linear map from `I` that vanishes on products to a linear map
  on the cotangent space `I/I²`.
* `Ideal.tensorCotangentTo`: The canonical map `T ⊗[R] I/I² → (I · (T ⊗[R] S))/(I · (T ⊗[R] S))²`.
* `Ideal.tensorCotangent`: When `T` is `R`-flat, `tensorCotangentTo` is a linear equivalence.
-/

noncomputable section

universe u

open TensorProduct

-- TODO: Move to `Mathlib.LinearAlgebra.TensorProduct.Quotient`
namespace TensorProduct.AlgebraTensorModule

variable {R : Type*} (A B : Type*) [CommRing R] [CommRing A] [Algebra R A]
  [CommRing B] [Algebra R B]
variable (M : Type*) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
variable {N : Type*} [AddCommGroup N] [Module R N] [Module B N] [IsScalarTower R B N]

/-- The tensor product of a module `M` with a quotient `N ⧸ n` is linearly equivalent to the
quotient of `M ⊗ N` by the range of `M ⊗ n → M ⊗ N`, as an `A`-linear equivalence. -/
def tensorQuotientEquiv (n : Submodule B N) :
    M ⊗[R] (N ⧸ n) ≃ₗ[A] (M ⊗[R] N) ⧸ LinearMap.range (lTensor A M (n.subtype.restrictScalars R)) :=
  let f : M ⊗[R] (N ⧸ n) ≃ₗ[R]
      M ⊗[R] N ⧸ LinearMap.range (lTensor A M (n.subtype.restrictScalars R)) :=
    TensorProduct.tensorQuotientEquiv M (n.restrictScalars R)
  f.toAddEquiv.toLinearEquiv <| fun c x ↦ by
    simp only [AddEquiv.coe_mk, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
      LinearEquiv.invFun_eq_symm, Equiv.coe_fn_mk]
    induction x with
    | zero => simp
    | add x y hx hy => simp [hx, hy]
    | tmul x y =>
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [smul_tmul']
    rfl

@[simp]
lemma tensorQuotientEquiv_apply_tmul (n : Submodule B N) (x : M) (y : N) :
    tensorQuotientEquiv A B M n (x ⊗ₜ[R] Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (x ⊗ₜ[R] y) :=
  rfl

@[simp]
lemma tensorQuotientEquiv_symm_apply_mk_tmul (n : Submodule B N) (x : M) (y : N) :
    (tensorQuotientEquiv A B M n).symm (Submodule.Quotient.mk (x ⊗ₜ[R] y)) =
      x ⊗ₜ[R] Submodule.Quotient.mk y :=
  rfl

end TensorProduct.AlgebraTensorModule

-- TODO: Move to `Mathlib.RingTheory.TensorProduct.Basic`
namespace Algebra.TensorProduct

variable {R : Type*} (S T A : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [CommRing T] [Algebra R T]
  [CommRing A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]

lemma map_includeRight_eq (I : Ideal T) :
    (I.map (includeRight (A := A) (R := R))).restrictScalars S =
      LinearMap.range ((AlgebraTensorModule.lTensor S A) (I.subtype.restrictScalars R)) := by
  have := I.map_includeRight_eq (R := R) (A := A)
  rwa [Submodule.ext_iff] at this ⊢

/-- The tensor product of an `S`-algebra `A` over `R` with the quotient of `T` by an ideal `I`
is isomorphic to the quotient of `A ⊗[R] T` by the extended ideal, as an `S`-algebra. -/
def tensorQuotientEquiv (I : Ideal T) :
    A ⊗[R] (T ⧸ I) ≃ₐ[S] (A ⊗[R] T) ⧸ I.map (includeRight (A := A) (R := R)) :=
  let f : A ⊗[R] (T ⧸ I) ≃ₗ[S]
      A ⊗[R] T ⧸ LinearMap.range ((AlgebraTensorModule.lTensor S A)
        (I.subtype.restrictScalars R)) :=
    AlgebraTensorModule.tensorQuotientEquiv (R := R) S T A I
  have heq : LinearMap.range ((AlgebraTensorModule.lTensor S A)
      (I.subtype.restrictScalars R)) =
        (I.map (includeRight (A := A) (R := R))).restrictScalars S := by
    symm
    have := I.map_includeRight_eq (R := R) (A := A)
    rwa [Submodule.ext_iff] at this ⊢
  let g : (A ⊗[R] T ⧸ LinearMap.range ((AlgebraTensorModule.lTensor S A)
      (I.subtype.restrictScalars R))) ≃ₗ[S]
      A ⊗[R] T ⧸ (I.map (includeRight (A := A) (R := R))).restrictScalars S :=
    Submodule.quotEquivOfEq _ _ heq
  let e : A ⊗[R] (T ⧸ I) ≃ₗ[S] (A ⊗[R] T) ⧸ I.map (includeRight (A := A) (R := R)) :=
    f ≪≫ₗ g
  AlgEquiv.ofLinearEquiv e rfl <| by
    apply LinearMap.map_mul_of_map_mul_tmul
    intro a₁ a₂ b₁ b₂
    obtain ⟨b₁, rfl⟩ := Ideal.Quotient.mk_surjective b₁
    obtain ⟨b₂, rfl⟩ := Ideal.Quotient.mk_surjective b₂
    rw [← map_mul]
    have : (Ideal.Quotient.mk I) (b₁ * b₂) = Submodule.Quotient.mk (b₁ * b₂) := rfl
    simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply, e, f, g]
    rw [this, AlgebraTensorModule.tensorQuotientEquiv_apply_tmul]
    simp only [← Ideal.Quotient.mk_eq_mk, AlgebraTensorModule.tensorQuotientEquiv_apply_tmul]
    rw [← Algebra.TensorProduct.tmul_mul_tmul]
    rfl

@[simp]
lemma tensorQuotientEquiv_apply_tmul (I : Ideal T) (a : A) (t : T) :
    tensorQuotientEquiv (R := R) S T A I (a ⊗ₜ t) = a ⊗ₜ[R] t :=
  rfl

@[simp]
lemma tensorQuotientEquiv_symm_apply_tmul (I : Ideal T) (a : A) (t : T) :
    (tensorQuotientEquiv (R := R) S T A I).symm (a ⊗ₜ[R] t) = a ⊗ₜ[R] (Ideal.Quotient.mk I t) :=
  rfl

end Algebra.TensorProduct

namespace Ideal

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable (T : Type*) [CommRing T] [Algebra R T]
variable (I : Ideal S)

attribute [local instance] Algebra.TensorProduct.rightAlgebra

-- TODO: Move to `Mathlib.RingTheory.Ideal.Cotangent`
section

variable {I} in
/-- Lift a linear map `f : I →ₗ[R] M` that vanishes on products to a linear map on the
cotangent space `I ⧸ I ^ 2`. -/
def Cotangent.lift {M : Type*} [AddCommGroup M] [Module R M]
    (f : I →ₗ[R] M) (hf : ∀ (x y : I), f (x * y) = 0) :
    I.Cotangent →ₗ[R] M where
  __ := QuotientAddGroup.lift _ f.toAddMonoidHom <| by
    intro x hx
    simp only [Submodule.mem_toAddSubgroup] at hx
    simp only [AddMonoidHom.mem_ker]
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr y _
      exact hf ⟨r, hr⟩ y
    · intro x y hx hy
      simp only [map_add, hx, hy, add_zero]
  map_smul' r x := by
    obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
    have : r • I.toCotangent x = I.toCotangent (r • x) := by simp
    simp only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, RingHom.id_apply, this]
    apply map_smul f

variable {I} in
@[simp]
lemma Cotangent.lift_toCotangent {M : Type*} [AddCommGroup M] [Module R M]
    (f : I →ₗ[R] M) (hf : ∀ (x y : I), f (x * y) = 0)
    (x : I) :
    Cotangent.lift f hf (I.toCotangent x) = f x :=
  rfl

/-- The canonical map from the cotangent space to the quotient by the square is injective. -/
lemma cotangentToQuotientSquare_injective :
    Function.Injective I.cotangentToQuotientSquare := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
  rw [toCotangent_to_quotient_square] at hx
  rw [Ideal.toCotangent_eq_zero]
  exact (Submodule.Quotient.mk_eq_zero (I ^ 2)).mp hx

end

-- TODO: Move to `Mathlib.RingTheory.Ideal.Maps`
section

/-- `Algebra.idealMap S I` preserves multiplication. -/
@[simp]
lemma _root_.Algebra.idealMap_mul {R : Type*} [CommSemiring R] (S : Type*) [Semiring S]
    [Algebra R S] (I : Ideal R) (x y : I) :
    Algebra.idealMap S I (x * y) = Algebra.idealMap S I x * Algebra.idealMap S I y := by
  ext
  simp

end

variable (R)

/-- The canonical map from the base change of the cotangent space `T ⊗[R] I/I²` to the
cotangent space `(I · (T ⊗[R] S))/(I · (T ⊗[R] S))²` of the extended ideal. -/
def tensorCotangentTo :
    T ⊗[R] I.Cotangent →ₗ[T] (I.map <| algebraMap S (T ⊗[R] S)).Cotangent :=
  LinearMap.liftBaseChange T <|
    Cotangent.lift
      ((map (algebraMap S (T ⊗[R] S)) I).toCotangent.restrictScalars R ∘ₗ
        (Algebra.idealMap _ I).restrictScalars R) <| fun x y ↦ by
    simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
      Algebra.idealMap_mul, toCotangent_eq_zero, sq]
    apply mul_mem_mul
    · exact ((Algebra.idealMap (T ⊗[R] S) I) x).property
    · exact ((Algebra.idealMap (T ⊗[R] S) I) y).property

@[simp]
lemma tensorCotangentTo_tmul (t : T) (x : I) :
    tensorCotangentTo R T I (t ⊗ₜ[R] I.toCotangent x) =
      t • (I.map (algebraMap S (T ⊗[R] S))).toCotangent ((Algebra.idealMap (T ⊗[R] S) I) x) := by
  simp [tensorCotangentTo]

-- TODO: refactor using lift of surjective map is surjective
lemma tensorCotangentTo_surjective :
    Function.Surjective (I.tensorCotangentTo R T) := by
  intro x
  obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective _ x
  have := I.map_includeRight_eq (R := R) (A := T)
  rw [Submodule.ext_iff] at this
  simp only [Submodule.restrictScalars_mem, LinearMap.mem_range] at this
  have hmem (y : T ⊗[R] I) :
      (I.subtype.restrictScalars R).lTensor T y ∈ map (Algebra.TensorProduct.includeRight) I :=
    (this _).mpr ⟨y, rfl⟩
  obtain ⟨y, rfl⟩ : ∃ (y : T ⊗[R] I), ⟨(I.subtype.restrictScalars R).lTensor T y, hmem y⟩ = x :=
    let ⟨y, hy⟩ := (this _).mp x.property
    ⟨y, by ext; simpa⟩
  have htxm (t : T) (x : I) :
      t ⊗ₜ[R] ↑x ∈ map (algebraMap S (T ⊗[R] S)) I := hmem (t ⊗ₜ[R] ↑x)
  have heq (t : T) (x : I) :
      (map (algebraMap S (T ⊗[R] S)) I).toCotangent ⟨t ⊗ₜ[R] x, htxm t x⟩ =
        t • (I.map (algebraMap S (T ⊗[R] S))).toCotangent ((Algebra.idealMap (T ⊗[R] S) I) x) := by
    rw [← LinearMap.map_smul_of_tower]; congr; simp
  induction y with
  | zero =>
    exact ⟨0, by simp only [map_zero]; exact (map_zero _).symm⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by simp only [map_add, ha, hb]; rfl⟩
  | tmul t x =>
    exact ⟨t ⊗ₜ I.toCotangent x, by simpa using (heq ..).symm⟩

/-- If `T` is a flat `R`-module, the canonical map `tensorCotangentTo R T I` is injective. -/
lemma tensorCotangentTo_injective_of_flat [Module.Flat R T] :
    Function.Injective (I.tensorCotangentTo R T) := by
  let f : (I.map <| algebraMap S (T ⊗[R] S)).Cotangent →ₗ[T]
      T ⊗[R] S ⧸ (I.map <| algebraMap S (T ⊗[R] S)) ^ 2 :=
    (Ideal.cotangentToQuotientSquare _).restrictScalars T
  suffices h : Function.Injective (f ∘ₗ tensorCotangentTo R T I) by
    exact Function.Injective.of_comp h
  let g : T ⊗[R] I.Cotangent →ₗ[T] T ⊗[R] (S ⧸ I ^ 2) :=
    AlgebraTensorModule.lTensor T T I.cotangentToQuotientSquare
  have : (I.map <| algebraMap S (T ⊗[R] S)) ^ 2 = (I ^ 2).map (algebraMap S (T ⊗[R] S)) := by
    rw [Ideal.map_pow]
  let u : T ⊗[R] (S ⧸ I ^ 2) ≃ₐ[T] T ⊗[R] S ⧸ map (algebraMap S (T ⊗[R] S)) (I ^ 2) :=
    Algebra.TensorProduct.tensorQuotientEquiv ..
  let hₐ : T ⊗[R] (S ⧸ I ^ 2) ≃ₐ[T] T ⊗[R] S ⧸ (I.map <| algebraMap S (T ⊗[R] S)) ^ 2 :=
    AlgEquiv.trans u (Ideal.quotientEquivAlgOfEq T this.symm)
  have (x : S) : (u (1 ⊗ₜ[R] (Quotient.mk (I ^ 2)) x)) = Quotient.mk _ (1 ⊗ₜ[R] x) := by
    apply Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul
  have : f ∘ₗ tensorCotangentTo R T I = hₐ.toLinearMap ∘ₗ g := by
    ext x
    obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
    simp [f, g, hₐ, this]
    simp [RingHom.algebraMap_toAlgebra]
  simp only [this, LinearMap.coe_comp]
  apply Function.Injective.comp
  · exact hₐ.injective
  · apply Module.Flat.lTensor_preserves_injective_linearMap (M := T)
      (I.cotangentToQuotientSquare.restrictScalars R)
    apply cotangentToQuotientSquare_injective

/-- If `T` is a flat `R`-module, the base change of the cotangent space of `I` is linearly
equivalent to the cotangent space of the extended ideal `I · (T ⊗[R] S)`. -/
def tensorCotangent [Module.Flat R T] :
    T ⊗[R] I.Cotangent ≃ₗ[T] (I.map <| algebraMap S (T ⊗[R] S)).Cotangent :=
  LinearEquiv.ofBijective (I.tensorCotangentTo R T)
    ⟨I.tensorCotangentTo_injective_of_flat R T, I.tensorCotangentTo_surjective R T⟩

end Ideal
