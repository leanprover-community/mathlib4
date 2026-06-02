/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.Algebra.Algebra.Prod

/-!
# The R-algebra structure on families of R-algebras

The R-algebra structure on `Π i : I, A i` when each `A i` is an R-algebra.

## Main definitions

* `Pi.algebra`
* `Pi.evalAlgHom`
* `Pi.constAlgHom`
-/

@[expose] public section

namespace Pi

-- The indexing type
variable (ι : Type*)

-- The scalar type
variable {R : Type*}

-- The family of types already equipped with instances
variable (A : ι → Type*)
variable [CommSemiring R] [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)]

instance algebra : Algebra R (Π i, A i) where
  algebraMap := RingHom.pi fun i ↦ algebraMap R (A i)
  commutes' := fun a f ↦ by ext; simp [Algebra.commutes]
  smul_def' := fun a f ↦ by ext; simp [Algebra.smul_def]

@[push ←]
theorem algebraMap_def (a : R) : algebraMap R (Π i, A i) a = fun i ↦ algebraMap R (A i) a :=
  rfl

@[simp]
theorem algebraMap_apply (a : R) (i : ι) : algebraMap R (Π i, A i) a i = algebraMap R (A i) a :=
  rfl

variable {ι}

variable {A} in
/-- A family of algebra homomorphisms `g i : B →ₐ[R] A i` defines an algebra homomorphism
`AlgHom.pi g : B →ₐ[R] Π i, A i` given by `AlgHom.pi g x i = g i x`. -/
@[simps!]
def _root_.AlgHom.pi {B : Type*} [Semiring B] [Algebra R B] (g : Π i, B →ₐ[R] A i) :
    B →ₐ[R] Π i, A i where
  __ := RingHom.pi fun i ↦ (g i).toRingHom
  commutes' r := by ext; simp

variable (R)

/-- Use `AlgHom.pi` instead. -/
@[deprecated AlgHom.pi (since := "2026-05-30")] def algHom {B : Type*} [Semiring B] [Algebra R B]
    (g : Π i, B →ₐ[R] A i) : B →ₐ[R] Π i, A i :=
  .pi g

/-- Use `AlgHom.pi_apply` instead. -/
@[deprecated AlgHom.pi_apply (since := "2026-05-30")] theorem algHom_apply {B : Type*} [Semiring B]
    [Algebra R B] (g : Π i, B →ₐ[R] A i) (x : B) (i : ι) : Pi.algHom R A g x i = g i x :=
  AlgHom.pi_apply g x i

/-- `Function.eval` as an `AlgHom`. The name matches `Pi.evalRingHom`, `Pi.evalMonoidHom`,
etc. -/
@[simps]
def evalAlgHom (i : ι) : (Π i, A i) →ₐ[R] A i :=
  { Pi.evalRingHom A i with
    toFun := fun f ↦ f i
    commutes' := fun _ ↦ rfl }

lemma coe_evalAlgHom (i : ι) : evalAlgHom R A i = evalRingHom A i := rfl

@[simp]
theorem algHom_evalAlgHom : AlgHom.pi (evalAlgHom R A) = AlgHom.id R (Π i, A i) := rfl

/-- `Pi.algHom` commutes with composition. -/
theorem algHom_comp {B C : Type*} [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]
    (g : ∀ i, C →ₐ[R] A i) (h : B →ₐ[R] C) :
    (AlgHom.pi g).comp h = AlgHom.pi (fun i ↦ (g i).comp h) := rfl

variable (S : ι → Type*) [∀ i, CommSemiring (S i)]

instance [∀ i, Algebra (S i) (A i)] : Algebra (Π i, S i) (Π i, A i) where
  algebraMap := RingHom.pi fun _ ↦ (algebraMap _ _).comp (Pi.evalRingHom S _)
  commutes' _ _ := funext fun _ ↦ Algebra.commutes _ _
  smul_def' _ _ := funext fun _ ↦ Algebra.smul_def _ _

example : Pi.instAlgebraForall S S = Algebra.id _ := rfl

variable (A B : Type*) [Semiring B] [Algebra R B]

/-- `Function.const` as an `AlgHom`. The name matches `Pi.constRingHom`, `Pi.constMonoidHom`,
etc. -/
@[simps]
def constAlgHom : B →ₐ[R] A → B :=
  { Pi.constRingHom A B with
    toFun := Function.const _
    commutes' := fun _ ↦ rfl }

/-- When `R` is commutative and permits an `algebraMap`, `Pi.constRingHom` is equal to that
map. -/
@[simp]
theorem constRingHom_eq_algebraMap : constRingHom A R = algebraMap R (A → R) :=
  rfl

@[simp]
theorem constAlgHom_eq_algebra_ofId : constAlgHom R A R = Algebra.ofId R (A → R) :=
  rfl

end Pi

/-- A special case of `Pi.algebra` for non-dependent types. Lean struggles to elaborate
definitions elsewhere in the library without this. -/
instance Function.algebra {R : Type*} (ι : Type*) (A : Type*) [CommSemiring R] [Semiring A]
    [Algebra R A] : Algebra R (ι → A) :=
  Pi.algebra _ _

namespace AlgHom

variable {R A B : Type*}
variable [CommSemiring R] [Semiring A] [Semiring B]
variable [Algebra R A] [Algebra R B]

/-- `R`-algebra homomorphism between the function spaces `ι → A` and `ι → B`, induced by an
`R`-algebra homomorphism `f` between `A` and `B`. -/
@[simps]
protected def compLeft (f : A →ₐ[R] B) (ι : Type*) : (ι → A) →ₐ[R] ι → B :=
  { f.toRingHom.compLeft ι with
    toFun := fun h ↦ f ∘ h
    commutes' := fun c ↦ by
      ext
      exact f.commutes' c }

end AlgHom

namespace AlgEquiv

variable {α β R ι : Type*} {A₁ A₂ A₃ : ι → Type*}
variable [CommSemiring R] [∀ i, Semiring (A₁ i)] [∀ i, Semiring (A₂ i)] [∀ i, Semiring (A₃ i)]
variable [∀ i, Algebra R (A₁ i)] [∀ i, Algebra R (A₂ i)] [∀ i, Algebra R (A₃ i)]

/-- A family of algebra equivalences `∀ i, (A₁ i ≃ₐ A₂ i)` generates a
multiplicative equivalence between `Π i, A₁ i` and `Π i, A₂ i`.

This is the `AlgEquiv` version of `Equiv.piCongrRight`, and the dependent version of
`AlgEquiv.arrowCongr`.
-/
@[simps apply]
def piCongrRight (e : ∀ i, A₁ i ≃ₐ[R] A₂ i) : (Π i, A₁ i) ≃ₐ[R] Π i, A₂ i :=
  { @RingEquiv.piCongrRight ι A₁ A₂ _ _ fun i ↦ (e i).toRingEquiv with
    toFun := fun x j ↦ e j (x j)
    invFun := fun x j ↦ (e j).symm (x j)
    commutes' := fun r ↦ by
      ext i
      simp }

@[simp]
theorem piCongrRight_refl :
    (piCongrRight fun i ↦ (AlgEquiv.refl : A₁ i ≃ₐ[R] A₁ i)) = AlgEquiv.refl :=
  rfl

@[simp]
theorem piCongrRight_symm (e : ∀ i, A₁ i ≃ₐ[R] A₂ i) :
    (piCongrRight e).symm = piCongrRight fun i ↦ (e i).symm :=
  rfl

@[simp]
theorem piCongrRight_trans (e₁ : ∀ i, A₁ i ≃ₐ[R] A₂ i) (e₂ : ∀ i, A₂ i ≃ₐ[R] A₃ i) :
    (piCongrRight e₁).trans (piCongrRight e₂) = piCongrRight fun i ↦ (e₁ i).trans (e₂ i) :=
  rfl

variable (R A₁) in
/-- The opposite of a direct product is isomorphic to the direct product of the opposites as
algebras. -/
def piMulOpposite : (Π i, A₁ i)ᵐᵒᵖ ≃ₐ[R] Π i, (A₁ i)ᵐᵒᵖ where
  __ := RingEquiv.piMulOpposite A₁
  commutes' _ := rfl

variable (R A₁) in
/--
Transport dependent functions through an equivalence of the base space.

This is `Equiv.piCongrLeft'` as an `AlgEquiv`.
-/
def piCongrLeft' {ι' : Type*} (e : ι ≃ ι') : (Π i, A₁ i) ≃ₐ[R] Π i, A₁ (e.symm i) where
  __ := RingEquiv.piCongrLeft' A₁ e
  commutes' _ := rfl

-- Priority `low` to ensure generic `map_{add, mul, zero, one}` lemmas are applied first
@[simp low]
lemma piCongrLeft'_apply {ι' : Type*} (e : ι ≃ ι') (x : (Π i, A₁ i)) :
    piCongrLeft' R A₁ e x = Equiv.piCongrLeft' _ _ x := rfl

-- Priority `low` to ensure generic `map_{add, mul, zero, one}` lemmas are applied first
@[simp low]
lemma piCongrLeft'_symm_apply {ι' : Type*} (e : ι ≃ ι') (x : Π i, A₁ (e.symm i)) :
    (piCongrLeft' R A₁ e).symm x = (Equiv.piCongrLeft' _ _).symm x := rfl

variable (R A₁) in
/--
Transport dependent functions through an equivalence of the base space, expressed as
"simplification".

This is `Equiv.piCongrLeft` as an `AlgEquiv`.
-/
def piCongrLeft {ι' : Type*} (e : ι' ≃ ι) : (Π i, A₁ (e i)) ≃ₐ[R] Π i, A₁ i :=
  (AlgEquiv.piCongrLeft' R A₁ e.symm).symm

-- Priority `low` to ensure generic `map_{add, mul, zero, one}` lemmas are applied first
@[simp low]
lemma piCongrLeft_apply {ι' : Type*} (e : ι' ≃ ι) (x : Π i, A₁ (e i)) :
    piCongrLeft R A₁ e x = Equiv.piCongrLeft _ _ x := rfl

-- Priority `low` to ensure generic `map_{add, mul, zero, one}` lemmas are applied first
@[simp low]
lemma piCongrLeft_symm_apply {ι' : Type*} (e : ι' ≃ ι) (x : Π i, A₁ i) :
    (piCongrLeft R A₁ e).symm x = (Equiv.piCongrLeft _ _).symm x := rfl

section

variable (S : Type*) [Semiring S] [Algebra R S]

variable (ι R) in
/-- If `ι` has a unique element, then `ι → S` is isomorphic to `S` as an `R`-algebra. -/
def funUnique [Unique ι] : (ι → S) ≃ₐ[R] S :=
  .ofRingEquiv (f := .piUnique (fun i : ι ↦ S)) (by simp)

-- Priority `low` to ensure generic `map_{add, mul, zero, one}` lemmas are applied first
@[simp low]
lemma funUnique_apply [Unique ι] (x : ι → S) : funUnique R ι S x = Equiv.funUnique ι S x := rfl

-- Priority `low` to ensure generic `map_{add, mul, zero, one}` lemmas are applied first
@[simp low]
lemma funUnique_symm_apply [Unique ι] (x : S) :
    (funUnique R ι S).symm x = (Equiv.funUnique ι S).symm x := rfl

variable (α β R) in
/-- `Equiv.sumArrowEquivProdArrow` as an algebra equivalence. -/
def sumArrowEquivProdArrow : (α ⊕ β → S) ≃ₐ[R] (α → S) × (β → S) :=
  .ofRingEquiv (f := .sumArrowEquivProdArrow α β S) (by intro; ext <;> simp)

-- Priority `low` to ensure generic `map_{add, mul, zero, one}` lemmas are applied first
@[simp low]
lemma sumArrowEquivProdArrow_apply (x : α ⊕ β → S) :
    sumArrowEquivProdArrow α β R S x = Equiv.sumArrowEquivProdArrow α β S x := rfl

-- Priority `low` to ensure generic `map_{add, mul, zero, one}` lemmas are applied first
@[simp low]
lemma sumArrowEquivProdArrow_symm_apply_inr (x : (α → S) × (β → S)) :
    (sumArrowEquivProdArrow α β R S).symm x = (Equiv.sumArrowEquivProdArrow α β S).symm x :=
  rfl

end

end AlgEquiv

/-- Apply an algebra map component-wise along a vector. -/
protected def Pi.algebraMap (ι R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A] :
    (ι → R) →ₗ[R] (ι → A) where
  toFun v := algebraMap R A ∘ v
  map_add' v w := by simp
  map_smul' t v := by ext; simp [Algebra.smul_def]
