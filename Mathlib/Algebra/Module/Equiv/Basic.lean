/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro, Anne Baanen,
  Frédéric Dupuis, Heather Macbeth
-/
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.GroupWithZero.Action.Basic
import Mathlib.Algebra.GroupWithZero.Action.Units
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Algebra.Module.Hom
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Prod

/-!
# Further results on (semi)linear equivalences.
-/

open Function

variable {R : Type*} {R₂ : Type*}
variable {K : Type*} {S : Type*} {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

section AddCommMonoid

namespace LinearEquiv

variable [Semiring R] [Semiring S] [Semiring R₂] [AddCommMonoid M] [AddCommMonoid M₂]

section RestrictScalars

variable (R)
variable [Module R M] [Module R M₂] [Module S M] [Module S M₂]
  [LinearMap.CompatibleSMul M M₂ R S]

/-- If `M` and `M₂` are both `R`-semimodules and `S`-semimodules and `R`-semimodule structures
are defined by an action of `R` on `S` (formally, we have two scalar towers), then any `S`-linear
equivalence from `M` to `M₂` is also an `R`-linear equivalence.

See also `LinearMap.restrictScalars`. -/
@[simps]
def restrictScalars (f : M ≃ₗ[S] M₂) : M ≃ₗ[R] M₂ :=
  { f.toLinearMap.restrictScalars R with
    toFun := f
    invFun := f.symm
    left_inv := f.left_inv
    right_inv := f.right_inv }

theorem restrictScalars_injective :
    Function.Injective (restrictScalars R : (M ≃ₗ[S] M₂) → M ≃ₗ[R] M₂) := fun _ _ h ↦
  ext (LinearEquiv.congr_fun h :)

@[simp]
theorem restrictScalars_inj (f g : M ≃ₗ[S] M₂) :
    f.restrictScalars R = g.restrictScalars R ↔ f = g :=
  (restrictScalars_injective R).eq_iff

end RestrictScalars

theorem _root_.Module.End.isUnit_iff [Module R M] (f : Module.End R M) :
    IsUnit f ↔ Function.Bijective f :=
  ⟨fun h ↦
    Function.bijective_iff_has_inverse.mpr <|
      ⟨h.unit.inv,
        ⟨Module.End.isUnit_inv_apply_apply_of_isUnit h,
        Module.End.isUnit_apply_inv_apply_of_isUnit h⟩⟩,
    fun H ↦
    let e : M ≃ₗ[R] M := { f, Equiv.ofBijective f H with }
    ⟨⟨_, e.symm, LinearMap.ext e.right_inv, LinearMap.ext e.left_inv⟩, rfl⟩⟩

@[deprecated (since := "2025-04-28")]
alias _root_.Module.End_isUnit_iff := _root_.Module.End.isUnit_iff

section Automorphisms

variable [Module R M]

instance automorphismGroup : Group (M ≃ₗ[R] M) where
  mul f g := g.trans f
  one := LinearEquiv.refl R M
  inv f := f.symm
  mul_assoc _ _ _ := rfl
  mul_one _ := ext fun _ ↦ rfl
  one_mul _ := ext fun _ ↦ rfl
  inv_mul_cancel f := ext <| f.left_inv

lemma one_eq_refl : (1 : M ≃ₗ[R] M) = refl R M := rfl
lemma mul_eq_trans (f g : M ≃ₗ[R] M) : f * g = g.trans f := rfl

@[simp]
lemma coe_one : ↑(1 : M ≃ₗ[R] M) = id := rfl

@[simp]
lemma coe_toLinearMap_one : (↑(1 : M ≃ₗ[R] M) : M →ₗ[R] M) = LinearMap.id := rfl

@[simp]
lemma coe_toLinearMap_mul {e₁ e₂ : M ≃ₗ[R] M} :
    (↑(e₁ * e₂) : M →ₗ[R] M) = (e₁ : M →ₗ[R] M) * (e₂ : M →ₗ[R] M) :=
  rfl

theorem coe_pow (e : M ≃ₗ[R] M) (n : ℕ) : ⇑(e ^ n) = e^[n] := hom_coe_pow _ rfl (fun _ _ ↦ rfl) _ _

theorem pow_apply (e : M ≃ₗ[R] M) (n : ℕ) (m : M) : (e ^ n) m = e^[n] m := congr_fun (coe_pow e n) m

@[simp] lemma mul_apply (f : M ≃ₗ[R] M) (g : M ≃ₗ[R] M) (x : M) : (f * g) x = f (g x) := rfl

/-- Restriction from `R`-linear automorphisms of `M` to `R`-linear endomorphisms of `M`,
promoted to a monoid hom. -/
@[simps]
def automorphismGroup.toLinearMapMonoidHom : (M ≃ₗ[R] M) →* M →ₗ[R] M where
  toFun e := e.toLinearMap
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The tautological action by `M ≃ₗ[R] M` on `M`.

This generalizes `Function.End.applyMulAction`. -/
instance applyDistribMulAction : DistribMulAction (M ≃ₗ[R] M) M where
  smul := (· <| ·)
  smul_zero := LinearEquiv.map_zero
  smul_add := LinearEquiv.map_add
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp]
protected theorem smul_def (f : M ≃ₗ[R] M) (a : M) : f • a = f a :=
  rfl

/-- `LinearEquiv.applyDistribMulAction` is faithful. -/
instance apply_faithfulSMul : FaithfulSMul (M ≃ₗ[R] M) M :=
  ⟨LinearEquiv.ext⟩

instance apply_smulCommClass [SMul S R] [SMul S M] [IsScalarTower S R M] :
    SMulCommClass S (M ≃ₗ[R] M) M where
  smul_comm r e m := (e.map_smul_of_tower r m).symm

instance apply_smulCommClass' [SMul S R] [SMul S M] [IsScalarTower S R M] :
    SMulCommClass (M ≃ₗ[R] M) S M :=
  SMulCommClass.symm _ _ _

end Automorphisms

section OfSubsingleton

variable (M M₂)
variable [Module R M] [Module R M₂] [Subsingleton M] [Subsingleton M₂]

/-- Any two modules that are subsingletons are isomorphic. -/
@[simps]
def ofSubsingleton : M ≃ₗ[R] M₂ :=
  { (0 : M →ₗ[R] M₂) with
    toFun := fun _ ↦ 0
    invFun := fun _ ↦ 0
    left_inv := fun _ ↦ Subsingleton.elim _ _
    right_inv := fun _ ↦ Subsingleton.elim _ _ }

@[simp]
theorem ofSubsingleton_self : ofSubsingleton M M = refl R M := by
  ext
  simp [eq_iff_true_of_subsingleton]

end OfSubsingleton

end LinearEquiv

namespace Module

/-- `g : R ≃+* S` is `R`-linear when the module structure on `S` is `Module.compHom S g` . -/
@[simps]
def compHom.toLinearEquiv {R S : Type*} [Semiring R] [Semiring S] (g : R ≃+* S) :
    haveI := compHom S (↑g : R →+* S)
    R ≃ₗ[R] S :=
  letI := compHom S (↑g : R →+* S)
  { g with
    toFun := (g : R → S)
    invFun := (g.symm : S → R)
    map_smul' := g.map_mul }

end Module

namespace DistribMulAction

variable (R M) [Semiring R] [AddCommMonoid M] [Module R M]
variable [Group S] [DistribMulAction S M] [SMulCommClass S R M]

/-- Each element of the group defines a linear equivalence.

This is a stronger version of `DistribMulAction.toAddEquiv`. -/
@[simps!]
def toLinearEquiv (s : S) : M ≃ₗ[R] M :=
  { toAddEquiv M s, toLinearMap R M s with }

/-- Each element of the group defines a module automorphism.

This is a stronger version of `DistribMulAction.toAddAut`. -/
@[simps]
def toModuleAut : S →* M ≃ₗ[R] M where
  toFun := toLinearEquiv R M
  map_one' := LinearEquiv.ext <| one_smul _
  map_mul' _ _ := LinearEquiv.ext <| mul_smul _ _

end DistribMulAction

namespace AddEquiv

section AddCommMonoid

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Module R M] [Module R M₂]
variable (e : M ≃+ M₂)

/-- An additive equivalence whose underlying function preserves `smul` is a linear equivalence. -/
def toLinearEquiv (h : ∀ (c : R) (x), e (c • x) = c • e x) : M ≃ₗ[R] M₂ :=
  { e with map_smul' := h }

@[simp]
theorem coe_toLinearEquiv (h : ∀ (c : R) (x), e (c • x) = c • e x) : ⇑(e.toLinearEquiv h) = e :=
  rfl

@[simp]
theorem coe_toLinearEquiv_symm (h : ∀ (c : R) (x), e (c • x) = c • e x) :
    ⇑(e.toLinearEquiv h).symm = e.symm :=
  rfl

/-- An additive equivalence between commutative additive monoids is a linear equivalence between
ℕ-modules -/
def toNatLinearEquiv : M ≃ₗ[ℕ] M₂ :=
  e.toLinearEquiv fun c a ↦ by rw [map_nsmul]

@[simp]
theorem coe_toNatLinearEquiv : ⇑e.toNatLinearEquiv = e :=
  rfl

@[simp]
theorem coe_symm_toNatLinearEquiv : ⇑e.toNatLinearEquiv.symm = e.symm :=
  rfl

@[simp]
theorem toNatLinearEquiv_toAddEquiv : ↑e.toNatLinearEquiv = e :=
  rfl

@[simp]
theorem _root_.LinearEquiv.toAddEquiv_toNatLinearEquiv (e : M ≃ₗ[ℕ] M₂) :
    AddEquiv.toNatLinearEquiv ↑e = e :=
  DFunLike.coe_injective rfl

@[simp]
theorem toNatLinearEquiv_symm : e.symm.toNatLinearEquiv = e.toNatLinearEquiv.symm :=
  rfl

@[simp]
theorem toNatLinearEquiv_refl : (AddEquiv.refl M).toNatLinearEquiv = LinearEquiv.refl ℕ M :=
  rfl

@[simp]
theorem toNatLinearEquiv_trans (e₂ : M₂ ≃+ M₃) :
    (e.trans e₂).toNatLinearEquiv = e.toNatLinearEquiv.trans e₂.toNatLinearEquiv :=
  rfl

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup M] [AddCommGroup M₂] [AddCommGroup M₃]
variable (e : M ≃+ M₂)

/-- An additive equivalence between commutative additive groups is a linear
equivalence between ℤ-modules -/
def toIntLinearEquiv : M ≃ₗ[ℤ] M₂ :=
  e.toLinearEquiv fun c a ↦ e.toAddMonoidHom.map_zsmul a c

@[simp]
theorem coe_toIntLinearEquiv : ⇑e.toIntLinearEquiv = e :=
  rfl

@[simp]
theorem coe_symm_toIntLinearEquiv : ⇑e.toIntLinearEquiv.symm = e.symm :=
  rfl

@[simp]
theorem toIntLinearEquiv_toAddEquiv : ↑e.toIntLinearEquiv = e := by
  ext
  rfl

@[simp]
theorem _root_.LinearEquiv.toAddEquiv_toIntLinearEquiv (e : M ≃ₗ[ℤ] M₂) :
    AddEquiv.toIntLinearEquiv (e : M ≃+ M₂) = e :=
  DFunLike.coe_injective rfl

@[simp]
theorem toIntLinearEquiv_symm : e.symm.toIntLinearEquiv = e.toIntLinearEquiv.symm :=
  rfl

@[simp]
theorem toIntLinearEquiv_refl : (AddEquiv.refl M).toIntLinearEquiv = LinearEquiv.refl ℤ M :=
  rfl

@[simp]
theorem toIntLinearEquiv_trans (e₂ : M₂ ≃+ M₃) :
    (e.trans e₂).toIntLinearEquiv = e.toIntLinearEquiv.trans e₂.toIntLinearEquiv :=
  rfl

end AddCommGroup

end AddEquiv

namespace LinearMap

variable (R S M)
variable [Semiring R] [Semiring S] [AddCommMonoid M] [Module R M]

/-- The equivalence between R-linear maps from `R` to `M`, and points of `M` itself.
This says that the forgetful functor from `R`-modules to types is representable, by `R`.

This is an `S`-linear equivalence, under the assumption that `S` acts on `M` commuting with `R`.
When `R` is commutative, we can take this to be the usual action with `S = R`.
Otherwise, `S = ℕ` shows that the equivalence is additive.
See note [bundled maps over different rings].
-/
@[simps]
def ringLmapEquivSelf [Module S M] [SMulCommClass R S M] : (R →ₗ[R] M) ≃ₗ[S] M :=
  { applyₗ' S (1 : R) with
    toFun := fun f ↦ f 1
    invFun := smulRight (1 : R →ₗ[R] R)
    left_inv := fun f ↦ by
      ext
      simp only [coe_smulRight, Module.End.one_apply, smul_eq_mul, ← map_smul f, mul_one]
    right_inv := fun x ↦ by simp }

end LinearMap

/--
The `R`-linear equivalence between additive morphisms `A →+ B` and `ℕ`-linear morphisms `A →ₗ[ℕ] B`.
-/
@[simps]
def addMonoidHomLequivNat {A B : Type*} (R : Type*) [Semiring R] [AddCommMonoid A]
    [AddCommMonoid B] [Module R B] : (A →+ B) ≃ₗ[R] A →ₗ[ℕ] B where
  toFun := AddMonoidHom.toNatLinearMap
  invFun := LinearMap.toAddMonoidHom
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/--
The `R`-linear equivalence between additive morphisms `A →+ B` and `ℤ`-linear morphisms `A →ₗ[ℤ] B`.
-/
@[simps]
def addMonoidHomLequivInt {A B : Type*} (R : Type*) [Semiring R] [AddCommGroup A] [AddCommGroup B]
    [Module R B] : (A →+ B) ≃ₗ[R] A →ₗ[ℤ] B where
  toFun := AddMonoidHom.toIntLinearMap
  invFun := LinearMap.toAddMonoidHom
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Ring equivalence between additive group endomorphisms of an `AddCommGroup` `A` and
`ℤ`-module endomorphisms of `A.` -/
@[simps] def addMonoidEndRingEquivInt (A : Type*) [AddCommGroup A] :
    AddMonoid.End A ≃+* Module.End ℤ A :=
  { addMonoidHomLequivInt (B := A) ℤ with
    map_mul' := fun _ _ ↦ rfl }

namespace LinearEquiv

section AddCommMonoid

section Subsingleton

variable [Semiring R] [Semiring R₂]
variable [AddCommMonoid M] [AddCommMonoid M₂]
variable [Module R M] [Module R₂ M₂]
variable {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R}
variable [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]

section Module

variable [Subsingleton M] [Subsingleton M₂]

/-- Between two zero modules, the zero map is an equivalence. -/
instance : Zero (M ≃ₛₗ[σ₁₂] M₂) :=
  ⟨{ (0 : M →ₛₗ[σ₁₂] M₂) with
      toFun := 0
      invFun := 0
      right_inv := Subsingleton.elim _
      left_inv := Subsingleton.elim _ }⟩

-- Even though these are implied by `Subsingleton.elim` via the `Unique` instance below, they're
-- nice to have as `rfl`-lemmas for `dsimp`.
@[simp]
theorem zero_symm : (0 : M ≃ₛₗ[σ₁₂] M₂).symm = 0 :=
  rfl

@[simp]
theorem coe_zero : ⇑(0 : M ≃ₛₗ[σ₁₂] M₂) = 0 :=
  rfl

theorem zero_apply (x : M) : (0 : M ≃ₛₗ[σ₁₂] M₂) x = 0 :=
  rfl

/-- Between two zero modules, the zero map is the only equivalence. -/
instance : Unique (M ≃ₛₗ[σ₁₂] M₂) where
  uniq _ := toLinearMap_injective (Subsingleton.elim _ _)
  default := 0

end Module

instance uniqueOfSubsingleton [Subsingleton R] [Subsingleton R₂] : Unique (M ≃ₛₗ[σ₁₂] M₂) := by
  haveI := Module.subsingleton R M
  haveI := Module.subsingleton R₂ M₂
  infer_instance

end Subsingleton

section Uncurry

variable [Semiring R]
variable [AddCommMonoid M] [Module R M]
variable (V V₂ R M)

/-- Linear equivalence between a curried and uncurried function.
  Differs from `TensorProduct.curry`. -/
protected def curry : (V × V₂ → M) ≃ₗ[R] V → V₂ → M :=
  { Equiv.curry _ _ _ with
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl }

@[simp]
theorem coe_curry : ⇑(LinearEquiv.curry R M V V₂) = curry :=
  rfl

@[simp]
theorem coe_curry_symm : ⇑(LinearEquiv.curry R M V V₂).symm = uncurry :=
  rfl

end Uncurry

section

variable [Semiring R] [Semiring R₂]
variable [AddCommMonoid M] [AddCommMonoid M₂]
variable {module_M : Module R M} {module_M₂ : Module R₂ M₂}
variable {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R}
variable {re₁₂ : RingHomInvPair σ₁₂ σ₂₁} {re₂₁ : RingHomInvPair σ₂₁ σ₁₂}
variable (f : M →ₛₗ[σ₁₂] M₂) (g : M₂ →ₛₗ[σ₂₁] M)


/-- If a linear map has an inverse, it is a linear equivalence. -/
def ofLinear (h₁ : f.comp g = LinearMap.id) (h₂ : g.comp f = LinearMap.id) : M ≃ₛₗ[σ₁₂] M₂ :=
  { f with
    invFun := g
    left_inv := LinearMap.ext_iff.1 h₂
    right_inv := LinearMap.ext_iff.1 h₁ }

@[simp]
theorem ofLinear_apply {h₁ h₂} (x : M) : (ofLinear f g h₁ h₂ : M ≃ₛₗ[σ₁₂] M₂) x = f x :=
  rfl

@[simp]
theorem ofLinear_symm_apply {h₁ h₂} (x : M₂) : (ofLinear f g h₁ h₂ : M ≃ₛₗ[σ₁₂] M₂).symm x = g x :=
  rfl

@[simp]
theorem ofLinear_toLinearMap {h₁ h₂} : (ofLinear f g h₁ h₂ : M ≃ₛₗ[σ₁₂] M₂) = f := rfl

@[simp]
theorem ofLinear_symm_toLinearMap {h₁ h₂} : (ofLinear f g h₁ h₂ : M ≃ₛₗ[σ₁₂] M₂).symm = g := rfl

end

end AddCommMonoid

section Neg

variable (R) [Semiring R] [AddCommGroup M] [Module R M]

/-- `x ↦ -x` as a `LinearEquiv` -/
def neg : M ≃ₗ[R] M :=
  { Equiv.neg M, (-LinearMap.id : M →ₗ[R] M) with }

variable {R}

@[simp]
theorem coe_neg : ⇑(neg R : M ≃ₗ[R] M) = -id :=
  rfl

theorem neg_apply (x : M) : neg R x = -x := by simp

@[simp]
theorem symm_neg : (neg R : M ≃ₗ[R] M).symm = neg R :=
  rfl

end Neg

section Semiring

open LinearMap

section Semilinear

variable {R₁ R₂ R₁' R₂' : Type*} {M₁ M₂ M₁' M₂' : Type*}
variable [Semiring R₁] [Semiring R₂] [Semiring R₁'] [Semiring R₂']
variable [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₁'] [AddCommMonoid M₂']
variable [Module R₁ M₁] [Module R₂ M₂] [Module R₁' M₁'] [Module R₂' M₂']
variable {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁} {σ₁'₂' : R₁' →+* R₂'} {σ₂'₁' : R₂' →+* R₁'}
variable {σ₁₁' : R₁ →+* R₁'} {σ₂₂' : R₂ →+* R₂'}
variable {σ₂₁' : R₂ →+* R₁'} {σ₁₂' : R₁ →+* R₂'}
variable [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
variable [RingHomInvPair σ₁'₂' σ₂'₁'] [RingHomInvPair σ₂'₁' σ₁'₂']
variable [RingHomCompTriple σ₁₁' σ₁'₂' σ₁₂'] [RingHomCompTriple σ₂₁ σ₁₂' σ₂₂']
variable [RingHomCompTriple σ₂₂' σ₂'₁' σ₂₁'] [RingHomCompTriple σ₁₂ σ₂₁' σ₁₁']

/-- A linear isomorphism between the domains and codomains of two spaces of linear maps gives an
additive isomorphism between the two function spaces.

See also `LinearEquiv.arrowCongr` for the linear version of this isomorphism. -/
@[simps] def arrowCongrAddEquiv (e₁ : M₁ ≃ₛₗ[σ₁₂] M₂) (e₂ : M₁' ≃ₛₗ[σ₁'₂'] M₂') :
    (M₁ →ₛₗ[σ₁₁'] M₁') ≃+ (M₂ →ₛₗ[σ₂₂'] M₂') where
  toFun f := (e₂.comp f).comp e₁.symm.toLinearMap
  invFun f := (e₂.symm.comp f).comp e₁.toLinearMap
  left_inv f := by
    ext x
    simp only [symm_apply_apply, Function.comp_apply, coe_comp, coe_coe]
  right_inv f := by
    ext x
    simp only [Function.comp_apply, apply_symm_apply, coe_comp, coe_coe]
  map_add' f g := by
    ext x
    simp only [map_add, add_apply, Function.comp_apply, coe_comp, coe_coe]

/-- If `M` and `M₂` are linearly isomorphic then the endomorphism rings of `M` and `M₂`
are isomorphic.

See `LinearEquiv.conj` for the linear version of this isomorphism. -/
@[simps!] def conjRingEquiv (e : M₁ ≃ₛₗ[σ₁₂] M₂) : Module.End R₁ M₁ ≃+* Module.End R₂ M₂ where
  __ := arrowCongrAddEquiv e e
  map_mul' _ _ := by ext; simp [arrowCongrAddEquiv]

/-- A linear isomorphism between the domains an codomains of two spaces of linear maps gives a
linear isomorphism with respect to an action on the domains. -/
@[simps] def domMulActCongrRight [Semiring S] [Module S M₁]
    [SMulCommClass R₁ S M₁] [RingHomCompTriple σ₁₂' σ₂'₁' σ₁₁']
    (e₂ : M₁' ≃ₛₗ[σ₁'₂'] M₂') : (M₁ →ₛₗ[σ₁₁'] M₁') ≃ₗ[Sᵈᵐᵃ] (M₁ →ₛₗ[σ₁₂'] M₂') where
  __ := arrowCongrAddEquiv (.refl ..) e₂
  map_smul' := DomMulAct.mk.forall_congr_right.mp fun _ _ ↦ by ext; simp

end Semilinear

end Semiring

section CommSemiring

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Module R M] [Module R M₂] [Module R M₃]

open LinearMap

/-- Multiplying by a unit `a` of the ring `R` is a linear equivalence. -/
def smulOfUnit (a : Rˣ) : M ≃ₗ[R] M :=
  DistribMulAction.toLinearEquiv R M a

section arrowCongr

-- Difference from above: `R₁` and `R₂` are commutative
/-!
The modules for `arrowCongr` and its lemmas below are related via the semilinearities
```
M₁  ←⎯⎯⎯σ₁₂⎯⎯⎯→ M₂  ←⎯⎯⎯σ₂₃⎯⎯⎯→ M₃
⏐               ⏐               ⏐
σ₁₁'            σ₂₂'            σ₃₃'
↓               ↓               ↓
M₁' ←⎯⎯σ₁'₂'⎯⎯→ M₂' ←⎯⎯σ₂'₃'⎯⎯→ M₃
⏐               ⏐
σ₁'₁''          σ₂'₂''
↓               ↓
M₁''←⎯σ₁''₂''⎯→ M₂''
```
where the horizontal direction corresponds to the `≃ₛₗ`s, and is needed for `arrowCongr_trans`,
while the vertical direction corresponds to the `→ₛₗ`s, and is needed `arrowCongr_comp`.

`Rᵢ` is not necessarily commutative, but `Rᵢ'` and `Rᵢ''` are.
-/
variable {R₁ R₂ R₃ R₁' R₂' R₃' R₁'' R₂'' : Type*} {M₁ M₂ M₃ M₁' M₂' M₃' M₁'' M₂'' : Type*}
variable [Semiring R₁] [Semiring R₂] [Semiring R₃]
variable [CommSemiring R₁'] [CommSemiring R₂'] [CommSemiring R₃']
variable [CommSemiring R₁''] [CommSemiring R₂'']
variable [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [AddCommMonoid M₁'] [AddCommMonoid M₂'] [AddCommMonoid M₃']
variable [AddCommMonoid M₁''] [AddCommMonoid M₂'']
variable [Module R₁ M₁] [Module R₂ M₂] [Module R₃ M₃]
variable [Module R₁' M₁'] [Module R₂' M₂'] [Module R₃' M₃']
variable [Module R₁'' M₁''] [Module R₂'' M₂'']
-- horizontal edges and closures
variable {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁}
variable {σ₂₃ : R₂ →+* R₃} {σ₃₂ : R₃ →+* R₂}
variable {σ₁₃ : R₁ →+* R₃} {σ₃₁ : R₃ →+* R₁}
variable {σ₁'₂' : R₁' →+* R₂'} {σ₂'₁' : R₂' →+* R₁'}
variable {σ₂'₃' : R₂' →+* R₃'} {σ₃'₂' : R₃' →+* R₂'}
variable {σ₁'₃' : R₁' →+* R₃'} {σ₃'₁' : R₃' →+* R₁'}
-- vertical edges and closures
variable {σ₁''₂'' : R₁'' →+* R₂''} {σ₂''₁'' : R₂'' →+* R₁''}
variable {σ₁₁' : R₁ →+* R₁'} {σ₂₂' : R₂ →+* R₂'} {σ₃₃' : R₃ →+* R₃'}
variable {σ₁'₁'' : R₁' →+* R₁''} {σ₂'₂'' : R₂' →+* R₂''}
variable {σ₁₁'' : R₁ →+* R₁''} {σ₂₂'' : R₂ →+* R₂''}
-- diagonals
variable {σ₂₁' : R₂ →+* R₁'} {σ₁₂' : R₁ →+* R₂'}
variable {σ₃₂' : R₃ →+* R₂'} {σ₂₃' : R₂ →+* R₃'}
variable {σ₃₁' : R₃ →+* R₁'} {σ₁₃' : R₁ →+* R₃'}
variable {σ₂'₁'' : R₂' →+* R₁''} {σ₁'₂'' : R₁' →+* R₂''}
variable {σ₂₁'' : R₂ →+* R₁''} {σ₁₂'' : R₁ →+* R₂''}
variable [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
variable [RingHomInvPair σ₁'₂' σ₂'₁'] [RingHomInvPair σ₂'₁' σ₁'₂']
variable [RingHomInvPair σ₂₃ σ₃₂] [RingHomInvPair σ₃₂ σ₂₃]
variable [RingHomInvPair σ₂'₃' σ₃'₂'] [RingHomInvPair σ₃'₂' σ₂'₃']
variable [RingHomInvPair σ₁₃ σ₃₁] [RingHomInvPair σ₃₁ σ₁₃]
variable [RingHomInvPair σ₁'₃' σ₃'₁'] [RingHomInvPair σ₃'₁' σ₁'₃']
variable [RingHomInvPair σ₁''₂'' σ₂''₁''] [RingHomInvPair σ₂''₁'' σ₁''₂'']
variable [RingHomCompTriple σ₁₁' σ₁'₁'' σ₁₁''] [RingHomCompTriple σ₂₂' σ₂'₂'' σ₂₂'']
variable [RingHomCompTriple σ₁₁' σ₁'₂' σ₁₂'] [RingHomCompTriple σ₂₁ σ₁₂' σ₂₂']
variable [RingHomCompTriple σ₂₂' σ₂'₁' σ₂₁'] [RingHomCompTriple σ₁₂ σ₂₁' σ₁₁']
variable [RingHomCompTriple σ₁₁' σ₁'₃' σ₁₃'] [RingHomCompTriple σ₃₁ σ₁₃' σ₃₃']
variable [RingHomCompTriple σ₃₃' σ₃'₁' σ₃₁'] [RingHomCompTriple σ₁₃ σ₃₁' σ₁₁']
variable [RingHomCompTriple σ₂₂' σ₂'₃' σ₂₃'] [RingHomCompTriple σ₃₂ σ₂₃' σ₃₃']
variable [RingHomCompTriple σ₃₃' σ₃'₂' σ₃₂'] [RingHomCompTriple σ₂₃ σ₃₂' σ₂₂']
variable [RingHomCompTriple σ₁₁'' σ₁''₂'' σ₁₂''] [RingHomCompTriple σ₂₁ σ₁₂'' σ₂₂'']
variable [RingHomCompTriple σ₂₂'' σ₂''₁'' σ₂₁''] [RingHomCompTriple σ₁₂ σ₂₁'' σ₁₁'']
variable [RingHomCompTriple σ₁'₁'' σ₁''₂'' σ₁'₂''] [RingHomCompTriple σ₂'₁' σ₁'₂'' σ₂'₂'']
variable [RingHomCompTriple σ₂'₂'' σ₂''₁'' σ₂'₁''] [RingHomCompTriple σ₁'₂' σ₂'₁'' σ₁'₁'']
variable [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomCompTriple σ₃₂ σ₂₁ σ₃₁]
variable [RingHomCompTriple σ₁'₂' σ₂'₃' σ₁'₃'] [RingHomCompTriple σ₃'₂' σ₂'₁' σ₃'₁']

/-- A linear isomorphism between the domains and codomains of two spaces of linear maps gives a
linear isomorphism between the two function spaces.

See `LinearEquiv.arrowCongrAddEquiv` for the additive version of this isomorphism that works
over a not necessarily commutative semiring. -/
def arrowCongr (e₁ : M₁ ≃ₛₗ[σ₁₂] M₂) (e₂ : M₁' ≃ₛₗ[σ₁'₂'] M₂') :
    (M₁ →ₛₗ[σ₁₁'] M₁') ≃ₛₗ[σ₁'₂'] (M₂ →ₛₗ[σ₂₂'] M₂') where
  __ := arrowCongrAddEquiv e₁ e₂
  map_smul' c f := by ext; simp [arrowCongrAddEquiv, map_smulₛₗ]

@[simp]
theorem arrowCongr_apply (e₁ : M₁ ≃ₛₗ[σ₁₂] M₂) (e₂ : M₁' ≃ₛₗ[σ₁'₂'] M₂') (f : M₁ →ₛₗ[σ₁₁'] M₁')
    (x : M₂) : arrowCongr e₁ e₂ f x = e₂ (f (e₁.symm x)) :=
  rfl

@[simp]
theorem arrowCongr_symm_apply (e₁ : M₁ ≃ₛₗ[σ₁₂] M₂) (e₂ : M₁' ≃ₛₗ[σ₁'₂'] M₂') (f : M₂ →ₛₗ[σ₂₂'] M₂')
    (x : M₁) : (arrowCongr e₁ e₂).symm f x = e₂.symm (f (e₁ x)) :=
  rfl

theorem arrowCongr_comp
    (e₁ : M₁ ≃ₛₗ[σ₁₂] M₂) (e₂ : M₁' ≃ₛₗ[σ₁'₂'] M₂') (e₃ : M₁'' ≃ₛₗ[σ₁''₂''] M₂'')
    (f : M₁ →ₛₗ[σ₁₁'] M₁') (g : M₁' →ₛₗ[σ₁'₁''] M₁'') :
    arrowCongr e₁ e₃ (g.comp f) = (arrowCongr e₂ e₃ g).comp (arrowCongr e₁ e₂ f) := by
  ext
  simp only [symm_apply_apply, arrowCongr_apply, LinearMap.comp_apply]

theorem arrowCongr_trans
    (e₁ : M₁ ≃ₛₗ[σ₁₂] M₂) (e₁' : M₁' ≃ₛₗ[σ₁'₂'] M₂')
    (e₂ : M₂ ≃ₛₗ[σ₂₃] M₃) (e₂' : M₂' ≃ₛₗ[σ₂'₃'] M₃') :
    ((arrowCongr e₁ e₁').trans (arrowCongr e₂ e₂' : (M₂ →ₛₗ[σ₂₂'] M₂') ≃ₛₗ[σ₂'₃'] _)) =
      arrowCongr (e₁.trans e₂) (e₁'.trans e₂') :=
  rfl

/-- If `M` and `M₂` are linearly isomorphic then the two spaces of linear maps from `M` and `M₂` to
themselves are linearly isomorphic.

See `LinearEquiv.conjRingEquiv` for the isomorphism between endomorphism rings,
which works over a not necessarily commutative semiring. -/
-- TODO: upgrade to AlgEquiv (but this file currently cannot import AlgEquiv)
def conj (e : M₁' ≃ₛₗ[σ₁'₂'] M₂') : Module.End R₁' M₁' ≃ₛₗ[σ₁'₂'] Module.End R₂' M₂' :=
  arrowCongr e e

theorem conj_apply (e : M₁' ≃ₛₗ[σ₁'₂'] M₂') (f : Module.End R₁' M₁') :
    e.conj f = ((↑e : M₁' →ₛₗ[σ₁'₂'] M₂').comp f).comp (e.symm : M₂' →ₛₗ[σ₂'₁'] M₁') :=
  rfl

theorem conj_apply_apply (e : M₁' ≃ₛₗ[σ₁'₂'] M₂') (f : Module.End R₁' M₁') (x : M₂') :
    e.conj f x = e (f (e.symm x)) :=
  rfl

theorem symm_conj_apply (e : M₁' ≃ₛₗ[σ₁'₂'] M₂') (f : Module.End R₂' M₂') :
    e.symm.conj f = ((↑e.symm : M₂' →ₛₗ[σ₂'₁'] M₁').comp f).comp (e : M₁' →ₛₗ[σ₁'₂'] M₂') :=
  rfl

theorem conj_comp (e : M₁' ≃ₛₗ[σ₁'₂'] M₂') (f g : Module.End R₁' M₁') :
    e.conj (g.comp f) = (e.conj g).comp (e.conj f) :=
  arrowCongr_comp e e e f g

theorem conj_trans (e₁ : M₁' ≃ₛₗ[σ₁'₂'] M₂') (e₂ : M₂' ≃ₛₗ[σ₂'₃'] M₃') :
    e₁.conj.trans e₂.conj = (e₁.trans e₂).conj :=
  rfl

@[simp] lemma conj_conj_symm (e : M₁' ≃ₛₗ[σ₁'₂'] M₂') (f : Module.End R₂' M₂') :
    e.conj (e.symm.conj f) = f := by ext; simp [conj_apply]

@[simp] lemma conj_symm_conj (e : M₁' ≃ₛₗ[σ₁'₂'] M₂') (f : Module.End R₁' M₁') :
    e.symm.conj (e.conj f) = f := by ext; simp [conj_apply]

@[simp]
theorem conj_id (e : M₁' ≃ₛₗ[σ₁'₂'] M₂') : e.conj LinearMap.id = LinearMap.id := by
  ext
  simp [conj_apply]

@[simp]
theorem conj_refl (f : Module.End R M) : (refl R M).conj f = f := rfl

end arrowCongr

/-- If `M₂` and `M₃` are linearly isomorphic then the two spaces of linear maps from `M` into `M₂`
and `M` into `M₃` are linearly isomorphic. -/
def congrRight (f : M₂ ≃ₗ[R] M₃) : (M →ₗ[R] M₂) ≃ₗ[R] M →ₗ[R] M₃ :=
  arrowCongr (LinearEquiv.refl R M) f

variable (M) in
/-- An `R`-linear isomorphism between two `R`-modules `M₂` and `M₃` induces an `S`-linear
isomorphism between `M₂ →ₗ[R] M` and `M₃ →ₗ[R] M`, if `M` is both an `R`-module and an
`S`-module and their actions commute. -/
def congrLeft {R} (S) [Semiring R] [Semiring S] [Module R M₂] [Module R M₃] [Module R M]
    [Module S M] [SMulCommClass R S M] (e : M₂ ≃ₗ[R] M₃) : (M₂ →ₗ[R] M) ≃ₗ[S] (M₃ →ₗ[R] M) where
  __ := e.arrowCongrAddEquiv (.refl ..)
  map_smul' _ _ := rfl

end CommSemiring

section Field

variable [Field K] [AddCommGroup M] [Module K M]
variable (K) (M)

open LinearMap

/-- Multiplying by a nonzero element `a` of the field `K` is a linear equivalence. -/
@[simps!]
def smulOfNeZero (a : K) (ha : a ≠ 0) : M ≃ₗ[K] M :=
  smulOfUnit <| Units.mk0 a ha

end Field

end LinearEquiv

namespace Equiv

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M₂] [Module R M₂]

/-- An equivalence whose underlying function is linear is a linear equivalence. -/
def toLinearEquiv (e : M ≃ M₂) (h : IsLinearMap R (e : M → M₂)) : M ≃ₗ[R] M₂ :=
  { e, h.mk' e with }

end Equiv

section FunLeft

variable (R M) [Semiring R] [AddCommMonoid M] [Module R M]
variable {m n p : Type*}

namespace LinearMap

/-- Given an `R`-module `M` and a function `m → n` between arbitrary types,
construct a linear map `(n → M) →ₗ[R] (m → M)` -/
def funLeft (f : m → n) : (n → M) →ₗ[R] m → M where
  toFun := (· ∘ f)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem funLeft_apply (f : m → n) (g : n → M) (i : m) : funLeft R M f g i = g (f i) :=
  rfl

@[simp]
theorem funLeft_id (g : n → M) : funLeft R M _root_.id g = g :=
  rfl

theorem funLeft_comp (f₁ : n → p) (f₂ : m → n) :
    funLeft R M (f₁ ∘ f₂) = (funLeft R M f₂).comp (funLeft R M f₁) :=
  rfl

theorem funLeft_surjective_of_injective (f : m → n) (hf : Injective f) :
    Surjective (funLeft R M f) :=
  hf.surjective_comp_right

theorem funLeft_injective_of_surjective (f : m → n) (hf : Surjective f) :
    Injective (funLeft R M f) :=
  hf.injective_comp_right

end LinearMap

namespace LinearEquiv

open LinearMap

/-- Given an `R`-module `M` and an equivalence `m ≃ n` between arbitrary types,
construct a linear equivalence `(n → M) ≃ₗ[R] (m → M)` -/
def funCongrLeft (e : m ≃ n) : (n → M) ≃ₗ[R] m → M :=
  LinearEquiv.ofLinear (funLeft R M e) (funLeft R M e.symm)
    (LinearMap.ext fun x ↦
      funext fun i ↦ by rw [id_apply, ← funLeft_comp, Equiv.symm_comp_self, LinearMap.funLeft_id])
    (LinearMap.ext fun x ↦
      funext fun i ↦ by rw [id_apply, ← funLeft_comp, Equiv.self_comp_symm, LinearMap.funLeft_id])

@[simp]
theorem funCongrLeft_apply (e : m ≃ n) (x : n → M) : funCongrLeft R M e x = funLeft R M e x :=
  rfl

@[simp]
theorem funCongrLeft_id : funCongrLeft R M (Equiv.refl n) = LinearEquiv.refl R (n → M) :=
  rfl

@[simp]
theorem funCongrLeft_comp (e₁ : m ≃ n) (e₂ : n ≃ p) :
    funCongrLeft R M (Equiv.trans e₁ e₂) =
      LinearEquiv.trans (funCongrLeft R M e₂) (funCongrLeft R M e₁) :=
  rfl

@[simp]
theorem funCongrLeft_symm (e : m ≃ n) : (funCongrLeft R M e).symm = funCongrLeft R M e.symm :=
  rfl

end LinearEquiv

end FunLeft

section Pi

namespace LinearEquiv

/-- The product over `S ⊕ T` of a family of modules is isomorphic to the product of
(the product over `S`) and (the product over `T`).

This is `Equiv.sumPiEquivProdPi` as a `LinearEquiv`.
-/
@[simps -fullyApplied +simpRhs]
def sumPiEquivProdPi (R : Type*) [Semiring R] (S T : Type*) (A : S ⊕ T → Type*)
    [∀ st, AddCommMonoid (A st)] [∀ st, Module R (A st)] :
    (Π (st : S ⊕ T), A st) ≃ₗ[R] (Π (s : S), A (.inl s)) × (Π (t : T), A (.inr t)) where
  __ := Equiv.sumPiEquivProdPi _
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The product `Π t : α, f t` of a family of modules is linearly isomorphic to the module
`f ⬝` when `α` only contains `⬝`.

This is `Equiv.piUnique` as a `LinearEquiv`.
-/
@[simps -fullyApplied]
def piUnique {α : Type*} [Unique α] (R : Type*) [Semiring R] (f : α → Type*)
    [∀ x, AddCommMonoid (f x)] [∀ x, Module R (f x)] : (Π t : α, f t) ≃ₗ[R] f default where
  __ := Equiv.piUnique _
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end LinearEquiv

end Pi

end AddCommMonoid
