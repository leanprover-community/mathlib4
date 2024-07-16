/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro, Anne Baanen,
  Frédéric Dupuis, Heather Macbeth
-/
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Module.Hom
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.Pi
import Mathlib.GroupTheory.GroupAction.Group

#align_import algebra.module.equiv from "leanprover-community/mathlib"@"ea94d7cd54ad9ca6b7710032868abb7c6a104c9c"

/-!
# Further results on (semi)linear equivalences.
-/

open Function

universe u u' v w x y z

variable {R : Type*} {R₁ : Type*} {R₂ : Type*} {R₃ : Type*}
variable {k : Type*} {K : Type*} {S : Type*} {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}
variable {N₁ : Type*} {N₂ : Type*} {N₃ : Type*} {N₄ : Type*} {ι : Type*}

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
#align linear_equiv.restrict_scalars LinearEquiv.restrictScalars
#align linear_equiv.restrict_scalars_apply LinearEquiv.restrictScalars_apply
#align linear_equiv.restrict_scalars_symm_apply LinearEquiv.restrictScalars_symm_apply

theorem restrictScalars_injective :
    Function.Injective (restrictScalars R : (M ≃ₗ[S] M₂) → M ≃ₗ[R] M₂) := fun _ _ h =>
  ext (LinearEquiv.congr_fun h : _)
#align linear_equiv.restrict_scalars_injective LinearEquiv.restrictScalars_injective

@[simp]
theorem restrictScalars_inj (f g : M ≃ₗ[S] M₂) :
    f.restrictScalars R = g.restrictScalars R ↔ f = g :=
  (restrictScalars_injective R).eq_iff
#align linear_equiv.restrict_scalars_inj LinearEquiv.restrictScalars_inj

end RestrictScalars

theorem _root_.Module.End_isUnit_iff [Module R M] (f : Module.End R M) :
    IsUnit f ↔ Function.Bijective f :=
  ⟨fun h =>
    Function.bijective_iff_has_inverse.mpr <|
      ⟨h.unit.inv,
        ⟨Module.End_isUnit_inv_apply_apply_of_isUnit h,
        Module.End_isUnit_apply_inv_apply_of_isUnit h⟩⟩,
    fun H =>
    let e : M ≃ₗ[R] M := { f, Equiv.ofBijective f H with }
    ⟨⟨_, e.symm, LinearMap.ext e.right_inv, LinearMap.ext e.left_inv⟩, rfl⟩⟩
#align module.End_is_unit_iff Module.End_isUnit_iff

section Automorphisms

variable [Module R M]

instance automorphismGroup : Group (M ≃ₗ[R] M) where
  mul f g := g.trans f
  one := LinearEquiv.refl R M
  inv f := f.symm
  mul_assoc f g h := rfl
  mul_one f := ext fun x => rfl
  one_mul f := ext fun x => rfl
  mul_left_inv f := ext <| f.left_inv
#align linear_equiv.automorphism_group LinearEquiv.automorphismGroup

@[simp]
lemma coe_one : ↑(1 : M ≃ₗ[R] M) = id := rfl

@[simp]
lemma coe_toLinearMap_one : (↑(1 : M ≃ₗ[R] M) : M →ₗ[R] M) = LinearMap.id := rfl

@[simp]
lemma coe_toLinearMap_mul {e₁ e₂ : M ≃ₗ[R] M} :
    (↑(e₁ * e₂) : M →ₗ[R] M) = (e₁ : M →ₗ[R] M) * (e₂ : M →ₗ[R] M) := by
  rfl

theorem coe_pow (e : M ≃ₗ[R] M) (n : ℕ) : ⇑(e ^ n) = e^[n] := hom_coe_pow _ rfl (fun _ _ ↦ rfl) _ _

theorem pow_apply (e : M ≃ₗ[R] M) (n : ℕ) (m : M) : (e ^ n) m = e^[n] m := congr_fun (coe_pow e n) m

/-- Restriction from `R`-linear automorphisms of `M` to `R`-linear endomorphisms of `M`,
promoted to a monoid hom. -/
@[simps]
def automorphismGroup.toLinearMapMonoidHom : (M ≃ₗ[R] M) →* M →ₗ[R] M where
  toFun e := e.toLinearMap
  map_one' := rfl
  map_mul' _ _ := rfl
#align linear_equiv.automorphism_group.to_linear_map_monoid_hom LinearEquiv.automorphismGroup.toLinearMapMonoidHom
#align linear_equiv.automorphism_group.to_linear_map_monoid_hom_apply LinearEquiv.automorphismGroup.toLinearMapMonoidHom_apply

/-- The tautological action by `M ≃ₗ[R] M` on `M`.

This generalizes `Function.End.applyMulAction`. -/
instance applyDistribMulAction : DistribMulAction (M ≃ₗ[R] M) M where
  smul := (· <| ·)
  smul_zero := LinearEquiv.map_zero
  smul_add := LinearEquiv.map_add
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
#align linear_equiv.apply_distrib_mul_action LinearEquiv.applyDistribMulAction

@[simp]
protected theorem smul_def (f : M ≃ₗ[R] M) (a : M) : f • a = f a :=
  rfl
#align linear_equiv.smul_def LinearEquiv.smul_def

/-- `LinearEquiv.applyDistribMulAction` is faithful. -/
instance apply_faithfulSMul : FaithfulSMul (M ≃ₗ[R] M) M :=
  ⟨@fun _ _ => LinearEquiv.ext⟩
#align linear_equiv.apply_has_faithful_smul LinearEquiv.apply_faithfulSMul

instance apply_smulCommClass : SMulCommClass R (M ≃ₗ[R] M) M where
  smul_comm r e m := (e.map_smul r m).symm
#align linear_equiv.apply_smul_comm_class LinearEquiv.apply_smulCommClass

instance apply_smulCommClass' : SMulCommClass (M ≃ₗ[R] M) R M where
  smul_comm := LinearEquiv.map_smul
#align linear_equiv.apply_smul_comm_class' LinearEquiv.apply_smulCommClass'

end Automorphisms

section OfSubsingleton

variable (M M₂)
variable [Module R M] [Module R M₂] [Subsingleton M] [Subsingleton M₂]

/-- Any two modules that are subsingletons are isomorphic. -/
@[simps]
def ofSubsingleton : M ≃ₗ[R] M₂ :=
  { (0 : M →ₗ[R] M₂) with
    toFun := fun _ => 0
    invFun := fun _ => 0
    left_inv := fun _ => Subsingleton.elim _ _
    right_inv := fun _ => Subsingleton.elim _ _ }
#align linear_equiv.of_subsingleton LinearEquiv.ofSubsingleton
#align linear_equiv.of_subsingleton_symm_apply LinearEquiv.ofSubsingleton_symm_apply

@[simp]
theorem ofSubsingleton_self : ofSubsingleton M M = refl R M := by
  ext
  simp [eq_iff_true_of_subsingleton]
#align linear_equiv.of_subsingleton_self LinearEquiv.ofSubsingleton_self

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
#align module.comp_hom.to_linear_equiv Module.compHom.toLinearEquiv
#align module.comp_hom.to_linear_equiv_symm_apply Module.compHom.toLinearEquiv_symm_apply

end Module

namespace DistribMulAction

variable (R M) [Semiring R] [AddCommMonoid M] [Module R M]
variable [Group S] [DistribMulAction S M] [SMulCommClass S R M]

/-- Each element of the group defines a linear equivalence.

This is a stronger version of `DistribMulAction.toAddEquiv`. -/
@[simps!]
def toLinearEquiv (s : S) : M ≃ₗ[R] M :=
  { toAddEquiv M s, toLinearMap R M s with }
#align distrib_mul_action.to_linear_equiv DistribMulAction.toLinearEquiv
#align distrib_mul_action.to_linear_equiv_apply DistribMulAction.toLinearEquiv_apply
#align distrib_mul_action.to_linear_equiv_symm_apply DistribMulAction.toLinearEquiv_symm_apply

/-- Each element of the group defines a module automorphism.

This is a stronger version of `DistribMulAction.toAddAut`. -/
@[simps]
def toModuleAut : S →* M ≃ₗ[R] M where
  toFun := toLinearEquiv R M
  map_one' := LinearEquiv.ext <| one_smul _
  map_mul' _ _ := LinearEquiv.ext <| mul_smul _ _
#align distrib_mul_action.to_module_aut DistribMulAction.toModuleAut
#align distrib_mul_action.to_module_aut_apply DistribMulAction.toModuleAut_apply

end DistribMulAction

namespace AddEquiv

section AddCommMonoid

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Module R M] [Module R M₂]
variable (e : M ≃+ M₂)

/-- An additive equivalence whose underlying function preserves `smul` is a linear equivalence. -/
def toLinearEquiv (h : ∀ (c : R) (x), e (c • x) = c • e x) : M ≃ₗ[R] M₂ :=
  { e with map_smul' := h }
#align add_equiv.to_linear_equiv AddEquiv.toLinearEquiv

@[simp]
theorem coe_toLinearEquiv (h : ∀ (c : R) (x), e (c • x) = c • e x) : ⇑(e.toLinearEquiv h) = e :=
  rfl
#align add_equiv.coe_to_linear_equiv AddEquiv.coe_toLinearEquiv

@[simp]
theorem coe_toLinearEquiv_symm (h : ∀ (c : R) (x), e (c • x) = c • e x) :
    ⇑(e.toLinearEquiv h).symm = e.symm :=
  rfl
#align add_equiv.coe_to_linear_equiv_symm AddEquiv.coe_toLinearEquiv_symm

/-- An additive equivalence between commutative additive monoids is a linear equivalence between
ℕ-modules -/
def toNatLinearEquiv : M ≃ₗ[ℕ] M₂ :=
  e.toLinearEquiv fun c a => by rw [map_nsmul]
#align add_equiv.to_nat_linear_equiv AddEquiv.toNatLinearEquiv

@[simp]
theorem coe_toNatLinearEquiv : ⇑e.toNatLinearEquiv = e :=
  rfl
#align add_equiv.coe_to_nat_linear_equiv AddEquiv.coe_toNatLinearEquiv

@[simp]
theorem toNatLinearEquiv_toAddEquiv : ↑e.toNatLinearEquiv = e := by
  ext
  rfl
#align add_equiv.to_nat_linear_equiv_to_add_equiv AddEquiv.toNatLinearEquiv_toAddEquiv

@[simp]
theorem _root_.LinearEquiv.toAddEquiv_toNatLinearEquiv (e : M ≃ₗ[ℕ] M₂) :
    AddEquiv.toNatLinearEquiv ↑e = e :=
  DFunLike.coe_injective rfl
#align linear_equiv.to_add_equiv_to_nat_linear_equiv LinearEquiv.toAddEquiv_toNatLinearEquiv

@[simp]
theorem toNatLinearEquiv_symm : e.toNatLinearEquiv.symm = e.symm.toNatLinearEquiv :=
  rfl
#align add_equiv.to_nat_linear_equiv_symm AddEquiv.toNatLinearEquiv_symm

@[simp]
theorem toNatLinearEquiv_refl : (AddEquiv.refl M).toNatLinearEquiv = LinearEquiv.refl ℕ M :=
  rfl
#align add_equiv.to_nat_linear_equiv_refl AddEquiv.toNatLinearEquiv_refl

@[simp]
theorem toNatLinearEquiv_trans (e₂ : M₂ ≃+ M₃) :
    e.toNatLinearEquiv.trans e₂.toNatLinearEquiv = (e.trans e₂).toNatLinearEquiv :=
  rfl
#align add_equiv.to_nat_linear_equiv_trans AddEquiv.toNatLinearEquiv_trans

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup M] [AddCommGroup M₂] [AddCommGroup M₃]
variable (e : M ≃+ M₂)

/-- An additive equivalence between commutative additive groups is a linear
equivalence between ℤ-modules -/
def toIntLinearEquiv : M ≃ₗ[ℤ] M₂ :=
  e.toLinearEquiv fun c a => e.toAddMonoidHom.map_zsmul a c
#align add_equiv.to_int_linear_equiv AddEquiv.toIntLinearEquiv

@[simp]
theorem coe_toIntLinearEquiv : ⇑e.toIntLinearEquiv = e :=
  rfl
#align add_equiv.coe_to_int_linear_equiv AddEquiv.coe_toIntLinearEquiv

@[simp]
theorem toIntLinearEquiv_toAddEquiv : ↑e.toIntLinearEquiv = e := by
  ext
  rfl
#align add_equiv.to_int_linear_equiv_to_add_equiv AddEquiv.toIntLinearEquiv_toAddEquiv

@[simp]
theorem _root_.LinearEquiv.toAddEquiv_toIntLinearEquiv (e : M ≃ₗ[ℤ] M₂) :
    AddEquiv.toIntLinearEquiv (e : M ≃+ M₂) = e :=
  DFunLike.coe_injective rfl
#align linear_equiv.to_add_equiv_to_int_linear_equiv LinearEquiv.toAddEquiv_toIntLinearEquiv

@[simp]
theorem toIntLinearEquiv_symm : e.toIntLinearEquiv.symm = e.symm.toIntLinearEquiv :=
  rfl
#align add_equiv.to_int_linear_equiv_symm AddEquiv.toIntLinearEquiv_symm

@[simp]
theorem toIntLinearEquiv_refl : (AddEquiv.refl M).toIntLinearEquiv = LinearEquiv.refl ℤ M :=
  rfl
#align add_equiv.to_int_linear_equiv_refl AddEquiv.toIntLinearEquiv_refl

@[simp]
theorem toIntLinearEquiv_trans (e₂ : M₂ ≃+ M₃) :
    e.toIntLinearEquiv.trans e₂.toIntLinearEquiv = (e.trans e₂).toIntLinearEquiv :=
  rfl
#align add_equiv.to_int_linear_equiv_trans AddEquiv.toIntLinearEquiv_trans

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
    toFun := fun f => f 1
    invFun := smulRight (1 : R →ₗ[R] R)
    left_inv := fun f => by
      ext
      simp only [coe_smulRight, one_apply, smul_eq_mul, ← map_smul f, mul_one]
    right_inv := fun x => by simp }
#align linear_map.ring_lmap_equiv_self LinearMap.ringLmapEquivSelf

end LinearMap

/--
The `R`-linear equivalence between additive morphisms `A →+ B` and `ℕ`-linear morphisms `A →ₗ[ℕ] B`.
-/
@[simps]
def addMonoidHomLequivNat {A B : Type*} (R : Type*) [Semiring R] [AddCommMonoid A]
    [AddCommMonoid B] [Module R B] : (A →+ B) ≃ₗ[R] A →ₗ[ℕ] B
    where
  toFun := AddMonoidHom.toNatLinearMap
  invFun := LinearMap.toAddMonoidHom
  map_add' := by intros; ext; rfl
  map_smul' := by intros; ext; rfl
  left_inv := by intro f; ext; rfl
  right_inv := by intro f; ext; rfl
#align add_monoid_hom_lequiv_nat addMonoidHomLequivNat

/--
The `R`-linear equivalence between additive morphisms `A →+ B` and `ℤ`-linear morphisms `A →ₗ[ℤ] B`.
-/
@[simps]
def addMonoidHomLequivInt {A B : Type*} (R : Type*) [Semiring R] [AddCommGroup A] [AddCommGroup B]
    [Module R B] : (A →+ B) ≃ₗ[R] A →ₗ[ℤ] B
    where
  toFun := AddMonoidHom.toIntLinearMap
  invFun := LinearMap.toAddMonoidHom
  map_add' := by intros; ext; rfl
  map_smul' := by intros; ext; rfl
  left_inv := by intro f; ext; rfl
  right_inv := by intro f; ext; rfl
#align add_monoid_hom_lequiv_int addMonoidHomLequivInt

/-- Ring equivalence between additive group endomorphisms of an `AddCommGroup` `A` and
`ℤ`-module endomorphisms of `A.` -/
@[simps] def addMonoidEndRingEquivInt (A : Type*) [AddCommGroup A] :
    AddMonoid.End A ≃+* Module.End ℤ A :=
  { addMonoidHomLequivInt (B := A) ℤ with
    map_mul' := fun _ _ => rfl }

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
#align linear_equiv.zero_symm LinearEquiv.zero_symm

@[simp]
theorem coe_zero : ⇑(0 : M ≃ₛₗ[σ₁₂] M₂) = 0 :=
  rfl
#align linear_equiv.coe_zero LinearEquiv.coe_zero

theorem zero_apply (x : M) : (0 : M ≃ₛₗ[σ₁₂] M₂) x = 0 :=
  rfl
#align linear_equiv.zero_apply LinearEquiv.zero_apply

/-- Between two zero modules, the zero map is the only equivalence. -/
instance : Unique (M ≃ₛₗ[σ₁₂] M₂) where
  uniq _ := toLinearMap_injective (Subsingleton.elim _ _)
  default := 0


end Module

instance uniqueOfSubsingleton [Subsingleton R] [Subsingleton R₂] : Unique (M ≃ₛₗ[σ₁₂] M₂) := by
  haveI := Module.subsingleton R M
  haveI := Module.subsingleton R₂ M₂
  infer_instance
#align linear_equiv.unique_of_subsingleton LinearEquiv.uniqueOfSubsingleton

end Subsingleton

section Uncurry

variable [Semiring R] [Semiring R₂] [Semiring R₃]
variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable (V V₂ R)

/-- Linear equivalence between a curried and uncurried function.
  Differs from `TensorProduct.curry`. -/
protected def curry : (V × V₂ → R) ≃ₗ[R] V → V₂ → R :=
  { Equiv.curry _ _ _ with
    map_add' := fun _ _ => by
      ext
      rfl
    map_smul' := fun _ _ => by
      ext
      rfl }
#align linear_equiv.curry LinearEquiv.curry

@[simp]
theorem coe_curry : ⇑(LinearEquiv.curry R V V₂) = curry :=
  rfl
#align linear_equiv.coe_curry LinearEquiv.coe_curry

@[simp]
theorem coe_curry_symm : ⇑(LinearEquiv.curry R V V₂).symm = uncurry :=
  rfl
#align linear_equiv.coe_curry_symm LinearEquiv.coe_curry_symm

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
#align linear_equiv.of_linear LinearEquiv.ofLinear

@[simp]
theorem ofLinear_apply {h₁ h₂} (x : M) : (ofLinear f g h₁ h₂ : M ≃ₛₗ[σ₁₂] M₂) x = f x :=
  rfl
#align linear_equiv.of_linear_apply LinearEquiv.ofLinear_apply

@[simp]
theorem ofLinear_symm_apply {h₁ h₂} (x : M₂) : (ofLinear f g h₁ h₂ : M ≃ₛₗ[σ₁₂] M₂).symm x = g x :=
  rfl
#align linear_equiv.of_linear_symm_apply LinearEquiv.ofLinear_symm_apply

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
#align linear_equiv.neg LinearEquiv.neg

variable {R}

@[simp]
theorem coe_neg : ⇑(neg R : M ≃ₗ[R] M) = -id :=
  rfl
#align linear_equiv.coe_neg LinearEquiv.coe_neg

theorem neg_apply (x : M) : neg R x = -x := by simp
#align linear_equiv.neg_apply LinearEquiv.neg_apply

@[simp]
theorem symm_neg : (neg R : M ≃ₗ[R] M).symm = neg R :=
  rfl
#align linear_equiv.symm_neg LinearEquiv.symm_neg

end Neg

section CommSemiring

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Module R M] [Module R M₂] [Module R M₃]

open LinearMap

/-- Multiplying by a unit `a` of the ring `R` is a linear equivalence. -/
def smulOfUnit (a : Rˣ) : M ≃ₗ[R] M :=
  DistribMulAction.toLinearEquiv R M a
#align linear_equiv.smul_of_unit LinearEquiv.smulOfUnit

/-- A linear isomorphism between the domains and codomains of two spaces of linear maps gives a
linear isomorphism between the two function spaces. -/
def arrowCongr {R M₁ M₂ M₂₁ M₂₂ : Sort _} [CommSemiring R] [AddCommMonoid M₁] [AddCommMonoid M₂]
    [AddCommMonoid M₂₁] [AddCommMonoid M₂₂] [Module R M₁] [Module R M₂] [Module R M₂₁]
    [Module R M₂₂] (e₁ : M₁ ≃ₗ[R] M₂) (e₂ : M₂₁ ≃ₗ[R] M₂₂) : (M₁ →ₗ[R] M₂₁) ≃ₗ[R] M₂ →ₗ[R] M₂₂ where
  toFun := fun f : M₁ →ₗ[R] M₂₁ => (e₂ : M₂₁ →ₗ[R] M₂₂).comp <| f.comp (e₁.symm : M₂ →ₗ[R] M₁)
  invFun f := (e₂.symm : M₂₂ →ₗ[R] M₂₁).comp <| f.comp (e₁ : M₁ →ₗ[R] M₂)
  left_inv f := by
    ext x
    simp only [symm_apply_apply, Function.comp_apply, coe_comp, coe_coe]
  right_inv f := by
    ext x
    simp only [Function.comp_apply, apply_symm_apply, coe_comp, coe_coe]
  map_add' f g := by
    ext x
    simp only [map_add, add_apply, Function.comp_apply, coe_comp, coe_coe]
  map_smul' c f := by
    ext x
    simp only [smul_apply, Function.comp_apply, coe_comp, map_smulₛₗ e₂, coe_coe]
#align linear_equiv.arrow_congr LinearEquiv.arrowCongr

@[simp]
theorem arrowCongr_apply {R M₁ M₂ M₂₁ M₂₂ : Sort _} [CommSemiring R] [AddCommMonoid M₁]
    [AddCommMonoid M₂] [AddCommMonoid M₂₁] [AddCommMonoid M₂₂] [Module R M₁] [Module R M₂]
    [Module R M₂₁] [Module R M₂₂] (e₁ : M₁ ≃ₗ[R] M₂) (e₂ : M₂₁ ≃ₗ[R] M₂₂) (f : M₁ →ₗ[R] M₂₁)
    (x : M₂) : arrowCongr e₁ e₂ f x = e₂ (f (e₁.symm x)) :=
  rfl
#align linear_equiv.arrow_congr_apply LinearEquiv.arrowCongr_apply

@[simp]
theorem arrowCongr_symm_apply {R M₁ M₂ M₂₁ M₂₂ : Sort _} [CommSemiring R] [AddCommMonoid M₁]
    [AddCommMonoid M₂] [AddCommMonoid M₂₁] [AddCommMonoid M₂₂] [Module R M₁] [Module R M₂]
    [Module R M₂₁] [Module R M₂₂] (e₁ : M₁ ≃ₗ[R] M₂) (e₂ : M₂₁ ≃ₗ[R] M₂₂) (f : M₂ →ₗ[R] M₂₂)
    (x : M₁) : (arrowCongr e₁ e₂).symm f x = e₂.symm (f (e₁ x)) :=
  rfl
#align linear_equiv.arrow_congr_symm_apply LinearEquiv.arrowCongr_symm_apply

theorem arrowCongr_comp {N N₂ N₃ : Sort _} [AddCommMonoid N] [AddCommMonoid N₂] [AddCommMonoid N₃]
    [Module R N] [Module R N₂] [Module R N₃] (e₁ : M ≃ₗ[R] N) (e₂ : M₂ ≃ₗ[R] N₂) (e₃ : M₃ ≃ₗ[R] N₃)
    (f : M →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) :
    arrowCongr e₁ e₃ (g.comp f) = (arrowCongr e₂ e₃ g).comp (arrowCongr e₁ e₂ f) := by
  ext
  simp only [symm_apply_apply, arrowCongr_apply, LinearMap.comp_apply]
#align linear_equiv.arrow_congr_comp LinearEquiv.arrowCongr_comp

theorem arrowCongr_trans {M₁ M₂ M₃ N₁ N₂ N₃ : Sort _} [AddCommMonoid M₁] [Module R M₁]
    [AddCommMonoid M₂] [Module R M₂] [AddCommMonoid M₃] [Module R M₃] [AddCommMonoid N₁]
    [Module R N₁] [AddCommMonoid N₂] [Module R N₂] [AddCommMonoid N₃] [Module R N₃]
    (e₁ : M₁ ≃ₗ[R] M₂) (e₂ : N₁ ≃ₗ[R] N₂) (e₃ : M₂ ≃ₗ[R] M₃) (e₄ : N₂ ≃ₗ[R] N₃) :
    (arrowCongr e₁ e₂).trans (arrowCongr e₃ e₄) = arrowCongr (e₁.trans e₃) (e₂.trans e₄) :=
  rfl
#align linear_equiv.arrow_congr_trans LinearEquiv.arrowCongr_trans

/-- If `M₂` and `M₃` are linearly isomorphic then the two spaces of linear maps from `M` into `M₂`
and `M` into `M₃` are linearly isomorphic. -/
def congrRight (f : M₂ ≃ₗ[R] M₃) : (M →ₗ[R] M₂) ≃ₗ[R] M →ₗ[R] M₃ :=
  arrowCongr (LinearEquiv.refl R M) f
#align linear_equiv.congr_right LinearEquiv.congrRight

/-- If `M` and `M₂` are linearly isomorphic then the two spaces of linear maps from `M` and `M₂` to
themselves are linearly isomorphic. -/
def conj (e : M ≃ₗ[R] M₂) : Module.End R M ≃ₗ[R] Module.End R M₂ :=
  arrowCongr e e
#align linear_equiv.conj LinearEquiv.conj

theorem conj_apply (e : M ≃ₗ[R] M₂) (f : Module.End R M) :
    e.conj f = ((↑e : M →ₗ[R] M₂).comp f).comp (e.symm : M₂ →ₗ[R] M) :=
  rfl
#align linear_equiv.conj_apply LinearEquiv.conj_apply

theorem conj_apply_apply (e : M ≃ₗ[R] M₂) (f : Module.End R M) (x : M₂) :
    e.conj f x = e (f (e.symm x)) :=
  rfl
#align linear_equiv.conj_apply_apply LinearEquiv.conj_apply_apply

theorem symm_conj_apply (e : M ≃ₗ[R] M₂) (f : Module.End R M₂) :
    e.symm.conj f = ((↑e.symm : M₂ →ₗ[R] M).comp f).comp (e : M →ₗ[R] M₂) :=
  rfl
#align linear_equiv.symm_conj_apply LinearEquiv.symm_conj_apply

theorem conj_comp (e : M ≃ₗ[R] M₂) (f g : Module.End R M) :
    e.conj (g.comp f) = (e.conj g).comp (e.conj f) :=
  arrowCongr_comp e e e f g
#align linear_equiv.conj_comp LinearEquiv.conj_comp

theorem conj_trans (e₁ : M ≃ₗ[R] M₂) (e₂ : M₂ ≃ₗ[R] M₃) :
    e₁.conj.trans e₂.conj = (e₁.trans e₂).conj := by
  ext f x
  rfl
#align linear_equiv.conj_trans LinearEquiv.conj_trans

@[simp]
theorem conj_id (e : M ≃ₗ[R] M₂) : e.conj LinearMap.id = LinearMap.id := by
  ext
  simp [conj_apply]
#align linear_equiv.conj_id LinearEquiv.conj_id

variable (M) in
/-- An `R`-linear isomorphism between two `R`-modules `M₂` and `M₃` induces an `S`-linear
isomorphism between `M₂ →ₗ[R] M` and `M₃ →ₗ[R] M`, if `M` is both an `R`-module and an
`S`-module and their actions commute. -/
def congrLeft {R} (S) [Semiring R] [Semiring S] [Module R M₂] [Module R M₃] [Module R M]
    [Module S M] [SMulCommClass R S M] (e : M₂ ≃ₗ[R] M₃) : (M₂ →ₗ[R] M) ≃ₗ[S] (M₃ →ₗ[R] M) where
  toFun f := f.comp e.symm.toLinearMap
  invFun f := f.comp e.toLinearMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv f := by dsimp only; apply DFunLike.ext; exact (congr_arg f <| e.left_inv ·)
  right_inv f := by dsimp only; apply DFunLike.ext; exact (congr_arg f <| e.right_inv ·)

end CommSemiring

section Field

variable [Field K] [AddCommGroup M] [AddCommGroup M₂] [AddCommGroup M₃]
variable [Module K M] [Module K M₂] [Module K M₃]
variable (K) (M)

open LinearMap

/-- Multiplying by a nonzero element `a` of the field `K` is a linear equivalence. -/
@[simps!]
def smulOfNeZero (a : K) (ha : a ≠ 0) : M ≃ₗ[K] M :=
  smulOfUnit <| Units.mk0 a ha
#align linear_equiv.smul_of_ne_zero LinearEquiv.smulOfNeZero

end Field

end LinearEquiv

namespace Equiv

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M₂] [Module R M₂]

/-- An equivalence whose underlying function is linear is a linear equivalence. -/
def toLinearEquiv (e : M ≃ M₂) (h : IsLinearMap R (e : M → M₂)) : M ≃ₗ[R] M₂ :=
  { e, h.mk' e with }
#align equiv.to_linear_equiv Equiv.toLinearEquiv

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
#align linear_map.fun_left LinearMap.funLeft

@[simp]
theorem funLeft_apply (f : m → n) (g : n → M) (i : m) : funLeft R M f g i = g (f i) :=
  rfl
#align linear_map.fun_left_apply LinearMap.funLeft_apply

@[simp]
theorem funLeft_id (g : n → M) : funLeft R M _root_.id g = g :=
  rfl
#align linear_map.fun_left_id LinearMap.funLeft_id

theorem funLeft_comp (f₁ : n → p) (f₂ : m → n) :
    funLeft R M (f₁ ∘ f₂) = (funLeft R M f₂).comp (funLeft R M f₁) :=
  rfl
#align linear_map.fun_left_comp LinearMap.funLeft_comp

theorem funLeft_surjective_of_injective (f : m → n) (hf : Injective f) :
    Surjective (funLeft R M f) := by
  classical
    intro g
    refine ⟨fun x => if h : ∃ y, f y = x then g h.choose else 0, ?_⟩
    ext
    dsimp only [funLeft_apply]
    split_ifs with w
    · congr
      exact hf w.choose_spec
    · simp only [not_true, exists_apply_eq_apply] at w
#align linear_map.fun_left_surjective_of_injective LinearMap.funLeft_surjective_of_injective

theorem funLeft_injective_of_surjective (f : m → n) (hf : Surjective f) :
    Injective (funLeft R M f) := by
  obtain ⟨g, hg⟩ := hf.hasRightInverse
  suffices LeftInverse (funLeft R M g) (funLeft R M f) by exact this.injective
  intro x
  rw [← LinearMap.comp_apply, ← funLeft_comp, hg.id, funLeft_id]
#align linear_map.fun_left_injective_of_surjective LinearMap.funLeft_injective_of_surjective

end LinearMap

namespace LinearEquiv

open LinearMap

/-- Given an `R`-module `M` and an equivalence `m ≃ n` between arbitrary types,
construct a linear equivalence `(n → M) ≃ₗ[R] (m → M)` -/
def funCongrLeft (e : m ≃ n) : (n → M) ≃ₗ[R] m → M :=
  LinearEquiv.ofLinear (funLeft R M e) (funLeft R M e.symm)
    (LinearMap.ext fun x =>
      funext fun i => by rw [id_apply, ← funLeft_comp, Equiv.symm_comp_self, LinearMap.funLeft_id])
    (LinearMap.ext fun x =>
      funext fun i => by rw [id_apply, ← funLeft_comp, Equiv.self_comp_symm, LinearMap.funLeft_id])
#align linear_equiv.fun_congr_left LinearEquiv.funCongrLeft

@[simp]
theorem funCongrLeft_apply (e : m ≃ n) (x : n → M) : funCongrLeft R M e x = funLeft R M e x :=
  rfl
#align linear_equiv.fun_congr_left_apply LinearEquiv.funCongrLeft_apply

@[simp]
theorem funCongrLeft_id : funCongrLeft R M (Equiv.refl n) = LinearEquiv.refl R (n → M) :=
  rfl
#align linear_equiv.fun_congr_left_id LinearEquiv.funCongrLeft_id

@[simp]
theorem funCongrLeft_comp (e₁ : m ≃ n) (e₂ : n ≃ p) :
    funCongrLeft R M (Equiv.trans e₁ e₂) =
      LinearEquiv.trans (funCongrLeft R M e₂) (funCongrLeft R M e₁) :=
  rfl
#align linear_equiv.fun_congr_left_comp LinearEquiv.funCongrLeft_comp

@[simp]
theorem funCongrLeft_symm (e : m ≃ n) : (funCongrLeft R M e).symm = funCongrLeft R M e.symm :=
  rfl
#align linear_equiv.fun_congr_left_symm LinearEquiv.funCongrLeft_symm

end LinearEquiv

end FunLeft

end AddCommMonoid
