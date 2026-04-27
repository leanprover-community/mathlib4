/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Ring.Action.Group

/-!
# Isomorphisms of `R`-algebras

This file defines bundled isomorphisms of `R`-algebras.

## Main definitions

* `AlgEquiv R A B`: the type of `R`-algebra isomorphisms between `A` and `B`.

## Notation

* `A ≃ₐ[R] B` : `R`-algebra equivalence from `A` to `B`.
-/

@[expose] public section

universe u v w x

/-- An equivalence of algebras (denoted as `A ≃ₐ[R] B`)
is an equivalence of rings commuting with the actions of scalars. -/
structure AlgEquiv {R : Type u} {S : Type v} [CommSemiring R] [CommSemiring S] (φ : R →+* S)
  {ψ : S →+* R} [RingHomInvPair φ ψ] [RingHomInvPair ψ φ] (A : Type w) (B : Type x) [Semiring A]
  [Semiring B] [Algebra R A] [Algebra S B] extends A ≃ B, A ≃+ B, A ≃* B, A ≃+* B where
  /-- An equivalence of algebras commutes with the action of scalars. -/
  protected commutes' : ∀ r : R, toFun (algebraMap R A r) = algebraMap S B (φ r)

attribute [nolint docBlame] AlgEquiv.toRingEquiv
attribute [nolint docBlame] AlgEquiv.toEquiv
attribute [nolint docBlame] AlgEquiv.toAddEquiv
attribute [nolint docBlame] AlgEquiv.toMulEquiv

@[inherit_doc]
notation:50 A " ≃ₛₐ[" φ "] " B => AlgEquiv φ A B

@[inherit_doc]
notation:50 A " ≃ₐ[" R "] " B => AlgEquiv (RingHom.id R) A B

class SemialgEquivClass (F : Type*) {R S : outParam Type*} [CommSemiring R] [CommSemiring S]
    (φ : outParam (R →+* S)) {ψ : outParam (S →+* R)} [RingHomInvPair φ ψ] [RingHomInvPair ψ φ]
    (A B : outParam Type*) [Semiring A] [Semiring B] [Algebra R A] [Algebra S B] [EquivLike F A B] :
    Prop extends RingEquivClass F A B where
  /-- An equivalence of algebras commutes with the action of scalars. -/
  commutes (f : F) (r : R) : f (algebraMap R A r) = algebraMap S B (φ r)

abbrev AlgEquivClass (F : Type*) (R A B : outParam Type*) [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] [EquivLike F A B] : Prop :=
  SemialgEquivClass F (RingHom.id R) A B

namespace SemialgEquivClass

variable {F : Type*} {R S : Type*} [CommSemiring R] [CommSemiring S]
    {φ : R →+* S} {ψ : S →+* R} [RingHomInvPair φ ψ] [RingHomInvPair ψ φ]
    {A B : Type*} [Semiring A] [Semiring B] [Algebra R A] [Algebra S B] [EquivLike F A B]
variable [SemialgEquivClass F φ A B]

instance (priority := 100) : SemialgHomClass F φ A B where __ := ‹SemialgEquivClass F φ A B›

@[coe]
def toAlgEquiv (f : F) : A ≃ₛₐ[φ] B where
  __ := RingEquivClass.toRingEquiv f
  commutes' := SemialgEquivClass.commutes f

end SemialgEquivClass

namespace AlgEquivClass

theorem commutes {F R : Type*} {A B : outParam Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] [EquivLike F A B] [h : AlgEquivClass F R A B] (f : F) (r : R) :
    f (algebraMap R A r) = algebraMap R B r := by
  simp [Algebra.algebraMap_eq_smul_one]

-- See note [lower instance priority]
instance (priority := 100) toAlgHomClass (F R A B : Type*) [CommSemiring R] [Semiring A]
    [Semiring B] [Algebra R A] [Algebra R B] [EquivLike F A B] [AlgEquivClass F R A B] :
    AlgHomClass F R A B where
  commutes := by simp [commutes]

instance (priority := 100) toLinearEquivClass (F R A B : Type*) [CommSemiring R]
    [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
    [EquivLike F A B] [h : AlgEquivClass F R A B] : LinearEquivClass F R A B :=
  { h with map_smulₛₗ := fun f => map_smulₛₗ f }

/-- Turn an element of a type `F` satisfying `AlgEquivClass F R A B` into an actual `AlgEquiv`.
This is declared as the default coercion from `F` to `A ≃ₐ[R] B`. -/
@[coe]
def toAlgEquiv {F R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A]
    [Algebra R B] [EquivLike F A B] [AlgEquivClass F R A B] (f : F) : A ≃ₐ[R] B where
  __ := RingEquivClass.toRingEquiv f
  commutes' := commutes f

end AlgEquivClass

namespace AlgEquiv

universe u₁ u₂
universe v₁ v₂ v₃
variable {R₁ : Type u₁} {R₂ : Type u₂}
variable [CommSemiring R₁] [CommSemiring R₂]


section Semiring

variable {φ : R₁ →+* R₂} {ψ : R₂ →+* R₁}
variable [RingHomInvPair φ ψ] [RingHomInvPair ψ φ]
variable {A₁ : Type v₁} {A₂ : Type v₂} {A₃ : Type v₃}
variable [Semiring A₁] [Semiring A₂] [Semiring A₃]
variable [Algebra R₁ A₁] [Algebra R₂ A₂] --[Algebra R₁ A₃]
variable (e : A₁ ≃ₛₐ[φ] A₂)

universe u₃ u₄
universe v₄
variable {R₃ : Type u₃} {R₄ : Type u₄}
variable {A₄ : Type v₄}
variable [CommSemiring R₃] [CommSemiring R₄] [Semiring A₄]
variable [Algebra R₃ A₃] [Algebra R₄ A₄]
variable {φ₁₂ : R₁ →+* R₂} {φ₂₁ : R₂ →+* R₁} [RingHomInvPair φ₁₂ φ₂₁] [RingHomInvPair φ₂₁ φ₁₂]
variable {φ₁₃ : R₁ →+* R₃} {φ₃₁ : R₃ →+* R₁} [RingHomInvPair φ₁₃ φ₃₁] [RingHomInvPair φ₃₁ φ₁₃]
variable {φ₁₄ : R₁ →+* R₄} {φ₄₁ : R₄ →+* R₁} [RingHomInvPair φ₁₄ φ₄₁] [RingHomInvPair φ₄₁ φ₁₄]
variable {φ₂₃ : R₂ →+* R₃} {φ₃₂ : R₃ →+* R₂} [RingHomInvPair φ₂₃ φ₃₂] [RingHomInvPair φ₃₂ φ₂₃]
variable {φ₂₄ : R₂ →+* R₄} {φ₄₂ : R₄ →+* R₂} [RingHomInvPair φ₂₄ φ₄₂] [RingHomInvPair φ₄₂ φ₂₄]
variable {φ₃₄ : R₃ →+* R₄} {φ₄₃ : R₄ →+* R₃} [RingHomInvPair φ₃₄ φ₄₃] [RingHomInvPair φ₄₃ φ₃₄]
variable [RingHomCompTriple φ₁₂ φ₂₃ φ₁₃]
variable [RingHomCompTriple φ₁₂ φ₂₄ φ₁₄] [RingHomCompTriple φ₄₂ φ₂₁ φ₄₁]
variable [RingHomCompTriple φ₁₃ φ₃₄ φ₁₄] [RingHomCompTriple φ₄₃ φ₃₁ φ₄₁]
variable [RingHomCompTriple φ₂₃ φ₃₄ φ₂₄] [RingHomCompTriple φ₄₃ φ₃₂ φ₄₂]
variable (e₁₂ : A₁ ≃ₛₐ[φ₁₂] A₂) (e₂₃ : A₂ ≃ₛₐ[φ₂₃] A₃)

section coe

instance : EquivLike (A₁ ≃ₛₐ[φ] A₂) A₁ A₂ where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by
    obtain ⟨⟨f, _⟩, _⟩ := f
    obtain ⟨⟨g, _⟩, _⟩ := g
    congr

/-- Helper instance since the coercion is not always found. -/
instance : FunLike (A₁ ≃ₛₐ[φ] A₂) A₁ A₂ where
  coe := DFunLike.coe
  coe_injective' := DFunLike.coe_injective'

instance : SemialgEquivClass (A₁ ≃ₛₐ[φ] A₂) φ A₁ A₂ where
  map_add f := f.map_add'
  map_mul f := f.map_mul'
  commutes f := f.commutes'

@[ext]
theorem ext {f g : A₁ ≃ₛₐ[φ] A₂} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

protected theorem congr_arg {f : A₁ ≃ₛₐ[φ] A₂} {x x' : A₁} : x = x' → f x = f x' :=
  DFunLike.congr_arg f

protected theorem congr_fun {f g : A₁ ≃ₛₐ[φ] A₂} (h : f = g) (x : A₁) : f x = g x :=
  DFunLike.congr_fun h x

@[simp]
theorem coe_mk {toEquiv map_mul map_add commutes} :
    ⇑(⟨toEquiv, map_mul, map_add, commutes⟩ : A₁ ≃ₛₐ[φ] A₂) = toEquiv :=
  rfl

@[simp]
theorem mk_coe (e : A₁ ≃ₛₐ[φ] A₂) (e' h₁ h₂ h₃ h₄ h₅) :
    (⟨⟨e, e', h₁, h₂⟩, h₃, h₄, h₅⟩ : A₁ ≃ₛₐ[φ] A₂) = e :=
  ext fun _ => rfl

@[simp]
theorem toEquiv_eq_coe : e.toEquiv = e :=
  rfl

@[simp]
protected theorem coe_coe {F : Type*} [EquivLike F A₁ A₂] [SemialgEquivClass F φ A₁ A₂] (e : F) :
    ⇑(SemialgEquivClass.toAlgEquiv e) = e :=
  rfl

theorem coe_fun_injective : @Function.Injective (A₁ ≃ₛₐ[φ] A₂) (A₁ → A₂) fun e => (e : A₁ → A₂) :=
  DFunLike.coe_injective

instance : CoeOut (A₁ ≃ₛₐ[φ] A₂) (A₁ ≃+* A₂) where coe := AlgEquiv.toRingEquiv

@[simp]
theorem coe_toEquiv : ((e : A₁ ≃ A₂) : A₁ → A₂) = e :=
  rfl

@[deprecated "Now a syntactic equality" (since := "2026-04-09"), nolint synTaut]
theorem toRingEquiv_eq_coe : e.toRingEquiv = e :=
  rfl

@[simp]
lemma toRingEquiv_toRingHom : ((e : A₁ ≃+* A₂) : A₁ →+* A₂) = e :=
  rfl

@[simp]
theorem coe_ringEquiv : ((e : A₁ ≃+* A₂) : A₁ → A₂) = e :=
  rfl

theorem coe_ringEquiv' : (e.toRingEquiv : A₁ → A₂) = e :=
  rfl

theorem coe_ringEquiv_injective : Function.Injective ((↑) : (A₁ ≃ₛₐ[φ] A₂) → A₁ ≃+* A₂) :=
  fun _ _ h => ext <| RingEquiv.congr_fun h

/-- Interpret an algebra equivalence as an algebra homomorphism.

This definition is included for symmetry with the other `to*Hom` projections.
The `simp` normal form is to use the coercion of the `AlgHomClass.coeTC` instance. -/
@[coe]
def toAlgHom : A₁ →ₛₐ[φ] A₂ :=
  { e with
    map_one' := map_one e
    map_zero' := map_zero e
    commutes' _:= e.commutes' _ }

theorem toAlgHom_eq_coeₛₐ : e.toAlgHom = e :=
  rfl

theorem toAlgHom_eq_coe [Algebra R₁ A₂] (e : A₁ ≃ₐ[R₁] A₂) : e.toAlgHom = e :=
  rfl

theorem toAlgHom_apply (x : A₁) : e.toAlgHom x = e x :=
  rfl

@[simp, norm_cast]
theorem coe_algHom : DFunLike.coe (e.toAlgHom) = DFunLike.coe e :=
  rfl

theorem coe_algHom_injective : Function.Injective ((↑) : (A₁ ≃ₛₐ[φ] A₂) → A₁ →ₛₐ[φ] A₂) :=
  fun _ _ h => ext <| AlgHom.congr_fun h

@[simp, norm_cast]
lemma toAlgHom_toRingHom : (e.toAlgHom : A₁ →+* A₂) = e :=
  rfl

/-- The two paths coercion can take to a `RingHom` are equivalent -/
theorem coe_ringHom_commutes : (e.toAlgHom : A₁ →+* A₂) = (e : A₁ →+* A₂) :=
  rfl

@[simp]
theorem commutesₛₐ (r : R₁) : e (algebraMap R₁ A₁ r) = algebraMap R₂ A₂ (φ r) := by
  simp [Algebra.algebraMap_eq_smul_one, map_smulₛₗ]

theorem commutes [Algebra R₁ A₂] (e : A₁ ≃ₐ[R₁] A₂) (r : R₁) :
    e (algebraMap R₁ A₁ r) = algebraMap R₁ A₂ r := e.commutes' r

end coe

section bijective

protected theorem bijective : Function.Bijective e :=
  EquivLike.bijective e

protected theorem injective : Function.Injective e :=
  EquivLike.injective e

protected theorem surjective : Function.Surjective e :=
  EquivLike.surjective e

end bijective

section refl

/-- Algebra equivalences are reflexive. -/
@[refl]
def refl : A₁ ≃ₐ[R₁] A₁ where
  __ := RingEquiv.refl A₁
  commutes' _ := rfl

instance : Inhabited (A₁ ≃ₐ[R₁] A₁) :=
  ⟨refl⟩

@[simp, norm_cast] lemma refl_toAlgHom : refl.toAlgHom = AlgHom.id R₁ A₁ := rfl
@[simp, norm_cast] lemma refl_toRingHom : (refl : A₁ ≃ₐ[R₁] A₁) = RingHom.id A₁ := rfl

@[simp]
theorem coe_refl : ⇑(refl : A₁ ≃ₐ[R₁] A₁) = id :=
  rfl

end refl

section symm

/-- Algebra equivalences are symmetric. -/
@[symm]
def symm (e : A₁ ≃ₛₐ[φ] A₂) : A₂ ≃ₛₐ[ψ] A₁ where
  __ := e.toRingEquiv.symm
  commutes' r := by
    rw [← e.toRingEquiv.symm_apply_apply (algebraMap R₁ A₁ (ψ r))]
    simp

theorem invFun_eq_symm {e : A₁ ≃ₛₐ[φ] A₂} : e.invFun = e.symm :=
  rfl

@[simp]
theorem coe_apply_coe_coe_symm_apply {F : Type*} [EquivLike F A₁ A₂] [SemialgEquivClass F φ A₁ A₂]
    (f : F) (x : A₂) :
    f ((SemialgEquivClass.toAlgEquiv f).symm x) = x :=
  EquivLike.right_inv f x

@[simp]
theorem coe_coe_symm_apply_coe_apply {F : Type*} [EquivLike F A₁ A₂] [SemialgEquivClass F φ A₁ A₂]
    (f : F) (x : A₁) :
    (SemialgEquivClass.toAlgEquiv f).symm (f x) = x :=
  EquivLike.left_inv f x

@[simp]
theorem coe_apply_coe_coe_symm_apply' [Algebra R₁ A₂] {F : Type*} [EquivLike F A₁ A₂]
    [AlgEquivClass F R₁ A₁ A₂] (f : F) (x : A₂) :
    f ((AlgEquivClass.toAlgEquiv f).symm x) = x :=
  EquivLike.right_inv f x

@[simp]
theorem coe_coe_symm_apply_coe_apply' [Algebra R₁ A₂] {F : Type*} [EquivLike F A₁ A₂]
    [AlgEquivClass F R₁ A₁ A₂] (f : F) (x : A₁) :
    (AlgEquivClass.toAlgEquiv f).symm (f x) = x :=
  EquivLike.left_inv f x

/-- `simp` normal form of `invFun_eq_symm` -/
@[simp]
theorem symm_toEquiv_eq_symm {e : A₁ ≃ₛₐ[φ] A₂} : (e : A₁ ≃ A₂).symm = e.symm :=
  rfl

@[simp]
theorem symm_symm (e : A₁ ≃ₛₐ[φ] A₂) : e.symm.symm = e := rfl

theorem symm_bijective : Function.Bijective (symm : (A₁ ≃ₛₐ[φ] A₂) → A₂ ≃ₛₐ[ψ] A₁) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]
theorem mk_coe' (e : A₁ ≃ₛₐ[φ] A₂) (f h₁ h₂ h₃ h₄ h₅) :
    (⟨⟨f, e, h₁, h₂⟩, h₃, h₄, h₅⟩ : A₂ ≃ₛₐ[ψ] A₁) = e.symm :=
  symm_bijective.injective <| ext fun _ => rfl

/-- Auxiliary definition to avoid looping in `dsimp` with `AlgEquiv.symm_mk`. -/
protected def symm_mk.aux (f f') (h₁ h₂ h₃ h₄ h₅) :=
  (⟨⟨f, f', h₁, h₂⟩, h₃, h₄, h₅⟩ : A₁ ≃ₛₐ[φ] A₂).symm

@[simp]
theorem symm_mk (f f') (h₁ h₂ h₃ h₄ h₅) :
    (⟨⟨f, f', h₁, h₂⟩, h₃, h₄, h₅⟩ : A₁ ≃ₛₐ[φ] A₂).symm =
      { symm_mk.aux f f' h₁ h₂ h₃ h₄ h₅ with
        toFun := f'
        invFun := f } :=
  rfl

@[simp]
theorem refl_symm : (AlgEquiv.refl : A₁ ≃ₐ[R₁] A₁).symm = AlgEquiv.refl :=
  rfl

theorem toRingEquiv_symm : (e : A₁ ≃+* A₂).symm = e.symm :=
  rfl

@[simp]
theorem symm_toRingEquiv : (e.symm : A₂ ≃+* A₁) = (e : A₁ ≃+* A₂).symm :=
  rfl

@[simp]
theorem symm_toAddEquiv : (e.symm : A₂ ≃+ A₁) = (e : A₁ ≃+ A₂).symm :=
  rfl

@[simp]
theorem symm_toMulEquiv : (e.symm : A₂ ≃* A₁) = (e : A₁ ≃* A₂).symm :=
  rfl

@[simp]
theorem apply_symm_apply (e : A₁ ≃ₛₐ[φ] A₂) : ∀ x, e (e.symm x) = x :=
  e.toEquiv.apply_symm_apply

@[simp]
theorem symm_apply_apply (e : A₁ ≃ₛₐ[φ] A₂) : ∀ x, e.symm (e x) = x :=
  e.toEquiv.symm_apply_apply

theorem symm_apply_eq (e : A₁ ≃ₛₐ[φ] A₂) {x y} : e.symm x = y ↔ x = e y :=
  e.toEquiv.symm_apply_eq

theorem eq_symm_apply (e : A₁ ≃ₛₐ[φ] A₂) {x y} : y = e.symm x ↔ e y = x :=
  e.toEquiv.eq_symm_apply

@[simp]
theorem comp_symm (e : A₁ ≃ₛₐ[φ] A₂) :
    AlgHom.comp e.toAlgHom e.symm.toAlgHom = AlgHom.id _ A₂ := by
  ext
  simp

@[simp]
theorem symm_comp (e : A₁ ≃ₛₐ[φ] A₂) : AlgHom.comp e.symm.toAlgHom e.toAlgHom = AlgHom.id _ A₁ := by
  ext
  simp

theorem leftInverse_symm (e : A₁ ≃ₛₐ[φ] A₂) : Function.LeftInverse e.symm e :=
  e.left_inv

theorem rightInverse_symm (e : A₁ ≃ₛₐ[φ] A₂) : Function.RightInverse e.symm e :=
  e.right_inv

end symm

section simps

/-- See Note [custom simps projection] -/
def Simps.apply (e : A₁ ≃ₛₐ[φ] A₂) : A₁ → A₂ :=
  e

/-- See Note [custom simps projection] -/
def Simps.toEquiv (e : A₁ ≃ₛₐ[φ] A₂) : A₁ ≃ A₂ :=
  e

/-- See Note [custom simps projection] -/
def Simps.symm_apply (e : A₁ ≃ₛₐ[φ] A₂) : A₂ → A₁ :=
  e.symm

initialize_simps_projections AlgEquiv (toFun → apply, invFun → symm_apply)

end simps

section trans

/-- Algebra equivalences are transitive. -/
@[trans]
def trans : A₁ ≃ₛₐ[φ₁₃] A₃ where
  __ := e₁₂.toRingEquiv.trans e₂₃.toRingEquiv
  commutes' r := by simp

@[simp]
theorem coe_trans (e₁ : A₁ ≃ₛₐ[φ₁₂] A₂) (e₂ : A₂ ≃ₛₐ[φ₂₃] A₃) : ⇑(e₁.trans e₂) = e₂ ∘ e₁ :=
  rfl

@[simp]
theorem trans_apply (e₁ : A₁ ≃ₛₐ[φ₁₂] A₂) (e₂ : A₂ ≃ₛₐ[φ₂₃] A₃) (x : A₁) :
    (e₁.trans e₂) x = e₂ (e₁ x) := rfl

@[simp]
theorem symm_trans_apply (e₁ : A₁ ≃ₛₐ[φ₁₂] A₂) (e₂ : A₂ ≃ₛₐ[φ₂₃] A₃) (x : A₃) :
    (e₁.trans e₂).symm x = e₁.symm (e₂.symm x) :=
  rfl

@[simp] lemma self_trans_symm (e : A₁ ≃ₛₐ[φ₁₂] A₂) : e.trans e.symm = refl := by ext; simp
@[simp] lemma symm_trans_self (e : A₁ ≃ₛₐ[φ₁₂] A₂) : e.symm.trans e = refl := by ext; simp

@[simp, norm_cast]
lemma toRingHom_trans (e₁ : A₁ ≃ₛₐ[φ₁₂] A₂) (e₂ : A₂ ≃ₛₐ[φ₂₃] A₃) :
    (e₁.trans e₂ : A₁ →+* A₃) = .comp e₂ (e₁ : A₁ →+* A₂) := rfl

end trans

/-- `Equiv.cast (congrArg _ h)` as an algebra equiv.

Note that unlike `Equiv.cast`, this takes an equality of indices rather than an equality of types,
to avoid having to deal with an equality of the algebraic structure itself. -/
@[simps!]
protected def cast {ι : Type*} {A : ι → Type*} [∀ i, Semiring (A i)] [∀ i, Algebra R₁ (A i)]
    {i j : ι} (h : i = j) : A i ≃ₐ[R₁] A j where
  __ := RingEquiv.cast h
  commutes' := by cases h; simp

universe w₁ w₂ w₃ w₄ w₅ w₆
variable {B₁ : Type w₁} {B₂ : Type w₂} {B₃ : Type w₃} {B₄ : Type w₄} {B₅ : Type w₅} {B₆ : Type w₆}
variable [Semiring B₁] [Semiring B₂] [Semiring B₃] [Semiring B₄] [Semiring B₅] [Semiring B₆]
variable [Algebra R₁ B₁] [Algebra R₁ B₂] [Algebra R₁ B₃] [Algebra R₁ B₄] [Algebra R₁ B₅]
  [Algebra R₁ B₆]

/-- If `A₁` is equivalent to `A₁'` and `A₂` is equivalent to `A₂'`, then the type of maps
`A₁ →ₐ[R₁] A₂` is equivalent to the type of maps `A₁' →ₐ[R₁] A₂'`. -/
@[simps apply]
def arrowCongr (e₁ : B₁ ≃ₐ[R₁] B₂) (e₂ : B₃ ≃ₐ[R₁] B₄) : (B₁ →ₐ[R₁] B₃) ≃ (B₂ →ₐ[R₁] B₄) where
  toFun f := (e₂.toAlgHom.comp f).comp e₁.symm.toAlgHom
  invFun f := (e₂.symm.toAlgHom.comp f).comp e₁.toAlgHom
  left_inv f := by
    simp only [AlgHom.comp_assoc, symm_comp]
    simp only [← AlgHom.comp_assoc, symm_comp, AlgHom.id_comp, AlgHom.comp_id]
  right_inv f := by
    simp only [AlgHom.comp_assoc, comp_symm]
    simp only [← AlgHom.comp_assoc, comp_symm, AlgHom.id_comp, AlgHom.comp_id]

theorem arrowCongr_comp (e₁ : B₁ ≃ₐ[R₁] B₂) (e₂ : B₂ ≃ₐ[R₁] B₃) (e₃ : B₃ ≃ₐ[R₁] B₄)
(f : B₁ →ₐ[R₁] B₂) (g : B₂ →ₐ[R₁] B₃) :
    arrowCongr e₁ e₃ (g.comp f) = (arrowCongr e₂ e₃ g).comp (arrowCongr e₁ e₂ f) := by
  ext
  simp

@[simp]
theorem arrowCongr_refl : arrowCongr AlgEquiv.refl AlgEquiv.refl = Equiv.refl (B₁ →ₐ[R₁] B₃) :=
  rfl

@[simp]
theorem arrowCongr_trans (e₁ : B₁ ≃ₐ[R₁] B₂) (e₁' : B₄ ≃ₐ[R₁] B₅)
    (e₂ : B₂ ≃ₐ[R₁] B₃) (e₂' : B₅ ≃ₐ[R₁] B₆) :
    arrowCongr (e₁.trans e₂) (e₁'.trans e₂') = (arrowCongr e₁ e₁').trans (arrowCongr e₂ e₂') :=
  rfl

@[simp]
theorem arrowCongr_symm (e₁ : B₁ ≃ₐ[R₁] B₂) (e₂ : B₃ ≃ₐ[R₁] B₄) :
    (arrowCongr e₁ e₂).symm = arrowCongr e₁.symm e₂.symm :=
  rfl

/-- If `A₁` is equivalent to `A₂` and `A₁'` is equivalent to `A₂'`, then the type of maps
`A₁ ≃ₐ[R₁] A₁'` is equivalent to the type of maps `A₂ ≃ₐ[R₁] A₂'`.

This is the `AlgEquiv` version of `AlgEquiv.arrowCongr`. -/
@[simps apply]
def equivCongr (e : B₁ ≃ₐ[R₁] B₂) (e' : B₃ ≃ₐ[R₁] B₄) : (B₁ ≃ₐ[R₁] B₃) ≃ (B₂ ≃ₐ[R₁] B₄) where
  toFun ψ := e.symm.trans (ψ.trans e')
  invFun ψ := e.trans (ψ.trans e'.symm)
  left_inv ψ := by
    ext
    simp_rw [trans_apply, symm_apply_apply]
  right_inv ψ := by
    ext
    simp_rw [trans_apply, apply_symm_apply]

@[simp]
theorem equivCongr_refl : equivCongr AlgEquiv.refl AlgEquiv.refl = Equiv.refl (B₁ ≃ₐ[R₁] B₃) :=
  rfl

@[simp]
theorem equivCongr_symm (e : B₁ ≃ₐ[R₁] B₂) (e' : B₃ ≃ₐ[R₁] B₄) :
    (equivCongr e e').symm = equivCongr e.symm e'.symm :=
  rfl

@[simp]
theorem equivCongr_trans (e₁₂ : B₁ ≃ₐ[R₁] B₂) (e₁₂' : B₄ ≃ₐ[R₁] B₅)
    (e₂₃ : B₂ ≃ₐ[R₁] B₃) (e₂₃' : B₅ ≃ₐ[R₁] B₆) :
    (equivCongr e₁₂ e₁₂').trans (equivCongr e₂₃ e₂₃') =
      equivCongr (e₁₂.trans e₂₃) (e₁₂'.trans e₂₃') :=
  rfl

/-- If an algebra morphism has an inverse, it is an algebra isomorphism. -/
@[simps]
def ofAlgHom (f : A₁ →ₛₐ[φ] A₂) (g : A₂ →ₛₐ[ψ] A₁) (h₁ : f.comp g = AlgHom.id _ A₂)
    (h₂ : g.comp f = AlgHom.id _ A₁) : A₁ ≃ₛₐ[φ] A₂ :=
  { f with
    toFun := f
    invFun := g
    left_inv := AlgHom.ext_iff.1 h₂
    right_inv := AlgHom.ext_iff.1 h₁ }

theorem coe_algHom_ofAlgHom (f : A₁ →ₛₐ[φ] A₂) (g : A₂ →ₛₐ[ψ] A₁) (h₁ h₂) :
    ↑(ofAlgHom f g h₁ h₂) = f :=
  rfl

@[simp]
theorem ofAlgHom_coe_algHom (f : A₁ ≃ₛₐ[φ] A₂) (g : A₂ →ₛₐ[ψ] A₁) (h₁ h₂) :
    ofAlgHom (↑f) g h₁ h₂ = f :=
  ext fun _ => rfl

theorem ofAlgHom_symm (f : A₁ →ₛₐ[φ] A₂) (g : A₂ →ₛₐ[ψ] A₁) (h₁ h₂) :
    (ofAlgHom f g h₁ h₂).symm = ofAlgHom g f h₂ h₁ :=
  rfl

/-- Forgetting the multiplicative structures, an equivalence of algebras is a linear equivalence. -/
@[simps apply]
def toLinearEquiv (e : A₁ ≃ₛₐ[φ] A₂) : A₁ ≃ₛₗ[φ] A₂ :=
  { e with
    toFun := e
    map_smul' := map_smulₛₗ e
    invFun := e.symm }

@[simp]
theorem toLinearEquiv_refl :
    (AlgEquiv.refl : A₁ ≃ₐ[R₁] A₁).toLinearEquiv = LinearEquiv.refl R₁ A₁ := rfl

@[simp]
theorem toLinearEquiv_symm (e : A₁ ≃ₛₐ[φ] A₂) : e.symm.toLinearEquiv = e.toLinearEquiv.symm :=
  rfl

@[simp]
theorem coe_toLinearEquiv (e : A₁ ≃ₛₐ[φ] A₂) : ⇑e.toLinearEquiv = e := rfl

@[simp]
theorem coe_symm_toLinearEquiv (e : A₁ ≃ₛₐ[φ] A₂) : ⇑e.toLinearEquiv.symm = e.symm := rfl

@[simp]
theorem toLinearEquiv_trans [RingHomCompTriple φ₃₂ φ₂₁ φ₃₁] (e₁ : A₁ ≃ₛₐ[φ₁₂] A₂)
    (e₂ : A₂ ≃ₛₐ[φ₂₃] A₃) : (e₁.trans e₂).toLinearEquiv = e₁.toLinearEquiv.trans e₂.toLinearEquiv :=
  rfl

theorem toLinearEquiv_injective : Function.Injective (toLinearEquiv : _ → A₁ ≃ₛₗ[φ] A₂) :=
  fun _ _ h => ext <| LinearEquiv.congr_fun h

/-- Interpret an algebra equivalence as a linear map. -/
def toLinearMap : A₁ →ₛₗ[φ] A₂ :=
  e.toAlgHom.toLinearMap

@[simp]
theorem toAlgHom_toLinearMap : e.toAlgHom.toLinearMap = e.toLinearMap :=
  rfl

theorem toLinearMap_ofAlgHom (f : A₁ →ₛₐ[φ] A₂) (g : A₂ →ₛₐ[ψ] A₁) (h₁ h₂) :
    (ofAlgHom f g h₁ h₂).toLinearMap = f.toLinearMap :=
  LinearMap.ext fun _ => rfl

@[simp]
theorem toLinearEquiv_toLinearMap : e.toLinearEquiv.toLinearMap = e.toLinearMap :=
  rfl

@[simp]
theorem toLinearMap_apply (x : A₁) : e.toLinearMap x = e x :=
  rfl

theorem toLinearMap_injective : Function.Injective (toLinearMap : _ → A₁ →ₛₗ[φ] A₂) := fun _ _ h =>
  ext <| LinearMap.congr_fun h

@[simp]
theorem trans_toLinearMap (f : A₁ ≃ₛₐ[φ₁₂] A₂) (g : A₂ ≃ₛₐ[φ₂₃] A₃) :
    (f.trans g).toLinearMap = g.toLinearMap.comp f.toLinearMap :=
  rfl

@[simp] theorem linearEquivConj_mulLeft (f : A₁ ≃ₛₐ[φ] A₂) (x : A₁) :
    f.toLinearEquiv.conj (.mulLeft _ x) = .mulLeft _ (f x) := by
  ext; simp

@[simp] theorem linearEquivConj_mulRight (f : A₁ ≃ₛₐ[φ] A₂) (x : A₁) :
    f.toLinearEquiv.conj (.mulRight _ x) = .mulRight _ (f x) := by
  ext; simp

@[simp] theorem linearEquivConj_mulLeftRight (f : A₁ ≃ₛₐ[φ] A₂) (x : A₁ × A₁) :
    f.toLinearEquiv.conj (.mulLeftRight _ x) = .mulLeftRight _ (Prod.map f f x) := by
  cases x; ext; simp

/-- Promotes a bijective algebra homomorphism to an algebra equivalence. -/
noncomputable def ofBijective (f : A₁ →ₛₐ[φ] A₂) (hf : Function.Bijective f) : A₁ ≃ₛₐ[φ] A₂ :=
  { RingEquiv.ofBijective (f : A₁ →+* A₂) hf, f with }

@[simp]
lemma coe_ofBijective (f : A₁ →ₛₐ[φ] A₂) (hf : Function.Bijective f) :
    (ofBijective f hf).toAlgHom = f := rfl

lemma ofBijective_apply (f : A₁ →ₛₐ[φ] A₂) (hf : Function.Bijective f) (a : A₁) :
    (ofBijective f hf) a = f a := rfl

@[simp]
lemma toLinearMap_ofBijective (f : A₁ →ₛₐ[φ] A₂) (hf : Function.Bijective f) :
    (ofBijective f hf).toLinearMap = f := rfl

@[simp]
lemma toAlgHom_ofBijective (f : A₁ →ₛₐ[φ] A₂) (hf : Function.Bijective f) :
    (ofBijective f hf).toAlgHom = f := rfl

lemma ofBijective_apply_symm_apply (f : A₁ →ₛₐ[φ] A₂) (hf : Function.Bijective f) (x : A₂) :
    f ((ofBijective f hf).symm x) = x :=
  (ofBijective f hf).apply_symm_apply x

@[simp]
lemma ofBijective_symm_apply_apply (f : A₁ →ₛₐ[φ] A₂) (hf : Function.Bijective f) (x : A₁) :
    (ofBijective f hf).symm (f x) = x :=
  (ofBijective f hf).symm_apply_apply x

section OfLinearEquiv

variable (l : A₁ ≃ₛₗ[φ] A₂) (map_one : l 1 = 1) (map_mul : ∀ x y : A₁, l (x * y) = l x * l y)

-- TODO : have an ₛₐ version
/--
Upgrade a linear equivalence to an algebra equivalence,
given that it distributes over multiplication and the identity
-/
@[simps apply]
def ofLinearEquiv : A₁ ≃ₛₐ[φ] A₂ where
  __ := l
  map_mul' := map_mul
  commutes' := by simp [Algebra.algebraMap_eq_smul_one, map_smulₛₗ, map_one]
  -- { l with
  --   toFun := l
  --   invFun := l.symm
  --   map_mul' := map_mul
  --   map_smul' := (AlgHom.ofLinearMap l map_one map_mul : A₁ →ₛₐ[φ] A₂).commutes }

/-- Auxiliary definition to avoid looping in `dsimp` with `AlgEquiv.ofLinearEquiv_symm`. -/
protected def ofLinearEquiv_symm.aux := (ofLinearEquiv l map_one map_mul).symm

@[simp]
theorem ofLinearEquiv_symm :
    (ofLinearEquiv l map_one map_mul).symm =
      ofLinearEquiv l.symm
        (_root_.map_one <| ofLinearEquiv_symm.aux l map_one map_mul)
        (_root_.map_mul (ofLinearEquiv_symm.aux l map_one map_mul)) :=
  rfl

@[simp]
theorem ofLinearEquiv_toLinearEquiv (map_one) (map_mul) :
    ofLinearEquiv e.toLinearEquiv map_one map_mul = e :=
  rfl

@[simp]
theorem toLinearEquiv_ofLinearEquiv : toLinearEquiv (ofLinearEquiv l map_one map_mul) = l :=
  rfl

end OfLinearEquiv

section OfRingEquiv

/-- Promotes a linear `RingEquiv` to an `AlgEquiv`. -/
@[simps apply symm_apply toEquiv]
def ofRingEquiv [Algebra R₁ A₂] {f : A₁ ≃+* A₂}
    (hf : ∀ x, f (algebraMap R₁ A₁ x) = algebraMap R₁ A₂ x) :
    A₁ ≃ₐ[R₁] A₂ :=
  { f with
    toFun := f
    invFun := f.symm
    commutes' := hf }

/-- Promotes a linear `RingEquiv` to an `AlgEquiv`. -/
@[simps apply symm_apply toEquiv]
def ofRingEquivₛₐ {f : A₁ ≃+* A₂} (hf : ∀ x, f (algebraMap R₁ A₁ x) = algebraMap R₂ A₂ (φ x)) :
    A₁ ≃ₛₐ[φ] A₂ :=
  { f with
    toFun := f
    invFun := f.symm
    commutes' := hf }

end OfRingEquiv

@[simps -isSimp one mul, stacks 09HR]
instance aut : Group (A₁ ≃ₐ[R₁] A₁) where
  mul ϕ ψ := ψ.trans ϕ
  mul_assoc _ _ _ := rfl
  one := refl
  one_mul _ := ext fun _ => rfl
  mul_one _ := ext fun _ => rfl
  inv := symm
  inv_mul_cancel ϕ := ext <| symm_apply_apply ϕ

@[simp]
theorem one_apply (x : A₁) : (1 : A₁ ≃ₐ[R₁] A₁) x = x :=
  rfl

@[simp]
theorem mul_apply (e₁ e₂ : A₁ ≃ₐ[R₁] A₁) (x : A₁) : (e₁ * e₂) x = e₁ (e₂ x) :=
  rfl

lemma aut_inv (ϕ : A₁ ≃ₐ[R₁] A₁) : ϕ⁻¹ = ϕ.symm := rfl

@[simp] lemma coe_inv (ϕ : A₁ ≃ₐ[R₁] A₁) : ⇑ϕ⁻¹ = ⇑ϕ.symm := rfl

@[simp] theorem coe_pow (e : A₁ ≃ₐ[R₁] A₁) (n : ℕ) : ⇑(e ^ n) = e^[n] :=
  n.rec (by ext; simp) fun _ ih ↦ by ext; simp [pow_succ, ih]

/-- An algebra isomorphism induces a group isomorphism between automorphism groups.

This is a more bundled version of `AlgEquiv.equivCongr`. -/
@[simps apply]
def autCongr (ϕ : B₁ ≃ₐ[R₁] B₂) : (B₁ ≃ₐ[R₁] B₁) ≃* B₂ ≃ₐ[R₁] B₂ where
  __ := equivCongr ϕ ϕ
  toFun ψ := ϕ.symm.trans (ψ.trans ϕ)
  invFun ψ := ϕ.trans (ψ.trans ϕ.symm)
  map_mul' ψ χ := by
    ext
    simp only [mul_apply, trans_apply, symm_apply_apply]

@[simp]
theorem autCongr_refl : autCongr AlgEquiv.refl = MulEquiv.refl (B₁ ≃ₐ[R₁] B₁) := rfl

@[simp]
theorem autCongr_symm (ϕ : B₁ ≃ₐ[R₁] B₂) : (autCongr ϕ).symm = autCongr ϕ.symm :=
  rfl

@[simp]
theorem autCongr_trans (ϕ : B₁ ≃ₐ[R₁] B₂) (ψ : B₂ ≃ₐ[R₁] B₃) :
    (autCongr ϕ).trans (autCongr ψ) = autCongr (ϕ.trans ψ) :=
  rfl

/-- The tautological action by `A₁ ≃ₐ[R] A₁` on `A₁`.

This generalizes `Function.End.applyMulAction`. -/
instance applyMulSemiringAction : MulSemiringAction (A₁ ≃ₐ[R₁] A₁) A₁ where
  smul := (· <| ·)
  smul_zero := map_zero
  smul_add := map_add
  smul_one := map_one
  smul_mul := map_mul
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp]
protected theorem smul_def (f : A₁ ≃ₐ[R₁] A₁) (a : A₁) : f • a = f a :=
  rfl

instance apply_faithfulSMul : FaithfulSMul (A₁ ≃ₐ[R₁] A₁) A₁ :=
  ⟨AlgEquiv.ext⟩

instance apply_smulCommClass {S} [SMul S R₁] [SMul S A₁] [IsScalarTower S R₁ A₁] :
    SMulCommClass S (A₁ ≃ₐ[R₁] A₁) A₁ where
  smul_comm r e a := (e.toLinearEquiv.map_smul_of_tower r a).symm

instance apply_smulCommClass' {S} [SMul S R₁] [SMul S A₁] [IsScalarTower S R₁ A₁] :
    SMulCommClass (A₁ ≃ₐ[R₁] A₁) S A₁ :=
  SMulCommClass.symm _ _ _

instance : MulDistribMulAction (A₁ ≃ₐ[R₁] A₁) A₁ˣ where
  smul := fun f => Units.map f
  one_smul := fun x => by ext; rfl
  mul_smul := fun x y z => by ext; rfl
  smul_mul := fun x y z => by ext; exact map_mul x _ _
  smul_one := fun x => by ext; exact map_one x

@[simp]
theorem smul_units_def (f : A₁ ≃ₐ[R₁] A₁) (x : A₁ˣ) :
    f • x = Units.map f x := rfl

@[simp]
lemma _root_.MulSemiringAction.toRingEquiv_algEquiv (σ : A₁ ≃ₐ[R₁] A₁) :
    MulSemiringAction.toRingEquiv _ A₁ σ = σ := rfl

@[simp]
theorem algebraMap_eq_applyₛₐ (e : A₁ ≃ₛₐ[φ] A₂) {y : R₁} {x : A₁} :
    algebraMap R₂ A₂ (φ y) = e x ↔ algebraMap R₁ A₁ y = x :=
  ⟨fun h => by simpa using e.symm.toAlgHom.algebraMap_eq_applyₛₐ h, fun h =>
    e.toAlgHom.algebraMap_eq_applyₛₐ h⟩

theorem algebraMap_eq_apply [Algebra R₁ A₂] (e : A₁ ≃ₐ[R₁] A₂) {y : R₁} {x : A₁} :
    algebraMap R₁ A₂ y = e x ↔ algebraMap R₁ A₁ y = x :=
 ⟨fun h => by simpa using e.symm.toAlgHom.algebraMap_eq_apply h, fun h =>
    e.toAlgHom.algebraMap_eq_apply h⟩

/-- `AlgEquiv.toAlgHom` as a `MonoidHom`. -/
@[simps] def toAlgHomHom (R A) [CommSemiring R] [Semiring A] [Algebra R A] :
    (A ≃ₐ[R] A) →* A →ₐ[R] A where
  toFun := AlgEquiv.toAlgHom
  map_one' := rfl
  map_mul' _ _ := rfl

/-- `AlgEquiv.toLinearMap` as a `MonoidHom`. -/
@[simps!]
def toLinearMapHom (R A) [CommSemiring R] [Semiring A] [Algebra R A] :
    (A ≃ₐ[R] A) →* Module.End R A :=
  AlgHom.toEnd.comp (toAlgHomHom R A)

lemma pow_toLinearMap (σ : A₁ ≃ₐ[R₁] A₁) (n : ℕ) :
    (σ ^ n).toLinearMap = σ.toLinearMap ^ n :=
  (AlgEquiv.toLinearMapHom R₁ A₁).map_pow σ n

@[simp]
lemma one_toLinearMap :
    (1 : A₁ ≃ₐ[R₁] A₁).toLinearMap = 1 := rfl

/-- The units group of `S →ₐ[R] S` is `S ≃ₐ[R] S`.
See `LinearMap.GeneralLinearGroup.generalLinearEquiv` for the linear map version. -/
@[simps]
def algHomUnitsEquiv (R S : Type*) [CommSemiring R] [Semiring S] [Algebra R S] :
    (S →ₐ[R] S)ˣ ≃* (S ≃ₐ[R] S) where
  toFun := fun f ↦
    { (f : S →ₐ[R] S) with
      invFun := ↑(f⁻¹)
      left_inv := (fun x ↦ show (↑(f⁻¹ * f) : S →ₐ[R] S) x = x by rw [inv_mul_cancel]; rfl)
      right_inv := (fun x ↦ show (↑(f * f⁻¹) : S →ₐ[R] S) x = x by rw [mul_inv_cancel]; rfl) }
  invFun := fun f ↦ ⟨f, f.symm, f.comp_symm, f.symm_comp⟩
  map_mul' := fun _ _ ↦ rfl

/-- See also `Finite.algHom` -/
instance _root_.Finite.algEquiv [Finite (A₁ →ₛₐ[φ] A₂)] : Finite (A₁ ≃ₛₐ[φ] A₂) :=
  Finite.of_injective _ AlgEquiv.coe_algHom_injective

end Semiring

end AlgEquiv

namespace MulSemiringAction

variable {M G : Type*} (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]

section

variable [Group G] [MulSemiringAction G A] [SMulCommClass G R A]

/-- Each element of the group defines an algebra equivalence.

This is a stronger version of `MulSemiringAction.toRingEquiv` and
`DistribMulAction.toLinearEquiv`. -/
@[simps! apply symm_apply toEquiv]
def toAlgEquiv (g : G) : A ≃ₐ[R] A :=
  { MulSemiringAction.toRingEquiv _ _ g, MulSemiringAction.toAlgHom R A g with }

theorem toAlgEquiv_injective [FaithfulSMul G A] :
    Function.Injective (MulSemiringAction.toAlgEquiv R A : G → A ≃ₐ[R] A) := fun _ _ h =>
  eq_of_smul_eq_smul fun r => AlgEquiv.ext_iff.1 h r

variable (G)

/-- Each element of the group defines an algebra equivalence.

This is a stronger version of `MulSemiringAction.toRingAut` and
`DistribMulAction.toModuleEnd`. -/
@[simps]
def toAlgAut : G →* A ≃ₐ[R] A where
  toFun := toAlgEquiv R A
  map_one' := AlgEquiv.ext <| one_smul _
  map_mul' g h := AlgEquiv.ext <| mul_smul g h

end

end MulSemiringAction

section

variable {R S T : Type*} [CommSemiring R] [Semiring S] [Semiring T] [Algebra R S] [Algebra R T]

instance [Subsingleton S] [Subsingleton T] : Unique (S ≃ₐ[R] T) where
  default := AlgEquiv.ofAlgHom default default
    (AlgHom.ext fun _ ↦ Subsingleton.elim _ _)
    (AlgHom.ext fun _ ↦ Subsingleton.elim _ _)
  uniq _ := AlgEquiv.ext fun _ ↦ Subsingleton.elim _ _

@[simp]
lemma AlgEquiv.default_apply [Subsingleton S] [Subsingleton T] (x : S) :
    (default : S ≃ₐ[R] T) x = 0 :=
  rfl

end

/-- The algebra equivalence between `ULift A` and `A`. -/
@[simps! apply, simps! -isSimp symm_apply, pp_with_univ]
def ULift.algEquiv {R : Type u} {A : Type v} [CommSemiring R] [Semiring A] [Algebra R A] :
    ULift.{w} A ≃ₐ[R] A where
  __ := ULift.ringEquiv
  commutes' _ := rfl

@[simp]
lemma ULift.down_algEquiv_symm_apply {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    (a : A) :
    (ULift.algEquiv (R := R).symm a).down = a :=
  rfl

section

universe u₁ u₂ u₃
variable {R S T : Type*} [CommSemiring R] [Semiring S]
  [Semiring T] [Algebra R S] [Algebra R T]

attribute [local instance] ULift.algebra' in
/-- `ULift` is functorial for algebra homomorphisms. -/
@[pp_with_univ]
def AlgHom.ulift (f : S →ₐ[R] T) :
    ULift.{u₁} S →ₐ[ULift.{u₂} R] ULift.{u₃} T where
  __ := AlgHom.comp ULift.algEquiv.symm.toAlgHom (f.comp ULift.algEquiv.toAlgHom)
  commutes' := by simp

@[simp]
lemma AlgHom.down_ulift_apply (f : S →ₐ[R] T) (x : ULift S) :
    (f.ulift x).down = f x.down :=
  rfl

lemma AlgHom.ulift_apply (f : S →ₐ[R] T) (x : ULift S) :
    f.ulift x = ⟨f x.down⟩ :=
  rfl

end

/-- If an `R`-algebra `A` is isomorphic to `R` as `R`-module, then the canonical map `R → A` is an
equivalence of `R`-algebras.

Note that if `e : R ≃ₗ[R] A` is the linear equivalence, then this is not the same as the equivalence
of algebras provided here unless `e 1 = 1`. -/
@[simps] def LinearEquiv.algEquivOfRing
    {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    (e : R ≃ₗ[R] A) : R ≃ₐ[R] A where
  __ := Algebra.ofId R A
  invFun x := e.symm (e 1 * x)
  left_inv x := calc
    e.symm (e 1 * (algebraMap R A) x)
      = e.symm (x • e 1) := by rw [Algebra.smul_def, mul_comm]
    _ = x := by rw [map_smul, e.symm_apply_apply, smul_eq_mul, mul_one]
  right_inv x := calc
    (algebraMap R A) (e.symm (e 1 * x))
      = (algebraMap R A) (e.symm (e 1 * x)) * e (e.symm 1 • 1) := by
          rw [smul_eq_mul, mul_one, e.apply_symm_apply, mul_one]
    _ = x := by rw [map_smul, Algebra.smul_def, mul_left_comm, ← Algebra.smul_def _ (e 1),
          ← map_smul, smul_eq_mul, mul_one, e.apply_symm_apply, ← mul_assoc, ← Algebra.smul_def,
          ← map_smul, smul_eq_mul, mul_one, e.apply_symm_apply, one_mul]

namespace LinearEquiv
variable {R S M₁ M₂ : Type*} [CommSemiring R] [AddCommMonoid M₁] [Module R M₁]
  [AddCommMonoid M₂] [Module R M₂] [Semiring S] [Module S M₁] [Module S M₂]
  [SMulCommClass S R M₁] [SMulCommClass S R M₂] [SMul R S] [IsScalarTower R S M₁]
  [IsScalarTower R S M₂]

variable (R) in
/-- A linear equivalence of two modules induces an equivalence of algebras of their
endomorphisms. -/
@[simps!] def conjAlgEquiv (e : M₁ ≃ₗ[S] M₂) : Module.End S M₁ ≃ₐ[R] Module.End S M₂ where
  __ := e.conjRingEquiv
  commutes' _ := by ext; change e.restrictScalars R _ = _; simp

@[deprecated (since := "2025-12-06")] alias algConj := conjAlgEquiv

theorem conjAlgEquiv_apply (e : M₁ ≃ₗ[S] M₂) (f : Module.End S M₁) :
    e.conjAlgEquiv R f = e.toLinearMap ∘ₗ f ∘ₗ e.symm.toLinearMap := rfl

theorem symm_conjAlgEquiv (e : M₁ ≃ₗ[S] M₂) : (e.conjAlgEquiv R).symm = e.symm.conjAlgEquiv R := rfl

end LinearEquiv
