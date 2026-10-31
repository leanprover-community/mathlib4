/-
Copyright (c) 2026 Kevin Buzzard, Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Salvatore Mercuri
-/
module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Semialgebra.Hom

/-!
# Semialgebra isomorphisms

Let `φ : R →+* S` be a homomorphism of commutative semirings with inverse `ψ`, let `A` be an
`R`-algebra and let `B` be an `S`-algebra. A *`φ`-semialgebra isomorphism* from `A` to `B` is a
ring isomorphism `e : A ≃+* B` lying over `φ`, in the sense that
`e (algebraMap R A r) = algebraMap S B (φ r)` for all `r : R`.

As with `LinearEquiv`, the type is parametrised by an inverse pair `φ`, `ψ`; this is what makes
`SemialgEquiv.symm` available.

As with `SemialgHom` and `AlgHom`, `AlgEquiv` is *not* defined as the special case
`φ = RingHom.id R` of `SemialgEquiv`; the two types are kept separate, and related by
`AlgEquiv.toSemialgEquiv` and `SemialgEquiv.toAlgEquiv`.

## Main definitions

* `SemialgEquiv φ A B`, with notation `A ≃ₛₐ[φ] B`: the type of `φ`-semialgebra isomorphisms
  from `A` to `B`.
* `SemialgEquivClass F φ A B`: the class of types of `φ`-semialgebra isomorphisms.
* `AlgEquiv.toSemialgEquiv`, `SemialgEquiv.toAlgEquiv` and `AlgEquiv.semialgEquivEquiv`: the
  transfer between `A ≃ₐ[R] B` and `A ≃ₛₐ[RingHom.id R] B`.

## Notation

* `A ≃ₛₐ[φ] B` : `φ`-semialgebra isomorphism from `A` to `B`.
-/

@[expose] public section

universe uR uS uA uB

/-- An isomorphism of algebras (denoted `A ≃ₛₐ[φ] B`) is an isomorphism of rings commuting with
the actions of the scalars `R` on `A` and `S` on `B` via the ring homomorphism `φ : R →+* S`. -/
structure SemialgEquiv {R : Type uR} {S : Type uS} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) {ψ : S →+* R} [RingHomInvPair φ ψ] [RingHomInvPair ψ φ]
    (A : Type uA) (B : Type uB) [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
    extends A ≃ B, A ≃* B, A ≃+ B, A ≃+* B where
  /-- A semialgebra isomorphism lies over `φ`. -/
  protected commutes' (r : R) : toFun (algebraMap R A r) = algebraMap S B (φ r)

attribute [nolint docBlame] SemialgEquiv.toRingEquiv
attribute [nolint docBlame] SemialgEquiv.toEquiv
attribute [nolint docBlame] SemialgEquiv.toAddEquiv
attribute [nolint docBlame] SemialgEquiv.toMulEquiv

@[inherit_doc]
notation:50 A " ≃ₛₐ[" φ "] " B => SemialgEquiv φ A B

/-- `SemialgEquivClass F φ A B` states that `F` is a type of `φ`-semialgebra structure preserving
equivalences. You should extend this class when you extend `SemialgEquiv`. -/
class SemialgEquivClass (F : Type*) {R S : outParam Type*} [CommSemiring R] [CommSemiring S]
    (φ : outParam (R →+* S)) {ψ : outParam (S →+* R)} [RingHomInvPair φ ψ] [RingHomInvPair ψ φ]
    (A B : outParam Type*) [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
    [EquivLike F A B] : Prop extends RingEquivClass F A B where
  /-- A semialgebra isomorphism lies over `φ`. -/
  commutes (f : F) (r : R) : f (algebraMap R A r) = algebraMap S B (φ r)

-- Lowered so that `RingEquivClass (A ≃ₐ[R] B) A B` still resolves through
-- `AlgEquiv.instAlgEquivClass` rather than detouring via `AlgEquivClass.toSemialgEquivClass`.
attribute [instance 90] SemialgEquivClass.toRingEquivClass

namespace SemialgEquivClass

variable {F : Type*} {R S : Type*} [CommSemiring R] [CommSemiring S]
  {φ : R →+* S} {ψ : S →+* R} [RingHomInvPair φ ψ] [RingHomInvPair ψ φ]
  {A B : Type*} [Semiring A] [Semiring B] [Algebra R A] [Algebra S B] [EquivLike F A B]

section

variable [SemialgEquivClass F φ A B]

instance (priority := 100) toSemialgHomClass : SemialgHomClass F φ A B where
  __ := ‹SemialgEquivClass F φ A B›

instance (priority := 100) toSemilinearEquivClass : SemilinearEquivClass F φ A B where
  map_smulₛₗ f := map_smulₛₗ f

/-- Turn an element of a type `F` satisfying `SemialgEquivClass F φ A B` into an actual
`SemialgEquiv`. This is declared as the default coercion from `F` to `A ≃ₛₐ[φ] B`. -/
@[coe]
def toSemialgEquiv (f : F) : A ≃ₛₐ[φ] B where
  __ := RingEquivClass.toRingEquiv f
  commutes' := SemialgEquivClass.commutes f

end

/-- Every `AlgEquivClass` is a `SemialgEquivClass` for the identity ring homomorphism. -/
instance (priority := 100) _root_.AlgEquivClass.toSemialgEquivClass {F R A B : Type*}
    [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B] [EquivLike F A B]
    [AlgEquivClass F R A B] : SemialgEquivClass F (RingHom.id R) A B where
  commutes f r := AlgEquivClass.commutes f r

end SemialgEquivClass

namespace SemialgEquiv

section Semiring

variable {R : Type uR} {S : Type uS} [CommSemiring R] [CommSemiring S]
variable {φ : R →+* S} {ψ : S →+* R} [RingHomInvPair φ ψ] [RingHomInvPair ψ φ]
variable {A : Type uA} {B : Type uB} [Semiring A] [Semiring B]
variable [Algebra R A] [Algebra S B]
variable (e : A ≃ₛₐ[φ] B)

section coe

instance : EquivLike (A ≃ₛₐ[φ] B) A B where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by rcases f with ⟨⟨_, _⟩, _⟩; congr

/-- Helper instance since the coercion is not always found. -/
instance : FunLike (A ≃ₛₐ[φ] B) A B where
  coe := DFunLike.coe
  coe_injective := DFunLike.coe_injective

instance : SemialgEquivClass (A ≃ₛₐ[φ] B) φ A B where
  map_add f := f.map_add'
  map_mul f := f.map_mul'
  commutes f := f.commutes'

@[ext]
theorem ext {f g : A ≃ₛₐ[φ] B} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

protected theorem congr_arg {f : A ≃ₛₐ[φ] B} {x x' : A} : x = x' → f x = f x' :=
  DFunLike.congr_arg f

protected theorem congr_fun {f g : A ≃ₛₐ[φ] B} (h : f = g) (x : A) : f x = g x :=
  DFunLike.congr_fun h x

@[simp]
theorem coe_mk {toEquiv map_mul map_add commutes} :
    ⇑(⟨toEquiv, map_mul, map_add, commutes⟩ : A ≃ₛₐ[φ] B) = toEquiv :=
  rfl

@[simp]
theorem mk_coe (e' h₁ h₂ h₃ h₄ h₅) :
    (⟨⟨e, e', h₁, h₂⟩, h₃, h₄, h₅⟩ : A ≃ₛₐ[φ] B) = e :=
  ext fun _ ↦ rfl

@[simp]
theorem toEquiv_eq_coe : e.toEquiv = e :=
  rfl

@[simp]
protected theorem coe_coe {F : Type*} [EquivLike F A B] [SemialgEquivClass F φ A B] (f : F) :
    ⇑(SemialgEquivClass.toSemialgEquiv f) = f :=
  rfl

theorem coe_fun_injective : @Function.Injective (A ≃ₛₐ[φ] B) (A → B) (fun e ↦ (e : A → B)) :=
  DFunLike.coe_injective

instance : CoeOut (A ≃ₛₐ[φ] B) (A ≃+* B) where coe := toRingEquiv

@[simp]
theorem coe_toEquiv : ((e : A ≃ B) : A → B) = e :=
  rfl

@[simp]
lemma toRingEquiv_toRingHom : ((e : A ≃+* B) : A →+* B) = e :=
  rfl

theorem coe_ringEquiv : ((e : A ≃+* B) : A → B) = e := rfl

theorem coe_ringEquiv_injective : Function.Injective ((↑) : (A ≃ₛₐ[φ] B) → A ≃+* B) :=
  fun _ _ h ↦ ext <| RingEquiv.congr_fun h

/-- Interpret a semialgebra isomorphism as a semialgebra homomorphism. -/
@[coe]
def toSemialgHom : A →ₛₐ[φ] B where
  __ := ((e : A ≃+* B) : A →+* B)
  commutes' := e.commutes'

instance : CoeOut (A ≃ₛₐ[φ] B) (A →ₛₐ[φ] B) where coe := SemialgEquiv.toSemialgHom

theorem toSemialgHom_apply (x : A) : e.toSemialgHom x = e x :=
  rfl

@[simp, norm_cast]
theorem coe_toSemialgHom : ⇑e.toSemialgHom = e := rfl

theorem coe_toSemialgHom_injective :
    Function.Injective ((↑) : (A ≃ₛₐ[φ] B) → A →ₛₐ[φ] B) :=
  fun _ _ h ↦ ext <| SemialgHom.congr_fun h

@[simp, norm_cast]
lemma toSemialgHom_toRingHom : (e.toSemialgHom : A →+* B) = e :=
  rfl

/-- The two paths coercion can take to a `RingHom` are equivalent. -/
theorem coe_ringHom_commutes : (e.toSemialgHom : A →+* B) = (e : A →+* B) :=
  rfl

@[simp]
theorem commutes (r : R) : e (algebraMap R A r) = algebraMap S B (φ r) :=
  e.commutes' r

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

/-- Semialgebra isomorphisms are reflexive. -/
@[refl]
def refl : A ≃ₛₐ[RingHom.id R] A where
  __ := RingEquiv.refl A
  commutes' _ := rfl

instance : Inhabited (A ≃ₛₐ[RingHom.id R] A) :=
  ⟨refl⟩

@[simp, norm_cast]
lemma refl_toSemialgHom : (refl : A ≃ₛₐ[RingHom.id R] A).toSemialgHom = SemialgHom.id R A := rfl

@[simp]
lemma refl_toRingEquiv : ((refl : A ≃ₛₐ[RingHom.id R] A) : A ≃+* A) = RingEquiv.refl A := rfl

@[simp]
theorem coe_refl : ⇑(refl : A ≃ₛₐ[RingHom.id R] A) = id :=
  rfl

@[simp]
theorem refl_apply (x : A) : (refl : A ≃ₛₐ[RingHom.id R] A) x = x := rfl

end refl

section symm

/-- Semialgebra isomorphisms are symmetric. -/
@[symm]
def symm (e : A ≃ₛₐ[φ] B) : B ≃ₛₐ[ψ] A where
  __ := e.toRingEquiv.symm
  commutes' r := by
    have h : e (algebraMap R A (ψ r)) = algebraMap S B r := by
      rw [e.commutes, RingHomInvPair.comp_apply_eq₂]
    exact (Equiv.symm_apply_eq e.toEquiv).2 h.symm

theorem invFun_eq_symm {e : A ≃ₛₐ[φ] B} : e.invFun = e.symm :=
  rfl

/-- `simp` normal form of `invFun_eq_symm`. -/
@[simp]
theorem symm_toEquiv_eq_symm {e : A ≃ₛₐ[φ] B} : (e : A ≃ B).symm = e.symm :=
  rfl

@[simp]
theorem symm_symm (e : A ≃ₛₐ[φ] B) : e.symm.symm = e := rfl

theorem symm_bijective : Function.Bijective (symm : (A ≃ₛₐ[φ] B) → B ≃ₛₐ[ψ] A) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]
theorem mk_coe' (e : A ≃ₛₐ[φ] B) (f h₁ h₂ h₃ h₄ h₅) :
    (⟨⟨f, e, h₁, h₂⟩, h₃, h₄, h₅⟩ : B ≃ₛₐ[ψ] A) = e.symm :=
  symm_bijective.injective <| ext fun _ ↦ rfl

@[simp]
theorem refl_symm : (refl : A ≃ₛₐ[RingHom.id R] A).symm = refl :=
  rfl

theorem toRingEquiv_symm (e : A ≃ₛₐ[φ] B) : (e : A ≃+* B).symm = e.symm :=
  rfl

@[simp]
theorem symm_toRingEquiv : (e.symm : B ≃+* A) = (e : A ≃+* B).symm :=
  rfl

@[simp]
theorem symm_toAddEquiv : (e.symm : B ≃+ A) = (e : A ≃+ B).symm :=
  rfl

@[simp]
theorem symm_toMulEquiv : (e.symm : B ≃* A) = (e : A ≃* B).symm :=
  rfl

@[simp]
theorem apply_symm_apply (e : A ≃ₛₐ[φ] B) : ∀ x, e (e.symm x) = x :=
  e.toEquiv.apply_symm_apply

@[simp]
theorem symm_apply_apply (e : A ≃ₛₐ[φ] B) : ∀ x, e.symm (e x) = x :=
  e.toEquiv.symm_apply_apply

theorem symm_apply_eq (e : A ≃ₛₐ[φ] B) {x y} : e.symm x = y ↔ x = e y :=
  e.toEquiv.symm_apply_eq

theorem eq_symm_apply (e : A ≃ₛₐ[φ] B) {x y} : y = e.symm x ↔ e y = x :=
  e.toEquiv.eq_symm_apply

@[simp]
theorem coe_apply_coe_coe_symm_apply {F : Type*} [EquivLike F A B] [SemialgEquivClass F φ A B]
    (f : F) (x : B) : f ((SemialgEquivClass.toSemialgEquiv f).symm x) = x :=
  EquivLike.right_inv f x

@[simp]
theorem coe_coe_symm_apply_coe_apply {F : Type*} [EquivLike F A B] [SemialgEquivClass F φ A B]
    (f : F) (x : A) : (SemialgEquivClass.toSemialgEquiv f).symm (f x) = x :=
  EquivLike.left_inv f x

@[simp]
theorem symm_mk (e : A ≃ B) (h₁ h₂ h₃) : dsimp%
    (mk e h₁ h₂ h₃ : A ≃ₛₐ[φ] B).symm =
      { (mk e h₁ h₂ h₃ : A ≃ₛₐ[φ] B).symm with
        toEquiv := e.symm } :=
  rfl

@[simp]
theorem comp_symm (e : A ≃ₛₐ[φ] B) :
    e.toSemialgHom.comp e.symm.toSemialgHom = SemialgHom.id S B := by
  ext
  simp

@[simp]
theorem symm_comp (e : A ≃ₛₐ[φ] B) :
    e.symm.toSemialgHom.comp e.toSemialgHom = SemialgHom.id R A := by
  ext
  simp

theorem leftInverse_symm (e : A ≃ₛₐ[φ] B) : Function.LeftInverse e.symm e :=
  e.left_inv

theorem rightInverse_symm (e : A ≃ₛₐ[φ] B) : Function.RightInverse e.symm e :=
  e.right_inv

lemma image_symm_eq_preimage (e : A ≃ₛₐ[φ] B) (s : Set B) : e.symm '' s = e ⁻¹' s :=
  e.toEquiv.image_symm_eq_preimage _

end symm

section simps

/-- See Note [custom simps projection] -/
def Simps.apply (e : A ≃ₛₐ[φ] B) : A → B :=
  e

/-- See Note [custom simps projection] -/
def Simps.toEquiv (e : A ≃ₛₐ[φ] B) : A ≃ B :=
  e

/-- See Note [custom simps projection] -/
def Simps.symm_apply (e : A ≃ₛₐ[φ] B) : B → A :=
  e.symm

initialize_simps_projections SemialgEquiv (toFun → apply, invFun → symm_apply)

end simps

section ofSemialgHom

/-- Construct a semialgebra isomorphism from a pair of mutually inverse semialgebra
homomorphisms. -/
def ofSemialgHom (f : A →ₛₐ[φ] B) (g : B →ₛₐ[ψ] A) (h₁ : f.comp g = SemialgHom.id S B)
    (h₂ : g.comp f = SemialgHom.id R A) : A ≃ₛₐ[φ] B where
  __ := f
  toFun := f
  invFun := g
  left_inv := SemialgHom.ext_iff.1 h₂
  right_inv := SemialgHom.ext_iff.1 h₁
  commutes' := f.commutes'

@[simp]
theorem toSemialgHom_ofSemialgHom (f : A →ₛₐ[φ] B) (g : B →ₛₐ[ψ] A) (h₁ h₂) :
    (ofSemialgHom f g h₁ h₂ : A →ₛₐ[φ] B) = f :=
  SemialgHom.ext fun _ ↦ rfl

@[simp]
theorem ofSemialgHom_toSemialgHom (f : A ≃ₛₐ[φ] B) (g : B →ₛₐ[ψ] A) (h₁ h₂) :
    ofSemialgHom (↑f) g h₁ h₂ = f :=
  ext fun _ ↦ rfl

theorem ofSemialgHom_symm (f : A →ₛₐ[φ] B) (g : B →ₛₐ[ψ] A) (h₁ h₂) :
    (ofSemialgHom f g h₁ h₂).symm = ofSemialgHom g f h₂ h₁ :=
  rfl

end ofSemialgHom

section toLinearEquiv

/-- Forgetting the multiplicative structure, a semialgebra isomorphism is a semilinear
equivalence. -/
@[coe, simps! apply]
def toLinearEquiv (e : A ≃ₛₐ[φ] B) : A ≃ₛₗ[φ] B where
  toAddEquiv := e.toAddEquiv
  map_smul' := map_smulₛₗ e

instance : CoeOut (A ≃ₛₐ[φ] B) (A ≃ₛₗ[φ] B) where coe := toLinearEquiv

@[simp]
theorem toLinearEquiv_refl :
    (refl : A ≃ₛₐ[RingHom.id R] A).toLinearEquiv = LinearEquiv.refl R A := rfl

@[simp]
theorem toLinearEquiv_symm (e : A ≃ₛₐ[φ] B) : e.symm.toLinearEquiv = e.toLinearEquiv.symm :=
  rfl

@[simp]
theorem coe_toLinearEquiv (e : A ≃ₛₐ[φ] B) : ⇑e.toLinearEquiv = e := rfl

@[simp]
theorem coe_symm_toLinearEquiv (e : A ≃ₛₐ[φ] B) : ⇑e.toLinearEquiv.symm = e.symm := rfl

theorem toLinearEquiv_injective : Function.Injective (toLinearEquiv : _ → A ≃ₛₗ[φ] B) :=
  fun _ _ h ↦ ext <| LinearEquiv.congr_fun h

/-- Interpret a semialgebra isomorphism as a semilinear map. -/
abbrev toLinearMap : A →ₛₗ[φ] B :=
  e.toLinearEquiv

@[simp]
lemma toSemialgHom_toLinearMap : e.toSemialgHom.toLinearMap = e.toLinearEquiv.toLinearMap := rfl

theorem toLinearEquiv_toLinearMap : e.toLinearEquiv.toLinearMap = e.toLinearMap :=
  rfl

theorem toLinearMap_ofSemialgHom (f : A →ₛₐ[φ] B) (g : B →ₛₐ[ψ] A) (h₁ h₂) :
    (ofSemialgHom f g h₁ h₂).toLinearMap = f.toLinearMap :=
  LinearMap.ext fun _ ↦ rfl

@[simp]
theorem toLinearMap_apply (x : A) : e.toLinearMap x = e x :=
  rfl

theorem toLinearMap_injective : Function.Injective (toLinearMap : _ → A →ₛₗ[φ] B) :=
  fun _ _ h ↦ ext <| LinearMap.congr_fun h

end toLinearEquiv

section ofLinearEquiv

variable (l : A ≃ₛₗ[φ] B) (map_one : l 1 = 1) (map_mul : ∀ x y : A, l (x * y) = l x * l y)

/-- Upgrade a semilinear equivalence to a semialgebra isomorphism, given that it distributes over
multiplication and the identity. -/
@[simps! apply]
def ofLinearEquiv : A ≃ₛₐ[φ] B where
  __ := l
  toFun := l
  invFun := l.symm
  map_mul' := map_mul
  commutes' := by simp [Algebra.algebraMap_eq_smul_one, map_smulₛₗ, map_one]

@[simp]
theorem ofLinearEquiv_symm :
    (ofLinearEquiv l map_one map_mul).symm =
      ofLinearEquiv l.symm
        (_root_.map_one (ofLinearEquiv l map_one map_mul).symm)
        (_root_.map_mul (ofLinearEquiv l map_one map_mul).symm) :=
  rfl

@[simp]
theorem ofLinearEquiv_toLinearEquiv (map_one) (map_mul) :
    ofLinearEquiv e.toLinearEquiv map_one map_mul = e :=
  rfl

@[simp]
theorem toLinearEquiv_ofLinearEquiv : toLinearEquiv (ofLinearEquiv l map_one map_mul) = l :=
  rfl

end ofLinearEquiv

section ofRingEquiv

/-- Promote a `RingEquiv` lying over `φ` to a `SemialgEquiv`. -/
@[simps apply symm_apply toEquiv]
def ofRingEquiv {f : A ≃+* B} (hf : ∀ x, f (algebraMap R A x) = algebraMap S B (φ x)) :
    A ≃ₛₐ[φ] B :=
  { f with
    toFun := f
    invFun := f.symm
    commutes' := hf }

end ofRingEquiv

section ofBijective

/-- Promote a bijective semialgebra homomorphism to a semialgebra isomorphism. -/
noncomputable def ofBijective (f : A →ₛₐ[φ] B) (hf : Function.Bijective f) : A ≃ₛₐ[φ] B :=
  { RingEquiv.ofBijective (f : A →+* B) hf, f with }

lemma ofBijective_apply (f : A →ₛₐ[φ] B) (hf : Function.Bijective f) (a : A) :
    (ofBijective f hf) a = f a := rfl

@[simp]
lemma coe_ofBijective (f : A →ₛₐ[φ] B) (hf : Function.Bijective f) :
    ⇑(ofBijective f hf) = f := rfl

@[simp]
lemma toSemialgHom_ofBijective (f : A →ₛₐ[φ] B) (hf : Function.Bijective f) :
    (ofBijective f hf).toSemialgHom = f := rfl

@[simp]
lemma toLinearMap_ofBijective (f : A →ₛₐ[φ] B) (hf : Function.Bijective f) :
    (ofBijective f hf).toLinearMap = f.toLinearMap := rfl

lemma ofBijective_apply_symm_apply (f : A →ₛₐ[φ] B) (hf : Function.Bijective f) (x : B) :
    f ((ofBijective f hf).symm x) = x :=
  (ofBijective f hf).apply_symm_apply x

@[simp]
lemma ofBijective_symm_apply_apply (f : A →ₛₐ[φ] B) (hf : Function.Bijective f) (x : A) :
    (ofBijective f hf).symm (f x) = x :=
  (ofBijective f hf).symm_apply_apply x

end ofBijective

@[simp]
theorem algebraMap_eq_apply (e : A ≃ₛₐ[φ] B) {y : R} {x : A} :
    algebraMap S B (φ y) = e x ↔ algebraMap R A y = x := by
  refine ⟨fun h ↦ ?_, fun h ↦ e.toSemialgHom.algebraMap_eq_apply h⟩
  have h' := congrArg e.symm h
  rwa [e.symm_apply_apply, e.symm.commutes, RingHomInvPair.comp_apply_eq] at h'

/-- See also `Finite.algHom`. -/
instance [Finite (A →ₛₐ[φ] B)] : Finite (A ≃ₛₐ[φ] B) :=
  Finite.of_injective _ coe_toSemialgHom_injective

-- TODO Morally this is just `isLocalHom_equiv`: can we obviate the need for this instance?
instance : IsLocalHom e.toSemialgHom := by
  have : IsLocalHom e.toRingEquiv := inferInstance
  exact ⟨this.map_nonunit⟩

end Semiring

section trans

variable {R₁ : Type*} {R₂ : Type*} {R₃ : Type*}
variable [CommSemiring R₁] [CommSemiring R₂] [CommSemiring R₃]
variable {A₁ : Type*} {A₂ : Type*} {A₃ : Type*}
variable [Semiring A₁] [Semiring A₂] [Semiring A₃]
variable [Algebra R₁ A₁] [Algebra R₂ A₂] [Algebra R₃ A₃]
variable {φ₁₂ : R₁ →+* R₂} {φ₂₁ : R₂ →+* R₁} [RingHomInvPair φ₁₂ φ₂₁] [RingHomInvPair φ₂₁ φ₁₂]
variable {φ₂₃ : R₂ →+* R₃} {φ₃₂ : R₃ →+* R₂} [RingHomInvPair φ₂₃ φ₃₂] [RingHomInvPair φ₃₂ φ₂₃]
variable {φ₁₃ : R₁ →+* R₃} {φ₃₁ : R₃ →+* R₁} [RingHomInvPair φ₁₃ φ₃₁] [RingHomInvPair φ₃₁ φ₁₃]
variable [RingHomCompTriple φ₁₂ φ₂₃ φ₁₃]
variable (e₁₂ : A₁ ≃ₛₐ[φ₁₂] A₂) (e₂₃ : A₂ ≃ₛₐ[φ₂₃] A₃)

/-- Semialgebra isomorphisms are transitive. -/
@[trans]
def trans : A₁ ≃ₛₐ[φ₁₃] A₃ where
  __ := e₁₂.toRingEquiv.trans e₂₃.toRingEquiv
  commutes' r := by simp

@[simp]
theorem coe_trans : ⇑(e₁₂.trans e₂₃) = e₂₃ ∘ e₁₂ :=
  rfl

@[simp]
theorem trans_apply (x : A₁) : (e₁₂.trans e₂₃) x = e₂₃ (e₁₂ x) := rfl

@[simp]
theorem symm_trans_apply (x : A₃) :
    (e₁₂.trans e₂₃).symm x = e₁₂.symm (e₂₃.symm x) :=
  rfl

@[simp, norm_cast]
lemma toRingHom_trans : (e₁₂.trans e₂₃ : A₁ →+* A₃) = .comp (e₂₃ : A₂ →+* A₃) (e₁₂ : A₁ →+* A₂) :=
  rfl

@[simp, norm_cast]
lemma toSemialgHom_trans :
    (e₁₂.trans e₂₃).toSemialgHom = e₂₃.toSemialgHom.comp e₁₂.toSemialgHom :=
  rfl

@[simp]
theorem trans_toLinearMap :
    (e₁₂.trans e₂₃).toLinearMap = e₂₃.toLinearMap.comp e₁₂.toLinearMap :=
  rfl

@[simp]
theorem toLinearEquiv_trans [RingHomCompTriple φ₃₂ φ₂₁ φ₃₁] :
    (e₁₂.trans e₂₃).toLinearEquiv = e₁₂.toLinearEquiv.trans e₂₃.toLinearEquiv :=
  rfl

end trans

section symmTrans

variable {R S : Type*} [CommSemiring R] [CommSemiring S]
variable {φ : R →+* S} {ψ : S →+* R} [RingHomInvPair φ ψ] [RingHomInvPair ψ φ]
variable {A B : Type*} [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]

@[simp]
lemma self_trans_symm (e : A ≃ₛₐ[φ] B) : e.trans e.symm = refl := by ext; simp

@[simp]
lemma symm_trans_self (e : A ≃ₛₐ[φ] B) : e.symm.trans e = refl := by ext; simp

end symmTrans

section Subsingleton

variable {R S : Type*} [CommSemiring R] [CommSemiring S]
variable {φ : R →+* S} {ψ : S →+* R} [RingHomInvPair φ ψ] [RingHomInvPair ψ φ]
variable {A B : Type*} [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
variable [Subsingleton A] [Subsingleton B]

instance : Unique (A ≃ₛₐ[φ] B) where
  default := ofSemialgHom default default (SemialgHom.ext fun _ ↦  Subsingleton.elim _ _)
    (SemialgHom.ext fun _ ↦  Subsingleton.elim _ _)
  uniq _ := ext fun _ ↦ Subsingleton.elim _ _

@[simp]
lemma default_apply (x : A) : (default : A ≃ₛₐ[φ] B) x = 0 :=
  rfl

end Subsingleton

end SemialgEquiv

section transfer

variable {R : Type uR} [CommSemiring R] {A : Type uA} {B : Type uB} [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B]

/-- An `R`-algebra isomorphism is the same thing as a `RingHom.id R`-semialgebra isomorphism. -/
def AlgEquiv.toSemialgEquiv (e : A ≃ₐ[R] B) : A ≃ₛₐ[RingHom.id R] B where
  __ := (e : A ≃+* B)
  commutes' := e.commutes'

/-- A `RingHom.id R`-semialgebra isomorphism is the same thing as an `R`-algebra isomorphism. -/
def SemialgEquiv.toAlgEquiv (e : A ≃ₛₐ[RingHom.id R] B) : A ≃ₐ[R] B where
  __ := (e : A ≃+* B)
  commutes' := e.commutes'

@[simp]
theorem AlgEquiv.coe_toSemialgEquiv (e : A ≃ₐ[R] B) : ⇑e.toSemialgEquiv = e := rfl

@[simp]
theorem AlgEquiv.toRingEquiv_toSemialgEquiv (e : A ≃ₐ[R] B) :
    (e.toSemialgEquiv : A ≃+* B) = (e : A ≃+* B) := rfl

@[simp]
theorem SemialgEquiv.coe_toAlgEquiv (e : A ≃ₛₐ[RingHom.id R] B) : ⇑e.toAlgEquiv = e := rfl

@[simp]
theorem SemialgEquiv.toRingEquiv_toAlgEquiv (e : A ≃ₛₐ[RingHom.id R] B) :
    (e.toAlgEquiv : A ≃+* B) = (e : A ≃+* B) := rfl

@[simp]
theorem SemialgEquiv.toAlgEquiv_toSemialgEquiv (e : A ≃ₐ[R] B) :
    e.toSemialgEquiv.toAlgEquiv = e := rfl

@[simp]
theorem AlgEquiv.toSemialgEquiv_toAlgEquiv (e : A ≃ₛₐ[RingHom.id R] B) :
    e.toAlgEquiv.toSemialgEquiv = e := rfl

variable (R A B) in
/-- `R`-algebra isomorphisms are the same thing as `RingHom.id R`-semialgebra isomorphisms. -/
@[simps]
def AlgEquiv.semialgEquivEquiv : (A ≃ₐ[R] B) ≃ (A ≃ₛₐ[RingHom.id R] B) where
  toFun e := e.toSemialgEquiv
  invFun e := e.toAlgEquiv

@[simp]
theorem AlgEquiv.toSemialgEquiv_refl :
    (AlgEquiv.refl : A ≃ₐ[R] A).toSemialgEquiv = SemialgEquiv.refl := rfl

@[simp]
theorem SemialgEquiv.toAlgEquiv_refl :
    (SemialgEquiv.refl : A ≃ₛₐ[RingHom.id R] A).toAlgEquiv = AlgEquiv.refl := rfl

@[simp]
theorem AlgEquiv.toSemialgHom_toSemialgEquiv (e : A ≃ₐ[R] B) :
    e.toSemialgEquiv.toSemialgHom = (e : A →ₐ[R] B).toSemialgHom := rfl

theorem AlgEquiv.toSemialgEquiv_injective :
    Function.Injective (AlgEquiv.toSemialgEquiv : (A ≃ₐ[R] B) → A ≃ₛₐ[RingHom.id R] B) :=
  fun _ _ h ↦ AlgEquiv.ext fun x ↦ SemialgEquiv.congr_fun h x

theorem SemialgEquiv.toAlgEquiv_injective :
    Function.Injective (SemialgEquiv.toAlgEquiv : (A ≃ₛₐ[RingHom.id R] B) → A ≃ₐ[R] B) :=
  fun _ _ h ↦ SemialgEquiv.ext fun x ↦ AlgEquiv.congr_fun h x

@[simp]
theorem AlgEquiv.toSemialgEquiv_symm (e : A ≃ₐ[R] B) :
    e.symm.toSemialgEquiv = e.toSemialgEquiv.symm := rfl

@[simp]
theorem SemialgEquiv.toAlgEquiv_symm (e : A ≃ₛₐ[RingHom.id R] B) :
    e.symm.toAlgEquiv = e.toAlgEquiv.symm := rfl

@[simp]
theorem AlgEquiv.toSemialgEquiv_toLinearEquiv (e : A ≃ₐ[R] B) :
    e.toSemialgEquiv.toLinearEquiv = e.toLinearEquiv := rfl

variable {C : Type*} [Semiring C] [Algebra R C]

@[simp]
theorem AlgEquiv.toSemialgEquiv_trans (e₁ : A ≃ₐ[R] B) (e₂ : B ≃ₐ[R] C) :
    (e₁.trans e₂).toSemialgEquiv = e₁.toSemialgEquiv.trans e₂.toSemialgEquiv := rfl

@[simp]
theorem SemialgEquiv.toAlgEquiv_trans (e₁ : A ≃ₛₐ[RingHom.id R] B)
    (e₂ : B ≃ₛₐ[RingHom.id R] C) :
    (e₁.trans e₂).toAlgEquiv = e₁.toAlgEquiv.trans e₂.toAlgEquiv := rfl

end transfer
