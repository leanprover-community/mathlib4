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

universe uR uS uA uB

/-- An equivalence of algebras (denoted as `A ≃ₐ[R] B`)
is an equivalence of rings commuting with the actions of scalars. -/
structure AlgEquiv (R : Type uR) [CommSemiring R] (A : Type uA) (B : Type uB) [Semiring A]
  [Semiring B] [Algebra R A] [Algebra R B] extends A ≃ B, A ≃* B, A ≃+ B, A ≃+* B where
  /-- An equivalence of algebras commutes with the action of scalars. -/
  protected commutes' : ∀ r : R, toFun (algebraMap R A r) = algebraMap R B r

attribute [nolint docBlame] AlgEquiv.toRingEquiv
attribute [nolint docBlame] AlgEquiv.toEquiv
attribute [nolint docBlame] AlgEquiv.toAddEquiv
attribute [nolint docBlame] AlgEquiv.toMulEquiv

@[inherit_doc]
notation:50 A " ≃ₐ[" R "] " B => AlgEquiv R A B

/-- `AlgEquivClass F R A B` states that `F` is a type of algebra structure preserving
  equivalences. You should extend this class when you extend `AlgEquiv`. -/
class AlgEquivClass (F : Type*) (R : outParam Type*) [CommSemiring R] (A B : outParam Type*)
    [Semiring A] [Semiring B] [Algebra R A] [Algebra R B] [EquivLike F A B] : Prop
    extends RingEquivClass F A B where
  /-- An equivalence of algebras commutes with the action of scalars. -/
  commutes : ∀ (f : F) (r : R), f (algebraMap R A r) = algebraMap R B r

namespace AlgEquivClass

variable {F : Type*} {R : Type*} [CommSemiring R]
variable {A B : Type*} [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
variable [EquivLike F A B] [AlgEquivClass F R A B]

-- See note [lower instance priority]
instance (priority := 100) toAlgHomClass : AlgHomClass F R A B where __ := ‹AlgEquivClass F R A B›

instance (priority := 100) toLinearEquivClass : LinearEquivClass F R A B where
  map_smulₛₗ := fun f => map_smulₛₗ f

/-- Turn an element of a type `F` satisfying `AlgEquivClass F R A B` into an actual `AlgEquiv`.
This is declared as the default coercion from `F` to `A ≃ₐ[R] B`. -/
@[coe]
def toAlgEquiv (f : F) : A ≃ₐ[R] B :=
  { (f : A ≃ B), (RingEquivClass.toRingEquiv f : A ≃+* B) with commutes' := commutes f }

end AlgEquivClass

namespace AlgEquiv

section Semiring

variable {R : Type uR} [CommSemiring R]
variable {A : Type uA} {B : Type uB} [Semiring A] [Semiring B]
variable [Algebra R A] [Algebra R B]
variable (e : A ≃ₐ[R] B)

section coe

instance : EquivLike (A ≃ₐ[R] B) A B where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by
    obtain ⟨⟨f, _⟩, _⟩ := f
    obtain ⟨⟨g, _⟩, _⟩ := g
    congr

/-- Helper instance since the coercion is not always found. -/
instance : FunLike (A ≃ₐ[R] B) A B where
  coe := DFunLike.coe
  coe_injective' := DFunLike.coe_injective'

instance : AlgEquivClass (A ≃ₐ[R] B) R A B where
  map_add f := f.map_add'
  map_mul f := f.map_mul'
  commutes f := f.commutes'

@[ext]
theorem ext {f g : A ≃ₐ[R] B} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

protected theorem congr_arg {f : A ≃ₐ[R] B} {x x' : A} : x = x' → f x = f x' :=
  DFunLike.congr_arg f

protected theorem congr_fun {f g : A ≃ₐ[R] B} (h : f = g) (x : A) : f x = g x :=
  DFunLike.congr_fun h x

@[simp]
theorem coe_mk {toEquiv map_mul map_add commutes} :
    ⇑(⟨toEquiv, map_mul, map_add, commutes⟩ : A ≃ₐ[R] B) = toEquiv :=
  rfl

@[simp]
theorem mk_coe (e : A ≃ₐ[R] B) (e' h₁ h₂ h₃ h₄ h₅) :
    (⟨⟨e, e', h₁, h₂⟩, h₃, h₄, h₅⟩ : A ≃ₐ[R] B) = e :=
  ext fun _ => rfl

@[simp]
theorem toEquiv_eq_coe : e.toEquiv = e :=
  rfl

@[simp]
protected theorem coe_coe {F : Type*} [EquivLike F A B] [AlgEquivClass F R A B] (f : F) :
    ⇑(AlgEquivClass.toAlgEquiv f) = f :=
  rfl

theorem coe_fun_injective : @Function.Injective (A ≃ₐ[R] B) (A → B) fun e => (e : A → B) :=
  DFunLike.coe_injective

instance : CoeOut (A ≃ₐ[R] B) (A ≃+* B) where coe := AlgEquiv.toRingEquiv

@[simp]
theorem coe_toEquiv : ((e : A ≃ B) : A → B) = e :=
  rfl

@[deprecated "Now a syntactic equality" (since := "2026-04-09"), nolint synTaut]
theorem toRingEquiv_eq_coe : e.toRingEquiv = e :=
  rfl

@[simp]
lemma toRingEquiv_toRingHom : ((e : A ≃+* B) : A →+* B) = e :=
  rfl

@[simp]
theorem coe_ringEquiv : ((e : A ≃+* B) : A → B) = e :=
  rfl

theorem coe_ringEquiv' : (e.toRingEquiv : A → B) = e :=
  rfl

theorem coe_ringEquiv_injective : Function.Injective ((↑) : (A ≃ₐ[R] B) → A ≃+* B) :=
  fun _ _ h => ext <| RingEquiv.congr_fun h

/-- Interpret an algebra equivalence as an algebra homomorphism.

This definition is included for symmetry with the other `to*Hom` projections.
The `simp` normal form is to use the coercion of the `AlgHomClass.coeTC` instance. -/
@[coe]
def toAlgHom : A →ₐ[R] B :=
  { e with
    map_one' := map_one e
    map_zero' := map_zero e }

instance : CoeOut (A ≃ₐ[R] B) (A →ₐ[R] B) where coe := AlgEquiv.toAlgHom

@[deprecated "Now a syntactic equality" (since := "2026-04-29"), nolint synTaut]
theorem toAlgHom_eq_coe : e.toAlgHom = e :=
  rfl

theorem toAlgHom_apply (x : A) : e.toAlgHom x = e x :=
  rfl

@[simp, norm_cast]
theorem coe_toAlgHom :  DFunLike.coe e.toAlgHom = e := rfl

@[deprecated AlgEquiv.coe_toAlgHom (since := "2026-05-05")]
theorem coe_algHom : DFunLike.coe e.toAlgHom = DFunLike.coe e :=
  rfl

theorem coe_toAlgHom_injective : Function.Injective ((↑) : (A ≃ₐ[R] B) → A →ₐ[R] B) :=
  fun _ _ h => ext <| AlgHom.congr_fun h

@[deprecated AlgEquiv.coe_toAlgHom_injective (since := "2026-05-05")]
theorem coe_algHom_injective : Function.Injective ((↑) : (A ≃ₐ[R] B) → A →ₐ[R] B) :=
  fun _ _ h => ext <| AlgHom.congr_fun h

@[simp, norm_cast]
lemma toAlgHom_toRingHom : ((e : A →ₐ[R] B) : A →+* B) = e :=
  rfl

/-- The two paths coercion can take to a `RingHom` are equivalent -/
theorem coe_ringHom_commutes : ((e : A →ₐ[R] B) : A →+* B) = ((e : A ≃+* B) : A →+* B) :=
  rfl

@[simp]
theorem commutes : ∀ r : R, e (algebraMap R A r) = algebraMap R B r :=
  e.commutes'

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
def refl : A ≃ₐ[R] A :=
  { (.refl _ : A ≃+* A) with commutes' := fun _ => rfl }

instance : Inhabited (A ≃ₐ[R] A) :=
  ⟨refl⟩

@[simp, norm_cast] lemma refl_toAlgHom : (refl : A ≃ₐ[R] A) = AlgHom.id R A := rfl
@[simp, norm_cast] lemma refl_toRingHom : (refl : A ≃ₐ[R] A) = RingHom.id A := rfl

@[simp]
theorem coe_refl : ⇑(refl : A ≃ₐ[R] A) = id :=
  rfl

end refl

section symm

/-- Algebra equivalences are symmetric. -/
@[symm]
def symm (e : A ≃ₐ[R] B) : B ≃ₐ[R] A :=
  { e.toRingEquiv.symm with
    commutes' := fun r => by
      rw [← e.toRingEquiv.symm_apply_apply (algebraMap R A r)]
      congr
      simp }

theorem invFun_eq_symm {e : A ≃ₐ[R] B} : e.invFun = e.symm :=
  rfl

@[simp]
theorem coe_apply_coe_coe_symm_apply {F : Type*} [EquivLike F A B] [AlgEquivClass F R A B]
    (f : F) (x : B) :
    f ((AlgEquivClass.toAlgEquiv f).symm x) = x :=
  EquivLike.right_inv f x

@[simp]
theorem coe_coe_symm_apply_coe_apply {F : Type*} [EquivLike F A B] [AlgEquivClass F R A B]
    (f : F) (x : A) :
    (AlgEquivClass.toAlgEquiv f).symm (f x) = x :=
  EquivLike.left_inv f x

/-- `simp` normal form of `invFun_eq_symm` -/
@[simp]
theorem symm_toEquiv_eq_symm {e : A ≃ₐ[R] B} : (e : A ≃ B).symm = e.symm :=
  rfl

@[simp]
theorem symm_symm (e : A ≃ₐ[R] B) : e.symm.symm = e := rfl

theorem symm_bijective : Function.Bijective (symm : (A ≃ₐ[R] B) → B ≃ₐ[R] A) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]
theorem mk_coe' (e : A ≃ₐ[R] B) (f h₁ h₂ h₃ h₄ h₅) :
    (⟨⟨f, e, h₁, h₂⟩, h₃, h₄, h₅⟩ : B ≃ₐ[R] A) = e.symm :=
  symm_bijective.injective <| ext fun _ => rfl

/-- Auxiliary definition to avoid looping in `dsimp` with `AlgEquiv.symm_mk`. -/
protected def symm_mk.aux (f f') (h₁ h₂ h₃ h₄ h₅) :=
  (⟨⟨f, f', h₁, h₂⟩, h₃, h₄, h₅⟩ : A ≃ₐ[R] B).symm

@[simp]
theorem symm_mk (f f') (h₁ h₂ h₃ h₄ h₅) :
    (⟨⟨f, f', h₁, h₂⟩, h₃, h₄, h₅⟩ : A ≃ₐ[R] B).symm =
      { symm_mk.aux f f' h₁ h₂ h₃ h₄ h₅ with
        toFun := f'
        invFun := f } :=
  rfl

@[simp]
theorem refl_symm : (AlgEquiv.refl : A ≃ₐ[R] A).symm = AlgEquiv.refl :=
  rfl

theorem toRingEquiv_symm : (e : A ≃+* B).symm = e.symm :=
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
theorem apply_symm_apply (e : A ≃ₐ[R] B) : ∀ x, e (e.symm x) = x :=
  e.toEquiv.apply_symm_apply

@[simp]
theorem symm_apply_apply (e : A ≃ₐ[R] B) : ∀ x, e.symm (e x) = x :=
  e.toEquiv.symm_apply_apply

theorem symm_apply_eq (e : A ≃ₐ[R] B) {x y} : e.symm x = y ↔ x = e y :=
  e.toEquiv.symm_apply_eq

theorem eq_symm_apply (e : A ≃ₐ[R] B) {x y} : y = e.symm x ↔ e y = x :=
  e.toEquiv.eq_symm_apply

@[simp]
theorem comp_symm (e : A ≃ₐ[R] B) : AlgHom.comp (e : A →ₐ[R] B) ↑e.symm = AlgHom.id R B := by
  ext
  simp

@[simp]
theorem symm_comp (e : A ≃ₐ[R] B) : AlgHom.comp ↑e.symm (e : A →ₐ[R] B) = AlgHom.id R A := by
  ext
  simp

theorem leftInverse_symm (e : A ≃ₐ[R] B) : Function.LeftInverse e.symm e :=
  e.left_inv

theorem rightInverse_symm (e : A ≃ₐ[R] B) : Function.RightInverse e.symm e :=
  e.right_inv

end symm

section simps

/-- See Note [custom simps projection] -/
def Simps.apply (e : A ≃ₐ[R] B) : A → B :=
  e

/-- See Note [custom simps projection] -/
def Simps.toEquiv (e : A ≃ₐ[R] B) : A ≃ B :=
  e

/-- See Note [custom simps projection] -/
def Simps.symm_apply (e : A ≃ₐ[R] B) : B → A :=
  e.symm

initialize_simps_projections AlgEquiv (toFun → apply, invFun → symm_apply)

end simps

section cast

/-- `Equiv.cast (congrArg _ h)` as an algebra equiv.

Note that unlike `Equiv.cast`, this takes an equality of indices rather than an equality of types,
to avoid having to deal with an equality of the algebraic structure itself. -/
@[simps!]
protected def cast
    {ι : Type*} {A : ι → Type*} [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)] {i j : ι} (h : i = j) :
    A i ≃ₐ[R] A j where
  __ := RingEquiv.cast h
  commutes' _ := by cases h; rfl

end cast

section OfAlgHom

/-- If an algebra morphism has an inverse, it is an algebra isomorphism. -/
@[simps]
def ofAlgHom (f : A →ₐ[R] B) (g : B →ₐ[R] A) (h₁ : f.comp g = AlgHom.id R B)
    (h₂ : g.comp f = AlgHom.id R A) : A ≃ₐ[R] B :=
  { f with
    toFun := f
    invFun := g
    left_inv := AlgHom.ext_iff.1 h₂
    right_inv := AlgHom.ext_iff.1 h₁ }

theorem coe_toAlgHom_ofAlgHom (f : A →ₐ[R] B) (g : B →ₐ[R] A) (h₁ h₂) :
    ↑(ofAlgHom f g h₁ h₂) = f :=
  rfl

@[deprecated AlgEquiv.coe_toAlgHom_ofAlgHom (since := "2026-05-05")]
theorem coe_algHom_ofAlgHom (f : A →ₐ[R] B) (g : B →ₐ[R] A) (h₁ h₂) :
    ↑(ofAlgHom f g h₁ h₂) = f :=
  rfl

@[simp]
theorem ofAlgHom_coe_toAlgHom (f : A ≃ₐ[R] B) (g : B →ₐ[R] A) (h₁ h₂) :
    ofAlgHom (↑f) g h₁ h₂ = f :=
  ext fun _ => rfl

@[deprecated AlgEquiv.ofAlgHom_coe_toAlgHom (since := "2026-05-05")]
theorem ofAlgHom_coe_algHom (f : A ≃ₐ[R] B) (g : B →ₐ[R] A) (h₁ h₂) :
    ofAlgHom (↑f) g h₁ h₂ = f :=
  ext fun _ => rfl

theorem ofAlgHom_symm (f : A →ₐ[R] B) (g : B →ₐ[R] A) (h₁ h₂) :
    (ofAlgHom f g h₁ h₂).symm = ofAlgHom g f h₂ h₁ :=
  rfl

end OfAlgHom

section ToLinearEquiv

/-- Forgetting the multiplicative structures, an equivalence of algebras is a linear equivalence. -/
@[simps apply]
def toLinearEquiv (e : A ≃ₐ[R] B) : A ≃ₗ[R] B :=
  { e with
    toFun := e
    map_smul' := map_smul e
    invFun := e.symm }

@[simp]
theorem toLinearEquiv_refl : (AlgEquiv.refl : A ≃ₐ[R] A).toLinearEquiv = LinearEquiv.refl R A :=
  rfl

@[simp]
theorem toLinearEquiv_symm (e : A ≃ₐ[R] B) : e.symm.toLinearEquiv = e.toLinearEquiv.symm :=
  rfl

@[simp]
theorem coe_toLinearEquiv (e : A ≃ₐ[R] B) : ⇑e.toLinearEquiv = e := rfl

@[simp]
theorem coe_symm_toLinearEquiv (e : A ≃ₐ[R] B) : ⇑e.toLinearEquiv.symm = e.symm := rfl

theorem toLinearEquiv_injective : Function.Injective (toLinearEquiv : _ → A ≃ₗ[R] B) :=
  fun _ _ h => ext <| LinearEquiv.congr_fun h

/-- Interpret an algebra equivalence as a linear map. -/
def toLinearMap : A →ₗ[R] B :=
  e.toAlgHom.toLinearMap

@[simp]
theorem toAlgHom_toLinearMap : (e : A →ₐ[R] B).toLinearMap = e.toLinearMap :=
  rfl

theorem toLinearMap_ofAlgHom (f : A →ₐ[R] B) (g : B →ₐ[R] A) (h₁ h₂) :
    (ofAlgHom f g h₁ h₂).toLinearMap = f.toLinearMap :=
  LinearMap.ext fun _ => rfl

@[simp]
theorem toLinearEquiv_toLinearMap : e.toLinearEquiv.toLinearMap = e.toLinearMap :=
  rfl

@[simp]
theorem toLinearMap_apply (x : A) : e.toLinearMap x = e x :=
  rfl

theorem toLinearMap_injective : Function.Injective (toLinearMap : _ → A →ₗ[R] B) := fun _ _ h =>
  ext <| LinearMap.congr_fun h

@[simp] theorem linearEquivConj_mulLeft (f : A ≃ₐ[R] B) (x : A) :
    f.toLinearEquiv.conj (.mulLeft R x) = .mulLeft R (f x) := by
  ext; simp

@[simp] theorem linearEquivConj_mulRight (f : A ≃ₐ[R] B) (x : A) :
    f.toLinearEquiv.conj (.mulRight R x) = .mulRight R (f x) := by
  ext; simp

@[simp] theorem linearEquivConj_mulLeftRight (f : A ≃ₐ[R] B) (x : A × A) :
    f.toLinearEquiv.conj (.mulLeftRight R x) = .mulLeftRight R (Prod.map f f x) := by
  cases x; ext; simp

end ToLinearEquiv

section OfLinearEquiv

variable (l : A ≃ₗ[R] B) (map_one : l 1 = 1) (map_mul : ∀ x y : A, l (x * y) = l x * l y)

/--
Upgrade a linear equivalence to an algebra equivalence,
given that it distributes over multiplication and the identity
-/
@[simps apply]
def ofLinearEquiv : A ≃ₐ[R] B :=
  { l with
    toFun := l
    invFun := l.symm
    map_mul' := map_mul
    commutes' := (AlgHom.ofLinearMap l map_one map_mul : A →ₐ[R] B).commutes }

/-- Auxiliary definition to avoid looping in `dsimp` with `AlgEquiv.ofLinearEquiv_symm`. -/
protected def ofLinearEquiv_symm.aux := (ofLinearEquiv l map_one map_mul).symm

@[simp]
theorem ofLinearEquiv_symm :
    (ofLinearEquiv l map_one map_mul).symm =
      ofLinearEquiv l.symm
        (_root_.map_one <| ofLinearEquiv_symm.aux l map_one map_mul)
        (_root_.map_mul <| ofLinearEquiv_symm.aux l map_one map_mul) :=
  rfl

@[simp]
theorem ofLinearEquiv_toLinearEquiv (map_mul) (map_one) :
    ofLinearEquiv e.toLinearEquiv map_mul map_one = e :=
  rfl

@[simp]
theorem toLinearEquiv_ofLinearEquiv : toLinearEquiv (ofLinearEquiv l map_one map_mul) = l :=
  rfl

end OfLinearEquiv

section OfRingEquiv

/-- Promotes a linear `RingEquiv` to an `AlgEquiv`. -/
@[simps apply symm_apply toEquiv]
def ofRingEquiv {f : A ≃+* B} (hf : ∀ x, f (algebraMap R A x) = algebraMap R B x) :
    A ≃ₐ[R] B :=
  { f with
    toFun := f
    invFun := f.symm
    commutes' := hf }

end OfRingEquiv

section OfBijective

/-- Promotes a bijective algebra homomorphism to an algebra equivalence. -/
noncomputable def ofBijective (f : A →ₐ[R] B) (hf : Function.Bijective f) : A ≃ₐ[R] B :=
  { RingEquiv.ofBijective (f : A →+* B) hf, f with }

@[simp]
lemma coe_ofBijective (f : A →ₐ[R] B) (hf : Function.Bijective f) :
    (ofBijective f hf : A → B) = f := rfl

lemma ofBijective_apply (f : A →ₐ[R] B) (hf : Function.Bijective f) (a : A) :
    (ofBijective f hf) a = f a := rfl

@[simp]
lemma toLinearMap_ofBijective (f : A →ₐ[R] B) (hf : Function.Bijective f) :
    (ofBijective f hf).toLinearMap = f := rfl

@[simp]
lemma toAlgHom_ofBijective (f : A →ₐ[R] B) (hf : Function.Bijective f) :
    (ofBijective f hf).toAlgHom = f := rfl

lemma ofBijective_apply_symm_apply (f : A →ₐ[R] B) (hf : Function.Bijective f) (x : B) :
    f ((ofBijective f hf).symm x) = x :=
  (ofBijective f hf).apply_symm_apply x

@[simp]
lemma ofBijective_symm_apply_apply (f : A →ₐ[R] B) (hf : Function.Bijective f) (x : A) :
    (ofBijective f hf).symm (f x) = x :=
  (ofBijective f hf).symm_apply_apply x

end OfBijective

section trans

universe u₁ u₂ u₃
variable {A₁ : Type u₁} {A₂ : Type u₂} {A₃ : Type u₃}
variable [Semiring A₁] [Semiring A₂] [Semiring A₃]
variable [Algebra R A₁] [Algebra R A₂] [Algebra R A₃]
variable (e₁₂ : A₁ ≃ₐ[R] A₂) (e₂₃ : A₂ ≃ₐ[R] A₃)

/-- Algebra equivalences are transitive. -/
@[trans]
def trans (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) : A₁ ≃ₐ[R] A₃ :=
  { e₁.toRingEquiv.trans e₂.toRingEquiv with
    commutes' := fun r => show e₂.toFun (e₁.toFun _) = _ by rw [e₁.commutes', e₂.commutes'] }

@[simp]
theorem coe_trans (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) : ⇑(e₁.trans e₂) = e₂ ∘ e₁ :=
  rfl

@[simp]
theorem trans_apply (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) (x : A₁) : (e₁.trans e₂) x = e₂ (e₁ x) :=
  rfl

@[simp]
theorem symm_trans_apply (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) (x : A₃) :
    (e₁.trans e₂).symm x = e₁.symm (e₂.symm x) :=
  rfl

@[simp] lemma self_trans_symm (e : A₁ ≃ₐ[R] A₂) : e.trans e.symm = refl := by ext; simp
@[simp] lemma symm_trans_self (e : A₁ ≃ₐ[R] A₂) : e.symm.trans e = refl := by ext; simp

@[simp, norm_cast]
lemma toRingHom_trans (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) :
    (e₁.trans e₂ : A₁ →+* A₃) = .comp e₂ (e₁ : A₁ →+* A₂) := rfl

@[simp]
theorem toLinearEquiv_trans (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) :
    (e₁.trans e₂).toLinearEquiv = e₁.toLinearEquiv.trans e₂.toLinearEquiv :=
  rfl

@[simp]
theorem trans_toLinearMap (f : A₁ ≃ₐ[R] A₂) (g : A₂ ≃ₐ[R] A₃) :
    (f.trans g).toLinearMap = g.toLinearMap.comp f.toLinearMap :=
  rfl

end trans

section congr

universe u₁ u₂ u₃ v₁ v₂ v₃ w₁ w₂
variable {A₁ : Type u₁} {B₁ : Type v₁} {A₂ : Type u₂} {B₂ : Type v₂} {A₃ : Type u₃} {B₃ : Type v₃}
variable [Semiring A₁] [Semiring B₁] [Semiring A₂] [Semiring B₂] [Semiring A₃] [Semiring B₃]
variable [Algebra R A₁] [Algebra R B₁] [Algebra R A₂] [Algebra R B₂] [Algebra R A₃] [Algebra R B₃]
variable {C₁ : Type w₁} {C₂ : Type w₂} [Semiring C₁] [Semiring C₂] [Algebra R C₁] [Algebra R C₂]

/-- If `A₁` is equivalent to `A₁'` and `A₂` is equivalent to `A₂'`, then the type of maps
`A₁ →ₐ[R] A₂` is equivalent to the type of maps `A₁' →ₐ[R] A₂'`. -/
@[simps apply]
def arrowCongr (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : B₁ ≃ₐ[R] B₂) : (A₁ →ₐ[R] B₁) ≃ (A₂ →ₐ[R] B₂) where
  toFun f := (e₂.toAlgHom.comp f).comp e₁.symm.toAlgHom
  invFun f := (e₂.symm.toAlgHom.comp f).comp e₁.toAlgHom
  left_inv f := by
    simp only [AlgHom.comp_assoc, symm_comp]
    simp only [← AlgHom.comp_assoc, symm_comp, AlgHom.id_comp, AlgHom.comp_id]
  right_inv f := by
    simp only [AlgHom.comp_assoc, comp_symm]
    simp only [← AlgHom.comp_assoc, comp_symm, AlgHom.id_comp, AlgHom.comp_id]

theorem arrowCongr_comp (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : B₁ ≃ₐ[R] B₂)
    (e₃ : C₁ ≃ₐ[R] C₂) (f : A₁ →ₐ[R] B₁) (g : B₁ →ₐ[R] C₁) :
    arrowCongr e₁ e₃ (g.comp f) = (arrowCongr e₂ e₃ g).comp (arrowCongr e₁ e₂ f) := by
  ext
  simp

@[simp]
theorem arrowCongr_refl : arrowCongr AlgEquiv.refl AlgEquiv.refl = Equiv.refl (A₁ →ₐ[R] A₂) :=
  rfl

@[simp]
theorem arrowCongr_trans (e₁ : A₁ ≃ₐ[R] A₂) (e₁' : B₁ ≃ₐ[R] B₂)
    (e₂ : A₂ ≃ₐ[R] A₃) (e₂' : B₂ ≃ₐ[R] B₃) :
    arrowCongr (e₁.trans e₂) (e₁'.trans e₂') = (arrowCongr e₁ e₁').trans (arrowCongr e₂ e₂') :=
  rfl

@[simp]
theorem arrowCongr_symm (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : B₁ ≃ₐ[R] B₂) :
    (arrowCongr e₁ e₂).symm = arrowCongr e₁.symm e₂.symm :=
  rfl

/-- If `A₁` is equivalent to `A₂` and `A₁'` is equivalent to `A₂'`, then the type of maps
`A₁ ≃ₐ[R] A₁'` is equivalent to the type of maps `A₂ ≃ₐ[R] A₂'`.

This is the `AlgEquiv` version of `AlgEquiv.arrowCongr`. -/
@[simps apply]
def equivCongr (e : A₁ ≃ₐ[R] A₂) (e' : B₁ ≃ₐ[R] B₂) : (A₁ ≃ₐ[R] B₁) ≃ (A₂ ≃ₐ[R] B₂) where
  toFun ψ := e.symm.trans (ψ.trans e')
  invFun ψ := e.trans (ψ.trans e'.symm)
  left_inv ψ := by
    ext
    simp_rw [trans_apply, symm_apply_apply]
  right_inv ψ := by
    ext
    simp_rw [trans_apply, apply_symm_apply]

@[simp]
theorem equivCongr_refl : equivCongr AlgEquiv.refl AlgEquiv.refl = Equiv.refl (A₁ ≃ₐ[R] A₂) :=
  rfl

@[simp]
theorem equivCongr_symm (e : A₁ ≃ₐ[R] A₂) (e' : B₁ ≃ₐ[R] B₂) :
    (equivCongr e e').symm = equivCongr e.symm e'.symm :=
  rfl

@[simp]
theorem equivCongr_trans (e₁₂ : A₁ ≃ₐ[R] A₂) (e₁₂' : B₁ ≃ₐ[R] B₂) (e₂₃ : A₂ ≃ₐ[R] A₃)
    (e₂₃' : B₂ ≃ₐ[R] B₃) : (equivCongr e₁₂ e₁₂').trans (equivCongr e₂₃ e₂₃') =
      equivCongr (e₁₂.trans e₂₃) (e₁₂'.trans e₂₃') :=
  rfl

@[simps -isSimp one mul, stacks 09HR]
instance aut : Group (A ≃ₐ[R] A) where
  mul ϕ ψ := ψ.trans ϕ
  mul_assoc _ _ _ := rfl
  one := refl
  one_mul _ := ext fun _ => rfl
  mul_one _ := ext fun _ => rfl
  inv := symm
  inv_mul_cancel ϕ := ext <| symm_apply_apply ϕ

@[simp]
theorem one_apply (x : A) : (1 : A ≃ₐ[R] A) x = x :=
  rfl

@[simp]
theorem mul_apply (e₁ e₂ : A ≃ₐ[R] A) (x : A) : (e₁ * e₂) x = e₁ (e₂ x) :=
  rfl

lemma aut_inv (ϕ : A ≃ₐ[R] A) : ϕ⁻¹ = ϕ.symm := rfl

@[simp] lemma coe_inv (ϕ : A ≃ₐ[R] A) : ⇑ϕ⁻¹ = ⇑ϕ.symm := rfl

@[simp] theorem coe_pow (e : A ≃ₐ[R] A) (n : ℕ) : ⇑(e ^ n) = e^[n] :=
  n.rec (by ext; simp) fun _ ih ↦ by ext; simp [pow_succ, ih]

/-- An algebra isomorphism induces a group isomorphism between automorphism groups.

This is a more bundled version of `AlgEquiv.equivCongr`. -/
@[simps apply]
def autCongr (ϕ : A₁ ≃ₐ[R] A₂) : (A₁ ≃ₐ[R] A₁) ≃* A₂ ≃ₐ[R] A₂ where
  __ := equivCongr ϕ ϕ
  toFun ψ := ϕ.symm.trans (ψ.trans ϕ)
  invFun ψ := ϕ.trans (ψ.trans ϕ.symm)
  map_mul' ψ χ := by
    ext
    simp only [mul_apply, trans_apply, symm_apply_apply]

@[simp]
theorem autCongr_refl : autCongr AlgEquiv.refl = MulEquiv.refl (A₁ ≃ₐ[R] A₁) := rfl

@[simp]
theorem autCongr_symm (ϕ : A₁ ≃ₐ[R] A₂) : (autCongr ϕ).symm = autCongr ϕ.symm :=
  rfl

@[simp]
theorem autCongr_trans (ϕ : A₁ ≃ₐ[R] A₂) (ψ : A₂ ≃ₐ[R] A₃) :
    (autCongr ϕ).trans (autCongr ψ) = autCongr (ϕ.trans ψ) :=
  rfl

end congr

/-- The tautological action by `A₁ ≃ₐ[R] A₁` on `A₁`.

This generalizes `Function.End.applyMulAction`. -/
instance applyMulSemiringAction : MulSemiringAction (A ≃ₐ[R] A) A where
  smul := (· <| ·)
  smul_zero := map_zero
  smul_add := map_add
  smul_one := map_one
  smul_mul := map_mul
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp]
protected theorem smul_def (f : A ≃ₐ[R] A) (a : A) : f • a = f a :=
  rfl

instance apply_faithfulSMul : FaithfulSMul (A ≃ₐ[R] A) A :=
  ⟨AlgEquiv.ext⟩

instance apply_smulCommClass {S} [SMul S R] [SMul S A] [IsScalarTower S R A] :
    SMulCommClass S (A ≃ₐ[R] A) A where
  smul_comm r e a := (e.toLinearEquiv.map_smul_of_tower r a).symm

instance apply_smulCommClass' {S} [SMul S R] [SMul S A] [IsScalarTower S R A] :
    SMulCommClass (A ≃ₐ[R] A) S A :=
  SMulCommClass.symm _ _ _

instance : MulDistribMulAction (A ≃ₐ[R] A) Aˣ where
  smul := fun f => Units.map f
  one_smul := fun x => by ext; rfl
  mul_smul := fun x y z => by ext; rfl
  smul_mul := fun x y z => by ext; exact map_mul x _ _
  smul_one := fun x => by ext; exact map_one x

@[simp]
theorem smul_units_def (f : A ≃ₐ[R] A) (x : Aˣ) :
    f • x = Units.map f x := rfl

@[simp]
lemma _root_.MulSemiringAction.toRingEquiv_algEquiv (σ : A ≃ₐ[R] A) :
    MulSemiringAction.toRingEquiv _ A σ = σ := rfl

@[simp]
theorem algebraMap_eq_apply (e : A ≃ₐ[R] B) {y : R} {x : A} :
    algebraMap R B y = e x ↔ algebraMap R A y = x :=
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

lemma pow_toLinearMap (σ : A ≃ₐ[R] A) (n : ℕ) :
    (σ ^ n).toLinearMap = σ.toLinearMap ^ n :=
  (AlgEquiv.toLinearMapHom R A).map_pow σ n

@[simp]
lemma one_toLinearMap :
    (1 : A ≃ₐ[R] A).toLinearMap = 1 := rfl

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
instance _root_.Finite.algEquiv [Finite (A →ₐ[R] A)] : Finite (A ≃ₐ[R] A) :=
  Finite.of_injective _ AlgEquiv.coe_toAlgHom_injective

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

section ulift

universe w

/-- The algebra equivalence between `ULift A` and `A`. -/
@[simps! apply, simps! -isSimp symm_apply, pp_with_univ]
def ULift.algEquiv {R : Type uR} {A : Type uA} [CommSemiring R] [Semiring A] [Algebra R A] :
    ULift.{w} A ≃ₐ[R] A where
  __ := ULift.ringEquiv
  commutes' _ := rfl

@[simp]
lemma ULift.down_algEquiv_symm_apply {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    (a : A) :
    (ULift.algEquiv (R := R).symm a).down = a :=
  rfl

universe u₁ u₂ u₃
variable {R S T : Type*} [CommSemiring R] [Semiring S]
  [Semiring T] [Algebra R S] [Algebra R T]

attribute [local instance] ULift.algebra' in
/-- `ULift` is functorial for algebra homomorphisms. -/
@[pp_with_univ]
def AlgHom.ulift (f : S →ₐ[R] T) :
    ULift.{u₁} S →ₐ[ULift.{u₂} R] ULift.{u₃} T where
  __ := AlgHom.comp ULift.algEquiv.symm.toAlgHom (f.comp ULift.algEquiv.toAlgHom)
  commutes' _ := by simp

@[simp]
lemma AlgHom.down_ulift_apply (f : S →ₐ[R] T) (x : ULift S) :
    (f.ulift x).down = f x.down :=
  rfl

lemma AlgHom.ulift_apply (f : S →ₐ[R] T) (x : ULift S) :
    f.ulift x = ⟨f x.down⟩ :=
  rfl

end ulift

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
