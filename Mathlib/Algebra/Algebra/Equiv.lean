/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Ring.Action.Group

/-!
# Isomorphisms of `R`-algebras

This file defines bundled isomorphisms of `R`-algebras.

## Main definitions

* `AlgEquiv R A B`: the type of `R`-algebra isomorphisms between `A` and `B`.

## Notations

* `A ≃ₐ[R] B` : `R`-algebra equivalence from `A` to `B`.
-/

universe u v w u₁ v₁

/-- An equivalence of algebras (denoted as `A ≃ₐ[R] B`)
is an equivalence of rings commuting with the actions of scalars. -/
structure AlgEquiv (R : Type u) (A : Type v) (B : Type w) [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B] extends A ≃ B, A ≃* B, A ≃+ B, A ≃+* B where
  /-- An equivalence of algebras commutes with the action of scalars. -/
  protected commutes' : ∀ r : R, toFun (algebraMap R A r) = algebraMap R B r

attribute [nolint docBlame] AlgEquiv.toRingEquiv
attribute [nolint docBlame] AlgEquiv.toEquiv
attribute [nolint docBlame] AlgEquiv.toAddEquiv
attribute [nolint docBlame] AlgEquiv.toMulEquiv

@[inherit_doc]
notation:50 A " ≃ₐ[" R "] " A' => AlgEquiv R A A'

/-- `AlgEquivClass F R A B` states that `F` is a type of algebra structure preserving
  equivalences. You should extend this class when you extend `AlgEquiv`. -/
class AlgEquivClass (F : Type*) (R A B : outParam Type*) [CommSemiring R] [Semiring A]
    [Semiring B] [Algebra R A] [Algebra R B] [EquivLike F A B] : Prop
    extends RingEquivClass F A B where
  /-- An equivalence of algebras commutes with the action of scalars. -/
  commutes : ∀ (f : F) (r : R), f (algebraMap R A r) = algebraMap R B r

namespace AlgEquivClass

-- See note [lower instance priority]
instance (priority := 100) toAlgHomClass (F R A B : Type*) [CommSemiring R] [Semiring A]
    [Semiring B] [Algebra R A] [Algebra R B] [EquivLike F A B] [h : AlgEquivClass F R A B] :
    AlgHomClass F R A B :=
  { h with }

instance (priority := 100) toLinearEquivClass (F R A B : Type*) [CommSemiring R]
    [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
    [EquivLike F A B] [h : AlgEquivClass F R A B] : LinearEquivClass F R A B :=
  { h with map_smulₛₗ := fun f => map_smulₛₗ f }

/-- Turn an element of a type `F` satisfying `AlgEquivClass F R A B` into an actual `AlgEquiv`.
This is declared as the default coercion from `F` to `A ≃ₐ[R] B`. -/
@[coe]
def toAlgEquiv {F R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A]
    [Algebra R B] [EquivLike F A B] [AlgEquivClass F R A B] (f : F) : A ≃ₐ[R] B :=
  { (f : A ≃ B), (f : A ≃+* B) with commutes' := commutes f }

instance (F R A B : Type*) [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
    [EquivLike F A B] [AlgEquivClass F R A B] : CoeTC F (A ≃ₐ[R] B) :=
  ⟨toAlgEquiv⟩
end AlgEquivClass

namespace AlgEquiv

universe uR uA₁ uA₂ uA₃ uA₁' uA₂' uA₃'
variable {R : Type uR}
variable {A₁ : Type uA₁} {A₂ : Type uA₂} {A₃ : Type uA₃}
variable {A₁' : Type uA₁'} {A₂' : Type uA₂'} {A₃' : Type uA₃'}

section Semiring

variable [CommSemiring R] [Semiring A₁] [Semiring A₂] [Semiring A₃]
variable [Semiring A₁'] [Semiring A₂'] [Semiring A₃']
variable [Algebra R A₁] [Algebra R A₂] [Algebra R A₃]
variable [Algebra R A₁'] [Algebra R A₂'] [Algebra R A₃']
variable (e : A₁ ≃ₐ[R] A₂)

section coe

instance : EquivLike (A₁ ≃ₐ[R] A₂) A₁ A₂ where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by
    obtain ⟨⟨f,_⟩,_⟩ := f
    obtain ⟨⟨g,_⟩,_⟩ := g
    congr

/-- Helper instance since the coercion is not always found. -/
instance : FunLike (A₁ ≃ₐ[R] A₂) A₁ A₂ where
  coe := DFunLike.coe
  coe_injective' := DFunLike.coe_injective'

instance : AlgEquivClass (A₁ ≃ₐ[R] A₂) R A₁ A₂ where
  map_add f := f.map_add'
  map_mul f := f.map_mul'
  commutes f := f.commutes'

@[ext]
theorem ext {f g : A₁ ≃ₐ[R] A₂} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

protected theorem congr_arg {f : A₁ ≃ₐ[R] A₂} {x x' : A₁} : x = x' → f x = f x' :=
  DFunLike.congr_arg f

protected theorem congr_fun {f g : A₁ ≃ₐ[R] A₂} (h : f = g) (x : A₁) : f x = g x :=
  DFunLike.congr_fun h x

@[simp]
theorem coe_mk {toEquiv map_mul map_add commutes} :
    ⇑(⟨toEquiv, map_mul, map_add, commutes⟩ : A₁ ≃ₐ[R] A₂) = toEquiv :=
  rfl

@[simp]
theorem mk_coe (e : A₁ ≃ₐ[R] A₂) (e' h₁ h₂ h₃ h₄ h₅) :
    (⟨⟨e, e', h₁, h₂⟩, h₃, h₄, h₅⟩ : A₁ ≃ₐ[R] A₂) = e :=
  ext fun _ => rfl

@[simp]
theorem toEquiv_eq_coe : e.toEquiv = e :=
  rfl

@[simp]
protected theorem coe_coe {F : Type*} [EquivLike F A₁ A₂] [AlgEquivClass F R A₁ A₂] (f : F) :
    ⇑(f : A₁ ≃ₐ[R] A₂) = f :=
  rfl

theorem coe_fun_injective : @Function.Injective (A₁ ≃ₐ[R] A₂) (A₁ → A₂) fun e => (e : A₁ → A₂) :=
  DFunLike.coe_injective

instance hasCoeToRingEquiv : CoeOut (A₁ ≃ₐ[R] A₂) (A₁ ≃+* A₂) :=
  ⟨AlgEquiv.toRingEquiv⟩

@[simp]
theorem coe_toEquiv : ((e : A₁ ≃ A₂) : A₁ → A₂) = e :=
  rfl

@[simp]
theorem toRingEquiv_eq_coe : e.toRingEquiv = e :=
  rfl

@[simp, norm_cast]
lemma toRingEquiv_toRingHom : ((e : A₁ ≃+* A₂) : A₁ →+* A₂) = e :=
  rfl

@[simp, norm_cast]
theorem coe_ringEquiv : ((e : A₁ ≃+* A₂) : A₁ → A₂) = e :=
  rfl

theorem coe_ringEquiv' : (e.toRingEquiv : A₁ → A₂) = e :=
  rfl

theorem coe_ringEquiv_injective : Function.Injective ((↑) : (A₁ ≃ₐ[R] A₂) → A₁ ≃+* A₂) :=
  fun _ _ h => ext <| RingEquiv.congr_fun h

/-- Interpret an algebra equivalence as an algebra homomorphism.

This definition is included for symmetry with the other `to*Hom` projections.
The `simp` normal form is to use the coercion of the `AlgHomClass.coeTC` instance. -/
@[coe]
def toAlgHom : A₁ →ₐ[R] A₂ :=
  { e with
    map_one' := map_one e
    map_zero' := map_zero e }

@[simp]
theorem toAlgHom_eq_coe : e.toAlgHom = e :=
  rfl

@[simp, norm_cast]
theorem coe_algHom : DFunLike.coe (e.toAlgHom) = DFunLike.coe e :=
  rfl

theorem coe_algHom_injective : Function.Injective ((↑) : (A₁ ≃ₐ[R] A₂) → A₁ →ₐ[R] A₂) :=
  fun _ _ h => ext <| AlgHom.congr_fun h

@[simp, norm_cast]
lemma toAlgHom_toRingHom : ((e : A₁ →ₐ[R] A₂) : A₁ →+* A₂) = e :=
  rfl

/-- The two paths coercion can take to a `RingHom` are equivalent -/
theorem coe_ringHom_commutes : ((e : A₁ →ₐ[R] A₂) : A₁ →+* A₂) = ((e : A₁ ≃+* A₂) : A₁ →+* A₂) :=
  rfl

@[simp]
theorem commutes : ∀ r : R, e (algebraMap R A₁ r) = algebraMap R A₂ r :=
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
def refl : A₁ ≃ₐ[R] A₁ :=
  { (.refl _ : A₁ ≃+* A₁) with commutes' := fun _ => rfl }

instance : Inhabited (A₁ ≃ₐ[R] A₁) :=
  ⟨refl⟩

@[simp]
theorem refl_toAlgHom : ↑(refl : A₁ ≃ₐ[R] A₁) = AlgHom.id R A₁ :=
  rfl

@[simp]
theorem coe_refl : ⇑(refl : A₁ ≃ₐ[R] A₁) = id :=
  rfl

end refl

section symm

/-- Algebra equivalences are symmetric. -/
@[symm]
def symm (e : A₁ ≃ₐ[R] A₂) : A₂ ≃ₐ[R] A₁ :=
  { e.toRingEquiv.symm with
    commutes' := fun r => by
      rw [← e.toRingEquiv.symm_apply_apply (algebraMap R A₁ r)]
      congr
      simp }

theorem invFun_eq_symm {e : A₁ ≃ₐ[R] A₂} : e.invFun = e.symm :=
  rfl

@[simp]
theorem coe_apply_coe_coe_symm_apply {F : Type*} [EquivLike F A₁ A₂] [AlgEquivClass F R A₁ A₂]
    (f : F) (x : A₂) :
    f ((f : A₁ ≃ₐ[R] A₂).symm x) = x :=
  EquivLike.right_inv f x

@[simp]
theorem coe_coe_symm_apply_coe_apply {F : Type*} [EquivLike F A₁ A₂] [AlgEquivClass F R A₁ A₂]
    (f : F) (x : A₁) :
    (f : A₁ ≃ₐ[R] A₂).symm (f x) = x :=
  EquivLike.left_inv f x

/-- `simp` normal form of `invFun_eq_symm` -/
@[simp]
theorem symm_toEquiv_eq_symm {e : A₁ ≃ₐ[R] A₂} : (e : A₁ ≃ A₂).symm = e.symm :=
  rfl

@[simp]
theorem symm_symm (e : A₁ ≃ₐ[R] A₂) : e.symm.symm = e := rfl

theorem symm_bijective : Function.Bijective (symm : (A₁ ≃ₐ[R] A₂) → A₂ ≃ₐ[R] A₁) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]
theorem mk_coe' (e : A₁ ≃ₐ[R] A₂) (f h₁ h₂ h₃ h₄ h₅) :
    (⟨⟨f, e, h₁, h₂⟩, h₃, h₄, h₅⟩ : A₂ ≃ₐ[R] A₁) = e.symm :=
  symm_bijective.injective <| ext fun _ => rfl

/-- Auxiliary definition to avoid looping in `dsimp` with `AlgEquiv.symm_mk`. -/
protected def symm_mk.aux (f f') (h₁ h₂ h₃ h₄ h₅) :=
  (⟨⟨f, f', h₁, h₂⟩, h₃, h₄, h₅⟩ : A₁ ≃ₐ[R] A₂).symm

@[simp]
theorem symm_mk (f f') (h₁ h₂ h₃ h₄ h₅) :
    (⟨⟨f, f', h₁, h₂⟩, h₃, h₄, h₅⟩ : A₁ ≃ₐ[R] A₂).symm =
      { symm_mk.aux f f' h₁ h₂ h₃ h₄ h₅ with
        toFun := f'
        invFun := f } :=
  rfl

@[simp]
theorem refl_symm : (AlgEquiv.refl : A₁ ≃ₐ[R] A₁).symm = AlgEquiv.refl :=
  rfl

--this should be a simp lemma but causes a lint timeout
theorem toRingEquiv_symm (f : A₁ ≃ₐ[R] A₁) : (f : A₁ ≃+* A₁).symm = f.symm :=
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
theorem apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : ∀ x, e (e.symm x) = x :=
  e.toEquiv.apply_symm_apply

@[simp]
theorem symm_apply_apply (e : A₁ ≃ₐ[R] A₂) : ∀ x, e.symm (e x) = x :=
  e.toEquiv.symm_apply_apply

theorem symm_apply_eq (e : A₁ ≃ₐ[R] A₂) {x y} : e.symm x = y ↔ x = e y :=
  e.toEquiv.symm_apply_eq

theorem eq_symm_apply (e : A₁ ≃ₐ[R] A₂) {x y} : y = e.symm x ↔ e y = x :=
  e.toEquiv.eq_symm_apply

@[simp]
theorem comp_symm (e : A₁ ≃ₐ[R] A₂) : AlgHom.comp (e : A₁ →ₐ[R] A₂) ↑e.symm = AlgHom.id R A₂ := by
  ext
  simp

@[simp]
theorem symm_comp (e : A₁ ≃ₐ[R] A₂) : AlgHom.comp ↑e.symm (e : A₁ →ₐ[R] A₂) = AlgHom.id R A₁ := by
  ext
  simp

theorem leftInverse_symm (e : A₁ ≃ₐ[R] A₂) : Function.LeftInverse e.symm e :=
  e.left_inv

theorem rightInverse_symm (e : A₁ ≃ₐ[R] A₂) : Function.RightInverse e.symm e :=
  e.right_inv

end symm

section simps

/-- See Note [custom simps projection] -/
def Simps.apply (e : A₁ ≃ₐ[R] A₂) : A₁ → A₂ :=
  e

/-- See Note [custom simps projection] -/
def Simps.toEquiv (e : A₁ ≃ₐ[R] A₂) : A₁ ≃ A₂ :=
  e

/-- See Note [custom simps projection] -/
def Simps.symm_apply (e : A₁ ≃ₐ[R] A₂) : A₂ → A₁ :=
  e.symm

initialize_simps_projections AlgEquiv (toFun → apply, invFun → symm_apply)

end simps

section trans

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

end trans

/-- If `A₁` is equivalent to `A₁'` and `A₂` is equivalent to `A₂'`, then the type of maps
`A₁ →ₐ[R] A₂` is equivalent to the type of maps `A₁' →ₐ[R] A₂'`. -/
@[simps apply]
def arrowCongr (e₁ : A₁ ≃ₐ[R] A₁') (e₂ : A₂ ≃ₐ[R] A₂') : (A₁ →ₐ[R] A₂) ≃ (A₁' →ₐ[R] A₂') where
  toFun f := (e₂.toAlgHom.comp f).comp e₁.symm.toAlgHom
  invFun f := (e₂.symm.toAlgHom.comp f).comp e₁.toAlgHom
  left_inv f := by
    simp only [AlgHom.comp_assoc, toAlgHom_eq_coe, symm_comp]
    simp only [← AlgHom.comp_assoc, symm_comp, AlgHom.id_comp, AlgHom.comp_id]
  right_inv f := by
    simp only [AlgHom.comp_assoc, toAlgHom_eq_coe, comp_symm]
    simp only [← AlgHom.comp_assoc, comp_symm, AlgHom.id_comp, AlgHom.comp_id]

theorem arrowCongr_comp (e₁ : A₁ ≃ₐ[R] A₁') (e₂ : A₂ ≃ₐ[R] A₂')
    (e₃ : A₃ ≃ₐ[R] A₃') (f : A₁ →ₐ[R] A₂) (g : A₂ →ₐ[R] A₃) :
    arrowCongr e₁ e₃ (g.comp f) = (arrowCongr e₂ e₃ g).comp (arrowCongr e₁ e₂ f) := by
  ext
  simp

@[simp]
theorem arrowCongr_refl : arrowCongr AlgEquiv.refl AlgEquiv.refl = Equiv.refl (A₁ →ₐ[R] A₂) :=
  rfl

@[simp]
theorem arrowCongr_trans (e₁ : A₁ ≃ₐ[R] A₂) (e₁' : A₁' ≃ₐ[R] A₂')
    (e₂ : A₂ ≃ₐ[R] A₃) (e₂' : A₂' ≃ₐ[R] A₃') :
    arrowCongr (e₁.trans e₂) (e₁'.trans e₂') = (arrowCongr e₁ e₁').trans (arrowCongr e₂ e₂') :=
  rfl

@[simp]
theorem arrowCongr_symm (e₁ : A₁ ≃ₐ[R] A₁') (e₂ : A₂ ≃ₐ[R] A₂') :
    (arrowCongr e₁ e₂).symm = arrowCongr e₁.symm e₂.symm :=
  rfl

/-- If `A₁` is equivalent to `A₂` and `A₁'` is equivalent to `A₂'`, then the type of maps
`A₁ ≃ₐ[R] A₁'` is equivalent to the type of maps `A₂ ≃ₐ[R] A₂'`.

This is the `AlgEquiv` version of `AlgEquiv.arrowCongr`. -/
@[simps apply]
def equivCongr (e : A₁ ≃ₐ[R] A₂) (e' : A₁' ≃ₐ[R] A₂') : (A₁ ≃ₐ[R] A₁') ≃ A₂ ≃ₐ[R] A₂' where
  toFun ψ := e.symm.trans (ψ.trans e')
  invFun ψ := e.trans (ψ.trans e'.symm)
  left_inv ψ := by
    ext
    simp_rw [trans_apply, symm_apply_apply]
  right_inv ψ := by
    ext
    simp_rw [trans_apply, apply_symm_apply]

@[simp]
theorem equivCongr_refl : equivCongr AlgEquiv.refl AlgEquiv.refl = Equiv.refl (A₁ ≃ₐ[R] A₁') :=
  rfl

@[simp]
theorem equivCongr_symm (e : A₁ ≃ₐ[R] A₂) (e' : A₁' ≃ₐ[R] A₂') :
    (equivCongr e e').symm = equivCongr e.symm e'.symm :=
  rfl

@[simp]
theorem equivCongr_trans (e₁₂ : A₁ ≃ₐ[R] A₂) (e₁₂' : A₁' ≃ₐ[R] A₂')
    (e₂₃ : A₂ ≃ₐ[R] A₃) (e₂₃' : A₂' ≃ₐ[R] A₃') :
    (equivCongr e₁₂ e₁₂').trans (equivCongr e₂₃ e₂₃') =
      equivCongr (e₁₂.trans e₂₃) (e₁₂'.trans e₂₃') :=
  rfl

/-- If an algebra morphism has an inverse, it is an algebra isomorphism. -/
@[simps]
def ofAlgHom (f : A₁ →ₐ[R] A₂) (g : A₂ →ₐ[R] A₁) (h₁ : f.comp g = AlgHom.id R A₂)
    (h₂ : g.comp f = AlgHom.id R A₁) : A₁ ≃ₐ[R] A₂ :=
  { f with
    toFun := f
    invFun := g
    left_inv := AlgHom.ext_iff.1 h₂
    right_inv := AlgHom.ext_iff.1 h₁ }

theorem coe_algHom_ofAlgHom (f : A₁ →ₐ[R] A₂) (g : A₂ →ₐ[R] A₁) (h₁ h₂) :
    ↑(ofAlgHom f g h₁ h₂) = f :=
  rfl

@[simp]
theorem ofAlgHom_coe_algHom (f : A₁ ≃ₐ[R] A₂) (g : A₂ →ₐ[R] A₁) (h₁ h₂) :
    ofAlgHom (↑f) g h₁ h₂ = f :=
  ext fun _ => rfl

theorem ofAlgHom_symm (f : A₁ →ₐ[R] A₂) (g : A₂ →ₐ[R] A₁) (h₁ h₂) :
    (ofAlgHom f g h₁ h₂).symm = ofAlgHom g f h₂ h₁ :=
  rfl

/-- Forgetting the multiplicative structures, an equivalence of algebras is a linear equivalence. -/
@[simps apply]
def toLinearEquiv (e : A₁ ≃ₐ[R] A₂) : A₁ ≃ₗ[R] A₂ :=
  { e with
    toFun := e
    map_smul' := map_smul e
    invFun := e.symm }

@[simp]
theorem toLinearEquiv_refl : (AlgEquiv.refl : A₁ ≃ₐ[R] A₁).toLinearEquiv = LinearEquiv.refl R A₁ :=
  rfl

@[simp]
theorem toLinearEquiv_symm (e : A₁ ≃ₐ[R] A₂) : e.symm.toLinearEquiv = e.toLinearEquiv.symm :=
  rfl

@[simp]
theorem coe_toLinearEquiv (e : A₁ ≃ₐ[R] A₂) : ⇑e.toLinearEquiv = e := rfl

@[simp]
theorem coe_symm_toLinearEquiv (e : A₁ ≃ₐ[R] A₂) : ⇑e.toLinearEquiv.symm = e.symm := rfl

@[simp]
theorem toLinearEquiv_trans (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) :
    (e₁.trans e₂).toLinearEquiv = e₁.toLinearEquiv.trans e₂.toLinearEquiv :=
  rfl

theorem toLinearEquiv_injective : Function.Injective (toLinearEquiv : _ → A₁ ≃ₗ[R] A₂) :=
  fun _ _ h => ext <| LinearEquiv.congr_fun h

/-- Interpret an algebra equivalence as a linear map. -/
def toLinearMap : A₁ →ₗ[R] A₂ :=
  e.toAlgHom.toLinearMap

@[simp]
theorem toAlgHom_toLinearMap : (e : A₁ →ₐ[R] A₂).toLinearMap = e.toLinearMap :=
  rfl

theorem toLinearMap_ofAlgHom (f : A₁ →ₐ[R] A₂) (g : A₂ →ₐ[R] A₁) (h₁ h₂) :
    (ofAlgHom f g h₁ h₂).toLinearMap = f.toLinearMap :=
  LinearMap.ext fun _ => rfl

@[simp]
theorem toLinearEquiv_toLinearMap : e.toLinearEquiv.toLinearMap = e.toLinearMap :=
  rfl

@[simp]
theorem toLinearMap_apply (x : A₁) : e.toLinearMap x = e x :=
  rfl

theorem toLinearMap_injective : Function.Injective (toLinearMap : _ → A₁ →ₗ[R] A₂) := fun _ _ h =>
  ext <| LinearMap.congr_fun h

@[simp]
theorem trans_toLinearMap (f : A₁ ≃ₐ[R] A₂) (g : A₂ ≃ₐ[R] A₃) :
    (f.trans g).toLinearMap = g.toLinearMap.comp f.toLinearMap :=
  rfl

/-- Promotes a bijective algebra homomorphism to an algebra equivalence. -/
noncomputable def ofBijective (f : A₁ →ₐ[R] A₂) (hf : Function.Bijective f) : A₁ ≃ₐ[R] A₂ :=
  { RingEquiv.ofBijective (f : A₁ →+* A₂) hf, f with }

@[simp]
lemma coe_ofBijective (f : A₁ →ₐ[R] A₂) (hf : Function.Bijective f) :
    (ofBijective f hf : A₁ → A₂) = f := rfl

lemma ofBijective_apply (f : A₁ →ₐ[R] A₂) (hf : Function.Bijective f) (a : A₁) :
    (ofBijective f hf) a = f a := rfl

@[simp]
lemma toLinearMap_ofBijective (f : A₁ →ₐ[R] A₂) (hf : Function.Bijective f) :
    (ofBijective f hf).toLinearMap = f := rfl

section OfLinearEquiv

variable (l : A₁ ≃ₗ[R] A₂) (map_one : l 1 = 1) (map_mul : ∀ x y : A₁, l (x * y) = l x * l y)

/--
Upgrade a linear equivalence to an algebra equivalence,
given that it distributes over multiplication and the identity
-/
@[simps apply]
def ofLinearEquiv : A₁ ≃ₐ[R] A₂ :=
  { l with
    toFun := l
    invFun := l.symm
    map_mul' := map_mul
    commutes' := (AlgHom.ofLinearMap l map_one map_mul : A₁ →ₐ[R] A₂).commutes }

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
def ofRingEquiv {f : A₁ ≃+* A₂} (hf : ∀ x, f (algebraMap R A₁ x) = algebraMap R A₂ x) :
    A₁ ≃ₐ[R] A₂ :=
  { f with
    toFun := f
    invFun := f.symm
    commutes' := hf }

end OfRingEquiv

@[simps -isSimp one mul, stacks 09HR]
instance aut : Group (A₁ ≃ₐ[R] A₁) where
  mul ϕ ψ := ψ.trans ϕ
  mul_assoc _ _ _ := rfl
  one := refl
  one_mul _ := ext fun _ => rfl
  mul_one _ := ext fun _ => rfl
  inv := symm
  inv_mul_cancel ϕ := ext <| symm_apply_apply ϕ

@[simp]
theorem one_apply (x : A₁) : (1 : A₁ ≃ₐ[R] A₁) x = x :=
  rfl

@[simp]
theorem mul_apply (e₁ e₂ : A₁ ≃ₐ[R] A₁) (x : A₁) : (e₁ * e₂) x = e₁ (e₂ x) :=
  rfl

lemma aut_inv (ϕ : A₁ ≃ₐ[R] A₁) : ϕ⁻¹ = ϕ.symm := rfl

@[simp] theorem coe_pow (e : A₁ ≃ₐ[R] A₁) (n : ℕ) : ⇑(e ^ n) = e^[n] :=
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

/-- The tautological action by `A₁ ≃ₐ[R] A₁` on `A₁`.

This generalizes `Function.End.applyMulAction`. -/
instance applyMulSemiringAction : MulSemiringAction (A₁ ≃ₐ[R] A₁) A₁ where
  smul := (· <| ·)
  smul_zero := map_zero
  smul_add := map_add
  smul_one := map_one
  smul_mul := map_mul
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp]
protected theorem smul_def (f : A₁ ≃ₐ[R] A₁) (a : A₁) : f • a = f a :=
  rfl

instance apply_faithfulSMul : FaithfulSMul (A₁ ≃ₐ[R] A₁) A₁ :=
  ⟨AlgEquiv.ext⟩

instance apply_smulCommClass {S} [SMul S R] [SMul S A₁] [IsScalarTower S R A₁] :
    SMulCommClass S (A₁ ≃ₐ[R] A₁) A₁ where
  smul_comm r e a := (e.toLinearEquiv.map_smul_of_tower r a).symm

instance apply_smulCommClass' {S} [SMul S R] [SMul S A₁] [IsScalarTower S R A₁] :
    SMulCommClass (A₁ ≃ₐ[R] A₁) S A₁ :=
  SMulCommClass.symm _ _ _

instance : MulDistribMulAction (A₁ ≃ₐ[R] A₁) A₁ˣ where
  smul := fun f => Units.map f
  one_smul := fun x => by ext; rfl
  mul_smul := fun x y z => by ext; rfl
  smul_mul := fun x y z => by ext; exact map_mul x _ _
  smul_one := fun x => by ext; exact map_one x

@[simp]
theorem smul_units_def (f : A₁ ≃ₐ[R] A₁) (x : A₁ˣ) :
    f • x = Units.map f x := rfl

@[simp]
lemma _root_.MulSemiringAction.toRingEquiv_algEquiv (σ : A₁ ≃ₐ[R] A₁) :
    MulSemiringAction.toRingEquiv _ A₁ σ = σ := rfl

@[simp]
theorem algebraMap_eq_apply (e : A₁ ≃ₐ[R] A₂) {y : R} {x : A₁} :
    algebraMap R A₂ y = e x ↔ algebraMap R A₁ y = x :=
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

lemma pow_toLinearMap (σ : A₁ ≃ₐ[R] A₁) (n : ℕ) :
    (σ ^ n).toLinearMap = σ.toLinearMap ^ n :=
  (AlgEquiv.toLinearMapHom R A₁).map_pow σ n

@[simp]
lemma one_toLinearMap :
    (1 : A₁ ≃ₐ[R] A₁).toLinearMap = 1 := rfl

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
instance _root_.Finite.algEquiv [Finite (A₁ →ₐ[R] A₂)] : Finite (A₁ ≃ₐ[R] A₂) :=
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
@[simps! -isSimp apply]
def ULift.algEquiv {R : Type u} {A : Type v} [CommSemiring R] [Semiring A] [Algebra R A] :
    ULift.{w} A ≃ₐ[R] A where
  __ := ULift.ringEquiv
  commutes' _ := rfl

