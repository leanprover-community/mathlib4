/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Opposite
import Mathlib.Algebra.Hom.Ring
import Mathlib.Logic.Equiv.Set
import Mathlib.Util.AssertExists
import Mathlib.Algebra.Hom.Equiv.Basic

#align_import algebra.ring.equiv from "leanprover-community/mathlib"@"00f91228655eecdcd3ac97a7fd8dbcb139fe990a"

/-!
# (Semi)ring equivs

In this file we define an extension of `Equiv` called `RingEquiv`, which is a datatype representing
an isomorphism of `Semiring`s, `Ring`s, `DivisionRing`s, or `Field`s.

## Notations

* ``infixl ` ≃+* `:25 := RingEquiv``

The extended equiv have coercions to functions, and the coercion is the canonical notation when
treating the isomorphism as maps.

## Implementation notes

The fields for `RingEquiv` now avoid the unbundled `isMulHom` and `isAddHom`, as these are
deprecated.

Definition of multiplication in the groups of automorphisms agrees with function composition,
multiplication in `Equiv.Perm`, and multiplication in `CategoryTheory.End`, not with
`CategoryTheory.CategoryStruct.comp`.

## Tags

Equiv, MulEquiv, AddEquiv, RingEquiv, MulAut, AddAut, RingAut
-/


variable {F α β R S S' : Type*}


/-- makes a `NonUnitalRingHom` from the bijective inverse of a `NonUnitalRingHom` -/
@[simps] def NonUnitalRingHom.inverse
    [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]
    (f : R →ₙ+* S) (g : S → R)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) : S →ₙ+* R :=
  { (f : R →+ S).inverse g h₁ h₂, (f : R →ₙ* S).inverse g h₁ h₂ with toFun := g }

/-- makes a `RingHom` from the bijective inverse of a `RingHom` -/
@[simps] def RingHom.inverse [NonAssocSemiring R] [NonAssocSemiring S]
    (f : RingHom R S) (g : S → R)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) : S →+* R :=
  { (f : OneHom R S).inverse g h₁,
    (f : MulHom R S).inverse g h₁ h₂,
    (f : R →+ S).inverse g h₁ h₂ with toFun := g }

/-- An equivalence between two (non-unital non-associative semi)rings that preserves the
algebraic structure. -/
structure RingEquiv (R S : Type*) [Mul R] [Mul S] [Add R] [Add S] extends R ≃ S, R ≃* S, R ≃+ S
#align ring_equiv RingEquiv

-- mathport name: «expr ≃+* »*
/-- Notation for `RingEquiv`. -/
infixl:25 " ≃+* " => RingEquiv

/-- The "plain" equivalence of types underlying an equivalence of (semi)rings. -/
add_decl_doc RingEquiv.toEquiv
#align ring_equiv.to_equiv RingEquiv.toEquiv

/-- The equivalence of additive monoids underlying an equivalence of (semi)rings. -/
add_decl_doc RingEquiv.toAddEquiv
#align ring_equiv.to_add_equiv RingEquiv.toAddEquiv

/-- The equivalence of multiplicative monoids underlying an equivalence of (semi)rings. -/
add_decl_doc RingEquiv.toMulEquiv
#align ring_equiv.to_mul_equiv RingEquiv.toMulEquiv

/-- `RingEquivClass F R S` states that `F` is a type of ring structure preserving equivalences.
You should extend this class when you extend `RingEquiv`. -/
class RingEquivClass (F : Type*) (R S : outParam (Type*)) [Mul R] [Add R] [Mul S] [Add S] extends
  MulEquivClass F R S where
  /-- By definition, a ring isomorphism preserves the additive structure. -/
  map_add : ∀ (f : F) (a b), f (a + b) = f a + f b
#align ring_equiv_class RingEquivClass

namespace RingEquivClass

-- See note [lower instance priority]
instance (priority := 100) toAddEquivClass [Mul R] [Add R]
    [Mul S] [Add S] [h : RingEquivClass F R S] : AddEquivClass F R S :=
  { h with coe := h.coe }
#align ring_equiv_class.to_add_equiv_class RingEquivClass.toAddEquivClass

-- See note [lower instance priority]
instance (priority := 100) toRingHomClass [NonAssocSemiring R] [NonAssocSemiring S]
    [h : RingEquivClass F R S] : RingHomClass F R S :=
  { h with
    coe := h.coe
    coe_injective' := FunLike.coe_injective
    map_zero := map_zero
    map_one := map_one }
#align ring_equiv_class.to_ring_hom_class RingEquivClass.toRingHomClass

-- See note [lower instance priority]
instance (priority := 100) toNonUnitalRingHomClass [NonUnitalNonAssocSemiring R]
    [NonUnitalNonAssocSemiring S] [h : RingEquivClass F R S] : NonUnitalRingHomClass F R S :=
  { h with
    coe := h.coe
    coe_injective' := FunLike.coe_injective
    map_zero := map_zero }
#align ring_equiv_class.to_non_unital_ring_hom_class RingEquivClass.toNonUnitalRingHomClass

/-- Turn an element of a type `F` satisfying `RingEquivClass F α β` into an actual
`RingEquiv`. This is declared as the default coercion from `F` to `α ≃+* β`. -/
@[coe]
def toRingEquiv [Mul α] [Add α] [Mul β] [Add β] [RingEquivClass F α β] (f : F) :
  α ≃+* β :=
{ (f : α ≃* β), (f : α ≃+ β) with }

end RingEquivClass

/-- Any type satisfying `RingEquivClass` can be cast into `RingEquiv` via
`RingEquivClass.toRingEquiv`. -/
instance [Mul α] [Add α] [Mul β] [Add β] [RingEquivClass F α β] : CoeTC F (α ≃+* β) :=
  ⟨RingEquivClass.toRingEquiv⟩

namespace RingEquiv

section Basic

variable [Mul R] [Mul S] [Add R] [Add S] [Mul S'] [Add S']

instance : RingEquivClass (R ≃+* S) R S where
  coe f := f.toFun
  inv f := f.invFun
  coe_injective' e f h₁ h₂ := by
    cases e
    -- ⊢ { toEquiv := toEquiv✝, map_mul' := map_mul'✝, map_add' := map_add'✝ } = f
    cases f
    -- ⊢ { toEquiv := toEquiv✝¹, map_mul' := map_mul'✝¹, map_add' := map_add'✝¹ } = { …
    congr
    -- ⊢ toEquiv✝¹ = toEquiv✝
    apply Equiv.coe_fn_injective h₁
    -- 🎉 no goals
  map_add := map_add'
  map_mul := map_mul'
  left_inv f := f.left_inv
  right_inv f := f.right_inv

@[simp]
theorem toEquiv_eq_coe (f : R ≃+* S) : f.toEquiv = f :=
  rfl
#align ring_equiv.to_equiv_eq_coe RingEquiv.toEquiv_eq_coe

-- Porting note: `toFun_eq_coe` no longer needed in Lean4
#noalign ring_equiv.to_fun_eq_coe

@[simp]
theorem coe_toEquiv (f : R ≃+* S) : ⇑(f : R ≃ S) = f :=
  rfl
#align ring_equiv.coe_to_equiv RingEquiv.coe_toEquiv

/-- A ring isomorphism preserves multiplication. -/
protected theorem map_mul (e : R ≃+* S) (x y : R) : e (x * y) = e x * e y :=
  map_mul e x y
#align ring_equiv.map_mul RingEquiv.map_mul

/-- A ring isomorphism preserves addition. -/
protected theorem map_add (e : R ≃+* S) (x y : R) : e (x + y) = e x + e y :=
  map_add e x y
#align ring_equiv.map_add RingEquiv.map_add

/-- Two ring isomorphisms agree if they are defined by the
    same underlying function. -/
@[ext]
theorem ext {f g : R ≃+* S} (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext f g h
#align ring_equiv.ext RingEquiv.ext

@[simp]
theorem coe_mk (e h₃ h₄) : ⇑(⟨e, h₃, h₄⟩ : R ≃+* S) = e :=
  rfl
#align ring_equiv.coe_mk RingEquiv.coe_mkₓ

-- Porting note: `toEquiv_mk` no longer needed in Lean4
#noalign ring_equiv.to_equiv_mk

@[simp]
theorem mk_coe (e : R ≃+* S) (e' h₁ h₂ h₃ h₄) : (⟨⟨e, e', h₁, h₂⟩, h₃, h₄⟩ : R ≃+* S) = e :=
  ext fun _ => rfl
#align ring_equiv.mk_coe RingEquiv.mk_coe

protected theorem congr_arg {f : R ≃+* S} {x x' : R} : x = x' → f x = f x' :=
  FunLike.congr_arg f
#align ring_equiv.congr_arg RingEquiv.congr_arg

protected theorem congr_fun {f g : R ≃+* S} (h : f = g) (x : R) : f x = g x :=
  FunLike.congr_fun h x
#align ring_equiv.congr_fun RingEquiv.congr_fun

protected theorem ext_iff {f g : R ≃+* S} : f = g ↔ ∀ x, f x = g x :=
  FunLike.ext_iff
#align ring_equiv.ext_iff RingEquiv.ext_iff

@[simp]
theorem toAddEquiv_eq_coe (f : R ≃+* S) : f.toAddEquiv = ↑f :=
  rfl
#align ring_equiv.to_add_equiv_eq_coe RingEquiv.toAddEquiv_eq_coe

@[simp]
theorem toMulEquiv_eq_coe (f : R ≃+* S) : f.toMulEquiv = ↑f :=
  rfl
#align ring_equiv.to_mul_equiv_eq_coe RingEquiv.toMulEquiv_eq_coe

@[simp, norm_cast]
theorem coe_toMulEquiv (f : R ≃+* S) : ⇑(f : R ≃* S) = f :=
  rfl
#align ring_equiv.coe_to_mul_equiv RingEquiv.coe_toMulEquiv

@[simp]
theorem coe_toAddEquiv (f : R ≃+* S) : ⇑(f : R ≃+ S) = f :=
  rfl
#align ring_equiv.coe_to_add_equiv RingEquiv.coe_toAddEquiv

/-- The `RingEquiv` between two semirings with a unique element. -/
def ringEquivOfUnique {M N} [Unique M] [Unique N] [Add M] [Mul M] [Add N] [Mul N] : M ≃+* N :=
  { AddEquiv.addEquivOfUnique, MulEquiv.mulEquivOfUnique with }
#align ring_equiv.ring_equiv_of_unique RingEquiv.ringEquivOfUnique

instance {M N} [Unique M] [Unique N] [Add M] [Mul M] [Add N] [Mul N] :
    Unique (M ≃+* N) where
  default := ringEquivOfUnique
  uniq _ := ext fun _ => Subsingleton.elim _ _

variable (R)

/-- The identity map is a ring isomorphism. -/
@[refl]
def refl : R ≃+* R :=
  { MulEquiv.refl R, AddEquiv.refl R with }
#align ring_equiv.refl RingEquiv.refl

@[simp]
theorem refl_apply (x : R) : RingEquiv.refl R x = x :=
  rfl
#align ring_equiv.refl_apply RingEquiv.refl_apply

@[simp]
theorem coe_addEquiv_refl : (RingEquiv.refl R : R ≃+ R) = AddEquiv.refl R :=
  rfl
#align ring_equiv.coe_add_equiv_refl RingEquiv.coe_addEquiv_refl

@[simp]
theorem coe_mulEquiv_refl : (RingEquiv.refl R : R ≃* R) = MulEquiv.refl R :=
  rfl
#align ring_equiv.coe_mul_equiv_refl RingEquiv.coe_mulEquiv_refl

instance : Inhabited (R ≃+* R) :=
  ⟨RingEquiv.refl R⟩

variable {R}

/-- The inverse of a ring isomorphism is a ring isomorphism. -/
@[symm]
protected def symm (e : R ≃+* S) : S ≃+* R :=
  { e.toMulEquiv.symm, e.toAddEquiv.symm with }
#align ring_equiv.symm RingEquiv.symm

/-- See Note [custom simps projection] -/
def Simps.symm_apply (e : R ≃+* S) : S → R :=
  e.symm
#align ring_equiv.simps.symm_apply RingEquiv.Simps.symm_apply

initialize_simps_projections RingEquiv (toFun → apply, invFun → symm_apply)

@[simp]
theorem invFun_eq_symm (f : R ≃+* S) : EquivLike.inv f = f.symm :=
  rfl
#align ring_equiv.inv_fun_eq_symm RingEquiv.invFun_eq_symm

@[simp]
theorem symm_symm (e : R ≃+* S) : e.symm.symm = e :=
  ext fun _ => rfl
#align ring_equiv.symm_symm RingEquiv.symm_symm

--Porting note: new theorem
@[simp]
theorem symm_refl : (RingEquiv.refl R).symm = RingEquiv.refl R :=
  rfl

@[simp]
theorem coe_toEquiv_symm (e : R ≃+* S) : (e.symm : S ≃ R) = (e : R ≃ S).symm :=
  rfl
#align ring_equiv.coe_to_equiv_symm RingEquiv.coe_toEquiv_symm

theorem symm_bijective : Function.Bijective (RingEquiv.symm : R ≃+* S → S ≃+* R) :=
  Equiv.bijective ⟨RingEquiv.symm, RingEquiv.symm, symm_symm, symm_symm⟩
#align ring_equiv.symm_bijective RingEquiv.symm_bijective

@[simp]
theorem mk_coe' (e : R ≃+* S) (f h₁ h₂ h₃ h₄) :
    (⟨⟨f, ⇑e, h₁, h₂⟩, h₃, h₄⟩ : S ≃+* R) = e.symm :=
  symm_bijective.injective <| ext fun _ => rfl
#align ring_equiv.mk_coe' RingEquiv.mk_coe'

@[simp]
theorem symm_mk (f : R → S) (g h₁ h₂ h₃ h₄) :
    (mk ⟨f, g, h₁, h₂⟩ h₃ h₄).symm =
      { (mk ⟨f, g, h₁, h₂⟩ h₃ h₄).symm with
        toFun := g
        invFun := f } :=
  rfl
#align ring_equiv.symm_mk RingEquiv.symm_mk

/-- Transitivity of `RingEquiv`. -/
@[trans]
protected def trans (e₁ : R ≃+* S) (e₂ : S ≃+* S') : R ≃+* S' :=
  { e₁.toMulEquiv.trans e₂.toMulEquiv, e₁.toAddEquiv.trans e₂.toAddEquiv with }
#align ring_equiv.trans RingEquiv.trans

theorem trans_apply (e₁ : R ≃+* S) (e₂ : S ≃+* S') (a : R) : e₁.trans e₂ a = e₂ (e₁ a) :=
  rfl
#align ring_equiv.trans_apply RingEquiv.trans_apply

@[simp]
theorem coe_trans (e₁ : R ≃+* S) (e₂ : S ≃+* S') : (e₁.trans e₂ : R → S') = e₂ ∘ e₁ :=
  rfl
#align ring_equiv.coe_trans RingEquiv.coe_trans

@[simp]
theorem symm_trans_apply (e₁ : R ≃+* S) (e₂ : S ≃+* S') (a : S') :
    (e₁.trans e₂).symm a = e₁.symm (e₂.symm a) :=
  rfl
#align ring_equiv.symm_trans_apply RingEquiv.symm_trans_apply

theorem symm_trans (e₁ : R ≃+* S) (e₂ : S ≃+* S') : (e₁.trans e₂).symm = e₂.symm.trans e₁.symm :=
  rfl
#align ring_equiv.symm_trans RingEquiv.symm_trans

protected theorem bijective (e : R ≃+* S) : Function.Bijective e :=
  EquivLike.bijective e
#align ring_equiv.bijective RingEquiv.bijective

protected theorem injective (e : R ≃+* S) : Function.Injective e :=
  EquivLike.injective e
#align ring_equiv.injective RingEquiv.injective

protected theorem surjective (e : R ≃+* S) : Function.Surjective e :=
  EquivLike.surjective e
#align ring_equiv.surjective RingEquiv.surjective

@[simp]
theorem apply_symm_apply (e : R ≃+* S) : ∀ x, e (e.symm x) = x :=
  e.toEquiv.apply_symm_apply
#align ring_equiv.apply_symm_apply RingEquiv.apply_symm_apply

@[simp]
theorem symm_apply_apply (e : R ≃+* S) : ∀ x, e.symm (e x) = x :=
  e.toEquiv.symm_apply_apply
#align ring_equiv.symm_apply_apply RingEquiv.symm_apply_apply

theorem image_eq_preimage (e : R ≃+* S) (s : Set R) : e '' s = e.symm ⁻¹' s :=
  e.toEquiv.image_eq_preimage s
#align ring_equiv.image_eq_preimage RingEquiv.image_eq_preimage

@[simp]
theorem coe_mulEquiv_trans (e₁ : R ≃+* S) (e₂ : S ≃+* S') :
    (e₁.trans e₂ : R ≃* S') = (e₁ : R ≃* S).trans ↑e₂ :=
  rfl
#align ring_equiv.coe_mul_equiv_trans RingEquiv.coe_mulEquiv_trans

@[simp]
theorem coe_addEquiv_trans (e₁ : R ≃+* S) (e₂ : S ≃+* S') :
    (e₁.trans e₂ : R ≃+ S') = (e₁ : R ≃+ S).trans ↑e₂ :=
  rfl
#align ring_equiv.coe_add_equiv_trans RingEquiv.coe_addEquiv_trans

end Basic

section Opposite

open MulOpposite

/-- A ring iso `α ≃+* β` can equivalently be viewed as a ring iso `αᵐᵒᵖ ≃+* βᵐᵒᵖ`. -/
@[simps! symm_apply_apply symm_apply_symm_apply apply_apply apply_symm_apply]
protected def op {α β} [Add α] [Mul α] [Add β] [Mul β] :
    α ≃+* β ≃ (αᵐᵒᵖ ≃+* βᵐᵒᵖ) where
  toFun f := { AddEquiv.mulOp f.toAddEquiv, MulEquiv.op f.toMulEquiv with }
  invFun f := { AddEquiv.mulOp.symm f.toAddEquiv, MulEquiv.op.symm f.toMulEquiv with }
  left_inv f := by
    ext
    -- ⊢ ↑((fun f =>
    rfl
    -- 🎉 no goals
  right_inv f := by
    ext
    -- ⊢ ↑((fun f =>
    rfl
    -- 🎉 no goals
#align ring_equiv.op RingEquiv.op
#align ring_equiv.op_symm_apply_apply RingEquiv.op_symm_apply_apply
#align ring_equiv.op_symm_apply_symm_apply RingEquiv.op_symm_apply_symm_apply

/-- The 'unopposite' of a ring iso `αᵐᵒᵖ ≃+* βᵐᵒᵖ`. Inverse to `RingEquiv.op`. -/
@[simp]
protected def unop {α β} [Add α] [Mul α] [Add β] [Mul β] : αᵐᵒᵖ ≃+* βᵐᵒᵖ ≃ (α ≃+* β) :=
  RingEquiv.op.symm
#align ring_equiv.unop RingEquiv.unop

/-- A ring is isomorphic to the opposite of its opposite. -/
@[simps!]
def opOp (R : Type*) [Add R] [Mul R] : R ≃+* Rᵐᵒᵖᵐᵒᵖ where
  __ := MulEquiv.opOp R
  map_add' _ _ := rfl

section NonUnitalCommSemiring

variable (R) [NonUnitalCommSemiring R]

/-- A non-unital commutative ring is isomorphic to its opposite. -/
def toOpposite : R ≃+* Rᵐᵒᵖ :=
  { MulOpposite.opEquiv with
    map_add' := fun _ _ => rfl
    map_mul' := fun x y => mul_comm (op y) (op x) }
#align ring_equiv.to_opposite RingEquiv.toOpposite

@[simp]
theorem toOpposite_apply (r : R) : toOpposite R r = op r :=
  rfl
#align ring_equiv.to_opposite_apply RingEquiv.toOpposite_apply

@[simp]
theorem toOpposite_symm_apply (r : Rᵐᵒᵖ) : (toOpposite R).symm r = unop r :=
  rfl
#align ring_equiv.to_opposite_symm_apply RingEquiv.toOpposite_symm_apply

end NonUnitalCommSemiring

end Opposite

section NonUnitalSemiring

variable [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] (f : R ≃+* S) (x y : R)

/-- A ring isomorphism sends zero to zero. -/
protected theorem map_zero : f 0 = 0 :=
  map_zero f
#align ring_equiv.map_zero RingEquiv.map_zero

variable {x}

protected theorem map_eq_zero_iff : f x = 0 ↔ x = 0 :=
  AddEquivClass.map_eq_zero_iff f
#align ring_equiv.map_eq_zero_iff RingEquiv.map_eq_zero_iff

theorem map_ne_zero_iff : f x ≠ 0 ↔ x ≠ 0 :=
  AddEquivClass.map_ne_zero_iff f
#align ring_equiv.map_ne_zero_iff RingEquiv.map_ne_zero_iff

/-- Produce a ring isomorphism from a bijective ring homomorphism. -/
noncomputable def ofBijective [NonUnitalRingHomClass F R S] (f : F) (hf : Function.Bijective f) :
    R ≃+* S :=
  { Equiv.ofBijective f hf with
    map_mul' := map_mul f
    map_add' := map_add f }
#align ring_equiv.of_bijective RingEquiv.ofBijective

@[simp]
theorem coe_ofBijective [NonUnitalRingHomClass F R S] (f : F) (hf : Function.Bijective f) :
    (ofBijective f hf : R → S) = f :=
  rfl
#align ring_equiv.coe_of_bijective RingEquiv.coe_ofBijective

theorem ofBijective_apply [NonUnitalRingHomClass F R S] (f : F) (hf : Function.Bijective f)
    (x : R) : ofBijective f hf x = f x :=
  rfl
#align ring_equiv.of_bijective_apply RingEquiv.ofBijective_apply

/-- A family of ring isomorphisms `∀ j, (R j ≃+* S j)` generates a
ring isomorphisms between `∀ j, R j` and `∀ j, S j`.

This is the `RingEquiv` version of `Equiv.piCongrRight`, and the dependent version of
`RingEquiv.arrowCongr`.
-/
@[simps apply]
def piCongrRight {ι : Type*} {R S : ι → Type*} [∀ i, NonUnitalNonAssocSemiring (R i)]
    [∀ i, NonUnitalNonAssocSemiring (S i)] (e : ∀ i, R i ≃+* S i) : (∀ i, R i) ≃+* ∀ i, S i :=
  { @MulEquiv.piCongrRight ι R S _ _ fun i => (e i).toMulEquiv,
    @AddEquiv.piCongrRight ι R S _ _ fun i => (e i).toAddEquiv with
    toFun := fun x j => e j (x j)
    invFun := fun x j => (e j).symm (x j) }
#align ring_equiv.Pi_congr_right RingEquiv.piCongrRight
#align ring_equiv.Pi_congr_right_apply RingEquiv.piCongrRight_apply

@[simp]
theorem piCongrRight_refl {ι : Type*} {R : ι → Type*} [∀ i, NonUnitalNonAssocSemiring (R i)] :
    (piCongrRight fun i => RingEquiv.refl (R i)) = RingEquiv.refl _ :=
  rfl
#align ring_equiv.Pi_congr_right_refl RingEquiv.piCongrRight_refl

@[simp]
theorem piCongrRight_symm {ι : Type*} {R S : ι → Type*} [∀ i, NonUnitalNonAssocSemiring (R i)]
    [∀ i, NonUnitalNonAssocSemiring (S i)] (e : ∀ i, R i ≃+* S i) :
    (piCongrRight e).symm = piCongrRight fun i => (e i).symm :=
  rfl
#align ring_equiv.Pi_congr_right_symm RingEquiv.piCongrRight_symm

@[simp]
theorem piCongrRight_trans {ι : Type*} {R S T : ι → Type*}
    [∀ i, NonUnitalNonAssocSemiring (R i)] [∀ i, NonUnitalNonAssocSemiring (S i)]
    [∀ i, NonUnitalNonAssocSemiring (T i)] (e : ∀ i, R i ≃+* S i) (f : ∀ i, S i ≃+* T i) :
    (piCongrRight e).trans (piCongrRight f) = piCongrRight fun i => (e i).trans (f i) :=
  rfl
#align ring_equiv.Pi_congr_right_trans RingEquiv.piCongrRight_trans

end NonUnitalSemiring

section Semiring

variable [NonAssocSemiring R] [NonAssocSemiring S] (f : R ≃+* S) (x y : R)

/-- A ring isomorphism sends one to one. -/
protected theorem map_one : f 1 = 1 :=
  map_one f
#align ring_equiv.map_one RingEquiv.map_one

variable {x}

protected theorem map_eq_one_iff : f x = 1 ↔ x = 1 :=
  MulEquivClass.map_eq_one_iff f
#align ring_equiv.map_eq_one_iff RingEquiv.map_eq_one_iff

theorem map_ne_one_iff : f x ≠ 1 ↔ x ≠ 1 :=
  MulEquivClass.map_ne_one_iff f
#align ring_equiv.map_ne_one_iff RingEquiv.map_ne_one_iff

theorem coe_monoidHom_refl : (RingEquiv.refl R : R →* R) = MonoidHom.id R :=
  rfl
#align ring_equiv.coe_monoid_hom_refl RingEquiv.coe_monoidHom_refl

@[simp]
theorem coe_addMonoidHom_refl : (RingEquiv.refl R : R →+ R) = AddMonoidHom.id R :=
  rfl
#align ring_equiv.coe_add_monoid_hom_refl RingEquiv.coe_addMonoidHom_refl

/-! `RingEquiv.coe_mulEquiv_refl` and `RingEquiv.coe_addEquiv_refl` are proved above
in higher generality -/


@[simp]
theorem coe_ringHom_refl : (RingEquiv.refl R : R →+* R) = RingHom.id R :=
  rfl
#align ring_equiv.coe_ring_hom_refl RingEquiv.coe_ringHom_refl

@[simp]
theorem coe_monoidHom_trans [NonAssocSemiring S'] (e₁ : R ≃+* S) (e₂ : S ≃+* S') :
    (e₁.trans e₂ : R →* S') = (e₂ : S →* S').comp ↑e₁ :=
  rfl
#align ring_equiv.coe_monoid_hom_trans RingEquiv.coe_monoidHom_trans

@[simp]
theorem coe_addMonoidHom_trans [NonAssocSemiring S'] (e₁ : R ≃+* S) (e₂ : S ≃+* S') :
    (e₁.trans e₂ : R →+ S') = (e₂ : S →+ S').comp ↑e₁ :=
  rfl
#align ring_equiv.coe_add_monoid_hom_trans RingEquiv.coe_addMonoidHom_trans

/-! `RingEquiv.coe_mulEquiv_trans` and `RingEquiv.coe_addEquiv_trans` are proved above
in higher generality -/

@[simp]
theorem coe_ringHom_trans [NonAssocSemiring S'] (e₁ : R ≃+* S) (e₂ : S ≃+* S') :
    (e₁.trans e₂ : R →+* S') = (e₂ : S →+* S').comp ↑e₁ :=
  rfl
#align ring_equiv.coe_ring_hom_trans RingEquiv.coe_ringHom_trans

@[simp]
theorem comp_symm (e : R ≃+* S) : (e : R →+* S).comp (e.symm : S →+* R) = RingHom.id S :=
  RingHom.ext e.apply_symm_apply
#align ring_equiv.comp_symm RingEquiv.comp_symm

@[simp]
theorem symm_comp (e : R ≃+* S) : (e.symm : S →+* R).comp (e : R →+* S) = RingHom.id R :=
  RingHom.ext e.symm_apply_apply
#align ring_equiv.symm_comp RingEquiv.symm_comp

end Semiring

section NonUnitalRing

variable [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S] (f : R ≃+* S) (x y : R)

protected theorem map_neg : f (-x) = -f x :=
  map_neg f x
#align ring_equiv.map_neg RingEquiv.map_neg

protected theorem map_sub : f (x - y) = f x - f y :=
  map_sub f x y
#align ring_equiv.map_sub RingEquiv.map_sub

end NonUnitalRing

section Ring

variable [NonAssocRing R] [NonAssocRing S] (f : R ≃+* S) (x y : R)

-- Porting note: `simp` can now prove that, so we remove the `@[simp]` tag
theorem map_neg_one : f (-1) = -1 :=
  f.map_one ▸ f.map_neg 1
#align ring_equiv.map_neg_one RingEquiv.map_neg_one

theorem map_eq_neg_one_iff {x : R} : f x = -1 ↔ x = -1 := by
  rw [← neg_eq_iff_eq_neg, ← neg_eq_iff_eq_neg, ← map_neg, RingEquiv.map_eq_one_iff]
  -- 🎉 no goals
#align ring_equiv.map_eq_neg_one_iff RingEquiv.map_eq_neg_one_iff

end Ring

section NonUnitalSemiringHom

variable [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] [NonUnitalNonAssocSemiring S']

/-- Reinterpret a ring equivalence as a non-unital ring homomorphism. -/
def toNonUnitalRingHom (e : R ≃+* S) : R →ₙ+* S :=
  { e.toMulEquiv.toMulHom, e.toAddEquiv.toAddMonoidHom with }
#align ring_equiv.to_non_unital_ring_hom RingEquiv.toNonUnitalRingHom

theorem toNonUnitalRingHom_injective :
    Function.Injective (toNonUnitalRingHom : R ≃+* S → R →ₙ+* S) := fun _ _ h =>
  RingEquiv.ext (NonUnitalRingHom.ext_iff.1 h)
#align ring_equiv.to_non_unital_ring_hom_injective RingEquiv.toNonUnitalRingHom_injective

theorem toNonUnitalRingHom_eq_coe (f : R ≃+* S) : f.toNonUnitalRingHom = ↑f :=
  rfl
#align ring_equiv.to_non_unital_ring_hom_eq_coe RingEquiv.toNonUnitalRingHom_eq_coe

@[simp, norm_cast]
theorem coe_toNonUnitalRingHom (f : R ≃+* S) : ⇑(f : R →ₙ+* S) = f :=
  rfl
#align ring_equiv.coe_to_non_unital_ring_hom RingEquiv.coe_toNonUnitalRingHom

theorem coe_nonUnitalRingHom_inj_iff {R S : Type*} [NonUnitalNonAssocSemiring R]
    [NonUnitalNonAssocSemiring S] (f g : R ≃+* S) : f = g ↔ (f : R →ₙ+* S) = g :=
  ⟨fun h => by rw [h], fun h => ext <| NonUnitalRingHom.ext_iff.mp h⟩
               -- 🎉 no goals
#align ring_equiv.coe_non_unital_ring_hom_inj_iff RingEquiv.coe_nonUnitalRingHom_inj_iff

@[simp]
theorem toNonUnitalRingHom_refl :
    (RingEquiv.refl R).toNonUnitalRingHom = NonUnitalRingHom.id R :=
  rfl
#align ring_equiv.to_non_unital_ring_hom_refl RingEquiv.toNonUnitalRingHom_refl

@[simp]
theorem toNonUnitalRingHom_apply_symm_toNonUnitalRingHom_apply (e : R ≃+* S) :
    ∀ y : S, e.toNonUnitalRingHom (e.symm.toNonUnitalRingHom y) = y :=
  e.toEquiv.apply_symm_apply
#align ring_equiv.to_non_unital_ring_hom_apply_symm_to_non_unital_ring_hom_apply RingEquiv.toNonUnitalRingHom_apply_symm_toNonUnitalRingHom_apply

@[simp]
theorem symm_toNonUnitalRingHom_apply_toNonUnitalRingHom_apply (e : R ≃+* S) :
    ∀ x : R, e.symm.toNonUnitalRingHom (e.toNonUnitalRingHom x) = x :=
  Equiv.symm_apply_apply e.toEquiv
#align ring_equiv.symm_to_non_unital_ring_hom_apply_to_non_unital_ring_hom_apply RingEquiv.symm_toNonUnitalRingHom_apply_toNonUnitalRingHom_apply

@[simp]
theorem toNonUnitalRingHom_trans (e₁ : R ≃+* S) (e₂ : S ≃+* S') :
    (e₁.trans e₂).toNonUnitalRingHom = e₂.toNonUnitalRingHom.comp e₁.toNonUnitalRingHom :=
  rfl
#align ring_equiv.to_non_unital_ring_hom_trans RingEquiv.toNonUnitalRingHom_trans

@[simp]
theorem toNonUnitalRingHomm_comp_symm_toNonUnitalRingHom (e : R ≃+* S) :
    e.toNonUnitalRingHom.comp e.symm.toNonUnitalRingHom = NonUnitalRingHom.id _ := by
  ext
  -- ⊢ ↑(NonUnitalRingHom.comp (toNonUnitalRingHom e) (toNonUnitalRingHom (RingEqui …
  simp
  -- 🎉 no goals
#align ring_equiv.to_non_unital_ring_hom_comp_symm_to_non_unital_ring_hom RingEquiv.toNonUnitalRingHomm_comp_symm_toNonUnitalRingHom

@[simp]
theorem symm_toNonUnitalRingHom_comp_toNonUnitalRingHom (e : R ≃+* S) :
    e.symm.toNonUnitalRingHom.comp e.toNonUnitalRingHom = NonUnitalRingHom.id _ := by
  ext
  -- ⊢ ↑(NonUnitalRingHom.comp (toNonUnitalRingHom (RingEquiv.symm e)) (toNonUnital …
  simp
  -- 🎉 no goals
#align ring_equiv.symm_to_non_unital_ring_hom_comp_to_non_unital_ring_hom RingEquiv.symm_toNonUnitalRingHom_comp_toNonUnitalRingHom

end NonUnitalSemiringHom

section SemiringHom

variable [NonAssocSemiring R] [NonAssocSemiring S] [NonAssocSemiring S']

/-- Reinterpret a ring equivalence as a ring homomorphism. -/
def toRingHom (e : R ≃+* S) : R →+* S :=
  { e.toMulEquiv.toMonoidHom, e.toAddEquiv.toAddMonoidHom with }
#align ring_equiv.to_ring_hom RingEquiv.toRingHom

theorem toRingHom_injective : Function.Injective (toRingHom : R ≃+* S → R →+* S) := fun _ _ h =>
  RingEquiv.ext (RingHom.ext_iff.1 h)
#align ring_equiv.to_ring_hom_injective RingEquiv.toRingHom_injective

@[simp] theorem toRingHom_eq_coe (f : R ≃+* S) : f.toRingHom = ↑f :=
  rfl
#align ring_equiv.to_ring_hom_eq_coe RingEquiv.toRingHom_eq_coe

@[simp, norm_cast]
theorem coe_toRingHom (f : R ≃+* S) : ⇑(f : R →+* S) = f :=
  rfl
#align ring_equiv.coe_to_ring_hom RingEquiv.coe_toRingHom

theorem coe_ringHom_inj_iff {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S]
    (f g : R ≃+* S) : f = g ↔ (f : R →+* S) = g :=
  ⟨fun h => by rw [h], fun h => ext <| RingHom.ext_iff.mp h⟩
               -- 🎉 no goals
#align ring_equiv.coe_ring_hom_inj_iff RingEquiv.coe_ringHom_inj_iff

/-- The two paths coercion can take to a `NonUnitalRingEquiv` are equivalent -/
@[simp, norm_cast]
theorem toNonUnitalRingHom_commutes (f : R ≃+* S) :
    ((f : R →+* S) : R →ₙ+* S) = (f : R →ₙ+* S) :=
  rfl
#align ring_equiv.to_non_unital_ring_hom_commutes RingEquiv.toNonUnitalRingHom_commutes

/-- Reinterpret a ring equivalence as a monoid homomorphism. -/
abbrev toMonoidHom (e : R ≃+* S) : R →* S :=
  e.toRingHom.toMonoidHom
#align ring_equiv.to_monoid_hom RingEquiv.toMonoidHom

/-- Reinterpret a ring equivalence as an `AddMonoid` homomorphism. -/
abbrev toAddMonoidHom (e : R ≃+* S) : R →+ S :=
  e.toRingHom.toAddMonoidHom
#align ring_equiv.to_add_monoid_hom RingEquiv.toAddMonoidHom

/-- The two paths coercion can take to an `AddMonoidHom` are equivalent -/
theorem toAddMonoidMom_commutes (f : R ≃+* S) :
    (f : R →+* S).toAddMonoidHom = (f : R ≃+ S).toAddMonoidHom :=
  rfl
#align ring_equiv.to_add_monoid_hom_commutes RingEquiv.toAddMonoidMom_commutes

/-- The two paths coercion can take to a `MonoidHom` are equivalent -/
theorem toMonoidHom_commutes (f : R ≃+* S) :
    (f : R →+* S).toMonoidHom = (f : R ≃* S).toMonoidHom :=
  rfl
#align ring_equiv.to_monoid_hom_commutes RingEquiv.toMonoidHom_commutes

/-- The two paths coercion can take to an `Equiv` are equivalent -/
theorem toEquiv_commutes (f : R ≃+* S) : (f : R ≃+ S).toEquiv = (f : R ≃* S).toEquiv :=
  rfl
#align ring_equiv.to_equiv_commutes RingEquiv.toEquiv_commutes

@[simp]
theorem toRingHom_refl : (RingEquiv.refl R).toRingHom = RingHom.id R :=
  rfl
#align ring_equiv.to_ring_hom_refl RingEquiv.toRingHom_refl

@[simp]
theorem toMonoidHom_refl : (RingEquiv.refl R).toMonoidHom = MonoidHom.id R :=
  rfl
#align ring_equiv.to_monoid_hom_refl RingEquiv.toMonoidHom_refl

@[simp]
theorem toAddMonoidHom_refl : (RingEquiv.refl R).toAddMonoidHom = AddMonoidHom.id R :=
  rfl
#align ring_equiv.to_add_monoid_hom_refl RingEquiv.toAddMonoidHom_refl

-- Porting note : Now other `simp` can do this, so removed `simp` attribute
theorem toRingHom_apply_symm_toRingHom_apply (e : R ≃+* S) :
    ∀ y : S, e.toRingHom (e.symm.toRingHom y) = y :=
  e.toEquiv.apply_symm_apply
#align ring_equiv.to_ring_hom_apply_symm_to_ring_hom_apply RingEquiv.toRingHom_apply_symm_toRingHom_apply

-- Porting note : Now other `simp` can do this, so removed `simp` attribute
theorem symm_toRingHom_apply_toRingHom_apply (e : R ≃+* S) :
    ∀ x : R, e.symm.toRingHom (e.toRingHom x) = x :=
  Equiv.symm_apply_apply e.toEquiv
#align ring_equiv.symm_to_ring_hom_apply_to_ring_hom_apply RingEquiv.symm_toRingHom_apply_toRingHom_apply

@[simp]
theorem toRingHom_trans (e₁ : R ≃+* S) (e₂ : S ≃+* S') :
    (e₁.trans e₂).toRingHom = e₂.toRingHom.comp e₁.toRingHom :=
  rfl
#align ring_equiv.to_ring_hom_trans RingEquiv.toRingHom_trans

-- Porting note : Now other `simp` can do this, so removed `simp` attribute
theorem toRingHom_comp_symm_toRingHom (e : R ≃+* S) :
    e.toRingHom.comp e.symm.toRingHom = RingHom.id _ := by
  ext
  -- ⊢ ↑(RingHom.comp (toRingHom e) (toRingHom (RingEquiv.symm e))) x✝ = ↑(RingHom. …
  simp
  -- 🎉 no goals
#align ring_equiv.to_ring_hom_comp_symm_to_ring_hom RingEquiv.toRingHom_comp_symm_toRingHom

-- Porting note : Now other `simp` can do this, so removed `simp` attribute
theorem symm_toRingHom_comp_toRingHom (e : R ≃+* S) :
    e.symm.toRingHom.comp e.toRingHom = RingHom.id _ := by
  ext
  -- ⊢ ↑(RingHom.comp (toRingHom (RingEquiv.symm e)) (toRingHom e)) x✝ = ↑(RingHom. …
  simp
  -- 🎉 no goals
#align ring_equiv.symm_to_ring_hom_comp_to_ring_hom RingEquiv.symm_toRingHom_comp_toRingHom

/-- Construct an equivalence of rings from homomorphisms in both directions, which are inverses.
-/
@[simps]
def ofHomInv' {R S F G : Type*} [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]
    [NonUnitalRingHomClass F R S] [NonUnitalRingHomClass G S R] (hom : F) (inv : G)
    (hom_inv_id : (inv : S →ₙ+* R).comp (hom : R →ₙ+* S) = NonUnitalRingHom.id R)
    (inv_hom_id : (hom : R →ₙ+* S).comp (inv : S →ₙ+* R) = NonUnitalRingHom.id S) :
    R ≃+* S where
  toFun := hom
  invFun := inv
  left_inv := FunLike.congr_fun hom_inv_id
  right_inv := FunLike.congr_fun inv_hom_id
  map_mul' := map_mul hom
  map_add' := map_add hom
#align ring_equiv.of_hom_inv' RingEquiv.ofHomInv'
#align ring_equiv.of_hom_inv'_symm_apply RingEquiv.ofHomInv'_symm_apply
#align ring_equiv.of_hom_inv'_apply RingEquiv.ofHomInv'_apply

/--
Construct an equivalence of rings from unital homomorphisms in both directions, which are inverses.
-/
@[simps]
def ofHomInv {R S F G : Type*} [NonAssocSemiring R] [NonAssocSemiring S] [RingHomClass F R S]
    [RingHomClass G S R] (hom : F) (inv : G)
    (hom_inv_id : (inv : S →+* R).comp (hom : R →+* S) = RingHom.id R)
    (inv_hom_id : (hom : R →+* S).comp (inv : S →+* R) = RingHom.id S) :
    R ≃+* S where
  toFun := hom
  invFun := inv
  left_inv := FunLike.congr_fun hom_inv_id
  right_inv := FunLike.congr_fun inv_hom_id
  map_mul' := map_mul hom
  map_add' := map_add hom
#align ring_equiv.of_hom_inv RingEquiv.ofHomInv
#align ring_equiv.of_hom_inv_apply RingEquiv.ofHomInv_apply
#align ring_equiv.of_hom_inv_symm_apply RingEquiv.ofHomInv_symm_apply

end SemiringHom

section GroupPower

variable [Semiring R] [Semiring S]

protected theorem map_pow (f : R ≃+* S) (a) : ∀ n : ℕ, f (a ^ n) = f a ^ n :=
  map_pow f a
#align ring_equiv.map_pow RingEquiv.map_pow

end GroupPower

end RingEquiv

namespace MulEquiv

/-- Gives a `RingEquiv` from an element of a `MulEquivClass` preserving addition.-/
def toRingEquiv {R S F : Type*} [Add R] [Add S] [Mul R] [Mul S] [MulEquivClass F R S] (f : F)
    (H : ∀ x y : R, f (x + y) = f x + f y) : R ≃+* S :=
  { (f : R ≃* S).toEquiv, (f : R ≃* S), AddEquiv.mk' (f : R ≃* S).toEquiv H with }
#align mul_equiv.to_ring_equiv MulEquiv.toRingEquiv

end MulEquiv

namespace AddEquiv

/-- Gives a `RingEquiv` from an element of an `AddEquivClass` preserving addition.-/
def toRingEquiv {R S F : Type*} [Add R] [Add S] [Mul R] [Mul S] [AddEquivClass F R S] (f : F)
    (H : ∀ x y : R, f (x * y) = f x * f y) : R ≃+* S :=
  { (f : R ≃+ S).toEquiv, (f : R ≃+ S), MulEquiv.mk' (f : R ≃+ S).toEquiv H with }
#align add_equiv.to_ring_equiv AddEquiv.toRingEquiv

end AddEquiv

namespace RingEquiv

variable [Add R] [Add S] [Mul R] [Mul S]

@[simp]
theorem self_trans_symm (e : R ≃+* S) : e.trans e.symm = RingEquiv.refl R :=
  ext e.left_inv
#align ring_equiv.self_trans_symm RingEquiv.self_trans_symm

@[simp]
theorem symm_trans_self (e : R ≃+* S) : e.symm.trans e = RingEquiv.refl S :=
  ext e.right_inv
#align ring_equiv.symm_trans_self RingEquiv.symm_trans_self

end RingEquiv

namespace MulEquiv

/-- If two rings are isomorphic, and the second doesn't have zero divisors,
then so does the first. -/
protected theorem noZeroDivisors {A : Type*} (B : Type*) [MulZeroClass A] [MulZeroClass B]
    [NoZeroDivisors B] (e : A ≃* B) : NoZeroDivisors A :=
  e.injective.noZeroDivisors e (map_zero e) (map_mul e)
#noalign ring_equiv.no_zero_divisors

/-- If two rings are isomorphic, and the second is a domain, then so is the first. -/
protected theorem isDomain {A : Type*} (B : Type*) [Semiring A] [Semiring B] [IsDomain B]
    (e : A ≃* B) : IsDomain A :=
  { e.injective.isLeftCancelMulZero e (map_zero e) (map_mul e),
    e.injective.isRightCancelMulZero e (map_zero e) (map_mul e) with
    exists_pair_ne := ⟨e.symm 0, e.symm 1, e.symm.injective.ne zero_ne_one⟩ }
#noalign ring_equiv.is_domain

protected theorem isField {A : Type*} (B : Type*) [Semiring A] [Semiring B] (hB : IsField B)
    (e : A ≃* B) : IsField A where
  exists_pair_ne := have ⟨x, y, h⟩ := hB.exists_pair_ne; ⟨e.symm x, e.symm y, e.symm.injective.ne h⟩
  mul_comm := fun x y => e.injective <| by rw [map_mul, map_mul, hB.mul_comm]
                                           -- 🎉 no goals
  mul_inv_cancel := fun h => by
    obtain ⟨a', he⟩ := hB.mul_inv_cancel ((e.injective.ne h).trans_eq <| map_zero e)
    -- ⊢ ∃ b, a✝ * b = 1
    exact ⟨e.symm a', e.injective <| by rw [map_mul, map_one, e.apply_symm_apply, he]⟩
    -- 🎉 no goals

end MulEquiv

-- guard against import creep
assert_not_exists Fintype
