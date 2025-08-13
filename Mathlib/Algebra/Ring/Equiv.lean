/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
import Mathlib.Algebra.Group.Equiv.Opposite
import Mathlib.Algebra.GroupWithZero.Equiv
import Mathlib.Algebra.GroupWithZero.InjSurj
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Logic.Equiv.Set
import Mathlib.Algebra.Notation.Prod

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

-- guard against import creep
assert_not_exists Field Fintype

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

/-- Notation for `RingEquiv`. -/
infixl:25 " ≃+* " => RingEquiv

/-- The "plain" equivalence of types underlying an equivalence of (semi)rings. -/
add_decl_doc RingEquiv.toEquiv

/-- The equivalence of additive monoids underlying an equivalence of (semi)rings. -/
add_decl_doc RingEquiv.toAddEquiv

/-- The equivalence of multiplicative monoids underlying an equivalence of (semi)rings. -/
add_decl_doc RingEquiv.toMulEquiv

/-- `RingEquivClass F R S` states that `F` is a type of ring structure preserving equivalences.
You should extend this class when you extend `RingEquiv`. -/
class RingEquivClass (F R S : Type*) [Mul R] [Add R] [Mul S] [Add S] [EquivLike F R S] : Prop
  extends MulEquivClass F R S where
  /-- By definition, a ring isomorphism preserves the additive structure. -/
  map_add : ∀ (f : F) (a b), f (a + b) = f a + f b

namespace RingEquivClass

variable [EquivLike F R S]

-- See note [lower instance priority]
instance (priority := 100) toAddEquivClass [Mul R] [Add R]
    [Mul S] [Add S] [h : RingEquivClass F R S] : AddEquivClass F R S :=
  { h with }

-- See note [lower instance priority]
instance (priority := 100) toRingHomClass [NonAssocSemiring R] [NonAssocSemiring S]
    [h : RingEquivClass F R S] : RingHomClass F R S :=
  { h with
    map_zero := map_zero
    map_one := map_one }

-- See note [lower instance priority]
instance (priority := 100) toNonUnitalRingHomClass [NonUnitalNonAssocSemiring R]
    [NonUnitalNonAssocSemiring S] [h : RingEquivClass F R S] : NonUnitalRingHomClass F R S :=
  { h with
    map_zero := map_zero }

/-- Turn an element of a type `F` satisfying `RingEquivClass F α β` into an actual
`RingEquiv`. This is declared as the default coercion from `F` to `α ≃+* β`. -/
@[coe]
def toRingEquiv [Mul α] [Add α] [Mul β] [Add β] [EquivLike F α β] [RingEquivClass F α β] (f : F) :
    α ≃+* β :=
  { (f : α ≃* β), (f : α ≃+ β) with }

end RingEquivClass

/-- Any type satisfying `RingEquivClass` can be cast into `RingEquiv` via
`RingEquivClass.toRingEquiv`. -/
instance [Mul α] [Add α] [Mul β] [Add β] [EquivLike F α β] [RingEquivClass F α β] :
    CoeTC F (α ≃+* β) :=
  ⟨RingEquivClass.toRingEquiv⟩

namespace RingEquiv

section Basic

variable [Mul R] [Mul S] [Add R] [Add S] [Mul S'] [Add S']

section coe

instance : EquivLike (R ≃+* S) R S where
  coe f := f.toFun
  inv f := f.invFun
  coe_injective' e f h₁ h₂ := by
    cases e
    cases f
    congr
    apply Equiv.coe_fn_injective h₁
  left_inv f := f.left_inv
  right_inv f := f.right_inv

instance : RingEquivClass (R ≃+* S) R S where
  map_add f := f.map_add'
  map_mul f := f.map_mul'

/-- Two ring isomorphisms agree if they are defined by the same underlying function. -/
@[ext]
theorem ext {f g : R ≃+* S} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

protected theorem congr_arg {f : R ≃+* S} {x x' : R} : x = x' → f x = f x' :=
  DFunLike.congr_arg f

protected theorem congr_fun {f g : R ≃+* S} (h : f = g) (x : R) : f x = g x :=
  DFunLike.congr_fun h x

@[simp]
theorem coe_mk (e h₃ h₄) : ⇑(⟨e, h₃, h₄⟩ : R ≃+* S) = e :=
  rfl

@[simp]
theorem mk_coe (e : R ≃+* S) (e' h₁ h₂ h₃ h₄) : (⟨⟨e, e', h₁, h₂⟩, h₃, h₄⟩ : R ≃+* S) = e :=
  ext fun _ => rfl

@[simp]
theorem toEquiv_eq_coe (f : R ≃+* S) : f.toEquiv = f :=
  rfl

@[simp]
theorem coe_toEquiv (f : R ≃+* S) : ⇑(f : R ≃ S) = f :=
  rfl

@[simp]
theorem toAddEquiv_eq_coe (f : R ≃+* S) : f.toAddEquiv = ↑f :=
  rfl

@[simp]
theorem toMulEquiv_eq_coe (f : R ≃+* S) : f.toMulEquiv = ↑f :=
  rfl

@[simp, norm_cast]
theorem coe_toMulEquiv (f : R ≃+* S) : ⇑(f : R ≃* S) = f :=
  rfl

@[simp]
theorem coe_toAddEquiv (f : R ≃+* S) : ⇑(f : R ≃+ S) = f :=
  rfl

end coe

section map

/-- A ring isomorphism preserves multiplication. -/
protected theorem map_mul (e : R ≃+* S) (x y : R) : e (x * y) = e x * e y :=
  map_mul e x y

/-- A ring isomorphism preserves addition. -/
protected theorem map_add (e : R ≃+* S) (x y : R) : e (x + y) = e x + e y :=
  map_add e x y

end map

section bijective

protected theorem bijective (e : R ≃+* S) : Function.Bijective e :=
  EquivLike.bijective e

protected theorem injective (e : R ≃+* S) : Function.Injective e :=
  EquivLike.injective e

protected theorem surjective (e : R ≃+* S) : Function.Surjective e :=
  EquivLike.surjective e

end bijective

variable (R)

section refl

/-- The identity map is a ring isomorphism. -/
@[refl]
def refl : R ≃+* R :=
  { MulEquiv.refl R, AddEquiv.refl R with }

instance : Inhabited (R ≃+* R) :=
  ⟨RingEquiv.refl R⟩

@[simp]
theorem refl_apply (x : R) : RingEquiv.refl R x = x :=
  rfl

@[simp]
theorem coe_refl (R : Type*) [Mul R] [Add R] : ⇑(RingEquiv.refl R) = id :=
  rfl

@[deprecated coe_refl (since := "2025-02-10")]
alias coe_refl_id := coe_refl

@[simp]
theorem coe_addEquiv_refl : (RingEquiv.refl R : R ≃+ R) = AddEquiv.refl R :=
  rfl

@[simp]
theorem coe_mulEquiv_refl : (RingEquiv.refl R : R ≃* R) = MulEquiv.refl R :=
  rfl

end refl

variable {R}

section symm

/-- The inverse of a ring isomorphism is a ring isomorphism. -/
@[symm]
protected def symm (e : R ≃+* S) : S ≃+* R :=
  { e.toMulEquiv.symm, e.toAddEquiv.symm with }

@[simp]
theorem invFun_eq_symm (f : R ≃+* S) : EquivLike.inv f = f.symm :=
  rfl

@[simp]
theorem symm_symm (e : R ≃+* S) : e.symm.symm = e := rfl

theorem symm_bijective : Function.Bijective (RingEquiv.symm : (R ≃+* S) → S ≃+* R) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]
theorem mk_coe' (e : R ≃+* S) (f h₁ h₂ h₃ h₄) :
    (⟨⟨f, ⇑e, h₁, h₂⟩, h₃, h₄⟩ : S ≃+* R) = e.symm :=
  symm_bijective.injective <| ext fun _ => rfl

/-- Auxiliary definition to avoid looping in `dsimp` with `RingEquiv.symm_mk`. -/
protected def symm_mk.aux (f : R → S) (g h₁ h₂ h₃ h₄) := (mk ⟨f, g, h₁, h₂⟩ h₃ h₄).symm

@[simp]
theorem symm_mk (f : R → S) (g h₁ h₂ h₃ h₄) :
    (mk ⟨f, g, h₁, h₂⟩ h₃ h₄).symm =
      { symm_mk.aux f g h₁ h₂ h₃ h₄ with
        toFun := g
        invFun := f } :=
  rfl

@[simp]
theorem symm_refl : (RingEquiv.refl R).symm = RingEquiv.refl R :=
  rfl

@[simp]
theorem coe_toEquiv_symm (e : R ≃+* S) : (e.symm : S ≃ R) = (e : R ≃ S).symm :=
  rfl

@[simp]
theorem coe_toMulEquiv_symm (e : R ≃+* S) : (e.symm : S ≃* R) = (e : R ≃* S).symm :=
  rfl

@[simp]
theorem coe_toAddEquiv_symm (e : R ≃+* S) : (e.symm : S ≃+ R) = (e : R ≃+ S).symm :=
  rfl

@[simp]
theorem apply_symm_apply (e : R ≃+* S) : ∀ x, e (e.symm x) = x :=
  e.toEquiv.apply_symm_apply

@[simp]
theorem symm_apply_apply (e : R ≃+* S) : ∀ x, e.symm (e x) = x :=
  e.toEquiv.symm_apply_apply

theorem image_eq_preimage (e : R ≃+* S) (s : Set R) : e '' s = e.symm ⁻¹' s :=
  e.toEquiv.image_eq_preimage s

theorem symm_apply_eq (e : R ≃+* S) {x : S} {y : R} :
    e.symm x = y ↔ x = e y := Equiv.symm_apply_eq _

theorem eq_symm_apply (e : R ≃+* S) {x : S} {y : R} :
    y = e.symm x ↔ e y = x := Equiv.eq_symm_apply _

end symm

section simps

/-- See Note [custom simps projection] -/
def Simps.symm_apply (e : R ≃+* S) : S → R :=
  e.symm

initialize_simps_projections RingEquiv (toFun → apply, invFun → symm_apply)

end simps

section trans

/-- Transitivity of `RingEquiv`. -/
@[trans]
protected def trans (e₁ : R ≃+* S) (e₂ : S ≃+* S') : R ≃+* S' :=
  { e₁.toMulEquiv.trans e₂.toMulEquiv, e₁.toAddEquiv.trans e₂.toAddEquiv with }

@[simp]
theorem coe_trans (e₁ : R ≃+* S) (e₂ : S ≃+* S') : (e₁.trans e₂ : R → S') = e₂ ∘ e₁ :=
  rfl

theorem trans_apply (e₁ : R ≃+* S) (e₂ : S ≃+* S') (a : R) : e₁.trans e₂ a = e₂ (e₁ a) :=
  rfl

@[simp]
theorem symm_trans_apply (e₁ : R ≃+* S) (e₂ : S ≃+* S') (a : S') :
    (e₁.trans e₂).symm a = e₁.symm (e₂.symm a) :=
  rfl

theorem symm_trans (e₁ : R ≃+* S) (e₂ : S ≃+* S') : (e₁.trans e₂).symm = e₂.symm.trans e₁.symm :=
  rfl

@[simp]
theorem coe_mulEquiv_trans (e₁ : R ≃+* S) (e₂ : S ≃+* S') :
    (e₁.trans e₂ : R ≃* S') = (e₁ : R ≃* S).trans ↑e₂ :=
  rfl

@[simp]
theorem coe_addEquiv_trans (e₁ : R ≃+* S) (e₂ : S ≃+* S') :
    (e₁.trans e₂ : R ≃+ S') = (e₁ : R ≃+ S).trans ↑e₂ :=
  rfl

end trans

section unique

/-- The `RingEquiv` between two semirings with a unique element. -/
def ofUnique {M N} [Unique M] [Unique N] [Add M] [Mul M] [Add N] [Mul N] : M ≃+* N :=
  { AddEquiv.ofUnique, MulEquiv.ofUnique with }

instance {M N} [Unique M] [Unique N] [Add M] [Mul M] [Add N] [Mul N] :
    Unique (M ≃+* N) where
  default := .ofUnique
  uniq _ := ext fun _ => Subsingleton.elim _ _

end unique

end Basic

section Opposite

open MulOpposite

/-- A ring iso `α ≃+* β` can equivalently be viewed as a ring iso `αᵐᵒᵖ ≃+* βᵐᵒᵖ`. -/
@[simps! symm_apply_apply symm_apply_symm_apply apply_apply apply_symm_apply]
protected def op {α β} [Add α] [Mul α] [Add β] [Mul β] :
    α ≃+* β ≃ (αᵐᵒᵖ ≃+* βᵐᵒᵖ) where
  toFun f := { AddEquiv.mulOp f.toAddEquiv, MulEquiv.op f.toMulEquiv with }
  invFun f := { AddEquiv.mulOp.symm f.toAddEquiv, MulEquiv.op.symm f.toMulEquiv with }

/-- The 'unopposite' of a ring iso `αᵐᵒᵖ ≃+* βᵐᵒᵖ`. Inverse to `RingEquiv.op`. -/
@[simp]
protected def unop {α β} [Add α] [Mul α] [Add β] [Mul β] : αᵐᵒᵖ ≃+* βᵐᵒᵖ ≃ (α ≃+* β) :=
  RingEquiv.op.symm

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

@[simp]
theorem toOpposite_apply (r : R) : toOpposite R r = op r :=
  rfl

@[simp]
theorem toOpposite_symm_apply (r : Rᵐᵒᵖ) : (toOpposite R).symm r = unop r :=
  rfl

end NonUnitalCommSemiring

end Opposite

section NonUnitalSemiring

variable [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] (f : R ≃+* S) (x : R)

/-- A ring isomorphism sends zero to zero. -/
protected theorem map_zero : f 0 = 0 :=
  map_zero f

variable {x}

protected theorem map_eq_zero_iff : f x = 0 ↔ x = 0 :=
  EmbeddingLike.map_eq_zero_iff

theorem map_ne_zero_iff : f x ≠ 0 ↔ x ≠ 0 :=
  EmbeddingLike.map_ne_zero_iff

variable [FunLike F R S]

/-- Produce a ring isomorphism from a bijective ring homomorphism. -/
noncomputable def ofBijective [NonUnitalRingHomClass F R S] (f : F) (hf : Function.Bijective f) :
    R ≃+* S :=
  { Equiv.ofBijective f hf with
    map_mul' := map_mul f
    map_add' := map_add f }

@[simp]
theorem coe_ofBijective [NonUnitalRingHomClass F R S] (f : F) (hf : Function.Bijective f) :
    (ofBijective f hf : R → S) = f :=
  rfl

theorem ofBijective_apply [NonUnitalRingHomClass F R S] (f : F) (hf : Function.Bijective f)
    (x : R) : ofBijective f hf x = f x :=
  rfl

/-- Product of a singleton family of (non-unital non-associative semi)rings is isomorphic
to the only member of this family. -/
@[simps! -fullyApplied]
def piUnique {ι : Type*} (R : ι → Type*) [Unique ι] [∀ i, NonUnitalNonAssocSemiring (R i)] :
    (∀ i, R i) ≃+* R default where
  __ := Equiv.piUnique R
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

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

@[simp]
theorem piCongrRight_refl {ι : Type*} {R : ι → Type*} [∀ i, NonUnitalNonAssocSemiring (R i)] :
    (piCongrRight fun i => RingEquiv.refl (R i)) = RingEquiv.refl _ :=
  rfl

@[simp]
theorem piCongrRight_symm {ι : Type*} {R S : ι → Type*} [∀ i, NonUnitalNonAssocSemiring (R i)]
    [∀ i, NonUnitalNonAssocSemiring (S i)] (e : ∀ i, R i ≃+* S i) :
    (piCongrRight e).symm = piCongrRight fun i => (e i).symm :=
  rfl

@[simp]
theorem piCongrRight_trans {ι : Type*} {R S T : ι → Type*}
    [∀ i, NonUnitalNonAssocSemiring (R i)] [∀ i, NonUnitalNonAssocSemiring (S i)]
    [∀ i, NonUnitalNonAssocSemiring (T i)] (e : ∀ i, R i ≃+* S i) (f : ∀ i, S i ≃+* T i) :
    (piCongrRight e).trans (piCongrRight f) = piCongrRight fun i => (e i).trans (f i) :=
  rfl

/-- Transport dependent functions through an equivalence of the base space.

This is `Equiv.piCongrLeft'` as a `RingEquiv`. -/
@[simps!]
def piCongrLeft' {ι ι' : Type*} (R : ι → Type*) (e : ι ≃ ι')
    [∀ i, NonUnitalNonAssocSemiring (R i)] :
    ((i : ι) → R i) ≃+* ((i : ι') → R (e.symm i)) where
  toEquiv := Equiv.piCongrLeft' R e
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

@[simp]
theorem piCongrLeft'_symm {R : Type*} [NonUnitalNonAssocSemiring R] (e : α ≃ β) :
    (RingEquiv.piCongrLeft' (fun _ => R) e).symm = RingEquiv.piCongrLeft' _ e.symm := by
  simp only [piCongrLeft', RingEquiv.symm, MulEquiv.symm, Equiv.piCongrLeft'_symm]

/-- Transport dependent functions through an equivalence of the base space.

This is `Equiv.piCongrLeft` as a `RingEquiv`. -/
@[simps!]
def piCongrLeft {ι ι' : Type*} (S : ι' → Type*) (e : ι ≃ ι')
    [∀ i, NonUnitalNonAssocSemiring (S i)] :
    ((i : ι) → S (e i)) ≃+* ((i : ι') → S i) :=
  (RingEquiv.piCongrLeft' S e.symm).symm

/-- Splits the indices of ring `∀ (i : ι), Y i` along the predicate `p`. This is
`Equiv.piEquivPiSubtypeProd` as a `RingEquiv`. -/
@[simps!]
def piEquivPiSubtypeProd {ι : Type*} (p : ι → Prop) [DecidablePred p] (Y : ι → Type*)
    [∀ i, NonUnitalNonAssocSemiring (Y i)] :
    ((i : ι) → Y i) ≃+* ((i : { x : ι // p x }) → Y i) × ((i : { x : ι // ¬p x }) → Y i) where
  toEquiv := Equiv.piEquivPiSubtypeProd p Y
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- Product of ring equivalences. This is `Equiv.prodCongr` as a `RingEquiv`. -/
@[simps!]
def prodCongr {R R' S S' : Type*} [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring R']
    [NonUnitalNonAssocSemiring S] [NonUnitalNonAssocSemiring S']
    (f : R ≃+* R') (g : S ≃+* S') :
    R × S ≃+* R' × S' where
  toEquiv := Equiv.prodCongr f g
  map_mul' _ _ := by
    simp only [Equiv.toFun_as_coe, Equiv.prodCongr_apply, EquivLike.coe_coe,
      Prod.map, map_mul, Prod.mk_mul_mk]
  map_add' _ _ := by
    simp only [Equiv.toFun_as_coe, Equiv.prodCongr_apply, EquivLike.coe_coe,
      Prod.map, map_add, Prod.mk_add_mk]

@[simp]
theorem coe_prodCongr {R R' S S' : Type*} [NonUnitalNonAssocSemiring R]
    [NonUnitalNonAssocSemiring R'] [NonUnitalNonAssocSemiring S] [NonUnitalNonAssocSemiring S']
    (f : R ≃+* R') (g : S ≃+* S') :
    ⇑(RingEquiv.prodCongr f g) = Prod.map f g :=
  rfl

/-- This is `Equiv.piOptionEquivProd` as a `RingEquiv`. -/
@[simps!]
def piOptionEquivProd {ι : Type*} {R : Option ι → Type*} [Π i, NonUnitalNonAssocSemiring (R i)] :
    (Π i, R i) ≃+* R none × (Π i, R (some i)) where
  toEquiv := Equiv.piOptionEquivProd
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

end NonUnitalSemiring

section Semiring

variable [NonAssocSemiring R] [NonAssocSemiring S] (f : R ≃+* S) (x : R)

/-- A ring isomorphism sends one to one. -/
protected theorem map_one : f 1 = 1 :=
  map_one f

variable {x}

protected theorem map_eq_one_iff : f x = 1 ↔ x = 1 :=
  EmbeddingLike.map_eq_one_iff

theorem map_ne_one_iff : f x ≠ 1 ↔ x ≠ 1 :=
  EmbeddingLike.map_ne_one_iff

theorem coe_monoidHom_refl : (RingEquiv.refl R : R →* R) = MonoidHom.id R :=
  rfl

@[simp]
theorem coe_addMonoidHom_refl : (RingEquiv.refl R : R →+ R) = AddMonoidHom.id R :=
  rfl

/-! `RingEquiv.coe_mulEquiv_refl` and `RingEquiv.coe_addEquiv_refl` are proved above
in higher generality -/


@[simp]
theorem coe_ringHom_refl : (RingEquiv.refl R : R →+* R) = RingHom.id R :=
  rfl

@[simp]
theorem coe_monoidHom_trans [NonAssocSemiring S'] (e₁ : R ≃+* S) (e₂ : S ≃+* S') :
    (e₁.trans e₂ : R →* S') = (e₂ : S →* S').comp ↑e₁ :=
  rfl

@[simp]
theorem coe_addMonoidHom_trans [NonUnitalNonAssocSemiring S'] (e₁ : R ≃+* S) (e₂ : S ≃+* S') :
    (e₁.trans e₂ : R →+ S') = (e₂ : S →+ S').comp ↑e₁ :=
  rfl

/-! `RingEquiv.coe_mulEquiv_trans` and `RingEquiv.coe_addEquiv_trans` are proved above
in higher generality -/

@[simp]
theorem coe_ringHom_trans [NonAssocSemiring S'] (e₁ : R ≃+* S) (e₂ : S ≃+* S') :
    (e₁.trans e₂ : R →+* S') = (e₂ : S →+* S').comp ↑e₁ :=
  rfl

@[simp]
theorem comp_symm (e : R ≃+* S) : (e : R →+* S).comp (e.symm : S →+* R) = RingHom.id S :=
  RingHom.ext e.apply_symm_apply

@[simp]
theorem symm_comp (e : R ≃+* S) : (e.symm : S →+* R).comp (e : R →+* S) = RingHom.id R :=
  RingHom.ext e.symm_apply_apply

end Semiring

section NonUnitalRing

variable [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S] (f : R ≃+* S) (x y : R)

protected theorem map_neg : f (-x) = -f x :=
  map_neg f x

protected theorem map_sub : f (x - y) = f x - f y :=
  map_sub f x y

end NonUnitalRing

section Ring

variable [NonAssocRing R] [NonAssocRing S] (f : R ≃+* S)

@[simp]
theorem map_neg_one : f (-1) = -1 :=
  f.map_one ▸ f.map_neg 1

theorem map_eq_neg_one_iff {x : R} : f x = -1 ↔ x = -1 := by
  rw [← neg_eq_iff_eq_neg, ← neg_eq_iff_eq_neg, ← map_neg, RingEquiv.map_eq_one_iff]

end Ring

section NonUnitalSemiringHom

variable [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] [NonUnitalNonAssocSemiring S']

/-- Reinterpret a ring equivalence as a non-unital ring homomorphism. -/
def toNonUnitalRingHom (e : R ≃+* S) : R →ₙ+* S :=
  { e.toMulEquiv.toMulHom, e.toAddEquiv.toAddMonoidHom with }

theorem toNonUnitalRingHom_injective :
    Function.Injective (toNonUnitalRingHom : R ≃+* S → R →ₙ+* S) := fun _ _ h =>
  RingEquiv.ext (NonUnitalRingHom.ext_iff.1 h)

theorem toNonUnitalRingHom_eq_coe (f : R ≃+* S) : f.toNonUnitalRingHom = ↑f :=
  rfl

@[simp, norm_cast]
theorem coe_toNonUnitalRingHom (f : R ≃+* S) : ⇑(f : R →ₙ+* S) = f :=
  rfl

theorem coe_nonUnitalRingHom_inj_iff {R S : Type*} [NonUnitalNonAssocSemiring R]
    [NonUnitalNonAssocSemiring S] (f g : R ≃+* S) : f = g ↔ (f : R →ₙ+* S) = g :=
  ⟨fun h => by rw [h], fun h => ext <| NonUnitalRingHom.ext_iff.mp h⟩

@[simp]
theorem toNonUnitalRingHom_refl :
    (RingEquiv.refl R).toNonUnitalRingHom = NonUnitalRingHom.id R :=
  rfl

@[simp]
theorem toNonUnitalRingHom_apply_symm_toNonUnitalRingHom_apply (e : R ≃+* S) :
    ∀ y : S, e.toNonUnitalRingHom (e.symm.toNonUnitalRingHom y) = y :=
  e.toEquiv.apply_symm_apply

@[simp]
theorem symm_toNonUnitalRingHom_apply_toNonUnitalRingHom_apply (e : R ≃+* S) :
    ∀ x : R, e.symm.toNonUnitalRingHom (e.toNonUnitalRingHom x) = x :=
  Equiv.symm_apply_apply e.toEquiv

@[simp]
theorem toNonUnitalRingHom_trans (e₁ : R ≃+* S) (e₂ : S ≃+* S') :
    (e₁.trans e₂).toNonUnitalRingHom = e₂.toNonUnitalRingHom.comp e₁.toNonUnitalRingHom :=
  rfl

@[simp]
theorem toNonUnitalRingHomm_comp_symm_toNonUnitalRingHom (e : R ≃+* S) :
    e.toNonUnitalRingHom.comp e.symm.toNonUnitalRingHom = NonUnitalRingHom.id _ := by
  ext
  simp

@[simp]
theorem symm_toNonUnitalRingHom_comp_toNonUnitalRingHom (e : R ≃+* S) :
    e.symm.toNonUnitalRingHom.comp e.toNonUnitalRingHom = NonUnitalRingHom.id _ := by
  ext
  simp

end NonUnitalSemiringHom

section SemiringHom

variable [NonAssocSemiring R] [NonAssocSemiring S] [NonAssocSemiring S']

/-- Reinterpret a ring equivalence as a ring homomorphism. -/
def toRingHom (e : R ≃+* S) : R →+* S :=
  { e.toMulEquiv.toMonoidHom, e.toAddEquiv.toAddMonoidHom with }

theorem toRingHom_injective : Function.Injective (toRingHom : R ≃+* S → R →+* S) := fun _ _ h =>
  RingEquiv.ext (RingHom.ext_iff.1 h)

@[simp] theorem toRingHom_eq_coe (f : R ≃+* S) : f.toRingHom = ↑f :=
  rfl

@[simp, norm_cast]
theorem coe_toRingHom (f : R ≃+* S) : ⇑(f : R →+* S) = f :=
  rfl

theorem coe_ringHom_inj_iff {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S]
    (f g : R ≃+* S) : f = g ↔ (f : R →+* S) = g :=
  ⟨fun h => by rw [h], fun h => ext <| RingHom.ext_iff.mp h⟩

/-- The two paths coercion can take to a `NonUnitalRingEquiv` are equivalent -/
@[simp, norm_cast]
theorem toNonUnitalRingHom_commutes (f : R ≃+* S) :
    ((f : R →+* S) : R →ₙ+* S) = (f : R →ₙ+* S) :=
  rfl

/-- Reinterpret a ring equivalence as a monoid homomorphism. -/
abbrev toMonoidHom (e : R ≃+* S) : R →* S :=
  e.toRingHom.toMonoidHom

/-- Reinterpret a ring equivalence as an `AddMonoid` homomorphism. -/
abbrev toAddMonoidHom (e : R ≃+* S) : R →+ S :=
  e.toRingHom.toAddMonoidHom

/-- The two paths coercion can take to an `AddMonoidHom` are equivalent -/
theorem toAddMonoidMom_commutes (f : R ≃+* S) :
    (f : R →+* S).toAddMonoidHom = (f : R ≃+ S).toAddMonoidHom :=
  rfl

/-- The two paths coercion can take to a `MonoidHom` are equivalent -/
theorem toMonoidHom_commutes (f : R ≃+* S) :
    (f : R →+* S).toMonoidHom = (f : R ≃* S).toMonoidHom :=
  rfl

/-- The two paths coercion can take to an `Equiv` are equivalent -/
theorem toEquiv_commutes (f : R ≃+* S) : (f : R ≃+ S).toEquiv = (f : R ≃* S).toEquiv :=
  rfl

@[simp]
theorem toRingHom_refl : (RingEquiv.refl R).toRingHom = RingHom.id R :=
  rfl

@[simp]
theorem toMonoidHom_refl : (RingEquiv.refl R).toMonoidHom = MonoidHom.id R :=
  rfl

@[simp]
theorem toAddMonoidHom_refl : (RingEquiv.refl R).toAddMonoidHom = AddMonoidHom.id R :=
  rfl

theorem toRingHom_apply_symm_toRingHom_apply (e : R ≃+* S) :
    ∀ y : S, e.toRingHom (e.symm.toRingHom y) = y :=
  e.toEquiv.apply_symm_apply

theorem symm_toRingHom_apply_toRingHom_apply (e : R ≃+* S) :
    ∀ x : R, e.symm.toRingHom (e.toRingHom x) = x :=
  Equiv.symm_apply_apply e.toEquiv

@[simp]
theorem toRingHom_trans (e₁ : R ≃+* S) (e₂ : S ≃+* S') :
    (e₁.trans e₂).toRingHom = e₂.toRingHom.comp e₁.toRingHom :=
  rfl

theorem toRingHom_comp_symm_toRingHom (e : R ≃+* S) :
    e.toRingHom.comp e.symm.toRingHom = RingHom.id _ := by
  ext
  simp

theorem symm_toRingHom_comp_toRingHom (e : R ≃+* S) :
    e.symm.toRingHom.comp e.toRingHom = RingHom.id _ := by
  ext
  simp

/-- Construct an equivalence of rings from homomorphisms in both directions, which are inverses.
-/
@[simps]
def ofHomInv' {R S F G : Type*} [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]
    [FunLike F R S] [FunLike G S R]
    [NonUnitalRingHomClass F R S] [NonUnitalRingHomClass G S R] (hom : F) (inv : G)
    (hom_inv_id : (inv : S →ₙ+* R).comp (hom : R →ₙ+* S) = NonUnitalRingHom.id R)
    (inv_hom_id : (hom : R →ₙ+* S).comp (inv : S →ₙ+* R) = NonUnitalRingHom.id S) :
    R ≃+* S where
  toFun := hom
  invFun := inv
  left_inv := DFunLike.congr_fun hom_inv_id
  right_inv := DFunLike.congr_fun inv_hom_id
  map_mul' := map_mul hom
  map_add' := map_add hom

/--
Construct an equivalence of rings from unital homomorphisms in both directions, which are inverses.
-/
@[simps]
def ofHomInv {R S F G : Type*} [NonAssocSemiring R] [NonAssocSemiring S]
    [FunLike F R S] [FunLike G S R] [RingHomClass F R S]
    [RingHomClass G S R] (hom : F) (inv : G)
    (hom_inv_id : (inv : S →+* R).comp (hom : R →+* S) = RingHom.id R)
    (inv_hom_id : (hom : R →+* S).comp (inv : S →+* R) = RingHom.id S) :
    R ≃+* S where
  toFun := hom
  invFun := inv
  left_inv := DFunLike.congr_fun hom_inv_id
  right_inv := DFunLike.congr_fun inv_hom_id
  map_mul' := map_mul hom
  map_add' := map_add hom

end SemiringHom

variable [Semiring R] [Semiring S]

section GroupPower

protected theorem map_pow (f : R ≃+* S) (a) : ∀ n : ℕ, f (a ^ n) = f a ^ n :=
  map_pow f a

end GroupPower

end RingEquiv

namespace MulEquiv

/-- Gives a `RingEquiv` from an element of a `MulEquivClass` preserving addition. -/
def toRingEquiv {R S F : Type*} [Add R] [Add S] [Mul R] [Mul S] [EquivLike F R S]
    [MulEquivClass F R S] (f : F)
    (H : ∀ x y : R, f (x + y) = f x + f y) : R ≃+* S :=
  { (f : R ≃* S).toEquiv, (f : R ≃* S), AddEquiv.mk' (f : R ≃* S).toEquiv H with }

end MulEquiv

namespace AddEquiv

/-- Gives a `RingEquiv` from an element of an `AddEquivClass` preserving addition. -/
def toRingEquiv {R S F : Type*} [Add R] [Add S] [Mul R] [Mul S] [EquivLike F R S]
    [AddEquivClass F R S] (f : F)
    (H : ∀ x y : R, f (x * y) = f x * f y) : R ≃+* S :=
  { (f : R ≃+ S).toEquiv, (f : R ≃+ S), MulEquiv.mk' (f : R ≃+ S).toEquiv H with }

end AddEquiv

namespace RingEquiv

variable [Add R] [Add S] [Mul R] [Mul S]

@[simp]
theorem self_trans_symm (e : R ≃+* S) : e.trans e.symm = RingEquiv.refl R :=
  ext e.left_inv

@[simp]
theorem symm_trans_self (e : R ≃+* S) : e.symm.trans e = RingEquiv.refl S :=
  ext e.right_inv

end RingEquiv

namespace RingEquiv

variable [NonAssocSemiring R] [NonAssocSemiring S]

/-- If a ring homomorphism has an inverse, it is a ring isomorphism. -/
@[simps]
def ofRingHom (f : R →+* S) (g : S →+* R) (h₁ : f.comp g = RingHom.id S)
    (h₂ : g.comp f = RingHom.id R) : R ≃+* S :=
  { f with
    toFun := f
    invFun := g
    left_inv := RingHom.ext_iff.1 h₂
    right_inv := RingHom.ext_iff.1 h₁ }

theorem coe_ringHom_ofRingHom (f : R →+* S) (g : S →+* R) (h₁ h₂) : ofRingHom f g h₁ h₂ = f :=
  rfl

@[simp]
theorem ofRingHom_coe_ringHom (f : R ≃+* S) (g : S →+* R) (h₁ h₂) : ofRingHom (↑f) g h₁ h₂ = f :=
  ext fun _ ↦ rfl

theorem ofRingHom_symm (f : R →+* S) (g : S →+* R) (h₁ h₂) :
    (ofRingHom f g h₁ h₂).symm = ofRingHom g f h₂ h₁ :=
  rfl

variable (α β R) in
/-- `Equiv.sumArrowEquivProdArrow` as a ring isomorphism. -/
def sumArrowEquivProdArrow : (α ⊕ β → R) ≃+* (α → R) × (β → R) where
  __ := Equiv.sumArrowEquivProdArrow α β R
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

-- Priority `low` to ensure generic `map_{add, mul, zero, one}` lemmas are applied first
@[simp low]
lemma sumArrowEquivProdArrow_apply (x) :
    sumArrowEquivProdArrow α β R x = Equiv.sumArrowEquivProdArrow α β R x := rfl

-- Priority `low` to ensure generic `map_{add, mul, zero, one}` lemmas are applied first
@[simp low]
lemma sumArrowEquivProdArrow_symm_apply (x : (α → R) × (β → R)) :
    (sumArrowEquivProdArrow α β R).symm x = (Equiv.sumArrowEquivProdArrow α β R).symm x := rfl

end RingEquiv

namespace MulEquiv

/-- If two rings are isomorphic, and the second doesn't have zero divisors,
then so does the first. -/
protected theorem noZeroDivisors {A : Type*} (B : Type*) [MulZeroClass A] [MulZeroClass B]
    [NoZeroDivisors B] (e : A ≃* B) : NoZeroDivisors A :=
  e.injective.noZeroDivisors e (map_zero e) (map_mul e)

/-- If two rings are isomorphic, and the second is a domain, then so is the first. -/
protected theorem isDomain {A : Type*} (B : Type*) [Semiring A] [Semiring B] [IsDomain B]
    (e : A ≃* B) : IsDomain A :=
  { e.injective.isLeftCancelMulZero e (map_zero e) (map_mul e),
    e.injective.isRightCancelMulZero e (map_zero e) (map_mul e) with
    exists_pair_ne := ⟨e.symm 0, e.symm 1, e.symm.injective.ne zero_ne_one⟩ }

theorem isDomain_iff {A B : Type*} [Semiring A] [Semiring B] (e : A ≃* B) :
    IsDomain A ↔ IsDomain B where
  mp _ := e.symm.isDomain
  mpr _ := e.isDomain

variable {A B : Type*} [MulZeroClass A] [MulZeroClass B]

theorem noZeroDivisors_iff (e : A ≃* B) : NoZeroDivisors A ↔ NoZeroDivisors B where
  mp _ := e.symm.noZeroDivisors
  mpr _ := e.noZeroDivisors

theorem isLeftCancelMulZero_iff (e : A ≃* B) : IsLeftCancelMulZero A ↔ IsLeftCancelMulZero B where
  mp _ := e.symm.injective.isLeftCancelMulZero _ (map_zero _) (map_mul _)
  mpr _ := e.injective.isLeftCancelMulZero _ (map_zero _) (map_mul _)

theorem isRightCancelMulZero_iff (e : A ≃* B) :
    IsRightCancelMulZero A ↔ IsRightCancelMulZero B where
  mp _ := e.symm.injective.isRightCancelMulZero _ (map_zero _) (map_mul _)
  mpr _ := e.injective.isRightCancelMulZero _ (map_zero _) (map_mul _)

theorem isCancelMulZero_iff (e : A ≃* B) : IsCancelMulZero A ↔ IsCancelMulZero B where
  mp _ := e.symm.injective.isCancelMulZero _ (map_zero _) (map_mul _)
  mpr _ := e.injective.isCancelMulZero _ (map_zero _) (map_mul _)

end MulEquiv
