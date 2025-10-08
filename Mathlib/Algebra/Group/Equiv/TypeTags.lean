/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Notation.Prod
import Mathlib.Tactic.Spread

/-!
# Additive and multiplicative equivalences associated to `Multiplicative` and `Additive`.
-/

assert_not_exists Finite Fintype

variable {ι G H : Type*}

/-- Reinterpret `G ≃+ H` as `Multiplicative G ≃* Multiplicative H`. -/
@[simps]
def AddEquiv.toMultiplicative [AddZeroClass G] [AddZeroClass H] :
    G ≃+ H ≃ (Multiplicative G ≃* Multiplicative H) where
  toFun f :=
  { toFun := AddMonoidHom.toMultiplicative f.toAddMonoidHom
    invFun := AddMonoidHom.toMultiplicative f.symm.toAddMonoidHom
    left_inv := f.left_inv
    right_inv := f.right_inv
    map_mul' := map_add f }
  invFun f :=
  { toFun := AddMonoidHom.toMultiplicative.symm f.toMonoidHom
    invFun := AddMonoidHom.toMultiplicative.symm f.symm.toMonoidHom
    left_inv := f.left_inv
    right_inv := f.right_inv
    map_add' := map_mul f }

/-- Reinterpret `G ≃* H` as `Additive G ≃+ Additive H`. -/
@[simps]
def MulEquiv.toAdditive [MulOneClass G] [MulOneClass H] :
    G ≃* H ≃ (Additive G ≃+ Additive H) where
  toFun f :=
  { toFun := MonoidHom.toAdditive f.toMonoidHom
    invFun := MonoidHom.toAdditive f.symm.toMonoidHom
    left_inv := f.left_inv
    right_inv := f.right_inv
    map_add' := map_mul f }
  invFun f :=
  { toFun := MonoidHom.toAdditive.symm f.toAddMonoidHom
    invFun := MonoidHom.toAdditive.symm f.symm.toAddMonoidHom
    left_inv := f.left_inv
    right_inv := f.right_inv
    map_mul' := map_add f }

/-- Reinterpret `Additive G ≃+ H` as `G ≃* Multiplicative H`. -/
@[simps]
def AddEquiv.toMultiplicativeRight [MulOneClass G] [AddZeroClass H] :
    Additive G ≃+ H ≃ (G ≃* Multiplicative H) where
  toFun f :=
  { toFun := f.toAddMonoidHom.toMultiplicativeRight
    invFun := f.symm.toAddMonoidHom.toMultiplicativeLeft
    left_inv := f.left_inv
    right_inv := f.right_inv
    map_mul' := map_add f }
  invFun f :=
  { toFun := f.toMonoidHom.toAdditiveLeft
    invFun := f.symm.toMonoidHom.toAdditiveRight
    left_inv := f.left_inv
    right_inv := f.right_inv
    map_add' := map_mul f }

@[deprecated (since := "2025-09-19")]
alias AddEquiv.toMultiplicative' := AddEquiv.toMultiplicativeRight

/-- Reinterpret `G ≃* Multiplicative H` as `Additive G ≃+ H`. -/
abbrev MulEquiv.toAdditiveLeft [MulOneClass G] [AddZeroClass H] :
    G ≃* Multiplicative H ≃ (Additive G ≃+ H) :=
  AddEquiv.toMultiplicativeRight.symm

@[deprecated (since := "2025-09-19")] alias MulEquiv.toAdditive' := MulEquiv.toAdditiveLeft

/-- Reinterpret `G ≃+ Additive H` as `Multiplicative G ≃* H`. -/
@[simps]
def AddEquiv.toMultiplicativeLeft [AddZeroClass G] [MulOneClass H] :
    G ≃+ Additive H ≃ (Multiplicative G ≃* H) where
  toFun f :=
  { toFun := f.toAddMonoidHom.toMultiplicativeLeft
    invFun := f.symm.toAddMonoidHom.toMultiplicativeRight
    left_inv := f.left_inv
    right_inv := f.right_inv
    map_mul' := map_add f }
  invFun f :=
  { toFun := f.toMonoidHom.toAdditiveRight
    invFun := f.symm.toMonoidHom.toAdditiveLeft
    left_inv := f.left_inv
    right_inv := f.right_inv
    map_add' := map_mul f }

@[deprecated (since := "2025-09-19")]
alias AddEquiv.toMultiplicative'' := AddEquiv.toMultiplicativeLeft

/-- Reinterpret `Multiplicative G ≃* H` as `G ≃+ Additive H` as. -/
abbrev MulEquiv.toAdditiveRight [AddZeroClass G] [MulOneClass H] :
    Multiplicative G ≃* H ≃ (G ≃+ Additive H) :=
  AddEquiv.toMultiplicativeLeft.symm

@[deprecated (since := "2025-09-19")] alias MulEquiv.toAdditive'' := MulEquiv.toAdditiveRight

/-- The multiplicative version of an additivized monoid is mul-equivalent to itself. -/
@[simps! apply symm_apply]
def MulEquiv.toMultiplicative_toAdditive [MulOneClass G] :
    Multiplicative (Additive G) ≃* G :=
  AddEquiv.toMultiplicativeLeft <| MulEquiv.toAdditive (.refl _)

/-- The additive version of an multiplicativized additive monoid is add-equivalent to itself. -/
@[simps! apply symm_apply]
def AddEquiv.toAdditive_toMultiplicative [AddZeroClass G] :
    Additive (Multiplicative G) ≃+ G :=
  MulEquiv.toAdditiveLeft <| AddEquiv.toMultiplicative (.refl _)

/-- Multiplicative equivalence between multiplicative endomorphisms of a `MulOneClass` `M`
and additive endomorphisms of `Additive M`. -/
@[simps!] def monoidEndToAdditive (M : Type*) [MulOneClass M] :
    Monoid.End M ≃* AddMonoid.End (Additive M) :=
  { MonoidHom.toAdditive with
    map_mul' := fun _ _ => rfl }

/-- Multiplicative equivalence between additive endomorphisms of an `AddZeroClass` `A`
and multiplicative endomorphisms of `Multiplicative A`. -/
@[simps!] def addMonoidEndToMultiplicative (A : Type*) [AddZeroClass A] :
    AddMonoid.End A ≃* Monoid.End (Multiplicative A) :=
  { AddMonoidHom.toMultiplicative with
    map_mul' := fun _ _ => rfl }

/-- `Multiplicative (∀ i : ι, K i)` is equivalent to `∀ i : ι, Multiplicative (K i)`. -/
@[simps]
def MulEquiv.piMultiplicative (K : ι → Type*) [∀ i, Add (K i)] :
    Multiplicative (∀ i : ι, K i) ≃* (∀ i : ι, Multiplicative (K i)) where
  toFun x := fun i ↦ Multiplicative.ofAdd <| x.toAdd i
  invFun x := Multiplicative.ofAdd fun i ↦ (x i).toAdd
  map_mul' _ _ := rfl

variable (ι) (G) in
/-- `Multiplicative (ι → G)` is equivalent to `ι → Multiplicative G`. -/
abbrev MulEquiv.funMultiplicative [Add G] :
    Multiplicative (ι → G) ≃* (ι → Multiplicative G) :=
  MulEquiv.piMultiplicative fun _ ↦ G

/-- `Additive (∀ i : ι, K i)` is equivalent to `∀ i : ι, Additive (K i)`. -/
@[simps]
def AddEquiv.piAdditive (K : ι → Type*) [∀ i, Mul (K i)] :
    Additive (∀ i : ι, K i) ≃+ (∀ i : ι, Additive (K i)) where
  toFun x := fun i ↦ Additive.ofMul <| x.toMul i
  invFun x := Additive.ofMul fun i ↦ (x i).toMul
  map_add' _ _ := rfl

variable (ι) (G) in
/-- `Additive (ι → G)` is equivalent to `ι → Additive G`. -/
abbrev AddEquiv.funAdditive [Mul G] :
    Additive (ι → G) ≃+ (ι → Additive G) :=
  AddEquiv.piAdditive fun _ ↦ G

section

variable (G) (H)

/-- `Additive (Multiplicative G)` is just `G`. -/
@[simps!]
def AddEquiv.additiveMultiplicative [AddZeroClass G] : Additive (Multiplicative G) ≃+ G :=
  MulEquiv.toAdditiveLeft (MulEquiv.refl (Multiplicative G))

/-- `Multiplicative (Additive H)` is just `H`. -/
@[simps!]
def MulEquiv.multiplicativeAdditive [MulOneClass H] : Multiplicative (Additive H) ≃* H :=
  AddEquiv.toMultiplicativeLeft (AddEquiv.refl (Additive H))

/-- `Multiplicative (G × H)` is equivalent to `Multiplicative G × Multiplicative H`. -/
@[simps]
def MulEquiv.prodMultiplicative [Add G] [Add H] :
    Multiplicative (G × H) ≃* Multiplicative G × Multiplicative H where
  toFun x := (Multiplicative.ofAdd x.toAdd.1,
    Multiplicative.ofAdd x.toAdd.2)
  invFun := fun (x, y) ↦ Multiplicative.ofAdd (x.toAdd, y.toAdd)
  map_mul' _ _ := rfl

/-- `Additive (G × H)` is equivalent to `Additive G × Additive H`. -/
@[simps]
def AddEquiv.prodAdditive [Mul G] [Mul H] :
    Additive (G × H) ≃+ Additive G × Additive H where
  toFun x := (Additive.ofMul x.toMul.1,
    Additive.ofMul x.toMul.2)
  invFun := fun (x, y) ↦ Additive.ofMul (x.toMul, y.toMul)
  map_add' _ _ := rfl

end

section End

variable {M : Type*}

/-- `Monoid.End M` is equivalent to `AddMonoid.End (Additive M)`. -/
@[simps! apply]
def MulEquiv.Monoid.End [Monoid M] : Monoid.End M ≃* AddMonoid.End (Additive M) where
  __ := MonoidHom.toAdditive
  map_mul' := fun _ _ ↦ rfl

/-- `AddMonoid.End M` is equivalent to `Monoid.End (Multiplicative M)`. -/
@[simps! apply]
def MulEquiv.AddMonoid.End [AddMonoid M] :
    AddMonoid.End M ≃* _root_.Monoid.End (Multiplicative M) where
  __ := AddMonoidHom.toMultiplicative
  map_mul' := fun _ _ ↦ rfl

end End
