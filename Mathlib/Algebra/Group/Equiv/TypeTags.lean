/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.TypeTags

/-!
# Additive and multiplicative equivalences associated to `Multiplicative` and `Additive`.
-/


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
  left_inv x := by ext; rfl
  right_inv x := by ext; rfl

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
  left_inv x := by ext; rfl
  right_inv x := by ext; rfl

/-- Reinterpret `Additive G ≃+ H` as `G ≃* Multiplicative H`. -/
@[simps]
def AddEquiv.toMultiplicative' [MulOneClass G] [AddZeroClass H] :
    Additive G ≃+ H ≃ (G ≃* Multiplicative H) where
  toFun f :=
  { toFun := AddMonoidHom.toMultiplicative' f.toAddMonoidHom
    invFun := AddMonoidHom.toMultiplicative'' f.symm.toAddMonoidHom
    left_inv := f.left_inv
    right_inv := f.right_inv
    map_mul' := map_add f }
  invFun f :=
  { toFun := AddMonoidHom.toMultiplicative'.symm f.toMonoidHom
    invFun := AddMonoidHom.toMultiplicative''.symm f.symm.toMonoidHom
    left_inv := f.left_inv
    right_inv := f.right_inv
    map_add' := map_mul f }
  left_inv x := by ext; rfl
  right_inv x := by ext; rfl

/-- Reinterpret `G ≃* Multiplicative H` as `Additive G ≃+ H` as. -/
abbrev MulEquiv.toAdditive' [MulOneClass G] [AddZeroClass H] :
    G ≃* Multiplicative H ≃ (Additive G ≃+ H) :=
  AddEquiv.toMultiplicative'.symm

/-- Reinterpret `G ≃+ Additive H` as `Multiplicative G ≃* H`. -/
@[simps]
def AddEquiv.toMultiplicative'' [AddZeroClass G] [MulOneClass H] :
    G ≃+ Additive H ≃ (Multiplicative G ≃* H) where
  toFun f :=
  { toFun := AddMonoidHom.toMultiplicative'' f.toAddMonoidHom
    invFun := AddMonoidHom.toMultiplicative' f.symm.toAddMonoidHom
    left_inv := f.left_inv
    right_inv := f.right_inv
    map_mul' := map_add f }
  invFun f :=
  { toFun := AddMonoidHom.toMultiplicative''.symm f.toMonoidHom
    invFun := AddMonoidHom.toMultiplicative'.symm f.symm.toMonoidHom
    left_inv := f.left_inv
    right_inv := f.right_inv
    map_add' := map_mul f }
  left_inv x := by ext; rfl
  right_inv x := by ext; rfl

/-- Reinterpret `Multiplicative G ≃* H` as `G ≃+ Additive H` as. -/
abbrev MulEquiv.toAdditive'' [AddZeroClass G] [MulOneClass H] :
    Multiplicative G ≃* H ≃ (G ≃+ Additive H) :=
  AddEquiv.toMultiplicative''.symm

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
def MulEquiv.piMultiplicative (K : ι → Type*) [∀ i, AddZeroClass (K i)] :
    Multiplicative (∀ i : ι, K i) ≃* (∀ i : ι, Multiplicative (K i)) where
  toFun := fun x i ↦ Multiplicative.ofAdd <| Multiplicative.ofAdd x i
  invFun := fun x ↦ Multiplicative.ofAdd fun i ↦ Multiplicative.toAdd (x i)
  left_inv := fun _ ↦ rfl
  right_inv := fun _ ↦ rfl
  map_mul' := fun _ _ ↦ rfl

/-- `Multiplicative (ι → G)` is equivalent to `ι → Multiplicative G`. -/
def MulEquiv.funMultiplicative (ι) (G) [AddZeroClass G] :
    Multiplicative (ι → G) ≃* (ι → Multiplicative G) :=
  MulEquiv.piMultiplicative fun _ ↦ G

/-- `Additive (∀ i : ι, K i)` is equivalent to `∀ i : ι, Additive (K i)`. -/
@[simps]
def AddEquiv.piAdditive (K : ι → Type*) [∀ i, MulOneClass (K i)] :
    Additive (∀ i : ι, K i) ≃+ (∀ i : ι, Additive (K i)) where
  toFun := fun x i ↦ Additive.ofMul <| Additive.ofMul x i
  invFun := fun x ↦ Additive.ofMul fun i ↦ Additive.toMul (x i)
  left_inv := fun _ ↦ rfl
  right_inv := fun _ ↦ rfl
  map_add' := fun _ _ ↦ rfl

/-- `Additive (ι → G)` is equivalent to `ι → Additive G`. -/
def AddEquiv.funAdditive (ι) (G) [MulOneClass G] :
    Additive (ι → G) ≃+ (ι → Additive G) :=
  AddEquiv.piAdditive fun _ ↦ G

section

variable (G) (H)

/-- `Additive (Multiplicative G)` is just `G`. -/
@[simps!]
def AddEquiv.additiveMultiplicative [AddZeroClass G] : Additive (Multiplicative G) ≃+ G :=
  MulEquiv.toAdditive' (MulEquiv.refl (Multiplicative G))

/-- `Multiplicative (Additive H)` is just `H`. -/
@[simps!]
def MulEquiv.multiplicativeAdditive [MulOneClass H] : Multiplicative (Additive H) ≃* H :=
  AddEquiv.toMultiplicative'' (AddEquiv.refl (Additive H))

end
