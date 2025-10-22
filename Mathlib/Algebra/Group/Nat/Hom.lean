/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.Tactic.Spread

/-!
# Extensionality of monoid homs from `ℕ`
-/

assert_not_exists OrderedCommMonoid MonoidWithZero

open Additive Multiplicative

variable {M : Type*}

section AddMonoidHomClass

variable {A B F : Type*} [FunLike F ℕ A]

lemma ext_nat' [AddZeroClass A] [AddMonoidHomClass F ℕ A] (f g : F) (h : f 1 = g 1) : f = g :=
  DFunLike.ext f g <| by
    intro n
    induction n with
    | zero => simp_rw [map_zero f, map_zero g]
    | succ n ihn =>
      simp [h, ihn]

@[ext]
lemma AddMonoidHom.ext_nat [AddZeroClass A] {f g : ℕ →+ A} : f 1 = g 1 → f = g :=
  ext_nat' f g

end AddMonoidHomClass

section AddMonoid
variable [AddMonoid M]

variable (M) in
/-- Additive homomorphisms from `ℕ` are defined by the image of `1`. -/
def multiplesHom : M ≃ (ℕ →+ M) where
  toFun x :=
  { toFun := fun n ↦ n • x
    map_zero' := zero_nsmul x
    map_add' := fun _ _ ↦ add_nsmul _ _ _ }
  invFun f := f 1
  left_inv := one_nsmul
  right_inv f := AddMonoidHom.ext_nat <| one_nsmul (f 1)

@[simp] lemma multiplesHom_apply (x : M) (n : ℕ) : multiplesHom M x n = n • x := rfl

@[simp] lemma multiplesHom_symm_apply (f : ℕ →+ M) : (multiplesHom M).symm f = f 1 := rfl

lemma AddMonoidHom.apply_nat (f : ℕ →+ M) (n : ℕ) : f n = n • f 1 := by
  rw [← multiplesHom_symm_apply, ← multiplesHom_apply, Equiv.apply_symm_apply]

end AddMonoid

section Monoid
variable [Monoid M]

variable (M) in
/-- Monoid homomorphisms from `Multiplicative ℕ` are defined by the image
of `Multiplicative.ofAdd 1`. -/
def powersHom : M ≃ (Multiplicative ℕ →* M) :=
  Additive.ofMul.trans <| (multiplesHom _).trans <| AddMonoidHom.toMultiplicativeLeft

@[simp] lemma powersHom_apply (x : M) (n : Multiplicative ℕ) :
    powersHom M x n = x ^ n.toAdd := rfl

@[simp] lemma powersHom_symm_apply (f : Multiplicative ℕ →* M) :
    (powersHom M).symm f = f (Multiplicative.ofAdd 1) := rfl

lemma MonoidHom.apply_mnat (f : Multiplicative ℕ →* M) (n : Multiplicative ℕ) :
    f n = f (Multiplicative.ofAdd 1) ^ n.toAdd := by
  rw [← powersHom_symm_apply, ← powersHom_apply, Equiv.apply_symm_apply]

@[ext]
lemma MonoidHom.ext_mnat ⦃f g : Multiplicative ℕ →* M⦄
    (h : f (Multiplicative.ofAdd 1) = g (Multiplicative.ofAdd 1)) : f = g :=
  MonoidHom.ext fun n ↦ by rw [f.apply_mnat, g.apply_mnat, h]

end Monoid

section AddCommMonoid
variable [AddCommMonoid M]

variable (M) in
/-- If `M` is commutative, `multiplesHom` is an additive equivalence. -/
def multiplesAddHom : M ≃+ (ℕ →+ M) where
  __ := multiplesHom M
  map_add' a b := AddMonoidHom.ext fun n ↦ by simp [nsmul_add]

@[simp] lemma multiplesAddHom_apply (x : M) (n : ℕ) : multiplesAddHom M x n = n • x := rfl

@[simp] lemma multiplesAddHom_symm_apply (f : ℕ →+ M) : (multiplesAddHom M).symm f = f 1 := rfl

end AddCommMonoid

section CommMonoid
variable [CommMonoid M]

variable (M) in
/-- If `M` is commutative, `powersHom` is a multiplicative equivalence. -/
def powersMulHom : M ≃* (Multiplicative ℕ →* M) where
  __ := powersHom M
  map_mul' a b := MonoidHom.ext fun n ↦ by simp [mul_pow]

@[simp]
lemma powersMulHom_apply (x : M) (n : Multiplicative ℕ) : powersMulHom M x n = x ^ n.toAdd := rfl

@[simp]
lemma powersMulHom_symm_apply (f : Multiplicative ℕ →* M) : (powersMulHom M).symm f = f (ofAdd 1) :=
  rfl

end CommMonoid
