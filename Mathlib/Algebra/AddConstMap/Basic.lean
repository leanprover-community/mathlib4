/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.Periodic

/-!
-/

open Function Set

structure AddConstMap (G H : Type _) [Add G] [Add H] (a : G) (b : H) where
  /-- The underlying function of an `AddConstMap`.
  Use automatic coercion to function instead. -/
  protected toFun : G → H
  /-- An `AddConstMap` satisfies `f (x + a) = f x + b`. Use `map_add_const` instead.-/
  map_add_const' (x : G) : toFun (x + a) = toFun x + b

notation:25 G " →+c[" a ", " b "] " H => AddConstMap G H a b
notation:25 G " →+1 " H => AddConstMap G H 1 1

class AddConstMapClass (F : Type _) (G H : outParam (Type _)) [Add G] [Add H]
    (a : outParam G) (b : outParam H) extends FunLike F G fun _ ↦ H where
  map_add_const (f : F) (x : G) : f (x + a) = f x + b

namespace AddConstMapClass

/-!
### Properties of `AddConstMapClass` maps

In this section we prove properties like `f (x + n • a) = f x + n • b`.
-/

attribute [simp] map_add_const

protected theorem semiconj [Add G] [Add H] [AddConstMapClass F G H a b] (f : F) :
    Semiconj f (· + a) (· + b) :=
  map_add_const f

@[simp]
theorem map_add_nsmul [AddMonoid G] [AddMonoid H] [AddConstMapClass F G H a b]
    (f : F) (x : G) (n : ℕ) : f (x + n • a) = f x + n • b := by
  simpa using (AddConstMapClass.semiconj f).iterate_right n x

@[simp]
theorem map_add_nat' [AddMonoidWithOne G] [AddMonoid H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) (n : ℕ) : f (x + n) = f x + n • b := by simp [← map_add_nsmul]

theorem map_add_one [AddMonoidWithOne G] [Add H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) : f (x + 1) = f x + b := map_add_const f x

@[simp]
theorem map_add_ofNat' [AddMonoidWithOne G] [AddMonoid H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) (n : ℕ) [n.AtLeastTwo] :
    f (x + OfNat.ofNat n) = f x + (OfNat.ofNat n : ℕ) • b :=
  map_add_nat' f x n

theorem map_add_nat [AddMonoidWithOne G] [AddMonoidWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (x : G) (n : ℕ) : f (x + n) = f x + n := by simp

theorem map_add_ofNat [AddMonoidWithOne G] [AddMonoidWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (x : G) (n : ℕ) [n.AtLeastTwo] : f (x + OfNat.ofNat n) = f x + OfNat.ofNat n :=
  map_add_nat f x n

@[simp]
theorem map_const [AddZeroClass G] [Add H] [AddConstMapClass F G H a b] (f : F) :
    f a = f 0 + b := by
  simpa using map_add_const f 0

theorem map_one [AddZeroClass G] [One G] [Add H] [AddConstMapClass F G H 1 b] (f : F) :
    f 1 = f 0 + b :=
  map_const f

@[simp]
theorem map_nsmul_const [AddMonoid G] [AddMonoid H] [AddConstMapClass F G H a b]
    (f : F) (n : ℕ) : f (n • a) = f 0 + n • b := by
  simpa using map_add_nsmul f 0 n

@[simp]
theorem map_nat' [AddMonoidWithOne G] [AddMonoid H] [AddConstMapClass F G H 1 b]
    (f : F) (n : ℕ) : f n = f 0 + n • b := by
  simpa using map_add_nat' f 0 n

theorem map_ofNat' [AddMonoidWithOne G] [AddMonoid H] [AddConstMapClass F G H 1 b]
    (f : F) (n : ℕ) [n.AtLeastTwo] : f (OfNat.ofNat n) = f 0 + (OfNat.ofNat n : ℕ) • b :=
  map_nat' f n

theorem map_nat [AddMonoidWithOne G] [AddMonoidWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (n : ℕ) : f n = f 0 + n := by simp

theorem map_ofNat [AddMonoidWithOne G] [AddMonoidWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (n : ℕ) [n.AtLeastTwo] : f (OfNat.ofNat n) = f 0 + OfNat.ofNat n := map_nat f n

@[simp]
theorem map_const_add [AddCommSemigroup G] [Add H] [AddConstMapClass F G H a b]
    (f : F) (x : G) : f (a + x) = f x + b := by
  rw [add_comm, map_add_const]

theorem map_one_add [AddCommMonoidWithOne G] [Add H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) : f (1 + x) = f x + b := map_const_add f x

@[simp]
theorem map_nsmul_add [AddCommMonoid G] [AddMonoid H] [AddConstMapClass F G H a b]
    (f : F) (n : ℕ) (x : G) : f (n • a + x) = f x + n • b := by
  rw [add_comm, map_add_nsmul]

@[simp]
theorem map_nat_add' [AddCommMonoidWithOne G] [AddMonoid H] [AddConstMapClass F G H 1 b]
    (f : F) (n : ℕ) (x : G) : f (↑n + x) = f x + n • b := by
  simpa using map_nsmul_add f n x

theorem map_ofNat_add' [AddCommMonoidWithOne G] [AddMonoid H] [AddConstMapClass F G H 1 b]
    (f : F) (n : ℕ) [n.AtLeastTwo] (x : G) : f (OfNat.ofNat n + x) = f x + OfNat.ofNat n • b :=
  map_nat_add' f n x

theorem map_nat_add [AddCommMonoidWithOne G] [AddMonoidWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (n : ℕ) (x : G) : f (↑n + x) = f x + n := by simp

theorem map_ofNat_add [AddCommMonoidWithOne G] [AddMonoidWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (n : ℕ) [n.AtLeastTwo] (x : G) : f (OfNat.ofNat n + x) = f x + OfNat.ofNat n :=
  map_nat_add f n x

@[simp]
theorem map_sub_nsmul [AddGroup G] [AddGroup H] [AddConstMapClass F G H a b]
    (f : F) (x : G) (n : ℕ) : f (x - n • a) = f x - n • b := by
  conv_rhs => rw [← sub_add_cancel x (n • a), map_add_nsmul, add_sub_cancel]

@[simp]
theorem map_sub_const [AddGroup G] [AddGroup H] [AddConstMapClass F G H a b]
    (f : F) (x : G) : f (x - a) = f x - b := by
  simpa using map_sub_nsmul f x 1

theorem map_sub_one [AddGroup G] [One G] [AddGroup H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) : f (x - 1) = f x - b :=
  map_sub_const f x

@[simp]
theorem map_sub_nat' [AddGroupWithOne G] [AddGroup H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) (n : ℕ) : f (x - n) = f x - n • b := by
  simpa using map_sub_nsmul f x n

@[simp]
theorem map_sub_ofNat' [AddGroupWithOne G] [AddGroup H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) (n : ℕ) [n.AtLeastTwo] : f (x - OfNat.ofNat n) = f x - OfNat.ofNat n • b :=
  map_sub_nat' f x n

@[simp]
theorem map_add_zsmul [AddGroup G] [AddGroup H] [AddConstMapClass F G H a b]
    (f : F) (x : G) : ∀ n : ℤ, f (x + n • a) = f x + n • b
  | (n : ℕ) => by simp
  | .negSucc n => by simp [← sub_eq_add_neg]

@[simp]
theorem map_add_int' [AddGroupWithOne G] [AddGroup H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) (n : ℤ) : f (x + n) = f x + n • b := by
  rw [← map_add_zsmul f x n, zsmul_one]

theorem map_add_int [AddGroupWithOne G] [AddGroupWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (x : G) (n : ℤ) : f (x + n) = f x + n := by simp

@[simp]
theorem map_sub_zsmul [AddGroup G] [AddGroup H] [AddConstMapClass F G H a b]
    (f : F) (x : G) (n : ℤ) : f (x - n • a) = f x - n • b := by
  simpa [sub_eq_add_neg] using map_add_zsmul f x (-n)

@[simp]
theorem map_sub_int' [AddGroupWithOne G] [AddGroup H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) (n : ℤ) : f (x - n) = f x - n • b := by
  rw [← map_sub_zsmul, zsmul_one]

theorem map_sub_int [AddGroupWithOne G] [AddGroupWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (x : G) (n : ℤ) : f (x - n) = f x - n := by simp

theorem map_fract [LinearOrderedRing R] [FloorRing R] [AddGroup H] [AddConstMapClass F R H 1 b]
    (f : F) (x : R) : f (Int.fract x) = f x - ⌊x⌋ • b := map_sub_int' ..

@[simp]
theorem map_zsmul_add [AddCommGroup G] [AddGroup H] [AddConstMapClass F G H a b]
    (f : F) (n : ℤ) (x : G) : f (n • a + x) = f x + n • b := by
  rw [add_comm, map_add_zsmul]

@[simp]
theorem map_int_add' [AddCommGroupWithOne G] [AddGroup H] [AddConstMapClass F G H 1 b]
    (f : F) (n : ℤ) (x : G) : f (↑n + x) = f x + n • b := by
  rw [← map_zsmul_add, zsmul_one]

theorem map_int_add [AddCommGroupWithOne G] [AddGroupWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (n : ℤ) (x : G) : f (↑n + x) = f x + n := by simp

end AddConstMapClass

open AddConstMapClass

namespace AddConstMap

section Add

variable {G H : Type _} [Add G] [Add H] {a : G} {b : H}

/-!
### Coercion to function
-/

instance : AddConstMapClass (G →+c[a, b] H) G H a b where
  coe := AddConstMap.toFun
  coe_injective' | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl
  map_add_const f := f.map_add_const'

@[simp] theorem coe_mk (f : G → H) (hf) : ⇑(mk f hf : G →+c[a, b] H) = f := rfl
@[simp] theorem mk_coe (f : G →+c[a, b] H) : mk f f.2 = f := rfl

@[ext] protected theorem ext {f g : G →+c[a, b] H} (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext _ _ h

initialize_simps_projections AddConstMap (toFun → coe, as_prefix coe)

/-!
### Constructions about `G →+c[a, b] H`
-/

/-- The identity map as `G →+c[a, a] G`. -/
@[simps (config := .asFn)]
protected def id : G →+c[a, a] G := ⟨id, fun _ ↦ rfl⟩

/-- Composition of two `AddConstMap`s. -/
@[simps (config := .asFn)]
def comp {K : Type _} [Add K] {c : K} (g : H →+c[b, c] K) (f : G →+c[a, b] H) :
    G →+c[a, c] K :=
  ⟨g ∘ f, by simp⟩

@[simp] theorem comp_id (f : G →+c[a, b] H) : f.comp .id = f := rfl
@[simp] theorem id_comp (f : G →+c[a, b] H) : .comp .id f = f := rfl

/-- Change constants `a` and `b` in `(f : G →+c[a, b] H)` to improve definitional equalities. -/
@[simps (config := .asFn)]
def replaceConsts (f : G →+c[a, b] H) (a' b') (ha : a = a') (hb : b = b') :
    G →+c[a', b'] H where
  toFun := f
  map_add_const' := ha ▸ hb ▸ f.map_add_const'

/-!
### Additive action on `G →+c[a, b] H`
-/

/-- If `f` is an `AddConstMap`, then so is `(c +ᵥ f ·)`. -/
instance {K : Type _} [VAdd K H] [VAddAssocClass K H H] : VAdd K (G →+c[a, b] H) :=
  ⟨fun c f ↦ ⟨c +ᵥ ⇑f, fun x ↦ by simp [vadd_add_assoc]⟩⟩

@[simp]
theorem coe_vadd {K : Type _} [VAdd K H] [VAddAssocClass K H H] (c : K) (f : G →+c[a, b] H) :
    ⇑(c +ᵥ f) = c +ᵥ ⇑f :=
  rfl

instance {K : Type _} [AddMonoid K] [AddAction K H] [VAddAssocClass K H H] :
    AddAction K (G →+c[a, b] H) :=
  FunLike.coe_injective.addAction _ coe_vadd

/-!
### Monoid structure on endomorphisms `G →+c[a, a] G`
-/

instance : Monoid (G →+c[a, a] G) where
  mul := comp
  one := .id
  mul_assoc _ _ _ := rfl
  one_mul := id_comp
  mul_one := comp_id

theorem mul_def (f g : G →+c[a, a] G) : f * g = f.comp g := rfl
@[simp] theorem coe_mul (f g : G →+c[a, a] G) : ⇑(f * g) = f ∘ g := rfl

theorem one_def : (1 : G →+c[a, a] G) = .id := rfl
@[simp] theorem coe_one : ⇑(1 : G →+c[a, a] G) = id := rfl

theorem coe_pow (f : G →+c[a, a] G) (n : ℕ) : ⇑(f ^ n) = f^[n] :=
  hom_coe_pow _ rfl (fun _ _ ↦ rfl) _ _

theorem pow_apply (f : G →+c[a, a] G) (n : ℕ) (x : G) : (f ^ n) x = f^[n] x :=
  congr_fun (coe_pow f n) x

end Add

section AddZeroClass

variable {G H K : Type _} [Add G] [AddZeroClass H]

/-!
### Multiplicative action on `(b : H) × (G →+c[a, b] H)`

If `K` acts distributively on `H`, then for each `f : G →+c[a, b] H`
we define `(AddConstMap.smul c f : G →+c[a, c • b] H)`.

One can show that this defines a multiplicative action of `K` on `(b : H) × (G →+c[a, b] H)`
but we don't do this at the moment because we don't need this.
-/

@[simps (config := .asFn)]
def smul [DistribSMul K H] (c : K) (f : G →+c[a, b] H) : G →+c[a, c • b] H where
  toFun := c • ⇑f
  map_add_const' x := by simp [smul_add]

end AddZeroClass

section AddMonoid

variable [AddMonoid G] {a : G}

@[simps! (config := .asFn)]
def addLeftHom : Multiplicative G →* (G →+c[a, a] G) where
  toFun c := Multiplicative.toAdd c +ᵥ .id
  map_one' := by ext; apply zero_add
  map_mul' _ _ := by ext; apply add_assoc

end AddMonoid

section AddCommGroup

variable [AddCommGroup G] [AddCommGroup H] {a : G} {b : H}

/-- If `f : G → H` is an `AddConstMap`, then so is `fun x ↦ -f (-x)`. -/
@[simps! apply_coe]
def conjNeg : (G →+c[a, b] H) ≃ (G →+c[a, b] H) :=
  Involutive.toPerm (fun f ↦ ⟨fun x ↦ - f (-x), fun _ ↦ by simp [neg_add_eq_sub]⟩) fun _ ↦
    AddConstMap.ext fun _ ↦ by simp

@[simp] theorem conjNeg_symm : (conjNeg (a := a) (b := b)).symm = conjNeg := rfl

end AddCommGroup

section FloorRing

variable [LinearOrderedRing R] [FloorRing R] [AddGroup G] (a : G)

def mkFract : (Ico (0 : R) 1 → G) ≃ (R →+c[1, a] G) where
  toFun f := ⟨fun x ↦ f ⟨Int.fract x, Int.fract_nonneg _, Int.fract_lt_one _⟩ + ⌊x⌋ • a, fun x ↦ by
    simp [add_one_zsmul, add_assoc]⟩
  invFun f x := f x
  left_inv _ := by ext x; simp [Int.fract_eq_self.2 x.2, Int.floor_eq_zero_iff.2 x.2]
  right_inv f := by ext x; simp [map_fract]

end FloorRing
