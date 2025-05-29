/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Kevin Buzzard, Kim Morrison, Johan Commelin, Chris Hughes,
  Johannes Hölzl, Yury Kudryashov
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Hom.Defs

/-!
# Additional lemmas about monoid and group homomorphisms

-/

-- `NeZero` cannot be additivised, hence its theory should be developed outside of the
-- `Algebra.Group` folder.
assert_not_imported Mathlib.Algebra.NeZero

variable {α M N P : Type*}

-- monoids
variable {G : Type*} {H : Type*}

-- groups
variable {F : Type*}

section CommMonoid
variable [CommMonoid α]

/-- The `n`th power map on a commutative monoid for a natural `n`, considered as a morphism of
monoids. -/
@[to_additive (attr := simps) "Multiplication by a natural `n` on a commutative additive monoid,
considered as a morphism of additive monoids."]
def powMonoidHom (n : ℕ) : α →* α where
  toFun := (· ^ n)
  map_one' := one_pow _
  map_mul' a b := mul_pow a b n

end CommMonoid

section DivisionCommMonoid

variable [DivisionCommMonoid α]

/-- The `n`-th power map (for an integer `n`) on a commutative group, considered as a group
homomorphism. -/
@[to_additive (attr := simps) "Multiplication by an integer `n` on a commutative additive group,
considered as an additive group homomorphism."]
def zpowGroupHom (n : ℤ) : α →* α where
  toFun := (· ^ n)
  map_one' := one_zpow n
  map_mul' a b := mul_zpow a b n

/-- Inversion on a commutative group, considered as a monoid homomorphism. -/
@[to_additive "Negation on a commutative additive group, considered as an additive monoid
homomorphism."]
def invMonoidHom : α →* α where
  toFun := Inv.inv
  map_one' := inv_one
  map_mul' := mul_inv

@[simp]
theorem coe_invMonoidHom : (invMonoidHom : α → α) = Inv.inv := rfl

@[simp]
theorem invMonoidHom_apply (a : α) : invMonoidHom a = a⁻¹ := rfl

end DivisionCommMonoid

namespace OneHom

open Function

variable [One M] [One N] [One P]

section LiftLeft

variable {f : OneHom M N} {p : OneHom M P} {g hg}

@[to_additive (attr := simp)]
theorem liftLeft_comp : (f.liftLeft p g hg).comp p = f := ext fun _ => hg _

@[to_additive]
theorem liftLeft_comp_apply : ∀ x, (f.liftLeft p g hg) (p x) = f x := hg

@[to_additive]
theorem eq_liftLeft (hp : Surjective p) {g'} (hg' : g'.comp p = f) :
    g' = f.liftLeft p g hg := by
  simpa only [cancel_right hp] using
    hg'.trans (liftLeft_comp (f := f) (p := p) (hg := hg)).symm

@[to_additive (attr := simp)]
theorem liftLeft_liftLeft : f.liftLeft p (f.liftLeft p g hg) liftLeft_comp_apply =
    f.liftLeft p g hg := rfl

end LiftLeft

section LiftRight

variable {f : OneHom M N} {p : OneHom P N} {hp : Injective p} {g hg}

@[to_additive (attr := simp)]
theorem comp_liftRight : p.comp (f.liftRight hp g hg) = f := ext fun _ => hg _

@[to_additive]
theorem comp_liftRight_apply : ∀ x, p ((f.liftRight hp g hg) x) = f x := hg

@[to_additive]
theorem eq_liftRight {g'} (hg' : p.comp g' = f) : g' = f.liftRight hp g hg := by
  simpa only [cancel_left hp] using
    hg'.trans (comp_liftRight (f := f) (hp := hp) (hg := hg)).symm

@[to_additive (attr := simp)]
theorem liftRight_liftRight : f.liftRight hp (f.liftRight hp g hg) comp_liftRight_apply =
    f.liftRight hp g hg := rfl

end LiftRight

section LiftOfRightInverse

variable {p : OneHom M P} {p_inv : P → M}  {f : OneHom M N}
  {hf : ∀ (x : M), f (p_inv (p x)) = f x} {φ : OneHom P N}

@[to_additive (attr := simp)]
theorem liftOfRightInverse_comp : (p.liftOfRightInverse p_inv f hf).comp p = f := liftLeft_comp

@[to_additive]
theorem liftOfRightInverse_comp_apply : ∀ x, (p.liftOfRightInverse p_inv f hf) (p x) = f x :=
  liftLeft_comp_apply

@[to_additive]
theorem eq_liftOfRightInverse {hp : RightInverse p_inv p} {f'} :
    f'.comp p = f → f' = p.liftOfRightInverse p_inv f hf := eq_liftLeft hp.surjective

@[to_additive (attr := simp)]
theorem liftLeft_liftOfRightInverse :
    f.liftLeft p (p.liftOfRightInverse p_inv f hf) liftOfRightInverse_comp_apply =
    p.liftOfRightInverse p_inv f hf := rfl

@[to_additive]
theorem liftOfRightInverse_apply_comp {hp : RightInverse p_inv p} :
    p.liftOfRightInverse p_inv (φ.comp p) (fun x => by simp only [comp_apply, hp (p x)]) = φ :=
  ext fun x => by simp only [liftOfRightInverse_apply, comp_apply, hp x]

end LiftOfRightInverse

section LiftOfLeftInverse

variable {p : OneHom P N} {p_inv : N → P} {hp : LeftInverse p_inv p} {f : OneHom M N}
  {hf : ∀ x, p (p_inv (f x)) = f x} {φ : OneHom M P}

@[to_additive (attr := simp)]
theorem comp_liftOfLeftInverse : p.comp (p.liftOfLeftInverse p_inv hp f hf) = f := comp_liftRight

@[to_additive]
theorem comp_liftOfLeftInverse_apply : ∀ x, p (p.liftOfLeftInverse p_inv hp f hf x) = f x :=
  comp_liftRight_apply

@[to_additive]
theorem eq_liftOfLeftInverse {f'} : p.comp f' = f → f' = p.liftOfLeftInverse p_inv hp f hf :=
  eq_liftRight

@[to_additive (attr := simp)]
theorem liftRight_liftOfLeftInverse :
    f.liftRight hp.injective (p.liftOfLeftInverse p_inv hp f hf) comp_liftOfLeftInverse_apply =
    p.liftOfLeftInverse p_inv hp f hf := rfl

@[to_additive (attr := simp)]
theorem liftOfLeftInverse_apply_comp : p.liftOfLeftInverse p_inv hp (p.comp φ)
    (fun _ => by simp only [comp_apply, hp (φ _)]) = φ := ext fun x => by
  simp only [liftOfLeftInverse_apply, comp_apply, hp (φ x)]

end LiftOfLeftInverse

section Inverse

variable {f : OneHom M N} {g : N → M} {h : LeftInverse g f}

@[to_additive (attr := simp)]
theorem inverse_comp : (f.inverse g h).comp f = id M := ext h
@[to_additive]
theorem inverse_comp_apply : ∀ x, (f.inverse g h) (f x) = x := h
@[to_additive (attr := simp)]
theorem comp_inverse (h' : RightInverse g f) : f.comp (f.inverse g h) = id N := ext h'
@[to_additive]
theorem comp_inverse_apply (h' : RightInverse g f) : ∀ x, f ((f.inverse g h) x) = x := h'

@[to_additive]
theorem inverse_eq_liftOfRightInverse : f.inverse g h = liftOfRightInverse f g (id M) h := rfl
@[to_additive]
theorem inverse_eq_liftOfLeftInverse (h' : RightInverse g f) :
    f.inverse g h = liftOfLeftInverse f g h (id N) h' := rfl
@[to_additive]
theorem inverse_eq_liftLeft : f.inverse g h = liftLeft (id M) f g h := rfl
@[to_additive]
theorem inverse_eq_liftRight (h' : RightInverse g f) : f.inverse g h =
  liftRight (id N) h.injective g h' := rfl

@[to_additive]
theorem eq_inverse_of_comp_right_eq_id {g'} (h' : RightInverse g f) (hg : f.comp g' = id N) :
    g' = f.inverse g h := eq_liftRight hg (hg := fun _ => h' _) (hp := h.injective)

@[to_additive]
theorem eq_inverse_of_comp_left_eq_id {g'} (h' : RightInverse g f) (hg : g'.comp f = id M) :
    g' = f.inverse g h := eq_liftLeft h'.surjective hg

@[to_additive]
theorem inverse_inverse (h' : RightInverse g f) :
    (f.inverse g h).inverse f (comp_inverse_apply h') = f := rfl

end Inverse

end OneHom

namespace MulHom

section

open Function

variable [Mul M] [Mul N] [Mul P]

section LiftLeft

variable {f : M →ₙ* N} {p : M →ₙ* P} {hp : Surjective p} {g hg}

@[to_additive (attr := simp)]
theorem liftLeft_comp : (f.liftLeft hp g hg).comp p = f := ext fun _ => hg _

@[to_additive]
theorem liftLeft_comp_apply : ∀ x, (f.liftLeft hp g hg) (p x) = f x := hg

@[to_additive]
theorem eq_liftLeft {g'} (hg' : g'.comp p = f) : g' = f.liftLeft hp g hg := by
  simpa only [cancel_right hp] using
    hg'.trans (liftLeft_comp (f := f) (hp := hp) (hg := hg)).symm

@[to_additive (attr := simp)]
theorem liftLeft_liftLeft : f.liftLeft hp (f.liftLeft hp g hg) liftLeft_comp_apply =
    f.liftLeft hp g hg := rfl

end LiftLeft

section LiftRight

variable {f : M →ₙ* N} {p : P →ₙ* N} {hp : Injective p} {g hg}

@[to_additive (attr := simp)]
theorem comp_liftRight : p.comp (f.liftRight hp g hg) = f := ext fun _ => hg _

@[to_additive]
theorem comp_liftRight_apply : ∀ x, p ((f.liftRight hp g hg) x) = f x := hg

@[to_additive]
theorem eq_liftRight {g'} (hg' : p.comp g' = f) : g' = f.liftRight hp g hg := by
  simpa only [cancel_left hp] using
    hg'.trans (comp_liftRight (f := f) (hp := hp) (hg := hg)).symm

@[to_additive (attr := simp)]
theorem liftRight_liftRight : f.liftRight hp (f.liftRight hp g hg) comp_liftRight_apply =
    f.liftRight hp g hg := rfl

end LiftRight

section LiftOfRightInverse

variable {p : M →ₙ* P} {p_inv : P → M} {hp : RightInverse p_inv p} {f : M →ₙ* N}
  {hf : ∀ (x : M), f (p_inv (p x)) = f x} {φ : P →ₙ* N}

@[to_additive (attr := simp)]
theorem liftOfRightInverse_comp : (p.liftOfRightInverse p_inv hp f hf).comp p = f := liftLeft_comp

@[to_additive]
theorem liftOfRightInverse_comp_apply : ∀ x, (p.liftOfRightInverse p_inv hp f hf) (p x) = f x :=
  liftLeft_comp_apply

@[to_additive]
theorem eq_liftOfRightInverse {f'} : f'.comp p = f → f' = p.liftOfRightInverse p_inv hp f hf :=
  eq_liftLeft

@[to_additive (attr := simp)]
theorem liftLeft_liftOfRightInverse :
    f.liftLeft hp.surjective (p.liftOfRightInverse p_inv hp f hf) liftOfRightInverse_comp_apply =
    p.liftOfRightInverse p_inv hp f hf := rfl

@[to_additive (attr := simp)]
theorem liftOfRightInverse_apply_comp : p.liftOfRightInverse p_inv hp (φ.comp p)
    (fun x => by simp only [comp_apply, hp (p x)]) = φ := ext fun x => by
  simp only [liftOfRightInverse_apply, comp_apply, hp x]

end LiftOfRightInverse

section LiftOfLeftInverse

variable {p : P →ₙ* N} {p_inv : N → P} {hp : LeftInverse p_inv p} {f : M →ₙ* N}
  {hf : ∀ x, p (p_inv (f x)) = f x} {φ : M →ₙ* P}

@[to_additive (attr := simp)]
theorem comp_liftOfLeftInverse : p.comp (p.liftOfLeftInverse p_inv hp f hf) = f := comp_liftRight

@[to_additive]
theorem comp_liftOfLeftInverse_apply : ∀ x, p (p.liftOfLeftInverse p_inv hp f hf x) = f x :=
  comp_liftRight_apply

@[to_additive]
theorem eq_liftOfLeftInverse {f'} : p.comp f' = f → f' = p.liftOfLeftInverse p_inv hp f hf :=
  eq_liftRight

@[to_additive (attr := simp)]
theorem liftRight_liftOfLeftInverse :
    f.liftRight hp.injective (p.liftOfLeftInverse p_inv hp f hf) comp_liftOfLeftInverse_apply =
    p.liftOfLeftInverse p_inv hp f hf := rfl

@[to_additive (attr := simp)]
theorem liftOfLeftInverse_apply_comp : p.liftOfLeftInverse p_inv hp (p.comp φ)
    (fun _ => by simp only [comp_apply, hp (φ _)]) = φ := ext fun x => by
  simp only [liftOfLeftInverse_apply, comp_apply, hp (φ x)]

end LiftOfLeftInverse

section Inverse

variable {f : M →ₙ* N} {g : N → M} {h₁ : LeftInverse g f} {h₂ : RightInverse g f}

@[to_additive (attr := simp)]
theorem inverse_comp : (f.inverse g h₁ h₂).comp f = id M := ext h₁
@[to_additive]
theorem inverse_comp_apply : ∀ x, (f.inverse g h₁ h₂) (f x) = x := h₁
@[to_additive (attr := simp)]
theorem comp_inverse : f.comp (f.inverse g h₁ h₂) = id N := ext h₂
@[to_additive]
theorem comp_inverse_apply : ∀ x, f ((f.inverse g h₁ h₂) x) = x := h₂

@[to_additive]
theorem inverse_eq_liftOfRightInverse : f.inverse g h₁ h₂ =
    liftOfRightInverse f g h₂ (id M) h₁ := rfl
@[to_additive]
theorem inverse_eq_liftOfLeftInverse : f.inverse g h₁ h₂ =
    liftOfLeftInverse f g h₁ (id N) h₂ := rfl
@[to_additive]
theorem inverse_eq_liftLeft : f.inverse g h₁ h₂ = liftLeft (id M) h₂.surjective g h₁ := rfl
@[to_additive]
theorem inverse_eq_liftRight : f.inverse g h₁ h₂ = liftRight (id N) h₁.injective g h₂ := rfl

@[to_additive]
theorem eq_inverse_of_comp_right_eq_id {g'} (hg : f.comp g' = id N) : g' = f.inverse g h₁ h₂ :=
  eq_liftRight hg (hg := fun _ => h₂ _) (hp := h₁.injective)

@[to_additive]
theorem eq_inverse_of_comp_left_eq_id {g'} (hg : g'.comp f = id M) : g' = f.inverse g h₁ h₂ :=
  eq_liftLeft hg (hg := fun _ => h₁ _) (hp := h₂.surjective)

@[to_additive (attr := simp)]
theorem inverse_inverse : (f.inverse g h₁ h₂).inverse f comp_inverse_apply inverse_comp_apply =
    f := rfl

end Inverse

end

/-- Given two mul morphisms `f`, `g` to a commutative semigroup, `f * g` is the mul morphism
sending `x` to `f x * g x`. -/
@[to_additive "Given two additive morphisms `f`, `g` to an additive commutative semigroup,
`f + g` is the additive morphism sending `x` to `f x + g x`."]
instance [Mul M] [CommSemigroup N] : Mul (M →ₙ* N) :=
  ⟨fun f g =>
    { toFun := fun m => f m * g m,
      map_mul' := fun x y => by
        show f (x * y) * g (x * y) = f x * g x * (f y * g y)
        rw [f.map_mul, g.map_mul, ← mul_assoc, ← mul_assoc, mul_right_comm (f x)] }⟩

@[to_additive (attr := simp)]
theorem mul_apply {M N} [Mul M] [CommSemigroup N] (f g : M →ₙ* N) (x : M) :
    (f * g) x = f x * g x := rfl

@[to_additive]
theorem mul_comp [Mul M] [Mul N] [CommSemigroup P] (g₁ g₂ : N →ₙ* P) (f : M →ₙ* N) :
    (g₁ * g₂).comp f = g₁.comp f * g₂.comp f := rfl

@[to_additive]
theorem comp_mul [Mul M] [CommSemigroup N] [CommSemigroup P] (g : N →ₙ* P) (f₁ f₂ : M →ₙ* N) :
    g.comp (f₁ * f₂) = g.comp f₁ * g.comp f₂ := by
  ext
  simp only [mul_apply, Function.comp_apply, map_mul, coe_comp]

end MulHom

namespace MonoidHom

section

open Function

variable [MulOneClass M] [MulOneClass N] [MulOneClass P]

section LiftLeft

variable {f : M →* N} {p : M →* P} {hp : Surjective p} {g hg} {φ : P →* N}

@[to_additive (attr := simp)]
theorem liftLeft_comp : (f.liftLeft hp g hg).comp p = f := ext fun _ => hg _

@[to_additive]
theorem liftLeft_comp_apply : ∀ x, (f.liftLeft hp g hg) (p x) = f x := hg

@[to_additive]
theorem eq_liftLeft {g'} (hg' : g'.comp p = f) : g' = f.liftLeft hp g hg := by
  simpa only [cancel_right hp] using
    hg'.trans (liftLeft_comp (f := f) (hp := hp) (hg := hg)).symm

@[to_additive (attr := simp)]
theorem liftLeft_liftLeft : f.liftLeft hp (f.liftLeft hp g hg) liftLeft_comp_apply =
    f.liftLeft hp g hg := rfl

@[to_additive (attr := simp)]
theorem toMulHom_liftLeft : (f.liftLeft hp g hg).toMulHom =
    f.toMulHom.liftLeft (p := p.toMulHom) hp g hg := rfl

@[to_additive (attr := simp)]
theorem toOneHom_liftLeft : (f.liftLeft hp g hg).toOneHom =
    f.toOneHom.liftLeft p.toOneHom g hg := rfl

theorem liftLeft_apply_comp : (φ.comp p).liftLeft hp φ (fun _ => rfl) = φ := rfl

end LiftLeft

section LiftRight

variable {f : M →* N} {p : P →* N} {hp : Injective p} {g hg}

@[to_additive (attr := simp)]
theorem comp_liftRight : p.comp (f.liftRight hp g hg) = f := ext fun _ => hg _

@[to_additive]
theorem comp_liftRight_apply : ∀ x, p ((f.liftRight hp g hg) x) = f x := hg

@[to_additive]
theorem eq_liftRight {g'} (hg' : p.comp g' = f) : g' = f.liftRight hp g hg := by
  simpa only [cancel_left hp] using
    hg'.trans (comp_liftRight (f := f) (hp := hp) (hg := hg)).symm

@[to_additive (attr := simp)]
theorem liftRight_liftRight : f.liftRight hp (f.liftRight hp g hg) comp_liftRight_apply =
    f.liftRight hp g hg := rfl

@[to_additive (attr := simp)]
theorem toMulHom_liftRight : (f.liftRight hp g hg).toMulHom =
    f.toMulHom.liftRight (p := p.toMulHom) hp g hg := rfl

@[to_additive (attr := simp)]
theorem toOneHom_liftRight : (f.liftRight hp g hg).toOneHom =
    f.toOneHom.liftRight (p := p.toOneHom) hp g hg := rfl

end LiftRight

section LiftOfRightInverse

variable {p : M →* P} {p_inv : P → M} {hp : RightInverse p_inv p} {f : M →* N}
  {hf : ∀ (x : M), f (p_inv (p x)) = f x} {φ : P →* N}

@[to_additive (attr := simp)]
theorem liftOfRightInverse_comp : (p.liftOfRightInverse p_inv hp f hf).comp p = f := liftLeft_comp

@[to_additive]
theorem liftOfRightInverse_comp_apply : ∀ x, (p.liftOfRightInverse p_inv hp f hf) (p x) = f x :=
  liftLeft_comp_apply

@[to_additive]
theorem eq_liftOfRightInverse {f'} : f'.comp p = f → f' = p.liftOfRightInverse p_inv hp f hf :=
  eq_liftLeft

@[to_additive (attr := simp)]
theorem liftLeft_liftOfRightInverse :
    f.liftLeft hp.surjective (p.liftOfRightInverse p_inv hp f hf) liftOfRightInverse_comp_apply =
    p.liftOfRightInverse p_inv hp f hf := rfl

@[to_additive (attr := simp)]
theorem toMulHom_liftOfRightInverse : (p.liftOfRightInverse p_inv hp f hf).toMulHom =
    p.toMulHom.liftOfRightInverse p_inv hp f hf := rfl

@[to_additive (attr := simp)]
theorem toOneHom_liftOfRightInverse : (p.liftOfRightInverse p_inv hp f hf).toOneHom =
    p.toOneHom.liftOfRightInverse p_inv f hf := rfl

@[to_additive (attr := simp)]
theorem liftOfRightInverse_apply_comp : p.liftOfRightInverse p_inv hp (φ.comp p)
    (fun x => by simp only [comp_apply, hp (p x)]) = φ := ext fun x => by
  simp only [liftOfRightInverse_apply, comp_apply, hp x]

end LiftOfRightInverse

section LiftOfLeftInverse

variable {p : P →* N} {p_inv : N → P} {hp : LeftInverse p_inv p} {f : M →* N}
  {hf : ∀ x, p (p_inv (f x)) = f x} {φ : M →* P}

@[to_additive (attr := simp)]
theorem comp_liftOfLeftInverse : p.comp (p.liftOfLeftInverse p_inv hp f hf) = f := comp_liftRight

@[to_additive]
theorem comp_liftOfLeftInverse_apply : ∀ x, p (p.liftOfLeftInverse p_inv hp f hf x) = f x :=
  comp_liftRight_apply

@[to_additive]
theorem eq_liftOfLeftInverse {f'} : p.comp f' = f → f' = p.liftOfLeftInverse p_inv hp f hf :=
  eq_liftRight

@[to_additive (attr := simp)]
theorem liftRight_liftOfLeftInverse :
    f.liftRight hp.injective (p.liftOfLeftInverse p_inv hp f hf) comp_liftOfLeftInverse_apply =
    p.liftOfLeftInverse p_inv hp f hf := rfl

@[to_additive (attr := simp)]
theorem toMulHom_liftOfLeftInverse : (p.liftOfLeftInverse p_inv hp f hf).toMulHom =
    p.toMulHom.liftOfLeftInverse p_inv hp f hf := rfl

@[to_additive (attr := simp)]
theorem toOneHom_liftOfLeftInverse : (p.liftOfLeftInverse p_inv hp f hf).toOneHom =
    p.toOneHom.liftOfLeftInverse p_inv hp f hf := rfl

@[to_additive (attr := simp)]
theorem liftOfLeftInverse_apply_comp : p.liftOfLeftInverse p_inv hp (p.comp φ)
    (fun _ => by simp only [comp_apply, hp (φ _)]) = φ := ext fun x => by
  simp only [liftOfLeftInverse_apply, comp_apply, hp (φ x)]

end LiftOfLeftInverse

section Inverse

variable {f : M →* N} {g : N → M} {h₁ : LeftInverse g f} {h₂ : RightInverse g f}

@[to_additive (attr := simp)]
theorem inverse_comp : (f.inverse g h₁ h₂).comp f = id M := ext h₁
@[to_additive]
theorem inverse_comp_apply : ∀ x, (f.inverse g h₁ h₂) (f x) = x := h₁
@[to_additive (attr := simp)]
theorem comp_inverse : f.comp (f.inverse g h₁ h₂) = id N := ext h₂
@[to_additive]
theorem comp_inverse_apply : ∀ x, f ((f.inverse g h₁ h₂) x) = x := h₂

@[to_additive]
theorem inverse_eq_liftOfRightInverse : f.inverse g h₁ h₂ =
    liftOfRightInverse f g h₂ (id M) h₁ := rfl
@[to_additive]
theorem inverse_eq_liftOfLeftInverse : f.inverse g h₁ h₂ = liftOfLeftInverse f g h₁ (id N) h₂ := rfl
@[to_additive]
theorem inverse_eq_liftLeft : f.inverse g h₁ h₂ = liftLeft (id M) h₂.surjective g h₁ := rfl
@[to_additive]
theorem inverse_eq_liftRight : f.inverse g h₁ h₂ = liftRight (id N) h₁.injective g h₂ := rfl

@[to_additive]
theorem eq_inverse_of_comp_right_eq_id {g'} (hg : f.comp g' = id N) : g' = f.inverse g h₁ h₂ :=
  eq_liftRight hg (hg := fun _ => h₂ _) (hp := h₁.injective)

@[to_additive]
theorem eq_inverse_of_comp_left_eq_id {g'} (hg : g'.comp f = id M) : g' = f.inverse g h₁ h₂ :=
  eq_liftLeft hg (hg := fun _ => h₁ _) (hp := h₂.surjective)

@[to_additive (attr := simp)]
theorem inverse_inverse : (f.inverse g h₁ h₂).inverse f comp_inverse_apply inverse_comp_apply =
    f := rfl

@[to_additive (attr := simp)]
theorem toMulHom_inverse : (f.inverse g h₁ h₂).toMulHom = f.toMulHom.inverse g h₁ h₂ := rfl

@[to_additive (attr := simp)]
theorem toOneHom_inverse : (f.inverse g h₁ h₂).toOneHom = f.toOneHom.inverse g h₁ := rfl

end Inverse

end

section Group
variable [Group G]

/-- A homomorphism from a group to a monoid is injective iff its kernel is trivial.
For the iff statement on the triviality of the kernel, see `injective_iff_map_eq_one'`. -/
@[to_additive
  "A homomorphism from an additive group to an additive monoid is injective iff
  its kernel is trivial. For the iff statement on the triviality of the kernel,
  see `injective_iff_map_eq_zero'`."]
theorem _root_.injective_iff_map_eq_one {G H} [Group G] [MulOneClass H]
    [FunLike F G H] [MonoidHomClass F G H]
    (f : F) : Function.Injective f ↔ ∀ a, f a = 1 → a = 1 :=
  ⟨fun h _ => (map_eq_one_iff f h).mp, fun h x y hxy =>
    mul_inv_eq_one.1 <| h _ <| by rw [map_mul, hxy, ← map_mul, mul_inv_cancel, map_one]⟩

/-- A homomorphism from a group to a monoid is injective iff its kernel is trivial,
stated as an iff on the triviality of the kernel.
For the implication, see `injective_iff_map_eq_one`. -/
@[to_additive
  "A homomorphism from an additive group to an additive monoid is injective iff its
  kernel is trivial, stated as an iff on the triviality of the kernel. For the implication, see
  `injective_iff_map_eq_zero`."]
theorem _root_.injective_iff_map_eq_one' {G H} [Group G] [MulOneClass H]
    [FunLike F G H] [MonoidHomClass F G H]
    (f : F) : Function.Injective f ↔ ∀ a, f a = 1 ↔ a = 1 :=
  (injective_iff_map_eq_one f).trans <|
    forall_congr' fun _ => ⟨fun h => ⟨h, fun H => H.symm ▸ map_one f⟩, Iff.mp⟩

/-- Makes a group homomorphism from a proof that the map preserves right division
`fun x y => x * y⁻¹`. See also `MonoidHom.of_map_div` for a version using `fun x y => x / y`.
-/
@[to_additive
  "Makes an additive group homomorphism from a proof that the map preserves
  the operation `fun a b => a + -b`. See also `AddMonoidHom.ofMapSub` for a version using
  `fun a b => a - b`."]
def ofMapMulInv {H : Type*} [Group H] (f : G → H)
    (map_div : ∀ a b : G, f (a * b⁻¹) = f a * (f b)⁻¹) : G →* H :=
  (mk' f) fun x y =>
    calc
      f (x * y) = f x * (f <| 1 * 1⁻¹ * y⁻¹)⁻¹ := by
        { simp only [one_mul, inv_one, ← map_div, inv_inv] }
      _ = f x * f y := by
        { simp only [map_div]
          simp only [mul_inv_cancel, one_mul, inv_inv] }

@[to_additive (attr := simp)]
theorem coe_of_map_mul_inv {H : Type*} [Group H] (f : G → H)
    (map_div : ∀ a b : G, f (a * b⁻¹) = f a * (f b)⁻¹) :
  ↑(ofMapMulInv f map_div) = f := rfl

/-- Define a morphism of additive groups given a map which respects ratios. -/
@[to_additive "Define a morphism of additive groups given a map which respects difference."]
def ofMapDiv {H : Type*} [Group H] (f : G → H) (hf : ∀ x y, f (x / y) = f x / f y) : G →* H :=
  ofMapMulInv f (by simpa only [div_eq_mul_inv] using hf)

@[to_additive (attr := simp)]
theorem coe_of_map_div {H : Type*} [Group H] (f : G → H) (hf : ∀ x y, f (x / y) = f x / f y) :
    ↑(ofMapDiv f hf) = f := rfl

end Group

section Mul
variable [MulOneClass M] [CommMonoid N]

/-- Given two monoid morphisms `f`, `g` to a commutative monoid, `f * g` is the monoid morphism
sending `x` to `f x * g x`. -/
@[to_additive]
instance mul : Mul (M →* N) :=
  ⟨fun f g =>
    { toFun := fun m => f m * g m,
      map_one' := by simp,
      map_mul' := fun x y => by
        rw [f.map_mul, g.map_mul, ← mul_assoc, ← mul_assoc, mul_right_comm (f x)] }⟩

/-- Given two additive monoid morphisms `f`, `g` to an additive commutative monoid,
`f + g` is the additive monoid morphism sending `x` to `f x + g x`. -/
add_decl_doc AddMonoidHom.add

@[to_additive (attr := simp)] lemma mul_apply (f g : M →* N) (x : M) : (f * g) x = f x * g x := rfl

@[to_additive]
lemma mul_comp [MulOneClass P] (g₁ g₂ : M →* N) (f : P →* M) :
    (g₁ * g₂).comp f = g₁.comp f * g₂.comp f := rfl

@[to_additive]
lemma comp_mul [CommMonoid P] (g : N →* P) (f₁ f₂ : M →* N) :
    g.comp (f₁ * f₂) = g.comp f₁ * g.comp f₂ := by
  ext; simp only [mul_apply, Function.comp_apply, map_mul, coe_comp]

end Mul

section InvDiv
variable [MulOneClass M] [MulOneClass N] [CommGroup G] [CommGroup H]

/-- If `f` is a monoid homomorphism to a commutative group, then `f⁻¹` is the homomorphism sending
`x` to `(f x)⁻¹`. -/
@[to_additive "If `f` is an additive monoid homomorphism to an additive commutative group,
then `-f` is the homomorphism sending `x` to `-(f x)`."]
instance : Inv (M →* G) where
  inv f := mk' (fun g ↦ (f g)⁻¹) fun a b ↦ by simp_rw [← mul_inv, f.map_mul]

@[to_additive (attr := simp)] lemma inv_apply (f : M →* G) (x : M) : f⁻¹ x = (f x)⁻¹ := rfl

@[to_additive (attr := simp)]
theorem inv_comp (φ : N →* G) (ψ : M →* N) : φ⁻¹.comp ψ = (φ.comp ψ)⁻¹ := rfl

@[to_additive (attr := simp)]
theorem comp_inv (φ : G →* H) (ψ : M →* G) : φ.comp ψ⁻¹ = (φ.comp ψ)⁻¹ := by
  ext
  simp only [Function.comp_apply, inv_apply, map_inv, coe_comp]

/-- If `f` and `g` are monoid homomorphisms to a commutative group, then `f / g` is the homomorphism
sending `x` to `(f x) / (g x)`. -/
@[to_additive "If `f` and `g` are monoid homomorphisms to an additive commutative group,
then `f - g` is the homomorphism sending `x` to `(f x) - (g x)`."]
instance : Div (M →* G) where
  div f g := mk' (fun x ↦ f x / g x) fun a b ↦ by
    simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

@[to_additive (attr := simp)] lemma div_apply (f g : M →* G) (x : M) : (f / g) x = f x / g x := rfl

@[to_additive (attr := simp)]
lemma div_comp (f g : N →* G) (h : M →* N) : (f / g).comp h = f.comp h / g.comp h := rfl

@[to_additive (attr := simp)]
lemma comp_div (f : G →* H) (g h : M →* G) : f.comp (g / h) = f.comp g / f.comp h := by
  ext; simp only [Function.comp_apply, div_apply, map_div, coe_comp]

end InvDiv

/-- If `H` is commutative and `G →* H` is injective, then `G` is commutative. -/
def commGroupOfInjective [Group G] [CommGroup H] (f : G →* H) (hf : Function.Injective f) :
    CommGroup G :=
  ⟨by simp_rw [← hf.eq_iff, map_mul, mul_comm, implies_true]⟩

/-- If `G` is commutative and `G →* H` is surjective, then `H` is commutative. -/
def commGroupOfSurjective [CommGroup G] [Group H] (f : G →* H) (hf : Function.Surjective f) :
    CommGroup H :=
  ⟨by simp_rw [hf.forall₂, ← map_mul, mul_comm, implies_true]⟩

end MonoidHom
