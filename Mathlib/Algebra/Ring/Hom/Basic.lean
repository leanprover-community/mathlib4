/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston, Jireh Loreaux
-/
import Mathlib.Algebra.Divisibility.Hom
import Mathlib.Algebra.GroupWithZero.InjSurj
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Data.Set.Insert

/-!
# Additional lemmas about homomorphisms of semirings and rings

These lemmas have been banished here to avoid unnecessary imports in
`Mathlib/Algebra/Hom/Ring/Defs.lean`.

They could be moved to more natural homes.
-/

assert_not_exists RelIso Field

open Function

variable {α β M N P : Type*}

namespace NonUnitalRingHom

section

open Function

variable [NonUnitalNonAssocSemiring M] [NonUnitalNonAssocSemiring N] [NonUnitalNonAssocSemiring P]

section LiftLeft

variable {f : M →ₙ+* N} {p : M →ₙ+* P} {hp : Surjective p} {g hg}

theorem liftLeft_comp : (f.liftLeft hp g hg).comp p = f := ext fun _ => hg _

theorem liftLeft_comp_apply : ∀ x, (f.liftLeft hp g hg) (p x) = f x := hg

theorem eq_liftLeft {g'} (hg' : g'.comp p = f) : g' = f.liftLeft hp g hg := by
  simpa only [cancel_right hp] using
    hg'.trans (liftLeft_comp (f := f) (hp := hp) (hg := hg)).symm

theorem liftLeft_liftLeft : f.liftLeft hp (f.liftLeft hp g hg) liftLeft_comp_apply =
    f.liftLeft hp g hg := rfl

end LiftLeft

section LiftRight

variable {f : M →ₙ+* N} {p : P →ₙ+* N} {hp : Injective p} {g hg}

theorem comp_liftRight : p.comp (f.liftRight hp g hg) = f := ext fun _ => hg _

theorem comp_liftRight_apply : ∀ x, p ((f.liftRight hp g hg) x) = f x := hg

theorem eq_liftRight {g'} (hg' : p.comp g' = f) : g' = f.liftRight hp g hg := by
  simpa only [cancel_left hp] using
    hg'.trans (comp_liftRight (f := f) (hp := hp) (hg := hg)).symm

theorem liftRight_liftRight : f.liftRight hp (f.liftRight hp g hg) comp_liftRight_apply =
    f.liftRight hp g hg := rfl

end LiftRight

section LiftOfRightInverse

variable {p : M →ₙ+* P} {p_inv : P → M} {hp : RightInverse p_inv p} {f : M →ₙ+* N}
  {hf : ∀ (x : M), f (p_inv (p x)) = f x} {φ : P →ₙ+* N}

theorem liftOfRightInverse_comp : (p.liftOfRightInverse p_inv hp f hf).comp p = f := liftLeft_comp

theorem liftOfRightInverse_comp_apply : ∀ x, (p.liftOfRightInverse p_inv hp f hf) (p x) = f x :=
  liftLeft_comp_apply

theorem eq_liftOfRightInverse {f'} : f'.comp p = f → f' = p.liftOfRightInverse p_inv hp f hf :=
  eq_liftLeft

theorem liftLeft_liftOfRightInverse :
    f.liftLeft hp.surjective (p.liftOfRightInverse p_inv hp f hf) liftOfRightInverse_comp_apply =
    p.liftOfRightInverse p_inv hp f hf := rfl

theorem liftOfRightInverse_apply_comp : p.liftOfRightInverse p_inv hp (φ.comp p)
    (fun x => by simp only [comp_apply, hp (p x)]) = φ := ext fun x => by
  simp only [liftOfRightInverse_apply, comp_apply, hp x]

end LiftOfRightInverse

section LiftOfLeftInverse

variable {p : P →ₙ+* N} {p_inv : N → P} {hp : LeftInverse p_inv p} {f : M →ₙ+* N}
  {hf : ∀ x, p (p_inv (f x)) = f x} {φ : M →ₙ+* P}

theorem comp_liftOfLeftInverse : p.comp (p.liftOfLeftInverse p_inv hp f hf) = f := comp_liftRight

theorem comp_liftOfLeftInverse_apply : ∀ x, p (p.liftOfLeftInverse p_inv hp f hf x) = f x :=
  comp_liftRight_apply

theorem eq_liftOfLeftInverse {f'} : p.comp f' = f → f' = p.liftOfLeftInverse p_inv hp f hf :=
  eq_liftRight

theorem liftRight_liftOfLeftInverse :
    f.liftRight hp.injective (p.liftOfLeftInverse p_inv hp f hf) comp_liftOfLeftInverse_apply =
    p.liftOfLeftInverse p_inv hp f hf := rfl

theorem liftOfLeftInverse_apply_comp : p.liftOfLeftInverse p_inv hp (p.comp φ)
    (fun _ => by simp only [comp_apply, hp (φ _)]) = φ := ext fun x => by
  simp only [liftOfLeftInverse_apply, comp_apply, hp (φ x)]

end LiftOfLeftInverse

section Inverse

variable {f : M →ₙ+* N} {g : N → M} {h₁ : LeftInverse g f} {h₂ : RightInverse g f}

theorem inverse_comp : (f.inverse g h₁ h₂).comp f = NonUnitalRingHom.id M := ext h₁

theorem inverse_comp_apply : ∀ x, (f.inverse g h₁ h₂) (f x) = x := h₁

theorem comp_inverse : f.comp (f.inverse g h₁ h₂) = NonUnitalRingHom.id N := ext h₂

theorem comp_inverse_apply : ∀ x, f ((f.inverse g h₁ h₂) x) = x := h₂

theorem inverse_eq_liftOfRightInverse : f.inverse g h₁ h₂ =
    liftOfRightInverse f g h₂ (NonUnitalRingHom.id M) h₁ := rfl

theorem inverse_eq_liftOfLeftInverse : f.inverse g h₁ h₂ =
    liftOfLeftInverse f g h₁ (NonUnitalRingHom.id N) h₂ := rfl

theorem inverse_eq_liftLeft : f.inverse g h₁ h₂ =
    liftLeft (NonUnitalRingHom.id M) h₂.surjective g h₁ := rfl

theorem inverse_eq_liftRight : f.inverse g h₁ h₂ =
    liftRight (NonUnitalRingHom.id N) h₁.injective g h₂ := rfl

theorem eq_inverse_of_comp_right_eq_id {g'} (hg : f.comp g' = NonUnitalRingHom.id N) :
    g' = f.inverse g h₁ h₂ :=
  eq_liftRight hg (hg := fun _ => h₂ _) (hp := h₁.injective)

theorem eq_inverse_of_comp_left_eq_id {g'} (hg : g'.comp f = NonUnitalRingHom.id M) :
    g' = f.inverse g h₁ h₂ :=
  eq_liftLeft hg (hg := fun _ => h₁ _) (hp := h₂.surjective)

theorem inverse_inverse : (f.inverse g h₁ h₂).inverse f comp_inverse_apply inverse_comp_apply =
    f := rfl

end Inverse

end

end NonUnitalRingHom


namespace RingHom

section

variable {_ : NonAssocSemiring α} {_ : NonAssocSemiring β} (f : α →+* β)

/-- `f : α →+* β` has a trivial codomain iff its range is `{0}`. -/
theorem codomain_trivial_iff_range_eq_singleton_zero : (0 : β) = 1 ↔ Set.range f = {0} :=
  f.codomain_trivial_iff_range_trivial.trans
    ⟨fun h =>
      Set.ext fun y => ⟨fun ⟨x, hx⟩ => by simp [← hx, h x], fun hy => ⟨0, by simpa using hy.symm⟩⟩,
      fun h x => Set.mem_singleton_iff.mp (h ▸ Set.mem_range_self x)⟩

end

section

open Function

variable [NonAssocSemiring M] [NonAssocSemiring N] [NonAssocSemiring P]

section LiftLeft

variable {f : M →+* N} {p : M →+* P} {hp : Surjective p} {g hg}

theorem liftLeft_comp : (f.liftLeft hp g hg).comp p = f := ext fun _ => hg _

theorem liftLeft_comp_apply : ∀ x, (f.liftLeft hp g hg) (p x) = f x := hg

theorem eq_liftLeft {g'} (hg' : g'.comp p = f) : g' = f.liftLeft hp g hg := by
  simpa only [cancel_right hp] using
    hg'.trans (liftLeft_comp (f := f) (hp := hp) (hg := hg)).symm

theorem liftLeft_liftLeft : f.liftLeft hp (f.liftLeft hp g hg) liftLeft_comp_apply =
    f.liftLeft hp g hg := rfl

end LiftLeft

section LiftRight

variable {f : M →+* N} {p : P →+* N} {hp : Injective p} {g hg}

theorem comp_liftRight : p.comp (f.liftRight hp g hg) = f := ext fun _ => hg _

theorem comp_liftRight_apply : ∀ x, p ((f.liftRight hp g hg) x) = f x := hg

theorem eq_liftRight {g'} (hg' : p.comp g' = f) : g' = f.liftRight hp g hg := by
  simpa only [cancel_left hp] using
    hg'.trans (comp_liftRight (f := f) (hp := hp) (hg := hg)).symm

theorem liftRight_liftRight : f.liftRight hp (f.liftRight hp g hg) comp_liftRight_apply =
    f.liftRight hp g hg := rfl

end LiftRight

section LiftOfRightInverse

variable {p : M →+* P} {p_inv : P → M} {hp : RightInverse p_inv p} {f : M →+* N}
  {hf : ∀ (x : M), f (p_inv (p x)) = f x} {φ : P →+* N}

theorem liftOfRightInverse_comp : (p.liftOfRightInverse p_inv hp f hf).comp p = f := liftLeft_comp

theorem liftOfRightInverse_comp_apply : ∀ x, (p.liftOfRightInverse p_inv hp f hf) (p x) = f x :=
  liftLeft_comp_apply

theorem eq_liftOfRightInverse {f'} : f'.comp p = f → f' = p.liftOfRightInverse p_inv hp f hf :=
  eq_liftLeft

theorem liftLeft_liftOfRightInverse :
    f.liftLeft hp.surjective (p.liftOfRightInverse p_inv hp f hf) liftOfRightInverse_comp_apply =
    p.liftOfRightInverse p_inv hp f hf := rfl

theorem liftOfRightInverse_apply_comp : p.liftOfRightInverse p_inv hp (φ.comp p)
    (fun x => by simp only [comp_apply, hp (p x)]) = φ := ext fun x => by
  simp only [liftOfRightInverse_apply, comp_apply, hp x]

end LiftOfRightInverse

section LiftOfLeftInverse

variable {p : P →+* N} {p_inv : N → P} {hp : LeftInverse p_inv p} {f : M →+* N}
  {hf : ∀ x, p (p_inv (f x)) = f x} {φ : M →+* P}

theorem comp_liftOfLeftInverse : p.comp (p.liftOfLeftInverse p_inv hp f hf) = f := comp_liftRight

theorem comp_liftOfLeftInverse_apply : ∀ x, p (p.liftOfLeftInverse p_inv hp f hf x) = f x :=
  comp_liftRight_apply

theorem eq_liftOfLeftInverse {f'} : p.comp f' = f → f' = p.liftOfLeftInverse p_inv hp f hf :=
  eq_liftRight

theorem liftRight_liftOfLeftInverse :
    f.liftRight hp.injective (p.liftOfLeftInverse p_inv hp f hf) comp_liftOfLeftInverse_apply =
    p.liftOfLeftInverse p_inv hp f hf := rfl

theorem liftOfLeftInverse_apply_comp : p.liftOfLeftInverse p_inv hp (p.comp φ)
    (fun _ => by simp only [comp_apply, hp (φ _)]) = φ := ext fun x => by
  simp only [liftOfLeftInverse_apply, comp_apply, hp (φ x)]

end LiftOfLeftInverse

section Inverse

variable {f : M →+* N} {g : N → M} {h₁ : LeftInverse g f} {h₂ : RightInverse g f}

theorem inverse_comp : (f.inverse g h₁ h₂).comp f = RingHom.id M := ext h₁

theorem inverse_comp_apply : ∀ x, (f.inverse g h₁ h₂) (f x) = x := h₁

theorem comp_inverse : f.comp (f.inverse g h₁ h₂) = RingHom.id N := ext h₂

theorem comp_inverse_apply : ∀ x, f ((f.inverse g h₁ h₂) x) = x := h₂

theorem inverse_eq_liftOfRightInverse : f.inverse g h₁ h₂ =
    liftOfRightInverse f g h₂ (RingHom.id M) h₁ := rfl

theorem inverse_eq_liftOfLeftInverse : f.inverse g h₁ h₂ =
    liftOfLeftInverse f g h₁ (RingHom.id N) h₂ := rfl

theorem inverse_eq_liftLeft : f.inverse g h₁ h₂ =
    liftLeft (RingHom.id M) h₂.surjective g h₁ := rfl

theorem inverse_eq_liftRight : f.inverse g h₁ h₂ =
    liftRight (RingHom.id N) h₁.injective g h₂ := rfl

theorem eq_inverse_of_comp_right_eq_id {g'} (hg : f.comp g' = RingHom.id N) :
    g' = f.inverse g h₁ h₂ :=
  eq_liftRight hg (hg := fun _ => h₂ _) (hp := h₁.injective)

theorem eq_inverse_of_comp_left_eq_id {g'} (hg : g'.comp f = RingHom.id M) :
    g' = f.inverse g h₁ h₂ :=
  eq_liftLeft hg (hg := fun _ => h₁ _) (hp := h₂.surjective)

theorem inverse_inverse : (f.inverse g h₁ h₂).inverse f comp_inverse_apply inverse_comp_apply =
    f := rfl

end Inverse

end

section Semiring

variable [Semiring α] [Semiring β]

protected theorem map_dvd (f : α →+* β) {a b : α} : a ∣ b → f a ∣ f b :=
  map_dvd f

end Semiring

end RingHom


/-- Pullback `IsDomain` instance along an injective function. -/
protected theorem Function.Injective.isDomain [Semiring α] [IsDomain α] [Semiring β] {F}
    [FunLike F β α] [MonoidWithZeroHomClass F β α] (f : F) (hf : Injective f) : IsDomain β where
  __ := domain_nontrivial f (map_zero _) (map_one _)
  __ := hf.isCancelMulZero f (map_zero _) (map_mul _)
