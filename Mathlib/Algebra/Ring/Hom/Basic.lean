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

end


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
