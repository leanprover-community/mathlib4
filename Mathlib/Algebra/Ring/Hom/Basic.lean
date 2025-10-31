/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston, Jireh Loreaux
-/

import Mathlib.Algebra.Ring.Hom.InjSurj

/-!
# Additional lemmas about homomorphisms of semirings and rings
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

end RingHom
