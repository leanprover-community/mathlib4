/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston, Jireh Loreaux
-/
import Mathlib.Algebra.Divisibility.Hom
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Data.Set.Insert

/-!
# Additional lemmas about homomorphisms of semirings and rings

These lemmas were in `Mathlib/Algebra/Hom/Ring/Defs.lean` and have now been deprecated.
-/

assert_not_exists RelIso Field

open Function

variable {α β : Type*}

namespace RingHom

section

variable {_ : NonAssocSemiring α} {_ : NonAssocSemiring β} (f : α →+* β)

/-- `f : α →+* β` has a trivial codomain iff its range is `{0}`. -/
@[deprecated "Use range_eq_singleton_iff and codomain_trivial_iff_range_trivial"
    (since := "2025-06-09")]
theorem codomain_trivial_iff_range_eq_singleton_zero : (0 : β) = 1 ↔ Set.range f = {0} :=
  f.codomain_trivial_iff_range_trivial.trans
    ⟨fun h =>
      Set.ext fun y => ⟨fun ⟨x, hx⟩ => by simp [← hx, h x], fun hy => ⟨0, by simpa using hy.symm⟩⟩,
      fun h x => Set.mem_singleton_iff.mp (h ▸ Set.mem_range_self x)⟩

end

section Semiring

variable [Semiring α] [Semiring β]
@[deprecated map_dvd (since := "2025-06-09")]
protected theorem map_dvd (f : α →+* β) {a b : α} : a ∣ b → f a ∣ f b :=
  map_dvd f

end Semiring

end RingHom
