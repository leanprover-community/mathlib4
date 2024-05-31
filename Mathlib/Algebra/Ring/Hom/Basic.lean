/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston, Jireh Loreaux
-/
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Algebra.GroupWithZero.InjSurj
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Data.Set.Basic

#align_import algebra.hom.ring from "leanprover-community/mathlib"@"cf9386b56953fb40904843af98b7a80757bbe7f9"

/-!
# Additional lemmas about homomorphisms of semirings and rings

These lemmas have been banished here to avoid unnecessary imports in
`Mathlib.Algebra.Hom.Ring.Defs`.

They could be moved to more natural homes.
-/


open Function

variable {F α β γ : Type*}

namespace RingHom

section

variable {_ : NonAssocSemiring α} {_ : NonAssocSemiring β} (f : α →+* β) {x y : α}

/-- `f : α →+* β` has a trivial codomain iff its range is `{0}`. -/
theorem codomain_trivial_iff_range_eq_singleton_zero : (0 : β) = 1 ↔ Set.range f = {0} :=
  f.codomain_trivial_iff_range_trivial.trans
    ⟨fun h =>
      Set.ext fun y => ⟨fun ⟨x, hx⟩ => by simp [← hx, h x], fun hy => ⟨0, by simpa using hy.symm⟩⟩,
      fun h x => Set.mem_singleton_iff.mp (h ▸ Set.mem_range_self x)⟩
#align ring_hom.codomain_trivial_iff_range_eq_singleton_zero RingHom.codomain_trivial_iff_range_eq_singleton_zero

end

section Semiring

variable [Semiring α] [Semiring β]

theorem isUnit_map (f : α →+* β) {a : α} : IsUnit a → IsUnit (f a) :=
  IsUnit.map f
#align ring_hom.is_unit_map RingHom.isUnit_map

protected theorem map_dvd (f : α →+* β) {a b : α} : a ∣ b → f a ∣ f b :=
  map_dvd f
#align ring_hom.map_dvd RingHom.map_dvd

end Semiring

end RingHom

/-- Pullback `IsDomain` instance along an injective function. -/
protected theorem Function.Injective.isDomain [Ring α] [IsDomain α] [Ring β] (f : β →+* α)
    (hf : Injective f) : IsDomain β := by
  haveI := pullback_nonzero f f.map_zero f.map_one
  haveI := IsRightCancelMulZero.to_noZeroDivisors α
  haveI := hf.noZeroDivisors f f.map_zero f.map_mul
  exact NoZeroDivisors.to_isDomain β
#align function.injective.is_domain Function.Injective.isDomain
