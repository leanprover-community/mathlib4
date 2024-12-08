/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston, Jireh Loreaux
-/
import Mathlib.Algebra.Divisibility.Hom
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Data.Set.Basic

/-!
# Additional lemmas about homomorphisms of semirings and rings

These lemmas have been banished here to avoid unnecessary imports in
`Mathlib.Algebra.Hom.Ring.Defs`.

They could be moved to more natural homes.
-/


open Function

variable {α β : Type*}

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

section Semiring

variable [Semiring α] [Semiring β]

protected theorem map_dvd (f : α →+* β) {a b : α} : a ∣ b → f a ∣ f b :=
  map_dvd f

end Semiring

end RingHom

/-- Pullback `IsDomain` instance along an injective function. -/
protected theorem Function.Injective.isDomain [Semiring α] [IsDomain α] [Semiring β] (f : β →+* α)
    (hf : Injective f) : IsDomain β where
  mul_left_cancel_of_ne_zero {a b c} h h2 := hf <| mul_left_cancel₀ (f.map_zero ▸ hf.ne h) <| by
    simpa only [map_mul] using congr(f $(h2))
  mul_right_cancel_of_ne_zero {a b c} h h2 := hf <| mul_right_cancel₀ (f.map_zero ▸ hf.ne h) <| by
    simpa only [map_mul] using congr(f $(h2))
  exists_pair_ne := f.domain_nontrivial.exists_pair_ne
