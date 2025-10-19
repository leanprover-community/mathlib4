/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau
-/
import Mathlib.Algebra.Group.Submonoid.Basic
import Mathlib.Data.DFinsupp.Defs

/-!
# Extensionality principles for `DFinsupp`

## Main results

* `DFinsupp.addHom_ext`, `DFinsupp.addHom_ext'`: if two additive homomorphisms from `Π₀ i, β i`
  are equal on each `single a b`, then they are equal.
-/


universe u u₁ u₂ v v₁ v₂ v₃ w x y l

variable {ι : Type u} {γ : Type w} {β : ι → Type v} {β₁ : ι → Type v₁} {β₂ : ι → Type v₂}

namespace DFinsupp

section DecidableEq
variable [DecidableEq ι]

section AddMonoid

variable [∀ i, AddZeroClass (β i)]

@[simp]
theorem add_closure_iUnion_range_single :
    AddSubmonoid.closure (⋃ i : ι, Set.range (single i : β i → Π₀ i, β i)) = ⊤ :=
  top_unique fun x _ => by
    apply DFinsupp.induction x
    · exact AddSubmonoid.zero_mem _
    exact fun a b f _ _ hf =>
      AddSubmonoid.add_mem _
        (AddSubmonoid.subset_closure <| Set.mem_iUnion.2 ⟨a, Set.mem_range_self _⟩) hf

/-- If two additive homomorphisms from `Π₀ i, β i` are equal on each `single a b`, then
they are equal. -/
theorem addHom_ext {γ : Type w} [AddZeroClass γ] ⦃f g : (Π₀ i, β i) →+ γ⦄
    (H : ∀ (i : ι) (y : β i), f (single i y) = g (single i y)) : f = g := by
  refine AddMonoidHom.eq_of_eqOn_denseM add_closure_iUnion_range_single fun f hf => ?_
  simp only [Set.mem_iUnion, Set.mem_range] at hf
  rcases hf with ⟨x, y, rfl⟩
  apply H

/-- If two additive homomorphisms from `Π₀ i, β i` are equal on each `single a b`, then
they are equal.

See note [partially-applied ext lemmas]. -/
@[ext]
theorem addHom_ext' {γ : Type w} [AddZeroClass γ] ⦃f g : (Π₀ i, β i) →+ γ⦄
    (H : ∀ x, f.comp (singleAddHom β x) = g.comp (singleAddHom β x)) : f = g :=
  addHom_ext fun x => DFunLike.congr_fun (H x)

end AddMonoid

end DecidableEq

end DFinsupp
