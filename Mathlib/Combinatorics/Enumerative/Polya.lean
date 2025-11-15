/-
Copyright (c) 2025 Zihui Bai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zihui Bai, Zhengfeng Yang
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
## Main definitions and results

* `MulAction (Equiv.Perm X) (X → Y)`: action of permutations on colorings by precomposition.
* `coloringEquiv`: two colorings are equivalent if they lie in the same orbit.
* `coloringEquiv_equivalence`: this defines an equivalence relation.
* `orbit_size_eq_index`: the orbit–stabilizer theorem reformulated for colorings.

## Implementation notes

We model a coloring as a function `X → Y`, where `X` is a finite set of objects
and `Y` is a finite set of colors.
The permutation group `Equiv.Perm X` acts on colorings by precomposition.
-/

open scoped BigOperators
open MulAction Finset Equiv

namespace DistinctColorings

variable {X Y : Type*} (c : X → Y)

/--
A *coloring* is a function `X → Y`.
The permutation group `Equiv.Perm X` acts on colorings by precomposition:
`(g • c) x = c (g⁻¹ x)`.
-/
instance : MulAction (Equiv.Perm X) (X → Y) where
  smul g c := fun x ↦ c (g⁻¹ • x)
  one_smul := by
    intro c
    ext x
    simp [HSMul.hSMul]
    change c ((1 : Equiv.Perm X) • x) = c x
    rw [one_smul (Equiv.Perm X) x]
  mul_smul := by
    intro g g' f
    ext x
    simp [HSMul.hSMul]
    change f ((g'⁻¹ * g⁻¹) • x) = f (g'⁻¹ • (g⁻¹ • x))
    rw [mul_smul g'⁻¹ g⁻¹ x]

/--
For permutations `f, g : Equiv.Perm X`, the colorings `g • c` and `f • c`
are equal if and only if `f⁻¹ * g` belongs to the stabilizer of `c`.
-/
theorem smul_eq_iff_mem_stabilizer (f g : Equiv.Perm X) (c : X → Y) :
    g • c = f • c ↔ f⁻¹ * g ∈ MulAction.stabilizer (Equiv.Perm X) c := by
  constructor
  · intro h_eq
    simp [MulAction.stabilizer]
    ext x
    simp only [MulAction.mul_smul]
    rw [h_eq]
    change c (f⁻¹ • (f • x)) = c x
    rw [inv_smul_smul]
  · intro h
    simp [MulAction.stabilizer] at h
    rw [← h]
    simp [mul_smul]
    rw [mul_smul] at h
    exact h

/-- Two colorings are equivalent if they lie in the same orbit
under the action of `Equiv.Perm X`. -/
def coloringEquiv (c₁ c₂ : X → Y) : Prop :=
  ∃ f : Equiv.Perm X, f • c₁ = c₂

/-- The equivalence relation given by `coloringEquiv`. -/
theorem coloringEquiv_equivalence : Equivalence (coloringEquiv (X := X) (Y := Y)) where
  refl c := ⟨1, by simp⟩
  symm := by
    rintro c₁ c₂ ⟨f, h⟩
    use f⁻¹
    rw [← h]
    exact inv_smul_smul f c₁
  trans := by
    rintro c₁ c₂ c₃ ⟨f, h₁⟩ ⟨g, h₂⟩
    use g * f
    rw [← h₂, ← h₁]
    exact mul_smul g f c₁

/-- Reformulation of the orbit–stabilizer theorem for colorings. -/
theorem orbit_size_eq_index (c : X → Y)
  [Fintype (Equiv.Perm X)]
  [Fintype (MulAction.orbit (Equiv.Perm X) c)]
  [Fintype (MulAction.stabilizer (Equiv.Perm X) c)] :
  Fintype.card (MulAction.orbit (Equiv.Perm X) c)
    = Fintype.card (Equiv.Perm X) /
      Fintype.card (MulAction.stabilizer (Equiv.Perm X) c) := by
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (Equiv.Perm X) c

  have hb : 0 < Fintype.card (MulAction.stabilizer (Equiv.Perm X) c) := by
    simpa using (Fintype.card_pos_iff.mpr ⟨1, by simp [MulAction.stabilizer]⟩)
  rw [← h]
  exact (Nat.mul_div_cancel _ hb).symm

end DistinctColorings
