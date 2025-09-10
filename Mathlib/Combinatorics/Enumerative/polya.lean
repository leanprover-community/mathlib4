/-
Copyright 2025

This file develops some basic lemmas about colorings under the action of
the permutation group `Equiv.Perm X`. It contains:

* A `MulAction` instance of `Equiv.Perm X` on functions `X → Y`,
  where `X` is the set of objects to be colored, and `Y` is the set of colors.
* An equivalence relation on colorings given by the group action.
* A version of the orbit–stabilizer theorem for colorings.
-/

import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.GroupTheory.Index
open MulAction Finset Equiv BigOperators

/-
In this file we study how the permutation group `Equiv.Perm X` acts on functions `X → Y`
(called colorings). We introduce the equivalence relation of two colorings being in the same orbit,
prove that this is indeed an equivalence relation, and derive a version of the orbit–stabilizer
theorem in this context.
-/
namespace DistinctColorings

variable {X Y : Type*}
variable (c : X → Y)
/-- A coloring is a function `X → Y`.
The group `Equiv.Perm X` acts on colorings by precomposition. -/
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



/-- For two permutations `f, g`, the colorings `g • c` and `f • c` are equal
iff `f⁻¹ * g` lies in the stabilizer of `c`. -/
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
    rw [ mul_smul] at h
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
    rw [←h]
    simp
  trans := by
    rintro c₁ c₂ c₃ ⟨f, h₁⟩ ⟨g, h₂⟩
    use g * f
    rw [←h₂, ←h₁]
    exact mul_smul g f c₁

/-- Reformulation of the orbit–stabilizer theorem for colorings. -/
theorem orbit_size_eq_index (c : X → Y)
  [Fintype (Equiv.Perm X)]
  [Fintype (MulAction.orbit (Equiv.Perm X) c)]
  [Fintype (MulAction.stabilizer (Equiv.Perm X) c)] :
  Fintype.card (MulAction.orbit (Equiv.Perm X) c)
    = Fintype.card (Equiv.Perm X) /
      Fintype.card (MulAction.stabilizer (Equiv.Perm X) c) := by
  -- 基本等式
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (Equiv.Perm X) c

  -- stabilizer 非空 → 基数 > 0
  have hb : 0 < Fintype.card (MulAction.stabilizer (Equiv.Perm X) c) := by
    simpa using (Fintype.card_pos_iff.mpr ⟨1, by simp [MulAction.stabilizer]⟩)

  -- 利用等式 h: orbit_card * stab_card = group_card
  rw [← h]
  exact (Nat.mul_div_cancel _ hb).symm
end DistinctColorings
