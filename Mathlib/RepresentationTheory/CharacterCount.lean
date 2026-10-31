/-
Copyright (c) 2026 Keith Adler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keith Adler
-/
module

public import Mathlib.RepresentationTheory.Character
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Counting irreducible representations by conjugacy classes

Let `G` be a finite group and `k` an algebraically closed field in which `|G|` is invertible.  The
characters of pairwise non-isomorphic irreducible representations of `G` over `k` are linearly
independent class functions (`Representation.linearIndependent_classFunction`), and the class
functions `ConjClasses G → k` form a `k`-vector space of dimension `Nat.card (ConjClasses G)`.
Hence a family of pairwise non-isomorphic irreducible representations has at most
`Nat.card (ConjClasses G)` members (`Representation.card_le_card_conjClasses`).

This is the upper bound half of "the number of irreducible representations equals the number of
conjugacy classes"; it is all that is needed to show that an explicit list of
`Nat.card (ConjClasses G)` pairwise non-isomorphic irreducibles is complete.
-/

@[expose] public section

namespace Representation

open Module

variable {k G : Type*} [Field k] [Group G]

section classFunction

variable {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- The character of a representation, as a function on conjugacy classes. -/
noncomputable def classFunction (ρ : Representation k G V) : ConjClasses G → k :=
  Quotient.lift ρ.character fun a b (h : IsConj a b) => by
    obtain ⟨c, hc⟩ := isConj_iff.1 h
    rw [← hc, char_conj]

omit [FiniteDimensional k V] in
@[simp]
theorem classFunction_mk (ρ : Representation k G V) (g : G) :
    ρ.classFunction (ConjClasses.mk g) = ρ.character g := rfl

omit [FiniteDimensional k V] in
theorem classFunction_comp_mk (ρ : Representation k G V) :
    ρ.classFunction ∘ ConjClasses.mk = ρ.character := rfl

end classFunction

variable [Finite G] [Invertible (Nat.card G : k)] [IsAlgClosed k]
  {ι : Type*} {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
  [∀ i, FiniteDimensional k (V i)] (ρ : ∀ i, Representation k G (V i))
  [∀ i, (ρ i).IsIrreducible]

omit [Finite G] in
open scoped Classical in
/-- Orthogonality of characters for a family of pairwise non-isomorphic irreducible
representations, in indexed form. -/
theorem char_orthonormal_of_forall_equiv_imp_eq [Fintype G]
    (h : ∀ i j, Nonempty ((ρ i).Equiv (ρ j)) → i = j) (i j : ι) :
    (Nat.card G : k)⁻¹ * ∑ g, (ρ i).character g * (ρ j).character g⁻¹ =
      if i = j then 1 else 0 := by
  rw [char_orthonormal]
  by_cases hij : i = j
  · subst hij
    have : Nonempty ((ρ i).Equiv (ρ i)) := ⟨Representation.Equiv.refl _⟩
    simp [this]
  · have : ¬ Nonempty ((ρ j).Equiv (ρ i)) := fun ⟨φ⟩ => hij (h j i ⟨φ⟩).symm
    simp [this, hij]

/-- The characters of pairwise non-isomorphic irreducible representations are linearly
independent class functions. -/
theorem linearIndependent_classFunction (h : ∀ i j, Nonempty ((ρ i).Equiv (ρ j)) → i = j) :
    LinearIndependent k fun i => (ρ i).classFunction := by
  classical
  let _ := Fintype.ofFinite G
  rw [linearIndependent_iff']
  intro s c hsum j hj
  have hsum' : ∑ i ∈ s, c i • (ρ i).character = 0 := by
    have := congrArg (LinearMap.funLeft k k (ConjClasses.mk : G → ConjClasses G)) hsum
    rw [map_sum, map_zero] at this
    have hL : ∀ i, LinearMap.funLeft k k (ConjClasses.mk : G → ConjClasses G)
        (ρ i).classFunction = (ρ i).character := fun i => classFunction_comp_mk (ρ i)
    simpa only [map_smul, hL] using this
  have h0 : (Nat.card G : k)⁻¹ *
      ∑ x, (∑ i ∈ s, c i • (ρ i).character) x * (ρ j).character x⁻¹ = 0 := by
    rw [hsum']
    simp
  have h1 : (Nat.card G : k)⁻¹ *
      ∑ x, (∑ i ∈ s, c i • (ρ i).character) x * (ρ j).character x⁻¹ = c j := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [mul_assoc, ← Finset.mul_sum]
    rw [Finset.mul_sum]
    simp_rw [mul_left_comm ((Nat.card G : k)⁻¹), char_orthonormal_of_forall_equiv_imp_eq ρ h]
    simp [Finset.sum_ite_eq', hj]
  rw [h0] at h1
  exact h1.symm

/-- A finite group has at most `Nat.card (ConjClasses G)` pairwise non-isomorphic irreducible
representations. -/
theorem card_le_card_conjClasses [Fintype ι]
    (h : ∀ i j, Nonempty ((ρ i).Equiv (ρ j)) → i = j) :
    Fintype.card ι ≤ Nat.card (ConjClasses G) := by
  classical
  have : Finite (ConjClasses G) := Quotient.finite _
  let _ : Fintype (ConjClasses G) := Fintype.ofFinite _
  have := (linearIndependent_classFunction ρ h).fintype_card_le_finrank
  rw [Module.finrank_fintype_fun_eq_card] at this
  exact this.trans Fintype.card_eq_nat_card.le

end Representation
