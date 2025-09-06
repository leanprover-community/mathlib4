/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import Mathlib.Combinatorics.Quiver.Path

/-! # Strongly-connected Quivers-/

namespace Quiver

section Connected

/-- A quiver is strongly connected if for any two vertices there exists a path of positive
length between them. -/
abbrev IsStronglyConnected (V : Type*) [Quiver V] : Prop :=
  ∀ i j : V, Nonempty { p : Path i j // p.length > 0 }

/-- Expand `IsStronglyConnected` to an existential over paths with positive length. -/
theorem isStronglyConnected_iff_forall_exists_pos_length_path
    (V : Type*) [Quiver V] :
    IsStronglyConnected V ↔ ∀ i j : V, ∃ p : Path i j, 0 < p.length := by
  constructor
  · intro h i j
    rcases h i j with ⟨⟨p, hp⟩⟩
    exact ⟨p, hp⟩
  · intro h i j
    rcases h i j with ⟨p, hp⟩
    exact ⟨⟨p, hp⟩⟩

/-- From strong connectivity, get a path of positive length from `i` to `j`. -/
theorem exists_pos_length_path_of_isStronglyConnected
    {V : Type*} [Quiver V] (h : IsStronglyConnected V) (i j : V) :
    ∃ p : Path i j, 0 < p.length :=
  (isStronglyConnected_iff_forall_exists_pos_length_path V).1 h i j

/-- From strong connectivity, get a cycle of positive length at any vertex. -/
theorem exists_pos_length_cycle_of_isStronglyConnected
    {V : Type*} [Quiver V] (h : IsStronglyConnected V) (i : V) :
    ∃ p : Path i i, 0 < p.length :=
  exists_pos_length_path_of_isStronglyConnected h i i

/-- Equivalence relation for strong connectivity: each direction has a path. -/
def stronglyConnectedSetoid (V : Type*) [Quiver V] : Setoid V :=
  ⟨ (fun a b => (Nonempty (Path a b)) ∧ (Nonempty (Path b a))),
    (fun ?_ => ⟨⟨Path.nil⟩, ⟨Path.nil⟩⟩),
    (fun ⟨hab, hba⟩ => ⟨hba, hab⟩),
    (fun ⟨hab, hba⟩ ⟨hbc, hcb⟩ => ⟨⟨hab.some.comp hbc.some⟩, ⟨hcb.some.comp hba.some⟩⟩) ⟩

/-- Strongly connected components of a quiver. -/
def StronglyConnectedComponent (V : Type*) [Quiver V] : Type _ :=
  Quotient (stronglyConnectedSetoid V)

namespace StronglyConnectedComponent

variable {V} [Quiver V]

/-- The strongly connected component in which a vertex lives. -/
protected def mk : V → StronglyConnectedComponent V :=
  @Quotient.mk' _ (stronglyConnectedSetoid V)

instance : CoeTC V (StronglyConnectedComponent V) := ⟨StronglyConnectedComponent.mk⟩

protected theorem eq (a b : V) :
  (a : StronglyConnectedComponent V) = b
    ↔ (Nonempty (Path a b) ∧ Nonempty (Path b a)) :=
  Quotient.eq''

end StronglyConnectedComponent

end Connected

end Quiver
