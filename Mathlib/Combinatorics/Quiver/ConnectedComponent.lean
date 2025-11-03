/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn, Matteo Cipollina
-/
import Mathlib.Combinatorics.Quiver.Subquiver
import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Combinatorics.Quiver.Symmetric

/-!
## Weakly and strongly connected components

For a quiver `V`, define the type `WeaklyConnectedComponent V` as the quotient of `V` by
the relation which identifies `a` with `b` if there is a path from `a` to `b` in `Symmetrify V`.
(These zigzags can be seen as a proof-relevant analogue of `EqvGen`.)

We define:
* `Quiver.IsStronglyConnected V`: every pair of vertices is connected by a (possibly empty) path.
* `Quiver.IsSStronglyConnected V`: every pair of vertices is connected by a path of positive length.
* `Quiver.StronglyConnectedComponent V`: the quotient by the equivalence relation “paths in both
directions”.

These concepts relate strong and weak connectivity and let us reason about strongly connected
components in directed graphs.
-/

universe v u

namespace Quiver

variable (V : Type*) [Quiver.{u + 1} V]

/-- Two vertices are related in the zigzag setoid if there is a
zigzag of arrows from one to the other. -/
def zigzagSetoid : Setoid V :=
  ⟨fun a b ↦ Nonempty (@Path (Symmetrify V) _ a b), fun _ ↦ ⟨Path.nil⟩, fun ⟨p⟩ ↦
    ⟨p.reverse⟩, fun ⟨p⟩ ⟨q⟩ ↦ ⟨p.comp q⟩⟩

/-- The type of weakly connected components of a directed graph. Two vertices are
in the same weakly connected component if there is a zigzag of arrows from one
to the other. -/
def WeaklyConnectedComponent : Type _ :=
  Quotient (zigzagSetoid V)

namespace WeaklyConnectedComponent

variable {V}

/-- The weakly connected component corresponding to a vertex. -/
protected def mk : V → WeaklyConnectedComponent V :=
  @Quotient.mk' _ (zigzagSetoid V)

instance : CoeTC V (WeaklyConnectedComponent V) :=
  ⟨WeaklyConnectedComponent.mk⟩

instance [Inhabited V] : Inhabited (WeaklyConnectedComponent V) :=
  ⟨show V from default⟩

protected theorem eq (a b : V) :
    (a : WeaklyConnectedComponent V) = b ↔ Nonempty (@Path (Symmetrify V) _ a b) :=
  Quotient.eq''

end WeaklyConnectedComponent

variable {V}

/-- A wide subquiver `H` of `Symmetrify V` determines a wide subquiver of `V`, containing an
arrow `e` if either `e` or its reversal is in `H`. -/
def wideSubquiverSymmetrify (H : WideSubquiver (Symmetrify V)) : WideSubquiver V :=
  fun _ _ ↦ { e | H _ _ (Sum.inl e) ∨ H _ _ (Sum.inr e) }

/-!
## Strongly connected components (directed connectivity)

We define strong connectivity (`IsStronglyConnected`), its positive-length refinement
(`IsSStronglyConnected`), and strongly connected components.
-/

section StronglyConnected

variable (V : Type*) [Quiver V]

/-- Strong connectivity: every ordered pair of vertices is joined by a (possibly empty)
directed path. -/
def IsStronglyConnected : Prop :=
  ∀ i j : V, Nonempty (Path i j)

/-- Positive strong connectivity: every ordered pair of vertices is joined by a directed path
of positive length. -/
def IsSStronglyConnected : Prop :=
  ∀ i j : V, ∃ p : Path i j, 0 < p.length

@[simp] lemma isStronglyConnected_iff :
    IsStronglyConnected V ↔ ∀ i j : V, Nonempty (Path i j) := Iff.rfl

@[simp] lemma isSStronglyConnected_iff :
    IsSStronglyConnected V ↔ ∀ i j : V, ∃ p : Path i j, 0 < p.length := Iff.rfl

lemma IsStronglyConnected.nonempty_path
    (h : IsStronglyConnected V) (i j : V) : Nonempty (Path i j) := h i j

lemma IsSStronglyConnected.exists_pos_path
    (h : IsSStronglyConnected V) (i j : V) : ∃ p : Path i j, 0 < p.length := h i j

lemma IsSStronglyConnected.exists_pos_cycle
    (h : IsSStronglyConnected V) (i : V) : ∃ p : Path i i, 0 < p.length := h i i

lemma IsSStronglyConnected.isStronglyConnected
    (h : IsSStronglyConnected V) : IsStronglyConnected V := by
  intro i j; obtain ⟨p, _⟩ := h i j; exact ⟨p⟩

/-- Equivalence relation identifying vertices connected by directed paths in both directions. -/
def stronglyConnectedSetoid : Setoid V :=
  ⟨fun a b => (Nonempty (Path a b)) ∧ (Nonempty (Path b a)),
   fun _ => ⟨⟨Path.nil⟩, ⟨Path.nil⟩⟩, fun ⟨hab, hba⟩ => ⟨hba, hab⟩, fun ⟨hab, hba⟩ ⟨hbc, hcb⟩ =>
     ⟨⟨hab.some.comp hbc.some⟩, ⟨hcb.some.comp hba.some⟩⟩⟩

/-- The type of strongly connected components (bidirectional reachability classes). -/
def StronglyConnectedComponent : Type _ :=
  Quotient (stronglyConnectedSetoid V)

namespace StronglyConnectedComponent

variable {V}

/-- The canonical map from a vertex to its strongly connected component. -/
protected def mk : V → StronglyConnectedComponent V :=
  @Quotient.mk' _ (stronglyConnectedSetoid V)

instance : Coe V (StronglyConnectedComponent V) :=
  ⟨StronglyConnectedComponent.mk⟩

instance [Inhabited V] : Inhabited (StronglyConnectedComponent V) :=
  ⟨(default : V)⟩

protected lemma eq (a b : V) :
  (a : StronglyConnectedComponent V) = b
    ↔ (Nonempty (Path a b) ∧ Nonempty (Path b a)) := Quotient.eq''

@[simp] lemma mk_eq_mk {a b : V} :
    (StronglyConnectedComponent.mk a : StronglyConnectedComponent V) =
    StronglyConnectedComponent.mk b ↔ (Nonempty (Path a b) ∧ Nonempty (Path b a)) :=
  StronglyConnectedComponent.eq a b

lemma IsSStronglyConnected.pos_cycle (h : IsSStronglyConnected V) (v : V) :
    ∃ p : Path v v, 0 < p.length := h v v

end StronglyConnectedComponent

variable {V}

lemma stronglyConnectedComponent_eq_of_path {a b : V}
    (hab : Nonempty (Path a b)) (hba : Nonempty (Path b a)) :
    (a : StronglyConnectedComponent V) = b :=
  (StronglyConnectedComponent.eq (a := a) (b := b)).2 ⟨hab, hba⟩

lemma exists_path_of_stronglyConnectedComponent_eq {a b : V}
    (h : (a : StronglyConnectedComponent V) = b) :
    (Nonempty (Path a b)) ∧ (Nonempty (Path b a)) :=
  (StronglyConnectedComponent.eq (a := a) (b := b)).1 h

lemma stronglyConnectedComponent_singleton_iff (v : V) :
    (∀ w : V, (w : StronglyConnectedComponent V) = v → w = v) ↔
    (∀ w : V, w ≠ v → ¬(Nonempty (Path v w) ∧ Nonempty (Path w v))) := by
  constructor
  · intro h_singleton w hw_ne h_bidir
    obtain ⟨hab, hba⟩ := h_bidir
    have h_same_scc : (w : StronglyConnectedComponent V) = v :=
      stronglyConnectedComponent_eq_of_path (a := w) (b := v) hba hab
    obtain ⟨rfl⟩ := h_singleton w h_same_scc
    contradiction
  · intro h_no_bidir w h_same_scc
    by_contra hw_ne
    obtain ⟨hab, hba⟩ :=
      exists_path_of_stronglyConnectedComponent_eq (a := w) (b := v) h_same_scc
    exact (h_no_bidir w hw_ne) ⟨hba, hab⟩

lemma IsStronglyConnected.isStronglyConnected_symmetrify (h : IsStronglyConnected V) :
    IsStronglyConnected (Symmetrify V) := by
  intro a b
  obtain ⟨p⟩ := h a b
  induction p with
  | nil => exact ⟨Path.nil⟩
  | cons q e ih => exact ⟨ih.some.cons (Sum.inl e)⟩

lemma IsStronglyConnected.isSStronglyConnected_of_hom (h_sc : IsStronglyConnected V)
    {i₀ j₀ : V} (e₀ : i₀ ⟶ j₀) :
    IsSStronglyConnected V := by
  intro i j
  obtain ⟨p₁⟩ := h_sc i i₀
  obtain ⟨p₂⟩ := h_sc j₀ j
  let p : Path i j := p₁.comp (e₀.toPath.comp p₂)
  have hp_pos : 0 < p.length := by
    simpa [p, Path.length_comp, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      Nat.succ_pos (p₁.length + p₂.length)
  exact ⟨p, hp_pos⟩

end StronglyConnected

end Quiver
