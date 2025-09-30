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

We reuse `IsPreconnected V` for strong (directed) connectivity, i.e. `∀ i j, Nonempty (Path i j)`.
We also define:
* `Quiver.IsPreconnectedPos V`: every pair of vertices is connected by a path of positive length.
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
We reuse `IsPreconnected V` for directed strong connectivity and add a positive-length variant.
We then define the equivalence relation for strongly connected components and the quotient type.
-/

section StronglyConnected

variable (V : Type*) [Quiver V]

/-- Positive-length directed connectivity: every pair of vertices is connected by some
path of length > 0. -/
def IsPreconnectedPos : Prop :=
  ∀ i j : V, ∃ p : Path i j, 0 < p.length

/-- Unfold `IsPreconnectedPos` to an existential over paths. -/
lemma IsPreconnectedPos_iff :
    IsPreconnectedPos V ↔ ∀ i j : V, ∃ p : Path i j, 0 < p.length := Iff.rfl

/-- From positive connectivity, get a positive-length path from `i` to `j`. -/
lemma IsPreconnectedPos.exists
    {V : Type*} [Quiver V] (h : IsPreconnectedPos V) (i j : V) :
    ∃ p : Path i j, 0 < p.length :=
  h i j

/-- From positive connectivity, get a positive-length cycle at any vertex. -/
lemma IsPreconnectedPos.exists_same
    {V : Type*} [Quiver V] (h : IsPreconnectedPos V) (i : V) :
    ∃ p : Path i i, 0 < p.length :=
  h i i

/-- Compatibility alias: ordinary strong connectivity (directed preconnectedness). -/
abbrev IsStronglyConnected (V : Type*) [Quiver V] : Prop := IsPreconnected V

/-- Compatibility alias: positive-length strong connectivity. -/
abbrev IsSStronglyConnected (V : Type*) [Quiver V] : Prop := IsPreconnectedPos V

/-- Unfold `IsSStronglyConnected` to an existential over paths with positive length. -/
@[simp]
lemma IsSStronglyConnected_iff
    (V : Type*) [Quiver V] :
    IsSStronglyConnected V ↔ ∀ i j : V, ∃ p : Path i j, 0 < p.length := by
  simpa [IsSStronglyConnected] using (IsPreconnectedPos_iff (V))

/-- Unfold `IsStronglyConnected` to the usual preconnectedness. -/
lemma IsStronglyConnected_iff
    (V : Type*) [Quiver V] :
    IsStronglyConnected V ↔ ∀ i j : V, Nonempty (Path i j) := Iff.rfl

/-- Exact alias: `IsStronglyConnected V ↔ IsPreconnected V`. -/
@[simp]
lemma isStronglyConnected_iff_isPreconnected
    (V : Type*) [Quiver V] :
    IsStronglyConnected V ↔ IsPreconnected V := Iff.rfl

/-- From `IsSStronglyConnected`, get a positive-length path from `i` to `j`. -/
lemma IsSStronglyConnected.exists
    {V : Type*} [Quiver V] (h : IsSStronglyConnected V) (i j : V) :
    ∃ p : Path i j, 0 < p.length := by
  simpa [IsSStronglyConnected] using (IsPreconnectedPos.exists (V := V) h i j)

/-- From `IsSStronglyConnected`, get a positive-length cycle at any vertex. -/
lemma IsSStronglyConnected.exists_same
    {V : Type*} [Quiver V] (h : IsSStronglyConnected V) (i : V) :
    ∃ p : Path i i, 0 < p.length := by
  simpa [IsSStronglyConnected] using (IsPreconnectedPos.exists_same (V := V) h i)

/-- Equivalence relation for strong connectivity: paths exist in both directions. -/
def stronglyConnectedSetoid (V : Type*) [Quiver V] : Setoid V :=
  ⟨fun a b => (Nonempty (Path a b)) ∧ (Nonempty (Path b a)),
   fun _ => ⟨⟨Path.nil⟩, ⟨Path.nil⟩⟩,
   fun ⟨hab, hba⟩ => ⟨hba, hab⟩,
   fun ⟨hab, hba⟩ ⟨hbc, hcb⟩ =>
     ⟨⟨hab.some.comp hbc.some⟩, ⟨hcb.some.comp hba.some⟩⟩⟩

/-- Strongly connected components of a quiver (w.r.t. directed reachability). -/
def StronglyConnectedComponent (V : Type*) [Quiver V] : Type _ :=
  Quotient (stronglyConnectedSetoid V)

namespace StronglyConnectedComponent

variable {V} [Quiver V]

/-- The strongly connected component in which a vertex lives. -/
protected def mk : V → StronglyConnectedComponent V :=
  @Quotient.mk' _ (stronglyConnectedSetoid V)

instance : Coe V (StronglyConnectedComponent V) :=
  ⟨StronglyConnectedComponent.mk⟩

instance [Inhabited V] : Inhabited (StronglyConnectedComponent V) := ⟨(default : V)⟩

variable (V : Type*) [Quiver V]

protected lemma eq (a b : V) :
  (a : StronglyConnectedComponent V) = b
    ↔ (Nonempty (Path a b) ∧ Nonempty (Path b a)) :=
  Quotient.eq''

@[simp]
lemma mk_eq_mk {a b : V} :
    (StronglyConnectedComponent.mk a : StronglyConnectedComponent V) =
    StronglyConnectedComponent.mk b ↔
    (Nonempty (Path a b) ∧ Nonempty (Path b a)) :=
  StronglyConnectedComponent.eq V a b

/-- Compatibility alias inside the SCC namespace. -/
lemma IsSStronglyConnected.exists
    {V : Type*} [Quiver V] (h : IsSStronglyConnected V) (v : V) :
    ∃ p : Path v v, 0 < p.length :=
  IsSStronglyConnected.exists_same (V := V) h v

end StronglyConnectedComponent

/-- If there are paths in both directions, then the vertices are in the same SCC. -/
lemma stronglyConnectedComponent_eq_of_path {V : Type*} [Quiver V] {a b : V}
    (hab : Nonempty (Path a b)) (hba : Nonempty (Path b a)) :
    (a : StronglyConnectedComponent V) = b :=
  (StronglyConnectedComponent.eq (V := V) a b).2 ⟨hab, hba⟩

/-- If two vertices are in the same SCC, then there are paths in both directions. -/
lemma exists_path_of_stronglyConnectedComponent_eq {V : Type*} [Quiver V] {a b : V}
    (h : (a : StronglyConnectedComponent V) = b) :
    (Nonempty (Path a b)) ∧ (Nonempty (Path b a)) :=
  (StronglyConnectedComponent.eq (V := V) a b).1 h

/-- A vertex forms a singleton strongly connected component iff
no other distinct vertex has paths in both directions with it. -/
lemma stronglyConnectedComponent_singleton_iff {V : Type*} [Quiver V] (v : V) :
    (∀ w : V, (w : StronglyConnectedComponent V) = v → w = v) ↔
    (∀ w : V, w ≠ v → ¬(Nonempty (Path v w) ∧ Nonempty (Path w v))) := by
  constructor
  · intro h_singleton w hw_ne h_bidir
    obtain ⟨hab, hba⟩ := h_bidir
    have h_same_scc : (w : StronglyConnectedComponent V) = v :=
      stronglyConnectedComponent_eq_of_path hba hab
    have : w = v := h_singleton w h_same_scc
    exact hw_ne this
  · intro h_no_bidir w h_same_scc
    by_contra hw_ne
    obtain ⟨hab, hba⟩ := exists_path_of_stronglyConnectedComponent_eq (V := V) h_same_scc
    exact (h_no_bidir w hw_ne) ⟨hba, hab⟩

/-- Directed preconnectedness implies preconnectedness of the symmetrification. -/
lemma preconnected_symmetrify_of_preconnected {V : Type*} [Quiver V]
    (h : IsPreconnected V) : @IsPreconnected (Symmetrify V) _ := by
  intro a b
  obtain ⟨p⟩ := h a b
  induction p with
  | nil => exact ⟨Path.nil⟩
  | cons q e ih => exact ⟨ih.some.cons (Sum.inl e)⟩

/-- Positive-length directed connectivity implies (ordinary) directed connectivity. -/
lemma isPreconnected_of_pos {V : Type*} [Quiver V]
    (h : IsPreconnectedPos V) : IsPreconnected V := by
  intro i j
  obtain ⟨p, _hp⟩ := h i j
  exact ⟨p⟩

/-- From positive to ordinary strong connectivity. -/
lemma isStronglyConnected_of_pos {V : Type*} [Quiver V]
    (h : IsSStronglyConnected V) : IsStronglyConnected V := by
  simpa [IsStronglyConnected, IsSStronglyConnected] using
    (isPreconnected_of_pos (V := V) (h := h))

/-- If a directedly preconnected quiver has at least one edge, then it is
positively preconnected. -/
lemma isPreconnectedPos_of_hasEdge {V : Type*} [Quiver V]
    (h_pc : IsPreconnected V)
    (h_edge : ∃ (i j : V), Nonempty (i ⟶ j)) :
    IsPreconnectedPos V := by
  intro i j
  obtain ⟨i₀, j₀, ⟨e₀⟩⟩ := h_edge
  obtain ⟨p₁⟩ := h_pc i i₀
  obtain ⟨p₂⟩ := h_pc j₀ j
  let p : Path i j := p₁.comp (e₀.toPath.comp p₂)
  have hp_pos : 0 < p.length := by
    simpa [p, Path.length_comp, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      Nat.succ_pos (p₁.length + p₂.length)
  exact ⟨p, hp_pos⟩

/-- The edge criterion for positive strong connectivity. -/
lemma isStronglyConnectedPos_of_hasEdge {V : Type*} [Quiver V]
    (h_sc : IsStronglyConnected V)
    (h_edge : ∃ (i j : V), Nonempty (i ⟶ j)) :
    IsSStronglyConnected V := by
  simpa [IsSStronglyConnected] using
    (isPreconnectedPos_of_hasEdge (V := V) (h_pc := h_sc) (h_edge := h_edge))

/-- Strong connectivity implies preconnectedness of the symmetrification. -/
lemma isPreconnected_symmetrify_of_isStronglyConnected {V : Type*} [Quiver V]
    (h : IsStronglyConnected V) : @IsPreconnected (Symmetrify V) _ :=
  preconnected_symmetrify_of_preconnected (V := V) h

lemma isStronglyConnected_implies_symmetrify_preconnected {V : Type*} [Quiver V] :
    IsStronglyConnected V → @IsPreconnected (Symmetrify V) _ :=
  isPreconnected_symmetrify_of_isStronglyConnected

end StronglyConnected
end Quiver
