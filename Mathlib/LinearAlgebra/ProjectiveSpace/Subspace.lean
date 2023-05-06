/-
Copyright (c) 2022 Michael Blyth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Blyth

! This file was ported from Lean 3 source module linear_algebra.projective_space.subspace
! leanprover-community/mathlib commit 70fd9563a21e7b963887c9360bd29b2393e6225a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.ProjectiveSpace.Basic

/-!
# Subspaces of Projective Space

In this file we define subspaces of a projective space, and show that the subspaces of a projective
space form a complete lattice under inclusion.

## Implementation Details

A subspace of a projective space ℙ K V is defined to be a structure consisting of a subset of
ℙ K V such that if two nonzero vectors in V determine points in ℙ K V which are in the subset, and
the sum of the two vectors is nonzero, then the point determined by the sum of the two vectors is
also in the subset.

## Results

- There is a Galois insertion between the subsets of points of a projective space
  and the subspaces of the projective space, which is given by taking the span of the set of points.
- The subspaces of a projective space form a complete lattice under inclusion.

# Future Work
- Show that there is a one-to-one order-preserving correspondence between subspaces of a
  projective space and the submodules of the underlying vector space.
-/


variable (K V : Type _) [Field K] [AddCommGroup V] [Module K V]

namespace Projectivization

/-- A subspace of a projective space is a structure consisting of a set of points such that:
If two nonzero vectors determine points which are in the set, and the sum of the two vectors is
nonzero, then the point determined by the sum is also in the set. -/
@[ext]
structure Subspace where
  carrier : Set (ℙ K V)
  mem_add' (v w : V) (hv : v ≠ 0) (hw : w ≠ 0) (hvw : v + w ≠ 0) :
    mk K v hv ∈ carrier → mk K w hw ∈ carrier → mk K (v + w) hvw ∈ carrier
#align projectivization.subspace Projectivization.Subspace

namespace Subspace

variable {K V}

instance : SetLike (Subspace K V) (ℙ K V)
    where
  coe := carrier
  coe_injective' A B := by
    cases A
    cases B
    simp

@[simp]
theorem mem_carrier_iff (A : Subspace K V) (x : ℙ K V) : x ∈ A.carrier ↔ x ∈ A :=
  Iff.refl _
#align projectivization.subspace.mem_carrier_iff Projectivization.Subspace.mem_carrier_iff

theorem mem_add (T : Subspace K V) (v w : V) (hv : v ≠ 0) (hw : w ≠ 0) (hvw : v + w ≠ 0) :
    Projectivization.mk K v hv ∈ T →
      Projectivization.mk K w hw ∈ T → Projectivization.mk K (v + w) hvw ∈ T :=
  T.mem_add' v w hv hw hvw
#align projectivization.subspace.mem_add Projectivization.Subspace.mem_add

/-- The span of a set of points in a projective space is defined inductively to be the set of points
which contains the original set, and contains all points determined by the (nonzero) sum of two
nonzero vectors, each of which determine points in the span. -/
inductive spanCarrier (S : Set (ℙ K V)) : Set (ℙ K V)
  | of (x : ℙ K V) (hx : x ∈ S) : span_carrier x
  |
  mem_add (v w : V) (hv : v ≠ 0) (hw : w ≠ 0) (hvw : v + w ≠ 0) :
    span_carrier (Projectivization.mk K v hv) →
      span_carrier (Projectivization.mk K w hw) → span_carrier (Projectivization.mk K (v + w) hvw)
#align projectivization.subspace.span_carrier Projectivization.Subspace.spanCarrier

/-- The span of a set of points in projective space is a subspace. -/
def span (S : Set (ℙ K V)) : Subspace K V
    where
  carrier := spanCarrier S
  mem_add' v w hv hw hvw := spanCarrier.mem_add v w hv hw hvw
#align projectivization.subspace.span Projectivization.Subspace.span

/-- The span of a set of points contains the set of points. -/
theorem subset_span (S : Set (ℙ K V)) : S ⊆ span S := fun x hx => spanCarrier.of _ hx
#align projectivization.subspace.subset_span Projectivization.Subspace.subset_span

/-- The span of a set of points is a Galois insertion between sets of points of a projective space
and subspaces of the projective space. -/
def gi : GaloisInsertion (span : Set (ℙ K V) → Subspace K V) coe
    where
  choice S hS := span S
  gc A B :=
    ⟨fun h => le_trans (subset_span _) h, by
      intro h x hx
      induction hx
      · apply h
        assumption
      · apply B.mem_add
        assumption'⟩
  le_l_u S := subset_span _
  choice_eq _ _ := rfl
#align projectivization.subspace.gi Projectivization.Subspace.gi

/-- The span of a subspace is the subspace. -/
@[simp]
theorem span_coe (W : Subspace K V) : span ↑W = W :=
  GaloisInsertion.l_u_eq gi W
#align projectivization.subspace.span_coe Projectivization.Subspace.span_coe

/-- The infimum of two subspaces exists. -/
instance hasInf : Inf (Subspace K V) :=
  ⟨fun A B =>
    ⟨A ⊓ B, fun v w hv hw hvw h1 h2 =>
      ⟨A.mem_add _ _ hv hw _ h1.1 h2.1, B.mem_add _ _ hv hw _ h1.2 h2.2⟩⟩⟩
#align projectivization.subspace.has_inf Projectivization.Subspace.hasInf

/- warning: projectivization.subspace.has_Inf clashes with projectivization.subspace.has_inf -> Projectivization.Subspace.hasInf
warning: projectivization.subspace.has_Inf -> Projectivization.Subspace.hasInf is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} {V : Type.{u2}} [_inst_1 : Field.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} K V (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)], InfSet.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3)
but is expected to have type
  PUnit.{max (succ (succ u1)) (succ (succ u2))}
Case conversion may be inaccurate. Consider using '#align projectivization.subspace.has_Inf Projectivization.Subspace.hasInfₓ'. -/
/-- Infimums of arbitrary collections of subspaces exist. -/
instance hasInf : InfSet (Subspace K V) :=
  ⟨fun A =>
    ⟨infₛ (coe '' A), fun v w hv hw hvw h1 h2 t =>
      by
      rintro ⟨s, hs, rfl⟩
      exact s.mem_add v w hv hw _ (h1 s ⟨s, hs, rfl⟩) (h2 s ⟨s, hs, rfl⟩)⟩⟩
#align projectivization.subspace.has_Inf Projectivization.Subspace.hasInf

/-- The subspaces of a projective space form a complete lattice. -/
instance : CompleteLattice (Subspace K V) :=
  { (inferInstance : Inf _),
    completeLatticeOfInf (Subspace K V)
      (by
        refine' fun s => ⟨fun a ha x hx => hx _ ⟨a, ha, rfl⟩, fun a ha x hx E => _⟩
        rintro ⟨E, hE, rfl⟩
        exact ha hE hx) with
    inf_le_left := fun A B x hx => hx.1
    inf_le_right := fun A B x hx => hx.2
    le_inf := fun A B C h1 h2 x hx => ⟨h1 hx, h2 hx⟩ }

instance subspaceInhabited : Inhabited (Subspace K V) where default := ⊤
#align projectivization.subspace.subspace_inhabited Projectivization.Subspace.subspaceInhabited

/-- The span of the empty set is the bottom of the lattice of subspaces. -/
@[simp]
theorem span_empty : span (∅ : Set (ℙ K V)) = ⊥ :=
  gi.gc.l_bot
#align projectivization.subspace.span_empty Projectivization.Subspace.span_empty

/-- The span of the entire projective space is the top of the lattice of subspaces. -/
@[simp]
theorem span_univ : span (Set.univ : Set (ℙ K V)) = ⊤ :=
  by
  rw [eq_top_iff, SetLike.le_def]
  intro x hx
  exact subset_span _ (Set.mem_univ x)
#align projectivization.subspace.span_univ Projectivization.Subspace.span_univ

/-- The span of a set of points is contained in a subspace if and only if the set of points is
contained in the subspace. -/
theorem span_le_subspace_iff {S : Set (ℙ K V)} {W : Subspace K V} : span S ≤ W ↔ S ⊆ W :=
  gi.gc S W
#align projectivization.subspace.span_le_subspace_iff Projectivization.Subspace.span_le_subspace_iff

/-- If a set of points is a subset of another set of points, then its span will be contained in the
span of that set. -/
@[mono]
theorem monotone_span : Monotone (span : Set (ℙ K V) → Subspace K V) :=
  gi.gc.monotone_l
#align projectivization.subspace.monotone_span Projectivization.Subspace.monotone_span

theorem subset_span_trans {S T U : Set (ℙ K V)} (hST : S ⊆ span T) (hTU : T ⊆ span U) :
    S ⊆ span U :=
  gi.gc.le_u_l_trans hST hTU
#align projectivization.subspace.subset_span_trans Projectivization.Subspace.subset_span_trans

/-- The supremum of two subspaces is equal to the span of their union. -/
theorem span_union (S T : Set (ℙ K V)) : span (S ∪ T) = span S ⊔ span T :=
  (@gi K V _ _ _).gc.l_sup
#align projectivization.subspace.span_union Projectivization.Subspace.span_union

/-- The supremum of a collection of subspaces is equal to the span of the union of the
collection. -/
theorem span_unionᵢ {ι} (s : ι → Set (ℙ K V)) : span (⋃ i, s i) = ⨆ i, span (s i) :=
  (@gi K V _ _ _).gc.l_supᵢ
#align projectivization.subspace.span_Union Projectivization.Subspace.span_unionᵢ

/-- The supremum of a subspace and the span of a set of points is equal to the span of the union of
the subspace and the set of points. -/
theorem sup_span {S : Set (ℙ K V)} {W : Subspace K V} : W ⊔ span S = span (W ∪ S) := by
  rw [span_union, span_coe]
#align projectivization.subspace.sup_span Projectivization.Subspace.sup_span

theorem span_sup {S : Set (ℙ K V)} {W : Subspace K V} : span S ⊔ W = span (S ∪ W) := by
  rw [span_union, span_coe]
#align projectivization.subspace.span_sup Projectivization.Subspace.span_sup

/-- A point in a projective space is contained in the span of a set of points if and only if the
point is contained in all subspaces of the projective space which contain the set of points. -/
theorem mem_span {S : Set (ℙ K V)} (u : ℙ K V) : u ∈ span S ↔ ∀ W : Subspace K V, S ⊆ W → u ∈ W :=
  by
  simp_rw [← span_le_subspace_iff]
  exact ⟨fun hu W hW => hW hu, fun W => W (span S) (le_refl _)⟩
#align projectivization.subspace.mem_span Projectivization.Subspace.mem_span

/-- The span of a set of points in a projective space is equal to the infimum of the collection of
subspaces which contain the set. -/
theorem span_eq_infₛ {S : Set (ℙ K V)} : span S = infₛ { W | S ⊆ W } :=
  by
  ext
  simp_rw [mem_carrier_iff, mem_span x]
  refine' ⟨fun hx => _, fun hx W hW => _⟩
  · rintro W ⟨T, ⟨hT, rfl⟩⟩
    exact hx T hT
  · exact (@infₛ_le _ _ { W : Subspace K V | S ⊆ ↑W } W hW) x hx
#align projectivization.subspace.span_eq_Inf Projectivization.Subspace.span_eq_infₛ

/-- If a set of points in projective space is contained in a subspace, and that subspace is
contained in the span of the set of points, then the span of the set of points is equal to
the subspace. -/
theorem span_eq_of_le {S : Set (ℙ K V)} {W : Subspace K V} (hS : S ⊆ W) (hW : W ≤ span S) :
    span S = W :=
  le_antisymm (span_le_subspace_iff.mpr hS) hW
#align projectivization.subspace.span_eq_of_le Projectivization.Subspace.span_eq_of_le

/-- The spans of two sets of points in a projective space are equal if and only if each set of
points is contained in the span of the other set. -/
theorem span_eq_span_iff {S T : Set (ℙ K V)} : span S = span T ↔ S ⊆ span T ∧ T ⊆ span S :=
  ⟨fun h => ⟨h ▸ subset_span S, h.symm ▸ subset_span T⟩, fun h =>
    le_antisymm (span_le_subspace_iff.2 h.1) (span_le_subspace_iff.2 h.2)⟩
#align projectivization.subspace.span_eq_span_iff Projectivization.Subspace.span_eq_span_iff

end Subspace

end Projectivization

