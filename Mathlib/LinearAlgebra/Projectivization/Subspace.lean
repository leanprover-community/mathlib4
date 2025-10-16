/-
Copyright (c) 2022 Michael Blyth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Blyth
-/
import Mathlib.LinearAlgebra.Projectivization.Basic

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
- There is a one-to-one order-preserving correspondence between subspaces of a
  projective space and the submodules of the underlying vector space.
-/


variable (K V : Type*) [Field K] [AddCommGroup V] [Module K V]

namespace Projectivization

open scoped LinearAlgebra.Projectivization

/-- A subspace of a projective space is a structure consisting of a set of points such that:
If two nonzero vectors determine points which are in the set, and the sum of the two vectors is
nonzero, then the point determined by the sum is also in the set. -/
@[ext]
structure Subspace where
  /-- The set of points. -/
  carrier : Set (ℙ K V)
  /-- The addition rule. -/
  mem_add' (v w : V) (hv : v ≠ 0) (hw : w ≠ 0) (hvw : v + w ≠ 0) :
    mk K v hv ∈ carrier → mk K w hw ∈ carrier → mk K (v + w) hvw ∈ carrier

namespace Subspace

variable {K V}

instance : SetLike (Subspace K V) (ℙ K V) where
  coe := carrier
  coe_injective' A B := by
    cases A
    cases B
    simp

@[simp]
theorem mem_carrier_iff (A : Subspace K V) (x : ℙ K V) : x ∈ A.carrier ↔ x ∈ A :=
  Iff.refl _

theorem mem_add (T : Subspace K V) (v w : V) (hv : v ≠ 0) (hw : w ≠ 0) (hvw : v + w ≠ 0) :
    Projectivization.mk K v hv ∈ T →
      Projectivization.mk K w hw ∈ T → Projectivization.mk K (v + w) hvw ∈ T :=
  T.mem_add' v w hv hw hvw

/-- The span of a set of points in a projective space is defined inductively to be the set of points
which contains the original set, and contains all points determined by the (nonzero) sum of two
nonzero vectors, each of which determine points in the span. -/
inductive spanCarrier (S : Set (ℙ K V)) : Set (ℙ K V)
  | of (x : ℙ K V) (hx : x ∈ S) : spanCarrier S x
  | mem_add (v w : V) (hv : v ≠ 0) (hw : w ≠ 0) (hvw : v + w ≠ 0) :
      spanCarrier S (Projectivization.mk K v hv) →
      spanCarrier S (Projectivization.mk K w hw) → spanCarrier S (Projectivization.mk K (v + w) hvw)

/-- The span of a set of points in projective space is a subspace. -/
def span (S : Set (ℙ K V)) : Subspace K V where
  carrier := spanCarrier S
  mem_add' v w hv hw hvw := spanCarrier.mem_add v w hv hw hvw

/-- The span of a set of points contains the set of points. -/
theorem subset_span (S : Set (ℙ K V)) : S ⊆ span S := fun _x hx => spanCarrier.of _ hx

/-- The span of a set of points is a Galois insertion between sets of points of a projective space
and subspaces of the projective space. -/
def gi : GaloisInsertion (span : Set (ℙ K V) → Subspace K V) SetLike.coe where
  choice S _hS := span S
  gc A B :=
    ⟨fun h => le_trans (subset_span _) h, by
      intro h x hx
      induction hx with
      | of => apply h; assumption
      | mem_add => apply B.mem_add; assumption'⟩
  le_l_u _ := subset_span _
  choice_eq _ _ := rfl

/-- The span of a subspace is the subspace. -/
@[simp]
theorem span_coe (W : Subspace K V) : span ↑W = W :=
  GaloisInsertion.l_u_eq gi W

/-- The infimum of two subspaces exists. -/
instance instInf : Min (Subspace K V) :=
  ⟨fun A B =>
    ⟨A ⊓ B, fun _v _w hv hw _hvw h1 h2 =>
      ⟨A.mem_add _ _ hv hw _ h1.1 h2.1, B.mem_add _ _ hv hw _ h1.2 h2.2⟩⟩⟩

/-- Infimums of arbitrary collections of subspaces exist. -/
instance instInfSet : InfSet (Subspace K V) :=
  ⟨fun A =>
    ⟨sInf (SetLike.coe '' A), fun v w hv hw hvw h1 h2 t => by
      rintro ⟨s, hs, rfl⟩
      exact s.mem_add v w hv hw _ (h1 s ⟨s, hs, rfl⟩) (h2 s ⟨s, hs, rfl⟩)⟩⟩

/-- The subspaces of a projective space form a complete lattice. -/
instance : CompleteLattice (Subspace K V) :=
  { __ := completeLatticeOfInf (Subspace K V)
      (by
        refine fun s => ⟨fun a ha x hx => hx _ ⟨a, ha, rfl⟩, fun a ha x hx E => ?_⟩
        rintro ⟨E, hE, rfl⟩
        exact ha hE hx)
    inf_le_left := fun A B _ hx => (@inf_le_left _ _ A B) hx
    inf_le_right := fun A B _ hx => (@inf_le_right _ _ A B) hx
    le_inf := fun _ _ _ h1 h2 _ hx => (le_inf h1 h2) hx }

instance subspaceInhabited : Inhabited (Subspace K V) where default := ⊤

/-- The span of the empty set is the bottom of the lattice of subspaces. -/
@[simp]
theorem span_empty : span (∅ : Set (ℙ K V)) = ⊥ := gi.gc.l_bot

/-- The span of the entire projective space is the top of the lattice of subspaces. -/
@[simp]
theorem span_univ : span (Set.univ : Set (ℙ K V)) = ⊤ := by
  rw [eq_top_iff, SetLike.le_def]
  intro x _hx
  exact subset_span _ (Set.mem_univ x)

/-- The span of a set of points is contained in a subspace if and only if the set of points is
contained in the subspace. -/
theorem span_le_subspace_iff {S : Set (ℙ K V)} {W : Subspace K V} : span S ≤ W ↔ S ⊆ W :=
  gi.gc S W

/-- If a set of points is a subset of another set of points, then its span will be contained in the
span of that set. -/
@[mono]
theorem monotone_span : Monotone (span : Set (ℙ K V) → Subspace K V) :=
  gi.gc.monotone_l

@[gcongr]
lemma span_le_span {s t : Set (ℙ K V)} (hst : s ⊆ t) : span s ≤ span t := monotone_span hst

theorem subset_span_trans {S T U : Set (ℙ K V)} (hST : S ⊆ span T) (hTU : T ⊆ span U) :
    S ⊆ span U :=
  gi.gc.le_u_l_trans hST hTU

/-- The supremum of two subspaces is equal to the span of their union. -/
theorem span_union (S T : Set (ℙ K V)) : span (S ∪ T) = span S ⊔ span T :=
  (@gi K V _ _ _).gc.l_sup

/-- The supremum of a collection of subspaces is equal to the span of the union of the
collection. -/
theorem span_iUnion {ι} (s : ι → Set (ℙ K V)) : span (⋃ i, s i) = ⨆ i, span (s i) :=
  (@gi K V _ _ _).gc.l_iSup

/-- The supremum of a subspace and the span of a set of points is equal to the span of the union of
the subspace and the set of points. -/
theorem sup_span {S : Set (ℙ K V)} {W : Subspace K V} : W ⊔ span S = span (W ∪ S) := by
  rw [span_union, span_coe]

theorem span_sup {S : Set (ℙ K V)} {W : Subspace K V} : span S ⊔ W = span (S ∪ W) := by
  rw [span_union, span_coe]

/-- A point in a projective space is contained in the span of a set of points if and only if the
point is contained in all subspaces of the projective space which contain the set of points. -/
theorem mem_span {S : Set (ℙ K V)} (u : ℙ K V) :
    u ∈ span S ↔ ∀ W : Subspace K V, S ⊆ W → u ∈ W := by
  simp_rw [← span_le_subspace_iff]
  exact ⟨fun hu W hW => hW hu, fun W => W (span S) (le_refl _)⟩

/-- The span of a set of points in a projective space is equal to the infimum of the collection of
subspaces which contain the set. -/
theorem span_eq_sInf {S : Set (ℙ K V)} : span S = sInf { W : Subspace K V| S ⊆ W } := by
  ext x
  simp_rw [mem_carrier_iff, mem_span x]
  refine ⟨fun hx => ?_, fun hx W hW => ?_⟩
  · rintro W ⟨T, hT, rfl⟩
    exact hx T hT
  · exact (@sInf_le _ _ { W : Subspace K V | S ⊆ ↑W } W hW) hx

/-- If a set of points in projective space is contained in a subspace, and that subspace is
contained in the span of the set of points, then the span of the set of points is equal to
the subspace. -/
theorem span_eq_of_le {S : Set (ℙ K V)} {W : Subspace K V} (hS : S ⊆ W) (hW : W ≤ span S) :
    span S = W :=
  le_antisymm (span_le_subspace_iff.mpr hS) hW

/-- The spans of two sets of points in a projective space are equal if and only if each set of
points is contained in the span of the other set. -/
theorem span_eq_span_iff {S T : Set (ℙ K V)} : span S = span T ↔ S ⊆ span T ∧ T ⊆ span S :=
  ⟨fun h => ⟨h ▸ subset_span S, h.symm ▸ subset_span T⟩, fun h =>
    le_antisymm (span_le_subspace_iff.2 h.1) (span_le_subspace_iff.2 h.2)⟩

/-- The submodule corresponding to a projective subspace `s`, consisting of the representatives of
points in `s` together with zero. This is the inverse of `Submodule.projectivization`. -/
def submodule : Projectivization.Subspace K V ≃o Submodule K V where
  toFun s :=
  { carrier := {x | (h : x ≠ 0) → Projectivization.mk K x h ∈ s.carrier}
    add_mem' {x y} hx₁ hy₁ := by
      rcases eq_or_ne x 0 with rfl | hx₂
      · rwa [zero_add]
      rcases eq_or_ne y 0 with rfl | hy₂
      · rwa [add_zero]
      intro hxy
      exact s.mem_add _ _ hx₂ hy₂ hxy (hx₁ hx₂) (hy₁ hy₂)
    zero_mem' h := h.irrefl.elim
    smul_mem' c x h₁ h₂ := by
      convert h₁ (right_ne_zero_of_smul h₂) using 1
      rw [Projectivization.mk_eq_mk_iff']
      exact ⟨c, rfl⟩ }
  invFun s :=
  { carrier := setOf <| Projectivization.lift (↑· ∈ s) <| by
      rintro ⟨-, h⟩ ⟨y, -⟩ c rfl
      exact Iff.eq <| s.smul_mem_iff <| left_ne_zero_of_smul h
    mem_add' _ _ _ _ _ h₁ h₂ := s.add_mem h₁ h₂ }
  left_inv s := by
    ext ⟨x, hx⟩
    exact ⟨fun h => h hx, fun h _ => h⟩
  right_inv s := by
    ext x
    suffices x = 0 → x ∈ s by
      simpa [imp_iff_not_or]
    rintro rfl
    exact s.zero_mem
  map_rel_iff'.mp h₁ := Projectivization.ind fun _ hx h₂ => h₁ (fun _ => h₂) hx
  map_rel_iff'.mpr h₁ _ h₂ hx := h₁ <| h₂ hx

@[simp]
theorem mem_submodule_iff (s : Projectivization.Subspace K V) {v : V} (hv : v ≠ 0) :
    v ∈ submodule s ↔ Projectivization.mk K v hv ∈ s :=
  ⟨fun h => h hv, fun h _ => h⟩

end Subspace

end Projectivization

namespace Submodule

open scoped LinearAlgebra.Projectivization

variable {K V}

/-- The projective subspace corresponding to a submodule `s`, consisting of the one-dimensional
subspaces of `s`. This is the inverse of `Projectivization.Subspace.submodule`. -/
abbrev projectivization : Submodule K V ≃o Projectivization.Subspace K V :=
  Projectivization.Subspace.submodule.symm

@[simp]
theorem mk_mem_projectivization_iff (s : Submodule K V) {v : V} (hv : v ≠ 0) :
    Projectivization.mk K v hv ∈ s.projectivization ↔ v ∈ s := Iff.rfl

theorem mem_projectivization_iff_submodule_le (s : Submodule K V) (x : ℙ K V) :
    x ∈ s.projectivization ↔ x.submodule ≤ s := by
  cases x
  rw [mk_mem_projectivization_iff, Projectivization.submodule_mk,
    Submodule.span_singleton_le_iff_mem]

end Submodule
